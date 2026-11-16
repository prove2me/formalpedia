-- Prove2me | Definitions.Def_NCFactorClosure607_Circuits_Supplement_FormulaExtraction
-- name    : NCFactorClosure607_Circuits_Supplement_FormulaExtraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:06:15.056716+00:00
-- url     : https://prove2.me/theorems/fd0eb8b8-cfd2-4358-bf05-40925c8716e7
-- title:
--   The direct formula construction for the cofactor-removal map $T$, with field-operation and writing counts
-- statement:
--   Fix cofactor data: a word $v=v_1\cdots v_b$, a scalar $c$ and suffix coefficients $d_1,\dots,d_b$, with reset labels $-\alpha_\ell=-d_\ell c^{-1}$ and scalar transition matrices $A_x\in F^{(b+1)\times(b+1)}$ on the erasing states $0,\dots,b$ ($(A_x)_{i,i+1}=1$ and $(A_x)_{i,0}=-\alpha_{i+1}$ when $v_{i+1}=x$, all other entries $0$). For a formula $\Phi$ with root $\rho$ and $b\ge1$ the construction $\mathrm{formulaExtract}(\Phi,\text{data})$ is:
--
--   1. compute $c^{-1}$ and the reset labels;
--   2. bottom-up, compute for every node $U$ the scalar matrix $C_U$: $A_x$ at a variable leaf $x$, $aI$ at a constant leaf $a$, $C_V+C_W$ at an addition node and $C_VC_W$ at a multiplication node with children $V,W$;
--   3. top-down from the root, with the column $z=e_b$, build formulas $F(U,z)$ for $R_Uz$ (where $R_U$ is the row of polynomial entries of $p_U(M)$ in the copying state):
--   $$F(U,z)=0\ \text{(constant leaf)},\qquad F(U,z)=e_0^{\mathsf T}A_xz\ \text{(variable leaf, one constant leaf)},$$
--   $$F(U,z)=F(V,z)+F(W,z),\qquad F(U,z)=p_V\cdot F(W,z)+F(V,C_Wz),$$
--   where $p_V$ is an unchanged copy of the original subtree at $V$;
--   4. output $c^{-1}\cdot F(\rho,e_b)$.
--
--   For a scalar cofactor ($b=0$) the output is $c^{-1}\cdot\Phi$.
--
--   The result records the output formula, the number of **field operations** performed (each addition, multiplication, negation and inversion in $F$, counted by the dot-product and matrix primitives that perform them), and the number of **writing operations** (one for every formula node written, including the nodes of copied subtrees).
--
--   This is the construction whose output size and cost Lemma 5.1 bounds.
--
--   **Formalization Note** Field operations are counted through a dot product $\sum_r u_rv_r$ that charges one operation per multiplication and per addition it performs; matrix addition charges one operation per entry. Letter comparisons are not field operations and are not counted.
--
--   The scalar matrices and columns are materialized as finite lists of computed entries. The inverse of $c$ is computed once. Later lookups perform no field operations, so the recorded counts include the arithmetic actually used by the construction.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), pp.10–12, §5.1, Lemma 5.1 and its proof (eqs. (10)–(15), paragraph Construction time); p.9, §4, matrices A_x and eq. (7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_TransitionMatrices
import Definitions.Def_NCFactorClosure607_Circuits_Supplement_Formula

/-!
# The direct formula construction for the cofactor-removal map, with operation counts

Arvind–Joglekar, *Factor Closure in Noncommutative Algebraic Complexity*,
STOC 2027 submission #607, §5.1, Lemma 5.1 and its proof, p.10–12 (recursions (10)–(15) and
the paragraph "Construction time").

Fix cofactor data with word `v` of length `b ≥ 1`, coefficient `c` and suffix coefficients
`d_ℓ` (base definition `NCFactorClosure607_Circuits_CofactorNFA`). For a formula `Φ` the
construction proceeds as in the proof of Lemma 5.1:

1. compute `c⁻¹` and the reset labels `-α_ℓ = -d_ℓ c⁻¹`;
2. bottom-up, compute for every node `U` the scalar `(b+1) × (b+1)` matrix `C_U`
   (`A_x` at a variable leaf, `a I` at a constant leaf, `C_V + C_W` or `C_V C_W` at internal
   nodes);
3. top-down from the root with the column `z = e_b`, build the formula `F(U, z)` by
   `F(U,z) = 0` at a constant leaf, `F(U,z) = e₀ᵀ A_x z` (one constant leaf) at a variable leaf,
   (11) `F(U,z) = F(V,z) + F(W,z)` and (12) `F(U,z) = p_V · F(W,z) + F(V, C_W z)`, where `p_V`
   is an unchanged copy of the original left subtree;
4. output `c⁻¹ · F(ρ, e_b)`.

For a scalar cofactor (`b = 0`) the output is `c⁻¹ · Φ`.

Every field operation (addition, multiplication, negation, inversion in `F`) performed by the
construction is counted, through the primitive `dot` product and the matrix operations below,
which count one operation per field addition or multiplication they perform. Every formula node
written by the construction (new nodes and the nodes of the copied subtrees) counts as one
writing operation.
-/

namespace NCFactorClosure607.Circuits.Supplement

open NCFactorClosure607.Circuits

namespace FormulaExtraction

variable {F : Type*} [Field F] {X : Type*}

/-- Evaluate each entry once and store its value and cost in finite lists. The returned
function only looks up stored values: later queries perform no field operations. -/
def tabulateCounted {α : Type*} (fallback : α) (n : ℕ) (f : Fin n → α × ℕ) :
    (Fin n → α) × ℕ :=
  let entries := List.ofFn f
  let values := entries.map Prod.fst
  (fun i => values.getD i.val fallback, (entries.map Prod.snd).sum)

/-- The dot product `Σ_{r<n} u_r v_r`, computed left to right, together with the number of field
operations it performs (`n` multiplications and `n - 1` additions when `n ≥ 1`). -/
def dot (n : ℕ) (u v : Fin n → F) : F × ℕ :=
  (List.finRange n).foldl
    (fun (acc : F × ℕ) (r : Fin n) =>
      if r.val = 0 then (u r * v r, acc.2 + 1) else (acc.1 + u r * v r, acc.2 + 2))
    (0, 0)

/-- Matrix addition, entry by entry: `n²` field additions. -/
def matAdd (n : ℕ) (A B : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F × ℕ :=
  tabulateCounted (fun _ => 0) n fun i =>
    tabulateCounted 0 n fun j => (A i j + B i j, 1)

/-- Matrix multiplication, every entry by the dot product of a row and a column; the count is
the sum of the counts of the `n²` dot products. -/
def matMul (n : ℕ) (A B : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F × ℕ :=
  tabulateCounted (fun _ => 0) n fun i =>
    tabulateCounted 0 n fun j => dot n (fun r => A i r) (fun r => B r j)

/-- Matrix times column vector, every entry by a dot product. -/
def matVec (n : ℕ) (A : Matrix (Fin n) (Fin n) F) (z : Fin n → F) : (Fin n → F) × ℕ :=
  tabulateCounted 0 n fun i => dot n (fun r => A i r) z

/-- Step 1: `c⁻¹` and the reset labels `-α_{i+1} = -(d_{i+1} · c⁻¹)` (`0 ≤ i < b`), with their
cost: one inversion, then one multiplication and one negation per label. -/
noncomputable def resetLabels (data : CofactorData F X) : F × (Fin data.b → F) × ℕ :=
  let cinv := data.c⁻¹
  let labels := tabulateCounted 0 data.b fun i =>
    (-(data.suffixCoeffs.getD i.val 0 * cinv), 2)
  (cinv, labels.1, 1 + labels.2)

open scoped Classical in
/-- The scalar matrix `A_x` on the erasing states `0, …, b`, read off from the precomputed reset
labels (no field operation): its `(i, i+1)` entry is `1` and its `(i, 0)` entry is `-α_{i+1}`
when `v_{i+1} = x` (`0 ≤ i < b`); all other entries are `0` (§3.1 and §4, p.6, p.9). -/
noncomputable def leafMatrix (data : CofactorData F X) (negAlpha : Fin data.b → F) (x : X) :
    Matrix (Fin (data.b + 1)) (Fin (data.b + 1)) F :=
  Matrix.of fun i j =>
    if h : i.val < data.b then
      if data.letter ⟨i.val, h⟩ = x then
        (if j.val = i.val + 1 then 1 else if j.val = 0 then negAlpha ⟨i.val, h⟩ else 0)
      else 0
    else 0

/-- What the bottom-up pass returns for a node `U`: the matrix `C_U`, the number of field
operations spent computing the matrices of the subtree, and the top-down builder
`z ↦ (F(U, z), field operations, writing operations)`. -/
structure Stage (F : Type*) (X : Type*) (n : ℕ) where
  mat : Matrix (Fin n) (Fin n) F
  matOps : ℕ
  build : (Fin n → F) → Formula F X × ℕ × ℕ

/-- Steps 2 and 3: the bottom-up computation of the matrices `C_U` (each computed once), and
the builder of the formulas `F(U, z)` following (11) and (12). -/
noncomputable def pass (data : CofactorData F X) (negAlpha : Fin data.b → F) :
    Formula F X → Stage F X (data.b + 1)
  | .const a =>
      { mat := Matrix.of fun i j => if i = j then a else 0
        matOps := 0
        build := fun _ => (.const 0, 0, 1) }
  | .var x =>
      { mat := leafMatrix data negAlpha x
        matOps := 0
        build := fun z =>
          let r := dot (data.b + 1) (fun j => leafMatrix data negAlpha x 0 j) z
          (.const r.1, r.2, 1) }
  | .add V W =>
      let sV := pass data negAlpha V
      let sW := pass data negAlpha W
      let m := matAdd (data.b + 1) sV.mat sW.mat
      { mat := m.1
        matOps := sV.matOps + sW.matOps + m.2
        build := fun z =>
          let rV := sV.build z
          let rW := sW.build z
          (.add rV.1 rW.1, rV.2.1 + rW.2.1, rV.2.2 + rW.2.2 + 1) }
  | .mul V W =>
      let sV := pass data negAlpha V
      let sW := pass data negAlpha W
      let m := matMul (data.b + 1) sV.mat sW.mat
      { mat := m.1
        matOps := sV.matOps + sW.matOps + m.2
        build := fun z =>
          let z' := matVec (data.b + 1) sW.mat z
          let rW := sW.build z
          let rV := sV.build z'.1
          (.add (.mul V rW.1) rV.1, z'.2 + rW.2.1 + rV.2.1, rW.2.2 + rV.2.2 + V.size + 2) }

end FormulaExtraction

open FormulaExtraction

/-- The output of the formula construction: the formula, the number of field operations and
the number of formula-writing operations. -/
structure FormulaExtractionResult (F : Type*) (X : Type*) where
  formula : Formula F X
  fieldOps : ℕ
  writeOps : ℕ

/-- The direct formula construction of Lemma 5.1 (p.10–12) applied to the formula `Φ` and
cofactor data `data`. For `b ≥ 1`: steps 1–4 above, the output being `c⁻¹ · F(ρ, e_b)`. For a
scalar cofactor (`b = 0`): the output is `c⁻¹ · Φ`, computed with one field operation (the
inversion) and two new nodes. The construction reads only `Φ` and the data. -/
noncomputable def formulaExtract {F : Type*} [Field F] {X : Type*} (Φ : Formula F X)
    (data : CofactorData F X) : FormulaExtractionResult F X :=
  if data.b = 0 then
    { formula := .mul (.const data.c⁻¹) Φ, fieldOps := 1, writeOps := 2 }
  else
    let pre := resetLabels data
    let s := pass data pre.2.1 Φ
    let r := s.build fun j => if j = Fin.last data.b then 1 else 0
    { formula := .mul (.const pre.1) r.1
      fieldOps := pre.2.2 + s.matOps + r.2.1
      writeOps := r.2.2 + 2 }

end NCFactorClosure607.Circuits.Supplement


