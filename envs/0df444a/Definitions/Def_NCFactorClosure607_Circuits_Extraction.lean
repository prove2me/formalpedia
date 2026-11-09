-- Prove2me | Definitions.Def_NCFactorClosure607_Circuits_Extraction
-- name    : NCFactorClosure607_Circuits_Extraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:18.248962+00:00
-- url     : https://prove2.me/theorems/77b21389-0616-45a2-86c2-f5e62e0f0a28
-- title:
--   The factor-extraction circuit constructions (matrix substitution, reversal)
-- statement:
--   Let $C$ be a circuit and fix cofactor data with word $v$ of length $b$, coefficient $c$ and suffix coefficients $d_\ell$.
--
--   1. **Right-cofactor removal** $\mathrm{extractRight}(C,\text{data})$. If $b\ge1$: replace every constant input $a$ of $C$ by the scalar matrix $aI_{b+2}$, every variable input $x$ by $M_x$, every addition gate by matrix addition and every multiplication gate by ordered matrix multiplication, writing each matrix entry with ordinary gates (an entry of a product is $\sum_r A_{p,r}B_{r,q}$) and sharing previously computed entries; then multiply the $(*,b)$ entry of the output matrix by the constant $c^{-1}$. If $b=0$: multiply the output of $C$ by the constant $c^{-1}$.
--   2. **Left-cofactor removal** $\mathrm{extractLeft}(C,\text{data})$: reverse $C$, apply right-cofactor removal, reverse the result.
--   3. **Central factor** $\mathrm{extractCentral}(C,\text{data}_b,\text{data}_a)$: apply right-cofactor removal with $\text{data}_b$, reverse, apply right-cofactor removal with $\text{data}_a$, reverse.
--
--   The constructions read only the input circuit and the supplied cofactor data. The constants they may introduce are $0$, $1$, $c^{-1}$ and the reset labels $-d_\ell c^{-1}$ $(1\le\ell\le b)$; this set is recorded as `constSet`.
--
--   **Formalization Note** The constructions are explicit Lean functions of the gate list and the data. A matrix entry of a product gate is computed by $b+2$ multiplication gates and $b+1$ addition gates; scalar and variable inputs give $(b+2)^2$ constant or variable gates, and addition gates give $(b+2)^2$ addition gates.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.9–10, proof of Lemma 4.1; p.10, proof of Theorem 1.1; p.2–3, Theorem 1.1 (cofactor data); p.6, §2.1 (constants); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Circuit
import Definitions.Def_NCFactorClosure607_Circuits_TransitionMatrices

/-!
# The factor-extraction circuit constructions

Arvind–Joglekar, *Factor Closure in Noncommutative Algebraic Complexity*,
STOC 2027 submission #607, proof of Lemma 4.1, p.9–10, and proof of Theorem 1.1, p.10.

`extractRight C data` is the matrix-substitution circuit of Lemma 4.1: every scalar input `a`
is replaced by `a·I_{b+2}`, every variable input `x` by `M_x`, every addition gate by matrix
addition and every multiplication gate by ordered matrix multiplication, each matrix entry being
written out with ordinary gates (an entry of a product is `Σ_r A_{p,r} B_{r,q}`), previously
computed entries being shared; finally the `(∗, b)` entry of the output matrix is multiplied by
the constant `c⁻¹`. For a scalar cofactor (`b = 0`) the output of `C` is multiplied by `c⁻¹`.
The construction reads only the circuit `C` and the cofactor data.
-/

namespace NCFactorClosure607.Circuits

namespace Extraction

variable {F : Type*} [Field F] {X : Type*}

/-- Append one gate; return the new gate list and the position of the appended gate. -/
def push (acc : List (Gate F X)) (g : Gate F X) : List (Gate F X) × ℕ :=
  (acc ++ [g], acc.length)

/-- Append gates computing `Σ_r (gate iᵣ) * (gate jᵣ)` for the operand pairs `(iᵣ, jᵣ)`
(products in this order, summed left to right); return the new list and the position of the
gate holding the sum. -/
def sumOfProducts (acc : List (Gate F X)) : List (ℕ × ℕ) → List (Gate F X) × ℕ
  | [] => push acc (.const 0)
  | (i, j) :: rest =>
      rest.foldl
        (fun (st : List (Gate F X) × ℕ) (pr : ℕ × ℕ) =>
          let st₁ := push st.1 (.mul pr.1 pr.2)
          push st₁.1 (.add st.2 st₁.2))
        (push acc (.mul i j))

/-- The states `∗, 0, 1, …, b` in this order. -/
def states (b : ℕ) : List (State b) := none :: (List.finRange (b + 1)).map some

/-- All index pairs `(p, q)` of a `(b+2) × (b+2)` matrix, row by row. -/
def entryList (b : ℕ) : List (State b × State b) :=
  (states b).flatMap fun p => (states b).map fun q => (p, q)

/-- For every matrix entry `(p, q)` in turn, append the gates produced by `gadget` for that
entry; return the new gate list and the table of positions of the entry gates. -/
def block {b : ℕ} (acc : List (Gate F X))
    (gadget : List (Gate F X) → State b → State b → List (Gate F X) × ℕ) :
    List (Gate F X) × (State b → State b → ℕ) :=
  (entryList b).foldl
    (fun (st : List (Gate F X) × (State b → State b → ℕ)) (pq : State b × State b) =>
      let r := gadget st.1 pq.1 pq.2
      (r.1, fun p q => if p = pq.1 ∧ q = pq.2 then r.2 else st.2 p q))
    (acc, fun _ _ => 0)

/-- The block of gates replacing one original gate: `tabs` holds, for each earlier original
gate, the positions of the gates computing the entries of its matrix. -/
noncomputable def gateBlock (data : CofactorData F X)
    (tabs : List (State data.b → State data.b → ℕ)) (acc : List (Gate F X)) :
    Gate F X → List (Gate F X) × (State data.b → State data.b → ℕ)
  | .const a => block acc fun acc p q => push acc (.const (if p = q then a else 0))
  | .var x => block acc fun acc p q =>
      match p, q with
      | none, none => push acc (.var x)
      | none, some j => push acc (.const (data.eraseMatrix x 0 j))
      | some _, none => push acc (.const 0)
      | some i, some j => push acc (.const (data.eraseMatrix x i j))
  | .add i j => block acc fun acc p q =>
      push acc (.add ((tabs.getD i fun _ _ => 0) p q) ((tabs.getD j fun _ _ => 0) p q))
  | .mul i j => block acc fun acc p q =>
      sumOfProducts acc ((states data.b).map fun r =>
        ((tabs.getD i fun _ _ => 0) p r, (tabs.getD j fun _ _ => 0) r q))

/-- The matrix-substitution gates for the whole circuit, with the entry-position table of every
original gate. -/
noncomputable def substGates (data : CofactorData F X) (C : Circuit F X) :
    List (Gate F X) × List (State data.b → State data.b → ℕ) :=
  C.gates.foldl
    (fun st g => let r := gateBlock data st.2 st.1 g; (r.1, st.2 ++ [r.2]))
    ([], [])

end Extraction

open Extraction

/-- Removal of a right cofactor (Lemma 4.1 and Theorem 3.1): from a circuit `C` and cofactor
data for a right cofactor, the circuit computing `c⁻¹ [C(M)]_{∗,b}` (for `b ≥ 1`) or
`c⁻¹ · C` (for `b = 0`). -/
noncomputable def extractRight {F : Type*} [Field F] {X : Type*} (C : Circuit F X)
    (data : CofactorData F X) : Circuit F X :=
  if data.b = 0 then
    ⟨C.gates ++ [.const data.c⁻¹, .mul C.gates.length (C.gates.length - 1)]⟩
  else
    let r := substGates data C
    let out := (r.2.getLastD fun _ _ => 0) none (some (Fin.last data.b))
    ⟨r.1 ++ [.const data.c⁻¹, .mul r.1.length out]⟩

/-- Removal of a left cofactor (proof of Theorem 1.1, p.10): reverse the circuit, remove the
right cofactor with the data (for `rev` of the left cofactor), reverse again. -/
noncomputable def extractLeft {F : Type*} [Field F] {X : Type*} (C : Circuit F X)
    (data : CofactorData F X) : Circuit F X :=
  (extractRight C.reverse data).reverse

/-- Central factor (proof of Theorem 1.1, p.10): from `f = a g b`, first remove the right
cofactor `b` (data `dataB`), then reverse, remove the right cofactor `rev a` (data `dataA`)
and reverse again. -/
noncomputable def extractCentral {F : Type*} [Field F] {X : Type*} (C : Circuit F X)
    (dataB dataA : CofactorData F X) : Circuit F X :=
  (extractRight (extractRight C dataB).reverse dataA).reverse

/-- The field constants a construction from the data may introduce (§2.1, p.6): `0`, `1`,
`c⁻¹` and the reset labels `-d_ℓ · c⁻¹` (`1 ≤ ℓ ≤ b`). -/
def CofactorData.constSet {F : Type*} [Field F] {X : Type*} (data : CofactorData F X) :
    Set F :=
  {0, 1, data.c⁻¹} ∪
    {a | ∃ (i : ℕ) (hi : i < data.suffixCoeffs.length), a = -(data.suffixCoeffs[i] * data.c⁻¹)}

end NCFactorClosure607.Circuits


