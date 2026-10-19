-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_Repeat
-- name    : MIPRE_Foundations_CL_Repeat
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T14:37:18.683658+00:00
-- url     : https://prove2.me/theorems/e049706d-0349-4110-a4b3-985cd0b089ec
-- title:
--   Direct sums of families of conditionally linear presentations
-- statement:
--   Let $F$ be a semiring, $\iota$ a finite index set, $k \geq 0$, and $\kappa$ a finite index set with a bijection $e : \mathrm{Fin}\,k \times \iota \simeq \kappa$. An $\ell$-level conditionally linear (CL) presentation `CLFun F ι ℓ` (blueprint `def:cl-function`) is `zero` at level $0$ and `cons S L₁ next` at level $\ell + 1$: a register subspace `S : Finset ι`, a register-linear map `L₁ : RegLinear F S` and a continuation `next : (ι → F) → CLFun F ι ℓ`. This bundle holds the nine definitions of `MIPRE.Foundations.CL.Repeat` forming the direct sum of $k$ such presentations (blueprint `lem:cl-famsum`).
--
--   Blocks: `MIPRE.CL.block e i x : ι → F` is the $i$-th block $j \mapsto x_{e(i,j)}$ of `x : κ → F`; `MIPRE.CL.join e v : κ → F` assembles `v : Fin k → ι → F` into one vector; `MIPRE.CL.blockEquiv e : (κ → F) ≃ (Fin k → ι → F)` packages the two; `MIPRE.CL.blockSet e T : Finset κ`, for `T : Fin k → Finset ι`, is the register subspace $\{e(i,j) : j \in T_i\}$. Maps: `MIPRE.CL.RegLinear.blockSum e L : RegLinear F (blockSet e T)`, for `L : (i : Fin k) → RegLinear F (T i)`, is $x \mapsto \mathrm{join}(i \mapsto L_i(\mathrm{block}_i x))$. Presentations: `MIPRE.CL.CLFun.hdS`, `hdL`, `tl` read off `S`, `L₁`, `next` from a `cons S L₁ next`; `MIPRE.CL.CLFun.famSum e ℓ P : CLFun F κ ℓ`, for `P : Fin k → CLFun F ι ℓ`, is `zero` at level $0$ and at level $\ell + 1$
--
--   $$\bigoplus_i P_i = \mathrm{cons}\Big(\mathrm{blockSet}\,(i \mapsto \mathrm{hdS}\,P_i),\ \mathrm{blockSum}\,(i \mapsto \mathrm{hdL}\,P_i),\ v \mapsto \bigoplus_i \mathrm{tl}\,P_i\,(\mathrm{block}_i v)\Big).$$
--
--   The eleven embedded lemmas are the `simp` unfolding rules of these objects and the block algebra the proof fields of `blockEquiv` and `blockSum` use. The module's theorems, among them `eval_famSum`, `IsCLFun.famSum` and `clDist_famSum`, are not part of this bundle. `MIPRE.Repeat.repSampler` (`thm:parallel-repetition`) uses `famSum` with $\kappa = \mathrm{Fin}(k \cdot s(n))$ and `e = finProdFinEquiv` for the $k$ copies of the input sampler's CL function.
--
--   **Formalization Note** `F : Type u` with `[Semiring F]`; `ι : Type v`, `κ : Type w` with `[DecidableEq] [Fintype]`; the general `κ ≃ Fin k × ι` means `Fin (k * s)` needs no reindexing. `hdS`, `hdL`, `tl` match on `cons` and are total since `CLFun F ι (ℓ + 1)` excludes `zero`. `famSum` is structural recursion on the level with the $k$ presentations side by side. The bundle imports the definition bundles of `CL.Register`, `CL.Basic` and `CL.Closure`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Repeat.lean; blueprint lem:cl-famsum

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Repeat.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure

/-!
# Direct sums of families of CL functions: the repeated sampler's functions

The `k`-fold direct sum of a family of `ℓ`-level CL presentations on `F^ι`, as an `ℓ`-level
presentation on `F^κ` for any `κ` in bijection with `Fin k × ι` (`CLFun.famSum`): stage by
stage, the register subspaces are the unions of the blocks' and the maps act blockwise. This is
`lem:cl-closure` (direct sums) iterated over `k` summands, in the form the repeated sampler of
`thm:parallel-repetition` needs: its CL function at index `n` is the direct sum of `k` copies
of the input sampler's on `𝔽₂^{k s(n)}`, `κ = Fin (k · s(n))` and `e = finProdFinEquiv`.

Everything the sampler's query interface asks is blockwise (the four `runs_*` clauses of
`MIPRE.CL.Sampler`), and everything the game needs is blockwise too, so the lemmas are stated
at the level of evaluation rather than as equalities of presentations:

* `eval_famSum`: `(⊕ᵢ Pᵢ)(x) = join (fun i => Pᵢ (block i x))`;
* `eval_truncate_famSum`, `factorOfPrefix_famSum`, `mapOfPrefix_famSum`: the marginals, factor
  spaces and stage maps read off a prefix are blockwise;
* `exactlyOn_famSum`: exactness is inherited (`lem:cl-kth`, item (2));
* `clDist_famSum`: the conditionally linear distribution of a direct sum is the product of the
  blocks' — the repeated game is the direct repetition.

The vocabulary: `block e i x` is the `i`-th block of `x : κ → F`, `join e v` assembles blocks,
and `blockSet e T` is the register subspace assembled from one per block.
-/

namespace MIPRE.CL

-- The block vocabulary is stated once for all the instances the file uses; the linter would
-- otherwise ask for an `omit` on every other lemma.
set_option linter.unusedSectionVars false

universe u v w

variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {κ : Type w}
  [DecidableEq κ] [Fintype κ] {k : ℕ}

/-! ## Blocks -/

section Blocks

variable (e : Fin k × ι ≃ κ)

/-- The `i`-th block of a vector on `κ ≃ Fin k × ι`. -/
def block (i : Fin k) (x : κ → F) : ι → F := fun j => x (e (i, j))

/-- The vector assembled from `k` blocks. -/
def join (v : Fin k → ι → F) : κ → F := fun p => v (e.symm p).1 (e.symm p).2

@[simp] theorem block_join (v : Fin k → ι → F) (i : Fin k) : block e i (join e v) = v i := by
  funext j; simp [block, join]

@[simp] theorem join_block (x : κ → F) : (join e fun i => block e i x) = x := by
  funext p; simp [block, join]

@[simp] theorem block_add (i : Fin k) (x y : κ → F) :
    block e i (x + y) = block e i x + block e i y := rfl

@[simp] theorem block_zero (i : Fin k) : block e i (0 : κ → F) = 0 := rfl

@[simp] theorem join_apply (v : Fin k → ι → F) (p : κ) :
    join e v p = v (e.symm p).1 (e.symm p).2 := rfl

@[simp] theorem join_apply_e (v : Fin k → ι → F) (i : Fin k) (j : ι) :
    join e v (e (i, j)) = v i j := by simp [join]

/-- The blocks of a vector, as an equivalence. -/
def blockEquiv : (κ → F) ≃ (Fin k → ι → F) where
  toFun x i := block e i x
  invFun := join e
  left_inv x := join_block e x
  right_inv v := funext fun i => block_join e v i

/-- The register subspace assembled from one register subspace per block. -/
def blockSet (T : Fin k → Finset ι) : Finset κ :=
  Finset.univ.filter fun p => (e.symm p).2 ∈ T (e.symm p).1

@[simp] theorem mem_blockSet (T : Fin k → Finset ι) (p : κ) :
    p ∈ blockSet e T ↔ (e.symm p).2 ∈ T (e.symm p).1 := by simp [blockSet]

@[simp] theorem blockSet_univ : blockSet e (fun _ => (Finset.univ : Finset ι)) = Finset.univ := by
  ext p; simp

theorem block_proj (T : Fin k → Finset ι) (i : Fin k) (x : κ → F) :
    block e i (proj (blockSet e T) x) = proj (T i) (block e i x) := by
  funext j
  simp [block, proj_apply]

end Blocks

/-! ## Direct sums of register-linear maps -/

namespace RegLinear

variable (e : Fin k × ι ≃ κ)

/-- The direct sum of a family of maps, one per block. -/
def blockSum {T : Fin k → Finset ι} (L : (i : Fin k) → RegLinear F (T i)) :
    RegLinear F (blockSet e T) where
  toLinearMap :=
    { toFun := fun x => join e fun i => L i (block e i x)
      map_add' := fun x y => by
        funext p
        simp only [join_apply, block_add, map_add, Pi.add_apply]
      map_smul' := fun c x => by
        funext p
        have : ∀ i, block e i (c • x) = c • block e i x := fun i => rfl
        simp only [join_apply, this, map_smul, RingHom.id_apply, Pi.smul_apply] }
  proj_comp_proj' := fun x => by
    funext p
    simp only [LinearMap.coe_mk, AddHom.coe_mk, join_apply, block_proj, RegLinear.apply_proj]
    rw [MIPRE.CL.proj_apply]
    by_cases h : p ∈ blockSet e T
    · rw [if_pos h]; rfl
    · rw [if_neg h]
      rw [mem_blockSet] at h
      have := congrFun ((L (e.symm p).1).proj_apply (block e (e.symm p).1 x)) (e.symm p).2
      rw [MIPRE.CL.proj_apply, if_neg h] at this
      exact this

@[simp] theorem blockSum_apply {T : Fin k → Finset ι} (L : (i : Fin k) → RegLinear F (T i))
    (x : κ → F) : blockSum e L x = join e fun i => L i (block e i x) := rfl

end RegLinear

/-! ## Direct sums of families of presentations -/

namespace CLFun

variable {ℓ : ℕ}

/-- The register subspace at the head of a presentation of positive level. -/
def hdS : CLFun F ι (ℓ + 1) → Finset ι
  | cons S _ _ => S

/-- The map at the head of a presentation of positive level. -/
def hdL : (P : CLFun F ι (ℓ + 1)) → RegLinear F P.hdS
  | cons _ L₁ _ => L₁

/-- The continuation of a presentation of positive level. -/
def tl : CLFun F ι (ℓ + 1) → (ι → F) → CLFun F ι ℓ
  | cons _ _ next => next

variable (e : Fin k × ι ≃ κ)

/-- The direct sum of a family of presentations, one per block, on `F^κ`, `κ ≃ Fin k × ι`. -/
def famSum : (ℓ : ℕ) → (Fin k → CLFun F ι ℓ) → CLFun F κ ℓ
  | 0, _ => zero
  | ℓ + 1, P =>
    cons (blockSet e fun i => (P i).hdS) (RegLinear.blockSum e fun i => (P i).hdL)
      fun v => famSum ℓ fun i => (P i).tl (block e i v)

@[simp] theorem famSum_zero (P : Fin k → CLFun F ι 0) : famSum e 0 P = zero := rfl

end CLFun

/-! ## The paper's statement, and the distribution -/

end MIPRE.CL


