-- Prove2me | Definitions.Def_MIPRE_Foundations_StateDistance
-- name    : MIPRE_Foundations_StateDistance
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:09:47.898974+00:00
-- url     : https://prove2.me/theorems/660b260e-76f3-46d7-869c-e246b08bc25b
-- title:
--   Definitions of StateDistance: The state-dependent distance on a bipartite state Every soundness argument in the Pauli basis test's appendix compares…
-- statement:
--   The definitions of the module `MIPRE.Foundations.StateDistance` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The state-dependent distance on a bipartite state. Every soundness argument in the Pauli basis test's appendix compares operators in the distance `A^x ≈_δ B^x` ⟺ `𝔼_{x ∼ μ} ⟨ψ| (A^x - B^x)† (A^x - B^x) |ψ⟩ ≤ δ`, where the operators act on **Alice's factor** of a bipartite state `|ψ⟩ ∈ ℂ^{dA} ⊗ ℂ^{dB}`. That is not the distance `MIPRE/Foundations/Distances.lean` defines: `povmDistance` and `IsPOVMClose` use the normalized Hilbert--Schmidt norm, which is the *tracial* — synchronous — specialization, and `MIPRE/Foundations/Closeness.lean` says so in its own docstring. This file is the…
--
--   **Definitions** (5): `MIPRE.stateNorm` (`‖(M ⊗ Id)|ψ⟩‖`.); `MIPRE.stateSqNorm` (`⟨ψ| M† M ⊗ Id |ψ⟩`, the squared state-dependent norm.); `MIPRE.stateVec` (`(M ⊗ Id)|ψ⟩`, as a vector of `EuclideanSpace ℂ (dA × dB)`.); `MIPRE.stateVecB` (`(Id ⊗ N)|ψ⟩`, as a vector of `EuclideanSpace ℂ (dA × dB)`: the `stateVec` of Bob's factor.); `MIPRE.swapVec` (`|ψ⟩` with its two tensor factors exchanged.).
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `stateVecB_smul`, `stateVec_add`, `stateVec_neg`, `stateVec_smul`, `stateVec_sub`, `stateVec_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.StateDistance` (`MIPRE/Foundations/StateDistance.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 4 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/StateDistance.lean; blueprint def:cross-distance, def:state-distance

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/StateDistance.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound

/-!
# The state-dependent distance on a bipartite state

Every soundness argument in the Pauli basis test's appendix compares operators in the distance

`A^x ≈_δ B^x` ⟺ `𝔼_{x ∼ μ} ⟨ψ| (A^x - B^x)† (A^x - B^x) |ψ⟩ ≤ δ`,

where the operators act on **Alice's factor** of a bipartite state `|ψ⟩ ∈ ℂ^{dA} ⊗ ℂ^{dB}`. That
is not the distance `MIPRE/Foundations/Distances.lean` defines: `povmDistance` and
`IsPOVMClose` use the normalized Hilbert--Schmidt norm, which is the *tracial* — synchronous —
specialization, and `MIPRE/Foundations/Closeness.lean` says so in its own docstring. This file
is the state-dependent one, and it is what blueprint `def:state-distance` names.

Two deliberate departures from the paper's `qld-prelim.tex`:

* **no `O(·)` inside the definition.** The paper writes `≤ O(δ)`; here the relation is
  `stateDist μ ψ A B ≤ δ` and the constants appear in the lemmas that produce them. That is
  stronger, not weaker: `stateSqNorm_avg_le` preserves `δ` exactly and `povm_to_obs` gives
  exactly `|𝒜| · δ`.
* **answer-indexed families as well.** The paper's `≈_δ` is for operators indexed by questions
  but not answers; the applications also need the form summed over a common outcome set
  (`cor:ortho-from-consistency` concludes `P_a ⊗ Id ≈ Q_a ⊗ Id`). Both are here, the second as
  `povmStateDist`.

## Implementation

`stateVec ψ A = (A ⊗ Id)|ψ⟩`, carried in `EuclideanSpace ℂ (dA × dB)` so that the triangle
inequality and `‖c • v‖ = ‖c‖‖v‖` are Mathlib's rather than rebuilt. The bridge to the
blueprint's quadratic-form spelling is `stateSqNorm_eq`, which is the only place the Kronecker
adjoint is used.
-/

namespace MIPRE

open Finset Matrix Kronecker

variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]

/-! ## The vector `(A ⊗ Id)|ψ⟩` -/

/-- `(M ⊗ Id)|ψ⟩`, as a vector of `EuclideanSpace ℂ (dA × dB)`. -/
noncomputable def stateVec (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    EuclideanSpace ℂ (dA × dB) :=
  WithLp.toLp 2 ((M ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ)

@[simp] theorem stateVec_add (ψ : dA × dB → ℂ) (M N : Matrix dA dA ℂ) :
    stateVec ψ (M + N) = stateVec ψ M + stateVec ψ N := by
  show WithLp.toLp 2 _ = WithLp.toLp 2 _ + WithLp.toLp 2 _
  rw [Matrix.add_kronecker, Matrix.add_mulVec]
  rfl

@[simp] theorem stateVec_smul (ψ : dA × dB → ℂ) (c : ℂ) (M : Matrix dA dA ℂ) :
    stateVec ψ (c • M) = c • stateVec ψ M := by
  show WithLp.toLp 2 _ = c • WithLp.toLp 2 _
  rw [Matrix.smul_kronecker, Matrix.smul_mulVec]
  rfl

@[simp] theorem stateVec_zero (ψ : dA × dB → ℂ) :
    stateVec ψ (0 : Matrix dA dA ℂ) = 0 := by
  show WithLp.toLp 2 _ = 0
  rw [Matrix.zero_kronecker, Matrix.zero_mulVec]
  rfl

@[simp] theorem stateVec_neg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateVec ψ (-M) = -stateVec ψ M := by
  have h : stateVec ψ M + stateVec ψ (-M) = 0 := by
    rw [← stateVec_add, add_neg_cancel, stateVec_zero]
  linear_combination (norm := module) h

@[simp] theorem stateVec_sub (ψ : dA × dB → ℂ) (M N : Matrix dA dA ℂ) :
    stateVec ψ (M - N) = stateVec ψ M - stateVec ψ N := by
  rw [sub_eq_add_neg, stateVec_add, stateVec_neg, sub_eq_add_neg]

/-! ## The norm, and the distance -/

/-- `‖(M ⊗ Id)|ψ⟩‖`. -/
noncomputable def stateNorm (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : ℝ := ‖stateVec ψ M‖

/-- `⟨ψ| M† M ⊗ Id |ψ⟩`, the squared state-dependent norm. -/
noncomputable def stateSqNorm (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : ℝ := stateNorm ψ M ^ 2

section POVMs

variable {A : Type*} [Fintype A] [DecidableEq A] [DecidableEq dA]

/-! ## The two closeness lemmas of the appendix's preliminaries -/

end POVMs

/-! ## Bob's factor, by the swap

`cor:ortho-from-consistency` compares `(Q_a ⊗ Id)|ψ⟩` against `(Id ⊗ R_a)|ψ⟩`, so it needs the
vectors of the *other* factor too. Rather than duplicate the calculus above, observe that Bob's
factor is Alice's factor of the swapped state: `swapVec` exchanges the two tensor factors, and
`norm_stateVecB` identifies the two norms. Every lemma proved above then applies on Bob's side
with `dA` and `dB` exchanged. -/

section Swap

variable [DecidableEq dA]

/-- `|ψ⟩` with its two tensor factors exchanged. -/
def swapVec (ψ : dA × dB → ℂ) : dB × dA → ℂ := fun p => ψ p.swap

/-- `(Id ⊗ N)|ψ⟩`, as a vector of `EuclideanSpace ℂ (dA × dB)`: the `stateVec` of Bob's
factor. -/
noncomputable def stateVecB (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) :
    EuclideanSpace ℂ (dA × dB) :=
  WithLp.toLp 2 (((1 : Matrix dA dA ℂ) ⊗ₖ N) *ᵥ ψ)

omit [DecidableEq dB] in
@[simp] theorem stateVecB_smul (ψ : dA × dB → ℂ) (c : ℂ) (N : Matrix dB dB ℂ) :
    stateVecB ψ (c • N) = c • stateVecB ψ N := by
  show WithLp.toLp 2 _ = c • WithLp.toLp 2 _
  rw [Matrix.kronecker_smul, Matrix.smul_mulVec]
  rfl

end Swap

end MIPRE


