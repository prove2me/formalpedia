-- Prove2me | Definitions.Def_MIPRE_Foundations_StateDistance_B
-- name    : MIPRE_Foundations_StateDistance_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:55:33.503461+00:00
-- url     : https://prove2.me/theorems/069de96c-2b65-4768-9736-ffc453ae9e30
-- title:
--   Definitions of StateDistance (addendum): The state-dependent distance on a bipartite state Every soundness argument in the Pauli basis test's appendix compares…
-- statement:
--   The definitions of the module `MIPRE.Foundations.StateDistance` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The state-dependent distance on a bipartite state. Every soundness argument in the Pauli basis test's appendix compares operators in the distance `A^x ≈_δ B^x` ⟺ `𝔼_{x ∼ μ} ⟨ψ| (A^x - B^x)† (A^x - B^x) |ψ⟩ ≤ δ`, where the operators act on **Alice's factor** of a bipartite state `|ψ⟩ ∈ ℂ^{dA} ⊗ ℂ^{dB}`. That is not the distance `MIPRE/Foundations/Distances.lean` defines: `povmDistance` and `IsPOVMClose` use the normalized Hilbert--Schmidt norm, which is the *tracial* — synchronous — specialization, and `MIPRE/Foundations/Closeness.lean` says so in its own docstring. This file is the…
--
--   This bundle **adds** the declarations below to the already published bundle `MIPRE_Foundations_StateDistance` of the same module, which the new statements of this upload need and the earlier bundle left out.
--
--   **Definitions** (2): `MIPRE.obsOf` (The generalized observable of a POVM family and a weighting of the outcomes: `A^x = ∑_a α_a A^x_a`.); `MIPRE.stateDist` (**The state-dependent distance** of two families of operators on Alice's factor, relative to a question distribution `μ` and the state `ψ`:…).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.StateDistance` (`MIPRE/Foundations/StateDistance.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 6 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/StateDistance.lean; blueprint def:state-distance, lem:qld-povm-to-obs

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/StateDistance.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_StateDistance does not carry);
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
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Theorems.Thm_MIPRE_quadForm_eq

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

/-! ## The norm, and the distance -/

/-- **The state-dependent distance** of two families of operators on Alice's factor, relative to
a question distribution `μ` and the state `ψ`: blueprint `def:state-distance`. -/
noncomputable def stateDist (μ : X → ℝ) (ψ : dA × dB → ℂ) (A B : X → Matrix dA dA ℂ) : ℝ :=
  ∑ x, μ x * stateSqNorm ψ (A x - B x)

section POVMs

variable {A : Type*} [Fintype A] [DecidableEq A] [DecidableEq dA]

/-! ## The two closeness lemmas of the appendix's preliminaries -/

/-- The generalized observable of a POVM family and a weighting of the outcomes:
`A^x = ∑_a α_a A^x_a`. -/
noncomputable def obsOf (α : A → ℂ) (M : X → POVM A dA) (x : X) : Matrix dA dA ℂ :=
  ∑ a, α a • ((M x).mats a).val

end POVMs

/-! ## Bob's factor, by the swap

`cor:ortho-from-consistency` compares `(Q_a ⊗ Id)|ψ⟩` against `(Id ⊗ R_a)|ψ⟩`, so it needs the
vectors of the *other* factor too. Rather than duplicate the calculus above, observe that Bob's
factor is Alice's factor of the swapped state: `swapVec` exchanges the two tensor factors, and
`norm_stateVecB` identifies the two norms. Every lemma proved above then applies on Bob's side
with `dA` and `dB` exchanged. -/

section Swap

variable [DecidableEq dA]

end Swap

end MIPRE


