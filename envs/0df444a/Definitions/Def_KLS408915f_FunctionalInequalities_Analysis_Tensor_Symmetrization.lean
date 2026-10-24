-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
-- name    : KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:01:25.904947+00:00
-- url     : https://prove2.me/theorems/f001e3ec-0bfc-43b9-bdd1-292090f458d6
-- title:
--   Permutation averages on selected tensor positions
-- statement:
--   For a finite index type $\Omega$, `fixingOutside s` is the finite set of permutations that fix every point outside a finite subset $s$. Given a monoid representation `ρ` of permutations by linear isometric equivalences of an inner-product space, `blockAverage ρ s v` is the normalized average of `ρ σ v` over those permutations, using the real inverse of the cardinality. This bundle contains definitions only and asserts no norm estimate.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L33-L42 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization`; the repository is private at upload time).

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic

noncomputable section
open Finset
namespace FunctionalInequalities
namespace Analysis
namespace Tensor
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
/-- The permutations of `Ω` fixing every point outside `s`. -/
def fixingOutside (s : Finset Ω) : Finset (Equiv.Perm Ω) :=
  univ.filter fun σ => ∀ x, x ∉ s → σ x = x
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
/-- The average of `ρ σ v` over the permutations fixing every point outside `s` (the operator
`S_q` of the source when `s` is the set of the first `q` positions). -/
def blockAverage (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) (s : Finset Ω) (v : V) : V :=
  ((fixingOutside s).card : ℝ)⁻¹ • ∑ σ ∈ fixingOutside s, ρ σ v
end Tensor
end Analysis
end FunctionalInequalities


