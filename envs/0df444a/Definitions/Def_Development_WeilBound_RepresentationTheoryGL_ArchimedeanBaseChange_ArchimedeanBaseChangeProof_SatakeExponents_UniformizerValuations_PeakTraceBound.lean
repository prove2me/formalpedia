-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBound
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:22.646459+00:00
-- url     : https://prove2.me/theorems/a5a454d2-b6bb-4dc8-a0e8-ef978c060348
-- title:
--   Peak Trace Bound
-- statement:
--   Definitions and structural lemmas for Peak Trace Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/PeakTraceBound.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.Rg.BcB.F
def PeakTraceBound : Prop := ∀ (A : Type) [CommRing A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  (ι : Type) [Fintype ι] [Nonempty ι] (H : ι → Type) [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] (R : ∀ s, A →⋆ₐ[ℂ] (H s →L[ℂ] H s)) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ)
  (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (u : Module.End ℂ V)
  (p : A →⋆ₐ[ℂ] ℂ) (a₀ : A),
  (∀ s g, Commute (β s) (R s g)) → (∀ g, Commute u (ρ g)) → p a₀ ≠ 0 →
  (∀ g ∈ Ideal.span {a₀}, ∃ (C : ℝ) (N j : ℕ), ∀ᶠ k : ℕ in Filter.atTop,
    ‖LinearMap.trace ℂ V ((u * ρ g) ^ k)‖ ≤ C * (1 + k) ^ N *
      Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * R s g) ^ (k - j)‖)) →
  (∃ v : V, v ≠ 0 ∧ u v = v ∧ ∀ g, ρ g v = p g • v) →
  ∃ (s : ι) (χ : StarAlgebra.adjoin ℂ (Set.range (R s) ∪ {star (β s ^ m) * β s ^ m}) →⋆ₐ[ℂ] ℂ),
    (∀ x, ‖χ x‖ ≤ ‖(x : H s →L[ℂ] H s)‖) ∧
    (∀ g, χ ⟨R s g, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)⟩ = p g) ∧
    χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0
end PositivityTheory.Rg.BcB.F
end


