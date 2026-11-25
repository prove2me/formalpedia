-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:12:40.383174+00:00
-- url     : https://prove2.me/theorems/ddcc8613-595d-495f-84a5-bcf4cfc15fba
-- title:
--   Nat Card Alg Hom Eq Finrank Of Is Reduced Of Is Fraction Rin
-- statement:
--   Definitions and structural lemmas for Nat Card Alg Hom Eq Finrank Of Is Reduced Of Is Fraction Rin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
namespace GlobalTheory
section Index
variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] [DecidableEq ι]
variable [IsDomain R] [IsDiscreteValuationRing R]
end Index
section Points
variable {R S L ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing L] [IsDomain L]
  [Algebra R L] [Fintype ι] [DecidableEq ι]
variable [Module.Free R S] [Module.Finite R S]
end Points
section Count
theorem etale_of_isReduced_of_perfectField (K S : Type*) [Field K] [PerfectField K] [CommRing S]
    [Algebra K S] [Module.Finite K S] [IsReduced S] : Algebra.Etale K S := by
  have : IsArtinianRing S := .of_finite K S
  have (I : MaximalSpectrum S) : Algebra.FormallyEtale K (S ⧸ I.asIdeal) := by
    letI := Ideal.Quotient.field I.asIdeal
    exact Algebra.FormallyEtale.of_isSeparable K (S ⧸ I.asIdeal)
  exact ⟨.of_equiv ((IsArtinianRing.equivPi S).restrictScalars K).symm,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
variable (R S L : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field L] [Algebra R L]
theorem natCard_algHom_eq_finrank_of_etale_baseChange [Module.Free R S] [Module.Finite R S]
    [IsSepClosed L] [Algebra.FormallyEtale L (L ⊗[R] S)] :
    Nat.card (S →ₐ[R] L) = finrank R S := by
  have := (algebraMap R L).domain_nontrivial
  have : IsArtinianRing (L ⊗[R] S) := .of_finite L _
  have := Fintype.ofFinite (PrimeSpectrum (L ⊗[R] S))
  rw [Nat.card_congr (AlgHom.liftEquiv R L S L),
    Nat.card_congr (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L (L ⊗[R] S)),
    ← Module.finrank_baseChange (R := L) (S := R) (M' := S),
    (Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[R] S)).toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
end Count
section Etale
variable (K : Type*) {S : Type*} (L : Type*) [Field K] [CommRing S] [Algebra K S] [Field L]
  [Algebra K L] [IsSepClosed L] [Algebra.Etale K S]
variable (S) in

theorem natCard_algHom_eq_finrank_of_etale : Nat.card (S →ₐ[K] L) = finrank K S :=
  have := Algebra.FormallyUnramified.finite_of_free K S
  natCard_algHom_eq_finrank_of_etale_baseChange K S L
variable {K L} {ι : Type*} [Fintype ι]
end Etale
section Reduced
variable {K S L ι : Type*} [Field K] [PerfectField K] [CommRing S] [Algebra K S]
  [Module.Finite K S] [IsReduced S] [Field L] [Algebra K L] [IsSepClosed L] [Fintype ι]
  [DecidableEq ι]
end Reduced
section Both
variable {R S L ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S]
  [Algebra R S] [CommRing L] [IsDomain L] [Algebra R L] [Fintype ι] [DecidableEq ι]
end Both
example : Nat.card (ℝ × ℂ →ₐ[ℝ] ℂ) = 3 := by
  have := etale_of_isReduced_of_perfectField ℝ (ℝ × ℂ)
  rw [natCard_algHom_eq_finrank_of_etale ℝ (ℝ × ℂ) ℂ]
  simp
end GlobalTheory


