-- Prove2me | solution 1 for AlgebraicCurve.kaehlerRankOne_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e3b8f68c-c606-5a58-93e4-cb393c668caa

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_kaehlerRankOne_of_transcendental

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open IntermediateField Polynomial TensorProduct Module

namespace S12Kaehler

variable (K : Type*) [Field K]

def kaehlerPolynomialBasis : Basis Unit K[X] Ω[K[X]⁄K] :=
  (Basis.singleton Unit K[X]).map (KaehlerDifferential.polynomialEquiv K).symm

scoped instance instFormallyEtalePolynomialRatFunc : Algebra.FormallyEtale K[X] (RatFunc K) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])

def kaehlerRatFuncBasis : Basis Unit (RatFunc K) Ω[(RatFunc K)⁄K] :=
  ((kaehlerPolynomialBasis K).baseChange (RatFunc K)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] (RatFunc K))

variable {F : Type*} [Field F] [Algebra K F]

def kaehlerOfRatFuncTowerBasis [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] : Basis Unit F Ω[F⁄K] :=
  haveI : Algebra.FormallyEtale (RatFunc K) F := Algebra.FormallyEtale.of_isSeparable _ _
  ((kaehlerRatFuncBasis K).baseChange F).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (RatFunc K) F)

theorem kaehlerRankOne_of_ratFuncTower [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] : Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 :=
  ⟨Module.Free.of_basis (kaehlerOfRatFuncTowerBasis K),
    (Module.finrank_eq_card_basis (kaehlerOfRatFuncTowerBasis K)).trans (by simp)⟩

variable {K}

theorem kaehlerRankOne_of_transcendental {x : F} (htr : Transcendental K x)
    (hsep : Algebra.IsSeparable K⟮x⟯ F) : Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 := by
  haveI := hsep
  let e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x htr
  letI : Algebra (RatFunc K) F :=
    ((algebraMap K⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
        (e.symm.toRingEquiv : K⟮x⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮x⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮x⟯ F (e (e.symm a)) = algebraMap K⟮x⟯ F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮x⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  exact kaehlerRankOne_of_ratFuncTower K

end S12Kaehler
p2m_reactivate "P2MW.S_AlgebraicCurve_kaehlerRankOne_of_transcendental.S12Kaehler"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_kaehlerRankOne_of_transcendental.S12Kaehler"

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 := by
  exact S12Kaehler.kaehlerRankOne_of_transcendental htr hsep

end S_AlgebraicCurve_kaehlerRankOne_of_transcendental
end P2MW
export P2MW.S_AlgebraicCurve_kaehlerRankOne_of_transcendental (solution)
