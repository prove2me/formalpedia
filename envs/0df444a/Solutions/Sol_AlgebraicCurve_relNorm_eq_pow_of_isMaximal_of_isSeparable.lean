-- Prove2me | solution 1 for AlgebraicCurve.relNorm_eq_pow_of_isMaximal_of_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0a1f12a9-36b5-5a01-9920-3aaf1f5a2cd2

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.FieldTheory.SeparableClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_relNorm_eq_pow_of_isMaximal_of_isSeparable

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

namespace F10d

section Closure

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Module.IsTorsionFree R S]

attribute [local instance 10] FractionRing.liftAlgebra

local notation3 "𝕂" => FractionRing R
local notation3 "𝕃" => FractionRing S
local notation3 "𝔼" => IntermediateField.normalClosure (FractionRing R) (FractionRing S)
    (AlgebraicClosure (FractionRing S))
local notation3 "𝕋" => Ring.NormalClosure R S

local instance : Algebra S 𝔼 := ((algebraMap 𝕃 𝔼).comp (algebraMap S 𝕃)).toAlgebra

local instance : IsScalarTower S 𝕃 𝔼 := IsScalarTower.of_algebraMap_eq' rfl

local instance : Algebra 𝕋 𝔼 := inferInstanceAs (Algebra (integralClosure S 𝔼) 𝔼)

local instance : IsScalarTower S 𝕋 𝔼 := inferInstanceAs (IsScalarTower S (integralClosure S 𝔼) 𝔼)

local instance : IsIntegralClosure 𝕋 S 𝔼 := integralClosure.isIntegralClosure S 𝔼

local instance : IsScalarTower R 𝕋 𝔼 :=
  IsScalarTower.of_algebraMap_eq fun r => Subtype.ext <| by
    show algebraMap R (AlgebraicClosure 𝕃) r
      = algebraMap 𝕃 (AlgebraicClosure 𝕃) (algebraMap S 𝕃 (algebraMap R S r))
    rw [IsScalarTower.algebraMap_apply R 𝕃 (AlgebraicClosure 𝕃), IsScalarTower.algebraMap_apply R S 𝕃]

local instance : FaithfulSMul S 𝔼 := (faithfulSMul_iff_algebraMap_injective S 𝔼).mpr <|
      (FaithfulSMul.algebraMap_injective 𝕃 𝔼).comp (FaithfulSMul.algebraMap_injective S 𝕃)

variable [Module.Finite R S]

local instance : FiniteDimensional 𝕃 𝔼 := Module.Finite.right 𝕂 𝕃 𝔼

local instance : IsFractionRing 𝕋 𝔼 := integralClosure.isFractionRing_of_finite_extension 𝕃 𝔼

variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

omit [Module.Finite R S] in

private theorem isSeparable_normalClosure : Algebra.IsSeparable 𝕂 𝔼 := by
  rw [← le_separableClosure_iff, normalClosure_le_iff]
  intro f x hx
  obtain ⟨y, rfl⟩ := f.mem_fieldRange.mp hx
  rw [mem_separableClosure_iff]
  exact IsSeparable.map f (f : 𝕃 →+* AlgebraicClosure 𝕃).injective
    (Algebra.IsSeparable.isSeparable 𝕂 y)

local instance : Algebra.IsSeparable 𝕂 𝔼 := isSeparable_normalClosure R S

local instance : Algebra.IsSeparable 𝕃 𝔼 := Algebra.isSeparable_tower_top_of_isSeparable 𝕂 𝕃 𝔼

local instance : IsAlgClosure 𝕂 (AlgebraicClosure 𝕃) :=
  IsAlgClosure.ofAlgebraic 𝕂 𝕃 (AlgebraicClosure 𝕃)

local instance : Normal 𝕂 𝔼 := normalClosure.normal _ _ _

local instance : IsGalois 𝕂 𝔼 := IsGalois.mk

local instance : IsGalois 𝕂 (FractionRing 𝕋) := by
  refine IsGalois.of_equiv_equiv (F := 𝕂) (E := 𝔼)
    (f := (FractionRing.algEquiv R 𝕂).symm.toRingEquiv)
    (g := (FractionRing.algEquiv 𝕋 𝔼).symm.toRingEquiv) ?_
  ext
  simpa using IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R 𝕂).symm
    (FractionRing.algEquiv 𝕋 𝔼).symm _

variable [IsDedekindDomain S]

local instance : Module.Finite S 𝕋 := IsIntegralClosure.finite S 𝕃 𝔼 𝕋

local instance : Module.Finite R 𝕋 := Module.Finite.trans S 𝕋

local instance : IsDedekindDomain 𝕋 := integralClosure.isDedekindDomain S 𝕃 𝔼

variable {R S}
variable [IsDedekindDomain R]

set_option maxHeartbeats 1600000 in

private theorem relNorm_eq_pow_of_isMaximal_fractionRing
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg' P := by
  obtain ⟨Q, hQ₁, hQ₂⟩ : ∃ Q : Ideal 𝕋, Q.IsMaximal ∧ Q.LiesOver P :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral P
  have : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have h := Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
  have : IsGalois 𝕃 (FractionRing 𝕋) := IsGalois.tower_top_of_isGalois 𝕂 𝕃 (FractionRing 𝕋)
  rwa [← Ideal.relNorm_relNorm R S, Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    ← Ideal.inertiaDeg'_eq_inertiaDeg p Q, ← Ideal.inertiaDeg'_eq_inertiaDeg P Q,
    Ideal.inertiaDeg'_algebra_tower p P Q, pow_mul, pow_left_inj] at h
  exact Nat.ne_zero_iff_zero_lt.mpr <| Ideal.inertiaDeg'_pos P Q

end Closure

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Module.IsTorsionFree R S] [Module.Finite R S]
  [IsDedekindDomain R] [IsDedekindDomain S]

attribute [local instance 10] FractionRing.liftAlgebra

private theorem relNorm_eq_pow_of_isMaximal_of_isSeparable (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsSeparable K L]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg' P := by
  haveI : Algebra.IsSeparable (FractionRing R) (FractionRing S) :=
    Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv R K).symm.toRingEquiv
      (FractionRing.algEquiv S L).symm.toRingEquiv (by
        ext x
        simpa using IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
          (FractionRing.algEquiv S L).symm x)
  exact relNorm_eq_pow_of_isMaximal_fractionRing P p

end Transport

end F10d

end AlgebraicCurve

end

theorem solution {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsSeparable K L]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg' P :=
  AlgebraicCurve.F10d.relNorm_eq_pow_of_isMaximal_of_isSeparable K L P p

example : ∀ {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsSeparable K L]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal],
    Ideal.relNorm R P = p ^ p.inertiaDeg' P := @solution

#print axioms solution

end S_AlgebraicCurve_relNorm_eq_pow_of_isMaximal_of_isSeparable
end P2MW
export P2MW.S_AlgebraicCurve_relNorm_eq_pow_of_isMaximal_of_isSeparable (solution)
