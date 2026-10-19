-- Prove2me | Definitions.Def_MazurTransfer_Order13LocalIntegralCoefficientMaps
-- name    : MazurTransfer_Order13LocalIntegralCoefficientMaps
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T08:54:46.682859+00:00
-- url     : https://prove2.me/theorems/11986e94-ebcd-4fec-a9da-ec56667f61ef
-- title:
--   The original local coefficient maps for rational and mod-three/mod-five Picard specialization
-- statement:
--   For a prime $q$, let $B_q=\mathbb Z_{(q)}$. The specified maps and instances make $B_q$ a discrete valuation ring with fraction field $\mathbb Q$ and give its specified map to $\mathbf F_q$. For $q=3$ or $5$, the element $104$ is invertible in $B_q$, and the original localization map factors through $$\mathbb Z[1/104]\longrightarrow B_q\longrightarrow\mathbb Q,\mathbf F_q.$$ The compositions are exactly the canonical rational and finite-field scalar maps. The fraction-field algebra action, scalar tower and fraction-ring structure are specified. These are the coefficient data for specialization through the same actual integral Picard family.
-- source:
--   Original complete Order13LocalIntegralCoefficientMaps.lean from MazurTheorem, Apache-2.0, Vas and contributors, with the one required original mapToRing_comp structural bridge from Order13IntegralCurveRationalAndFiniteFieldFibres.lean. All original declaration and instance bodies are unchanged; project imports alone become public interfaces. All sixteen complete original closed types and all five data construction values are kernel-compared. Four other instances are proof-valued. The original nondefault local-to-rational algebra action is retained, together with its scalar-tower and fraction-ring proofs. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumers: proper relative group valuation specialization, actual rational Picard reduction and local norm/Kummer conditions.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual coefficient maps from Z[1/104] through the
valuation ring Z_(q) to Q and F_q, retaining canonical scalar maps.
Named downstream consumer: same-family rational Picard reduction.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13SameIntegralPicardFamilyFiniteFibres
import Definitions.Def_MazurTransfer_Order13CanonicalRationalScalarMap
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
noncomputable section
namespace MazurTransfer.Order13IntegralBase
theorem mapToRing_comp (K : Type) [CommRing K] (h : IsUnit (104 : K)) :
    (mapToRing K h).comp (algebraMap ℤ BaseRing) = Int.castRingHom K :=
  IsLocalization.Away.lift_comp (104 : ℤ) _
end MazurTransfer.Order13IntegralBase


noncomputable section
namespace MazurTransfer.Order13LocalIntegralCoefficientMaps
open scoped nonZeroDivisors
open Order13IntegralBase Order13SameIntegralPicardFamilyFiniteFibres
variable (q : ℕ) [Fact q.Prime]

def primeIdeal : Ideal ℤ := Ideal.span {(q : ℤ)}

instance primeIdeal_isPrime : (primeIdeal q).IsPrime := by
  apply (Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr (Fact.out : q.Prime).ne_zero)).2
  exact Nat.prime_iff_prime_int.mp Fact.out

abbrev LocalRing := Localization.AtPrime (primeIdeal q)

theorem primeIdeal_ne_bot : primeIdeal q ≠ ⊥ := by
  rw [primeIdeal,ne_eq,Ideal.span_singleton_eq_bot]
  exact Int.ofNat_ne_zero.mpr (Fact.out : q.Prime).ne_zero

instance local_isDiscreteValuationRing : IsDiscreteValuationRing (LocalRing q) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
    (primeIdeal_ne_bot q) (LocalRing q)

theorem primeCompl_nonZeroDivisors : (primeIdeal q).primeCompl ≤ ℤ⁰ := by
  intro a ha
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact fun h => ha (h.symm ▸ (primeIdeal q).zero_mem)

instance localRationalAlgebra : Algebra (LocalRing q) ℚ :=
  IsLocalization.localizationAlgebraOfSubmonoidLe (LocalRing q) ℚ
    (primeIdeal q).primeCompl ℤ⁰ (primeCompl_nonZeroDivisors q)

instance localRationalTower :
    @IsScalarTower ℤ (LocalRing q) ℚ
      (inferInstance : Algebra ℤ (LocalRing q)).toSMul
      (localRationalAlgebra q).toSMul (inferInstance : Algebra ℤ ℚ).toSMul :=
  IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := LocalRing q) (A := ℚ)
    (Subsingleton.elim _ _)

instance localRationalFractionRing : IsFractionRing (LocalRing q) ℚ :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (primeIdeal q).primeCompl
    (LocalRing q) ℚ

def localFiniteFieldMap : LocalRing q →+* ZMod q :=
  IsLocalization.lift (M := (primeIdeal q).primeCompl)
    (g := Int.castRingHom (ZMod q)) (by
      intro a
      apply isUnit_iff_ne_zero.mpr
      intro h
      apply a.property
      exact Ideal.mem_span_singleton.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd a.val q).mp h))

theorem local_unit104 (hq : q=3 ∨ q=5) : IsUnit (104 : LocalRing q) := by
  have h : (104 : ℤ) ∈ (primeIdeal q).primeCompl := by
    change (104 : ℤ) ∉ Ideal.span {(q : ℤ)}
    rw [Ideal.mem_span_singleton]
    rcases hq with rfl | rfl <;> norm_num
  simpa only [map_ofNat] using IsLocalization.map_units (LocalRing q) ⟨104,h⟩

def localBaseMap (hq : q=3 ∨ q=5) : BaseRing →+* LocalRing q :=
  mapToRing (LocalRing q) (local_unit104 q hq)

theorem mapToRing_natural {A A' : Type} [CommRing A] [CommRing A']
    (g : A →+* A') (h : IsUnit (104 : A)) (h' : IsUnit (104 : A')) :
    g.comp (mapToRing A h) = mapToRing A' h' := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (104 : ℤ))
  rw [RingHom.comp_assoc,mapToRing_comp,mapToRing_comp]
  exact Subsingleton.elim _ _

theorem localRationalMap_comp (hq : q=3 ∨ q=5) :
    (algebraMap (LocalRing q) ℚ).comp (localBaseMap q hq) = canonicalRationalMap :=
  mapToRing_natural _ _ _

theorem localFiniteFieldMap_comp (hq : q=3 ∨ q=5) :
    (localFiniteFieldMap q).comp (localBaseMap q hq) = canonicalFiniteFieldMap q hq :=
  mapToRing_natural _ _ _

end MazurTransfer.Order13LocalIntegralCoefficientMaps
#print axioms MazurTransfer.Order13LocalIntegralCoefficientMaps.localRationalFractionRing
#print axioms MazurTransfer.Order13LocalIntegralCoefficientMaps.local_unit104


