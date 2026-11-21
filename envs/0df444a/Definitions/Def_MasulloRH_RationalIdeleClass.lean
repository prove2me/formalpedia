-- Prove2me | Definitions.Def_MasulloRH_RationalIdeleClass
-- name    : MasulloRH_RationalIdeleClass
-- status  : Definition
-- author  : @marozols
-- created : 2026-11-21T02:35:48.76217+00:00
-- url     : https://prove2.me/theorems/89c61f98-6e8b-40cd-b999-1acce9941b2a
-- title:
--   Rational idèle classes, their log norm, and spherical adelic theta functions
-- statement:
--   Take the actual rational idèles modulo principal rational units. The normalized positive real coordinate gives a multiplicative homomorphism on the quotient. A bilateral rational orbital theta sum descends under multiplication by principal units. Spherical theta functions average that descended function over the subgroup of finite integral units.
-- source:
--   A. M. Masullo, The Music of the Primes, rational trivial-character specialization of Chapters 9 and 10; https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Uses the certified rational idèle normalizer and the compact subgroup of finite unit idèles.

import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_MasulloRH_RationalFiniteRadial

open NumberField IsDedekindDomain RatIdele MeasureTheory
open MasulloRH.RationalFinite

namespace MasulloRH.RationalClass
noncomputable section

abbrev Ad := AdeleRing (𝓞 ℚ) ℚ
abbrev I := Adˣ
abbrev principal : ℚˣ →* I := Units.map (algebraMap ℚ Ad).toMonoidHom
abbrev C := I ⧸ principal.range
abbrev classOf : I →* C := QuotientGroup.mk' principal.range

/-- The positive real component of the unique representative with all finite valuations one. -/
def normHom : C →* ℝ :=
  let m : I →* ℝ := {
    toFun x := archCoord x / ((ρ x : ℚ) : ℝ)
    map_one' := by rw [archCoord_one,ρ_one]; norm_num
    map_mul' x y := by simp only [archCoord_mul,ρ_mul,Rat.cast_mul]; ring }
  QuotientGroup.lift principal.range m (by
    rintro _ ⟨q,rfl⟩
    change archCoord (principal q) / ((ρ (principal q) : ℚ):ℝ) = 1
    rw [show archCoord (principal q) = ((q:ℚ):ℝ) from archCoord_principal q,
      show ρ (principal q)=(q:ℚ) from ρ_principal q]
    exact div_self (Rat.cast_ne_zero.mpr q.ne_zero))

def logNorm (z : C) : ℝ := Real.log (normHom z)

/-- The finite compact unit subgroup embedded as classes with real component one. -/
def finiteUnit (u : K) : C := classOf (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) u.val)

def underlyingOrbit (F : Ad → ℂ) (z : I) : ℂ :=
  ∑' q : ℚ, F ((z:Ad)*algebraMap ℚ Ad q)

private theorem orbit_principal_mul (F : Ad → ℂ) (q : ℚˣ) (z : I) :
    underlyingOrbit F (principal q*z) = underlyingOrbit F z := by
  let m : Equiv.Perm ℚ := MulAction.toPerm q
  calc
    _ = ∑' j : ℚ, F ((z:Ad)*algebraMap ℚ Ad (m j)) := by
      apply tsum_congr
      intro j
      change F ((algebraMap ℚ Ad (q:ℚ)*(z:Ad))*algebraMap ℚ Ad j) =
        F ((z:Ad)*algebraMap ℚ Ad ((q:ℚ)*j))
      rw [map_mul]
      congr 1
      ring
    _ = _ := m.tsum_eq (fun j : ℚ => F ((z:Ad)*algebraMap ℚ Ad j))

/-- Bilateral orbital theta function on the actual rational idèle class quotient. -/
def orbitTheta (F : Ad → ℂ) : C → ℂ :=
  Quotient.lift (underlyingOrbit F) (fun x y h => by
    obtain ⟨q,hq⟩ := QuotientGroup.eq_iff_div_mem.mp (show classOf x=classOf y from Quotient.sound h)
    have he : x = principal q*y := by rw [hq,div_mul_cancel]
    exact he ▸ orbit_principal_mul F q y)

/-- Projection of an orbital theta function to the trivial finite-unit character. -/
def sphericalTheta [MeasurableSpace K] (κ : Measure K) (F : Ad → ℂ) (z : C) : ℂ :=
  ∫ u : K, orbitTheta F (z*finiteUnit u) ∂κ

end
end MasulloRH.RationalClass


