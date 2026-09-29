-- Prove2me | solution 1 for Algebra.QuasiFiniteAt.of_minimal_of_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/4ea675ee-0945-5b1f-aaff-43018de8af36

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_QuasiFiniteAt_of_minimal_of_maximal

set_option autoImplicit false

namespace P2mKcZmtIsolated

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem quasiFiniteAt_of_forall_eq [Algebra.FiniteType R S] (𝔮 : Ideal S) [𝔮.IsPrime]
    (hmin : ∀ P : Ideal S, P.IsPrime → P ≤ 𝔮 →
      P.comap (algebraMap R S) = 𝔮.comap (algebraMap R S) → P = 𝔮)
    (hmax : ∀ P : Ideal S, P.IsPrime → 𝔮 ≤ P →
      P.comap (algebraMap R S) = 𝔮.comap (algebraMap R S) → P = 𝔮) :
    Algebra.QuasiFiniteAt R 𝔮 := by
  classical
  let q : PrimeSpectrum S := ⟨𝔮, ‹_›⟩
  let p : PrimeSpectrum R := q.comap (algebraMap R S)
  have hq : q ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} := rfl

  let x : ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) := ⟨q, hq⟩
  have hxmax : IsMax x := by
    rintro ⟨y, hy⟩ hxy
    have hy' : PrimeSpectrum.comap (algebraMap R S) y = p := hy
    have hle : 𝔮 ≤ y.asIdeal := hxy
    have hcomap : y.asIdeal.comap (algebraMap R S) = 𝔮.comap (algebraMap R S) :=
      congrArg PrimeSpectrum.asIdeal hy'
    have := hmax y.asIdeal y.2 hle hcomap
    change y ≤ q
    exact le_of_eq (PrimeSpectrum.ext this)
  have hxmin : IsMin x := by
    rintro ⟨y, hy⟩ hyx
    have hy' : PrimeSpectrum.comap (algebraMap R S) y = p := hy
    have hle : y.asIdeal ≤ 𝔮 := hyx
    have hcomap : y.asIdeal.comap (algebraMap R S) = 𝔮.comap (algebraMap R S) :=
      congrArg PrimeSpectrum.asIdeal hy'
    have := hmin y.asIdeal y.2 hle hcomap
    change q ≤ y
    exact le_of_eq (PrimeSpectrum.ext this.symm)
  refine Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber q ?_
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  rw [← e.isOpen_image, Set.image_singleton]
  haveI : IsNoetherianRing (p.asIdeal.Fiber S) :=
    Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
  haveI : IsJacobsonRing (p.asIdeal.Fiber S) :=
    isJacobsonRing_of_finiteType (A := p.asIdeal.ResidueField)
  have hex : e x = PrimeSpectrum.preimageOrderIsoFiber R S p x := rfl
  have htfae :=
    (PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing (e x)).out 0 2
  rw [htfae]
  refine ⟨?_, ?_⟩
  · rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal, ← PrimeSpectrum.isMax_iff, hex,
      OrderIso.isMax_apply]
    exact hxmax
  · rw [PrimeSpectrum.stableUnderGeneralization_singleton, ← PrimeSpectrum.isMin_iff, hex,
      OrderIso.isMin_apply]
    exact hxmin

theorem quasiFiniteAt_of_minimal_of_maximal [Algebra.FiniteType R S] (𝔮 : Ideal S) [𝔮.IsPrime]
    (hmin : Minimal
      (fun P : Ideal S => P.IsPrime ∧ P.comap (algebraMap R S) = 𝔮.comap (algebraMap R S)) 𝔮)
    (hmax : Maximal
      (fun P : Ideal S => P.IsPrime ∧ P.comap (algebraMap R S) = 𝔮.comap (algebraMap R S)) 𝔮) :
    Algebra.QuasiFiniteAt R 𝔮 :=
  quasiFiniteAt_of_forall_eq 𝔮
    (fun _ hP hle hc => le_antisymm hle (hmin.2 ⟨hP, hc⟩ hle))
    (fun _ hP hle hc => le_antisymm (hmax.2 ⟨hP, hc⟩ hle) hle)

end P2mKcZmtIsolated

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (𝔮 : Ideal S) [𝔮.IsPrime]
    (hmin : Minimal
      (fun P : Ideal S => P.IsPrime ∧ P.comap (algebraMap R S) = 𝔮.comap (algebraMap R S)) 𝔮)
    (hmax : Maximal
      (fun P : Ideal S => P.IsPrime ∧ P.comap (algebraMap R S) = 𝔮.comap (algebraMap R S)) 𝔮) :
    Algebra.QuasiFiniteAt R 𝔮 :=
  P2mKcZmtIsolated.quasiFiniteAt_of_minimal_of_maximal 𝔮 hmin hmax

end S_Algebra_QuasiFiniteAt_of_minimal_of_maximal
end P2MW
export P2MW.S_Algebra_QuasiFiniteAt_of_minimal_of_maximal (solution)
