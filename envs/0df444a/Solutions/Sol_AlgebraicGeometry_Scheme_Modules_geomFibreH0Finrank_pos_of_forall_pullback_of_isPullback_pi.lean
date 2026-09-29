-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_pos_of_forall_pullback_of_isPullback_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7e4e644f-ae44-568f-a88f-d17bb91697c8

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_pullback_of_isPullback_pi

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

namespace RingHom p2m_export "RingHom" "ext comp" end RingHom
p2m_open_scoped "RingHom" in

theorem RingHom.exists_eq_comp_evalRingHom_of_field {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)]
    (K : Type) [Field K] (sk : (∀ i, C i) →+* K) :
    ∃ (i : Fin k) (ski : C i →+* K), sk = ski.comp (Pi.evalRingHom C i) := by
  classical
  have hsingle_mul : ∀ (i : Fin k) (a b : C i), Pi.single i (a * b) = Pi.single i a * Pi.single i b := fun i a b => by
    ext j; by_cases h : j = i
    · subst h; simp
    · simp [h]
  have hidem : ∀ i, sk (Pi.single i 1) = 0 ∨ sk (Pi.single i 1) = 1 := fun i =>
    IsIdempotentElem.iff_eq_zero_or_one.1 (by
      show sk _ * sk _ = sk _
      rw [← map_mul, ← hsingle_mul, one_mul])
  have hsum : ∑ i, sk (Pi.single i ((1 : ∀ i, C i) i)) = 1 := by
    rw [← map_sum, Finset.univ_sum_single (1 : ∀ i, C i), map_one]
  obtain ⟨i, hi⟩ : ∃ i, sk (Pi.single i 1) = 1 := by
    by_contra h
    push Not at h
    have h0 : ∑ i, sk (Pi.single i ((1 : ∀ i, C i) i)) = 0 :=
      Finset.sum_eq_zero fun i _ => (hidem i).resolve_right (h i)
    rw [h0] at hsum
    exact zero_ne_one hsum
  refine ⟨i,
    { toFun := fun c => sk (Pi.single i c)
      map_one' := hi
      map_mul' := fun a b => by show sk _ = sk _ * sk _; rw [← map_mul, ← hsingle_mul]
      map_zero' := by show sk _ = 0; rw [Pi.single_zero, map_zero]
      map_add' := fun a b => by show sk _ = sk _ + sk _; rw [← map_add, Pi.single_add] }, ?_⟩
  refine RingHom.ext fun x => ?_
  show sk x = sk (Pi.single i (x i))
  have hx : x = Pi.single i (x i) + x * (1 - Pi.single i 1) := by
    ext j; by_cases h : j = i
    · subst h; simp
    · simp [h]
  conv_lhs => rw [hx]
  rw [map_add, map_mul, map_sub, map_one, hi, sub_self, mul_zero, add_zero]

theorem solution
    {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)]
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of (∀ i, C i))) (𝓛 : A'.Modules)
    {Ai : Fin k → Scheme.{0}} (fi : ∀ i, Ai i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Ai i ⟶ A')
    (hv : ∀ i, IsPullback (v i) (fi i) f' (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (hloc : ∀ (i : Fin k) (K : Type) [Field K] [IsAlgClosed K] (sk : C i →+* K),
      0 < Scheme.Modules.geomFibreH0Finrank (fi i) ((Scheme.Modules.pullback (v i)).obj 𝓛) K sk) :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (sk : (∀ i, C i) →+* K), 0 < Scheme.Modules.geomFibreH0Finrank f' 𝓛 K sk := by
  intro K _ _ sk
  obtain ⟨i, ski, rfl⟩ := RingHom.exists_eq_comp_evalRingHom_of_field C K sk
  rw [← AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback (Pi.evalRingHom C i) f' (fi i) (v i) (hv i)
    𝓛 _ (Iso.refl _) K ski]
  exact hloc i K ski

end S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_pullback_of_isPullback_pi
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_pullback_of_isPullback_pi (solution)
