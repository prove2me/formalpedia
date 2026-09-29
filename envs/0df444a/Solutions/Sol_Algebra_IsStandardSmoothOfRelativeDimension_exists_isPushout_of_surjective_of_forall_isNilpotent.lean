-- Prove2me | solution 1 for Algebra.IsStandardSmoothOfRelativeDimension.exists_isPushout_of_surjective_of_forall_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/67ff9a26-b0af-5dda-b9a5-02beb78cd304

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsStandardSmoothOfRelativeDimension_exists_isPushout_of_surjective_of_forall_isNilpotent

set_option autoImplicit false

open MvPolynomial

universe u

namespace SmoothLiftExists

variable {R R₀ : Type u} [CommRing R] [CommRing R₀] [Algebra R R₀]

theorem isUnit_of_isUnit_map_of_ker_le {A B : Type*} [CommRing A] [CommRing B] (g : A →+* B)
    (hg : Function.Surjective g) (hker : ∀ x ∈ RingHom.ker g, IsNilpotent x) {a : A}
    (ha : IsUnit (g a)) : IsUnit a := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨b, hb⟩ := hg (↑u⁻¹ : B)
  have h1 : a * b - 1 ∈ RingHom.ker g := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one, hb, ← hu, Units.mul_inv, sub_self]
  have h2 : IsUnit (a * b) := by
    have := (hker _ h1).isUnit_add_one
    rwa [sub_add_cancel] at this
  exact isUnit_of_mul_isUnit_left h2

end SmoothLiftExists

namespace SmoothLiftExists

variable {R R₀ : Type u} [CommRing R] [CommRing R₀] [Algebra R R₀]
variable (hf : Function.Surjective (algebraMap R R₀))
variable {A₀ : Type u} [CommRing A₀] [Algebra R₀ A₀] [Algebra R A₀] [IsScalarTower R R₀ A₀]
variable {ι σ : Type} [Finite σ] (P₀ : Algebra.SubmersivePresentation R₀ A₀ ι σ)

noncomputable def liftRel (j : σ) : MvPolynomial ι R :=
  (MvPolynomial.map_surjective (algebraMap R R₀) hf (P₀.relation j)).choose

omit [Algebra R A₀] [IsScalarTower R R₀ A₀] in
theorem map_liftRel (j : σ) :
    MvPolynomial.map (algebraMap R R₀) (liftRel hf P₀ j) = P₀.relation j :=
  (MvPolynomial.map_surjective (algebraMap R R₀) hf (P₀.relation j)).choose_spec

noncomputable def J : Ideal (MvPolynomial ι R) := Ideal.span (Set.range (liftRel hf P₀))

abbrev Lift : Type u := MvPolynomial ι R ⧸ J hf P₀

noncomputable def π : MvPolynomial ι R →ₐ[R] A₀ := MvPolynomial.aeval P₀.val

theorem π_apply (p : MvPolynomial ι R) :
    π P₀ p = MvPolynomial.aeval P₀.val (MvPolynomial.map (algebraMap R R₀) p) := by
  rw [π, MvPolynomial.aeval_map_algebraMap]

theorem π_liftRel (j : σ) : π (R := R) P₀ (liftRel hf P₀ j) = 0 := by
  rw [π_apply, map_liftRel, P₀.aeval_val_relation]

theorem J_le_ker_π : J hf P₀ ≤ RingHom.ker (π (R := R) P₀).toRingHom := by
  rw [J, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact π_liftRel hf P₀ j

include hf in
theorem π_surjective : Function.Surjective (π (R := R) P₀) := by
  intro a
  obtain ⟨p₀, hp₀⟩ := P₀.aeval_val_surjective a
  obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective (algebraMap R R₀) hf p₀
  exact ⟨p, by rw [π_apply, hp₀]⟩

theorem ker_π :
    RingHom.ker (π (R := R) P₀).toRingHom =
      J hf P₀ ⊔ Ideal.map (MvPolynomial.C : R →+* MvPolynomial ι R) (RingHom.ker (algebraMap R R₀)) := by
  apply le_antisymm
  · intro p hp
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, π_apply,
      ← RingHom.mem_ker] at hp
    have hp' : MvPolynomial.map (algebraMap R R₀) p ∈ Ideal.span (Set.range P₀.relation) := by
      rw [P₀.span_range_relation_eq_ker, P₀.ker_eq_ker_aeval_val]; exact hp

    have hJ : Ideal.span (Set.range P₀.relation) =
        (J hf P₀).map (MvPolynomial.map (algebraMap R R₀)) := by
      rw [J, Ideal.map_span, ← Set.range_comp]
      congr 1
      ext j
      simp [Function.comp, map_liftRel]
    rw [hJ, Ideal.mem_map_iff_of_surjective _ (MvPolynomial.map_surjective _ hf)] at hp'
    obtain ⟨q, hq, hqp⟩ := hp'
    have hpq : p - q ∈ RingHom.ker (MvPolynomial.map (σ := ι) (algebraMap R R₀)) := by
      rw [RingHom.mem_ker, map_sub, hqp, sub_self]
    rw [MvPolynomial.ker_map] at hpq
    have : p = q + (p - q) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hq) (Ideal.mem_sup_right hpq)
  · rw [sup_le_iff]
    refine ⟨J_le_ker_π hf P₀, ?_⟩
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, π,
      MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply R R₀ A₀, RingHom.mem_ker.mp hx, map_zero]

noncomputable def g : Lift hf P₀ →ₐ[R] A₀ :=
  Ideal.Quotient.liftₐ (J hf P₀) (π P₀) (fun _ hp => J_le_ker_π hf P₀ hp)

theorem g_mk (p : MvPolynomial ι R) : g hf P₀ (Ideal.Quotient.mk (J hf P₀) p) = π P₀ p := rfl

theorem g_surjective : Function.Surjective (g hf P₀) := by
  intro a
  obtain ⟨p, rfl⟩ := π_surjective hf P₀ a
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

theorem ker_g :
    RingHom.ker (g hf P₀).toRingHom =
      Ideal.map (algebraMap R (Lift hf P₀)) (RingHom.ker (algebraMap R R₀)) := by
  have h1 : RingHom.ker (g hf P₀).toRingHom = (RingHom.ker (π (R := R) P₀).toRingHom).map
      (Ideal.Quotient.mk (J hf P₀)) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact Ideal.mem_map_of_mem _ hx
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      exact hp
  rw [h1, ker_π hf P₀, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map]
  congr 1

theorem ker_g_nil (hnil : ∀ x ∈ RingHom.ker (algebraMap R R₀), IsNilpotent x) :
    ∀ x ∈ RingHom.ker (g hf P₀).toRingHom, IsNilpotent x := by
  rw [ker_g]
  intro x hx
  have : Ideal.map (algebraMap R (Lift hf P₀)) (RingHom.ker (algebraMap R R₀)) ≤ nilradical _ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    exact (hnil r hr).map _
  exact this hx

noncomputable def Q : Algebra.PreSubmersivePresentation R (Lift hf P₀) ι σ :=
  Algebra.PreSubmersivePresentation.naive (v := liftRel hf P₀) P₀.map P₀.map_inj

attribute [local instance] Fintype.ofFinite

theorem g_jacobian : g hf P₀ (Q hf P₀).jacobian = P₀.jacobian := by
  classical
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]

  have hQ : ∀ p : MvPolynomial ι R, algebraMap (Q hf P₀).Ring (Lift hf P₀) p =
      Ideal.Quotient.mk (J hf P₀) p := fun p => rfl
  rw [P₀.algebraMap_apply, hQ, g_mk, π_apply, RingHom.map_det]
  congr 2
  refine Matrix.ext fun i j => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
    Algebra.PreSubmersivePresentation.jacobiMatrix_apply]

  change MvPolynomial.map (algebraMap R R₀) (MvPolynomial.pderiv (P₀.map i) (liftRel hf P₀ j)) = _
  rw [← MvPolynomial.pderiv_map, map_liftRel]

private theorem _root_.SmoothLiftExists.jacobian_isUnit (hnil : ∀ x ∈ RingHom.ker (algebraMap R R₀), IsNilpotent x) :
    IsUnit (Q hf P₀).jacobian := by
  refine isUnit_of_isUnit_map_of_ker_le (g hf P₀).toRingHom (g_surjective hf P₀)
    (ker_g_nil hf P₀ hnil) ?_
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, g_jacobian]
  exact P₀.jacobian_isUnit

p2m_export "SmoothLiftExists" "jacobian_isUnit"

noncomputable def Qs (hnil : ∀ x ∈ RingHom.ker (algebraMap R R₀), IsNilpotent x) :
    Algebra.SubmersivePresentation R (Lift hf P₀) ι σ :=
  { Q hf P₀ with jacobian_isUnit := jacobian_isUnit hf P₀ hnil }

theorem Qs_dimension (hnil : ∀ x ∈ RingHom.ker (algebraMap R R₀), IsNilpotent x) :
    (Qs hf P₀ hnil).dimension = P₀.dimension := rfl

theorem isPushout :
    letI := (g hf P₀).toRingHom.toAlgebra
    haveI : IsScalarTower R (Lift hf P₀) A₀ := IsScalarTower.of_algebraMap_eq (fun r => ((g hf P₀).commutes r).symm)
    Algebra.IsPushout R R₀ (Lift hf P₀) A₀ := by
  letI := (g hf P₀).toRingHom.toAlgebra
  haveI : IsScalarTower R (Lift hf P₀) A₀ :=
    IsScalarTower.of_algebraMap_eq (fun r => ((g hf P₀).commutes r).symm)
  rw [Algebra.isPushout_iff]
  have htoAlg : (IsScalarTower.toAlgHom R (Lift hf P₀) A₀) = g hf P₀ := by
    ext x; rfl
  rw [htoAlg]
  refine IsBaseChange.of_lift_unique _ (fun Q _ _ _ _ r => ?_)

  have hvan : ∀ x ∈ RingHom.ker (g hf P₀).toRingHom, r x = 0 := by
    intro x hx
    rw [ker_g] at hx
    have hx' : x ∈ (RingHom.ker (algebraMap R R₀) • ⊤ : Submodule R (Lift hf P₀)) := by
      rw [Ideal.smul_top_eq_map]; exact hx
    clear hx
    induction hx' using Submodule.smul_induction_on' with
    | smul c hc m _ =>
      rw [LinearMap.map_smul]
      have : (c • r m : Q) = algebraMap R R₀ c • r m := (algebraMap_smul R₀ c (r m)).symm
      rw [this, RingHom.mem_ker.mp hc, zero_smul]
    | add x _ y _ hx hy => rw [map_add, hx, hy, add_zero]

  have hginj : ∀ x y, g hf P₀ x = g hf P₀ y → r x = r y := by
    intro x y hxy
    have hk : x - y ∈ RingHom.ker (g hf P₀).toRingHom := by
      rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, hxy, sub_self]
    have : x = y + (x - y) := by ring
    rw [this, map_add, hvan _ hk, add_zero]
  let s : A₀ → Lift hf P₀ := fun a => (g_surjective hf P₀ a).choose
  have hs : ∀ a, g hf P₀ (s a) = a := fun a => (g_surjective hf P₀ a).choose_spec
  let q : A₀ →ₗ[R₀] Q :=
    { toFun := fun a => r (s a)
      map_add' := fun a b => by
        rw [← map_add]
        exact hginj _ _ (by rw [map_add, hs, hs, hs])
      map_smul' := fun c₀ a => by
        obtain ⟨c, rfl⟩ := hf c₀
        rw [RingHom.id_apply, algebraMap_smul (A := R₀) c (r (s a)), ← LinearMap.map_smul]
        refine hginj _ _ ?_
        rw [hs, map_smul, hs, algebraMap_smul] }
  have hq : ∀ x, q (g hf P₀ x) = r x := fun x => hginj _ _ (hs _)
  refine ⟨q, LinearMap.ext hq, fun q' hq' => ?_⟩
  ext a
  rw [← hs a, hq]
  exact LinearMap.congr_fun hq' (s a)

end SmoothLiftExists

open SmoothLiftExists in

theorem solution
    (n : ℕ) {R R₀ : Type u} [CommRing R] [CommRing R₀] [Algebra R R₀]
    (hf : Function.Surjective (algebraMap R R₀))
    (hnil : ∀ x ∈ RingHom.ker (algebraMap R R₀), IsNilpotent x)
    (A₀ : Type u) [CommRing A₀] [Algebra R₀ A₀] [Algebra R A₀] [IsScalarTower R R₀ A₀]
    [Algebra.IsStandardSmoothOfRelativeDimension n R₀ A₀] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra A A₀) (_ : IsScalarTower R A A₀),
      Algebra.IsStandardSmoothOfRelativeDimension n R A ∧
      Function.Surjective (algebraMap A A₀) ∧
      RingHom.ker (algebraMap A A₀) = Ideal.map (algebraMap R A) (RingHom.ker (algebraMap R R₀)) ∧
      Algebra.IsPushout R R₀ A A₀ := by
  obtain ⟨ι, σ, _, _, P₀, hP₀⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension n R₀ A₀›.out
  letI := (g hf P₀).toRingHom.toAlgebra
  haveI : IsScalarTower R (Lift hf P₀) A₀ :=
    IsScalarTower.of_algebraMap_eq (fun r => ((g hf P₀).commutes r).symm)
  refine ⟨Lift hf P₀, inferInstance, inferInstance, inferInstance, inferInstance, ?_, g_surjective hf P₀,
    ker_g hf P₀, isPushout hf P₀⟩
  exact (Qs hf P₀ hnil).isStandardSmoothOfRelativeDimension (by rw [Qs_dimension, hP₀])

end S_Algebra_IsStandardSmoothOfRelativeDimension_exists_isPushout_of_surjective_of_forall_isNilpotent
end P2MW
export P2MW.S_Algebra_IsStandardSmoothOfRelativeDimension_exists_isPushout_of_surjective_of_forall_isNilpotent (solution)
