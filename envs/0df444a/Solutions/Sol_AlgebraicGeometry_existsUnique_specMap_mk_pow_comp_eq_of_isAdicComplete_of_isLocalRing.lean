-- Prove2me | solution 1 for AlgebraicGeometry.existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/abaef364-1a71-565a-b990-04db7bf1dbd1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace AdicPointsEngine

variable {S : Type u} [CommRing S] [IsLocalRing S] (I : Ideal S) [IsAdicComplete I S]

theorem ideal_ne_top : I ≠ ⊤ := by
  intro h
  have hle : I ≤ (⊥ : Ideal S).jacobson := IsAdicComplete.le_jacobson_bot I
  rw [h, top_le_iff, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top hle

theorem pow_succ_ne_top (n : ℕ) : I ^ (n + 1) ≠ ⊤ := fun h =>
  ideal_ne_top I (top_le_iff.mp (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))

scoped instance nontrivial_quot (n : ℕ) : Nontrivial (S ⧸ I ^ (n + 1)) :=
  Ideal.Quotient.nontrivial_iff.mpr (pow_succ_ne_top I n)

scoped instance isLocalRing_quot (n : ℕ) : IsLocalRing (S ⧸ I ^ (n + 1)) :=
  .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

abbrev truncHom (n : ℕ) : CommRingCat.of S ⟶ CommRingCat.of (S ⧸ I ^ (n + 1)) :=
  CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))

abbrev transHom (n : ℕ) :
    CommRingCat.of (S ⧸ I ^ (n + 1 + 1)) ⟶ CommRingCat.of (S ⧸ I ^ (n + 1)) :=
  CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1))

scoped instance isLocalHom_truncHom (n : ℕ) : IsLocalHom (truncHom I n).hom :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

scoped instance isLocalHom_transHom (n : ℕ) : IsLocalHom (transHom I n).hom :=
  IsLocalHom.of_surjective _ (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ _)))

omit [IsLocalRing S] [IsAdicComplete I S] in
theorem transHom_comp_truncHom (n : ℕ) : truncHom I (n + 1) ≫ transHom I n = truncHom I n := by
  simp only [truncHom, transHom, ← CommRingCat.ofHom_comp, Ideal.Quotient.factorPowSucc,
    Ideal.Quotient.factorPow, Ideal.Quotient.factor_comp_mk]

variable {I}
variable {X : Scheme.{u}}
  (x : ∀ n : ℕ, Spec (CommRingCat.of (S ⧸ I ^ (n + 1))) ⟶ X)
  (hx : ∀ n : ℕ, Spec.map (transHom I n) ≫ x (n + 1) = x n)

include hx in

theorem apply_closedPoint_eq (n : ℕ) :
    x n (closedPoint (S ⧸ I ^ (n + 1))) = x 0 (closedPoint (S ⧸ I ^ (0 + 1))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih, ← hx n, Scheme.Hom.comp_apply, Spec_closedPoint]

include hx in
theorem range_subset (n : ℕ) (U : X.Opens) (hU : x 0 (closedPoint (S ⧸ I ^ (0 + 1))) ∈ U) :
    Set.range (x n) ⊆ (U : Set X) := by
  have hmem : x n (closedPoint (S ⧸ I ^ (n + 1))) ∈ U := by
    rw [apply_closedPoint_eq x hx n]; exact hU
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem (x n) hmem
  rintro _ ⟨s, rfl⟩
  have : s ∈ (x n) ⁻¹ᵁ U := by rw [htop]; trivial
  exact this

section Chart

variable {U : X.Opens} (hU : IsAffineOpen U) (hU₀ : x 0 (closedPoint (S ⧸ I ^ (0 + 1))) ∈ U)

noncomputable def chartLift (n : ℕ) : Spec (CommRingCat.of (S ⧸ I ^ (n + 1))) ⟶ Spec Γ(X, U) :=
  IsOpenImmersion.lift U.ι (x n) (by rw [Scheme.Opens.range_ι]; exact range_subset x hx n U hU₀) ≫
    hU.isoSpec.hom

theorem chartLift_comp (n : ℕ) : chartLift x hx hU hU₀ n ≫ hU.isoSpec.inv ≫ U.ι = x n := by
  rw [chartLift, Category.assoc, Iso.hom_inv_id_assoc, IsOpenImmersion.lift_fac]

theorem transHom_comp_chartLift (n : ℕ) :
    Spec.map (transHom I n) ≫ chartLift x hx hU hU₀ (n + 1) = chartLift x hx hU hU₀ n := by
  have hmono : Mono (hU.isoSpec.inv ≫ U.ι) := mono_comp _ _
  rw [← cancel_mono (hU.isoSpec.inv ≫ U.ι), Category.assoc, chartLift_comp, chartLift_comp, hx n]

noncomputable def chartRingHom (n : ℕ) : Γ(X, U) →+* S ⧸ I ^ (n + 1) :=
  (Spec.preimage (chartLift x hx hU hU₀ n)).hom

theorem specMap_chartRingHom (n : ℕ) :
    Spec.map (CommRingCat.ofHom (chartRingHom x hx hU hU₀ n)) = chartLift x hx hU hU₀ n := by
  rw [chartRingHom, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem strictMono_succ : StrictMono (fun n : ℕ => n + 1) := fun _ _ h => Nat.add_lt_add_right h 1

theorem chartRingHom_compat (n : ℕ) :
    (Ideal.Quotient.factorPow I (strictMono_succ.monotone n.le_succ)).comp
        (chartRingHom x hx hU hU₀ (n + 1)) = chartRingHom x hx hU hU₀ n := by
  have h : Spec.map (CommRingCat.ofHom ((Ideal.Quotient.factorPowSucc I (n + 1)).comp
      (chartRingHom x hx hU hU₀ (n + 1)))) = Spec.map (CommRingCat.ofHom (chartRingHom x hx hU hU₀ n)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_chartRingHom, specMap_chartRingHom]
    exact transHom_comp_chartLift x hx hU hU₀ n
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa only [CommRingCat.hom_ofHom] using this

noncomputable def chartRingHomLimit : Γ(X, U) →+* S :=
  IsAdicComplete.StrictMono.liftRingHom I strictMono_succ (chartRingHom x hx hU hU₀)
    (fun {n} => chartRingHom_compat x hx hU hU₀ n)

theorem mk_comp_chartRingHomLimit (n : ℕ) :
    (Ideal.Quotient.mk (I ^ (n + 1))).comp (chartRingHomLimit x hx hU hU₀) = chartRingHom x hx hU hU₀ n :=
  IsAdicComplete.StrictMono.mk_comp_liftRingHom I strictMono_succ (chartRingHom x hx hU hU₀)
    (fun {n} => chartRingHom_compat x hx hU hU₀ n) (n := n)

noncomputable def limitPoint : Spec (CommRingCat.of S) ⟶ X :=
  Spec.map (CommRingCat.ofHom (chartRingHomLimit x hx hU hU₀)) ≫ hU.isoSpec.inv ≫ U.ι

theorem truncHom_comp_limitPoint (n : ℕ) :
    Spec.map (truncHom I n) ≫ limitPoint x hx hU hU₀ = x n := by
  rw [limitPoint, ← Spec.map_comp_assoc, truncHom, ← CommRingCat.ofHom_comp, mk_comp_chartRingHomLimit,
    specMap_chartRingHom, chartLift_comp]

include hx hU hU₀ in

theorem eq_of_forall_truncHom_comp_eq (y y' : Spec (CommRingCat.of S) ⟶ X)
    (hy : ∀ n, Spec.map (truncHom I n) ≫ y = x n) (hy' : ∀ n, Spec.map (truncHom I n) ≫ y' = x n) :
    y = y' := by

  have key : ∀ z : Spec (CommRingCat.of S) ⟶ X, (∀ n, Spec.map (truncHom I n) ≫ z = x n) →
      ∃ ρ : Γ(X, U) →+* S, z = Spec.map (CommRingCat.ofHom ρ) ≫ hU.isoSpec.inv ≫ U.ι ∧
        ∀ n, (Ideal.Quotient.mk (I ^ (n + 1))).comp ρ = chartRingHom x hx hU hU₀ n := by
    intro z hz
    have hzc : z (closedPoint S) ∈ U := by
      have : Spec.map (truncHom I 0) (closedPoint (S ⧸ I ^ (0 + 1))) = closedPoint S := Spec_closedPoint
      rw [← this, ← Scheme.Hom.comp_apply, hz 0]; exact hU₀
    have hzr : Set.range z ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨s, rfl⟩
      have htop := Scheme.preimage_eq_top_of_closedPoint_mem z hzc
      have : s ∈ z ⁻¹ᵁ U := by rw [htop]; trivial
      exact this
    refine ⟨(Spec.preimage (IsOpenImmersion.lift U.ι z hzr ≫ hU.isoSpec.hom)).hom, ?_, ?_⟩
    · rw [CommRingCat.ofHom_hom, Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc,
        IsOpenImmersion.lift_fac]
    · intro n
      have hmono : Mono (hU.isoSpec.inv ≫ U.ι) := mono_comp _ _
      have e : Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (I ^ (n + 1))).comp
          (Spec.preimage (IsOpenImmersion.lift U.ι z hzr ≫ hU.isoSpec.hom)).hom)) =
          Spec.map (CommRingCat.ofHom (chartRingHom x hx hU hU₀ n)) := by
        rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Spec.map_preimage,
          specMap_chartRingHom, ← cancel_mono (hU.isoSpec.inv ≫ U.ι), Category.assoc, Category.assoc,
          Iso.hom_inv_id_assoc, IsOpenImmersion.lift_fac, chartLift_comp]
        exact hz n
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  obtain ⟨ρ, hρ, hρn⟩ := key y hy
  obtain ⟨ρ', hρ', hρ'n⟩ := key y' hy'
  have : ρ = ρ' := by
    rw [IsAdicComplete.StrictMono.eq_liftRingHom I strictMono_succ (chartRingHom x hx hU hU₀)
        (fun {n} => chartRingHom_compat x hx hU hU₀ n) (F := ρ) hρn,
      IsAdicComplete.StrictMono.eq_liftRingHom I strictMono_succ (chartRingHom x hx hU hU₀)
        (fun {n} => chartRingHom_compat x hx hU hU₀ n) (F := ρ') hρ'n]
  rw [hρ, hρ', this]

end Chart

include hx in

theorem existsUnique_truncHom_comp_eq :
    ∃! y : Spec (CommRingCat.of S) ⟶ X, ∀ n, Spec.map (truncHom I n) ≫ y = x n := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hU₀, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x 0 (closedPoint (S ⧸ I ^ (0 + 1))))) isOpen_univ
  exact ⟨limitPoint x hx hU hU₀, truncHom_comp_limitPoint x hx hU hU₀,
    fun y hy => eq_of_forall_truncHom_comp_eq x hx hU hU₀ y _ hy (truncHom_comp_limitPoint x hx hU hU₀)⟩

end AdicPointsEngine
p2m_reactivate "P2MW.S_AlgebraicGeometry_existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing.AdicPointsEngine"

open AdicPointsEngine in
theorem solution
    {S : Type u} [CommRing S] [IsLocalRing S] (I : Ideal S) [IsAdicComplete I S] {X : Scheme.{u}}
    (x : ∀ n : ℕ, Spec (CommRingCat.of (S ⧸ I ^ (n + 1))) ⟶ X)
    (hx : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1))) ≫ x (n + 1) = x n) :
    ∃! y : Spec (CommRingCat.of S) ⟶ X,
      ∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ y = x n :=
  existsUnique_truncHom_comp_eq x hx

end S_AlgebraicGeometry_existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing (solution)
