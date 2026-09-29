-- Prove2me | solution 1 for AlgebraicCurve.Pic0.periodPairing_pullback_eq_periodPairing_pushforward_of_mumfordQuotient_theta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1b497b63-b35e-53bd-b829-3b3273ff1661

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Mathlib.GroupTheory.Abelianization.Defs
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_exists_adj_min_le_v_apply_le_max_of_isUnit
import Theorems.Thm_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_completion_of_liesOverPrime
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_presentation_conj_apply_eq_of_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_Mumford_finiteHom_pushforward_apply_eq_of_forall_addMonoidHom_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_Mumford_finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer
import Theorems.Thm_CerednikDrinfeld_Mumford_surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_stabilizer_vertex_of_finite_stabilizer_dart
import Theorems.Thm_CerednikDrinfeld_Omega_eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype
import Theorems.Thm_CerednikDrinfeld_Omega_period_pmoebius_pmoebius_of_mulEquiv_of_apply_eq_conj
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_periodPairing_pullback_eq_periodPairing_pushforward_of_mumfordQuotient_theta
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve ModularCurve

namespace Skel

theorem graphAction_subgroup {P : Type} [Group P] {W : Type} [MulAction P W] (𝒯 : SimpleGraph W)
    [Mumford.GraphAction P 𝒯] (S : Subgroup P) : Mumford.GraphAction ↥S 𝒯 :=
  ⟨fun g _ _ h => Mumford.GraphAction.smul_adj (g : P) h⟩
end Skel

section
open MulAction
namespace Skel

theorem card_stabilizer_inv_smul_eq {P : Type} [Group P] {W : Type} [MulAction P W] (𝒯 : SimpleGraph W)
    [GraphAction P 𝒯] (H G₂ : Subgroup P) [GraphAction ↥H 𝒯] [GraphAction ↥G₂ 𝒯] (p : P)
    (Γ' : Subgroup ↥G₂) [GraphAction ↥Γ' 𝒯]
    (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H)
    (hHG₂ : ∀ h : P, h ∈ H → p⁻¹ * h * p ∈ G₂) (d : 𝒯.Dart) :
    Nat.card (stabilizer ↥Γ' (p⁻¹ • d)) = Nat.card (stabilizer ↥H d) := by
  refine Nat.card_congr
    { toFun := fun γ => ⟨⟨p * ((γ.1 : ↥G₂) : P) * p⁻¹, (hΓ' γ.1).1 γ.1.2⟩, ?_⟩
      invFun := fun h => ⟨⟨⟨p⁻¹ * (h.1 : P) * p, hHG₂ _ h.1.2⟩, (hΓ' _).2 ?_⟩, ?_⟩
      left_inv := fun γ => Subtype.ext (Subtype.ext (Subtype.ext (by
        show p⁻¹ * (p * ((γ.1 : ↥G₂) : P) * p⁻¹) * p = ((γ.1 : ↥G₂) : P); group)))
      right_inv := fun h => Subtype.ext (Subtype.ext (by
        show p * (p⁻¹ * (h.1 : P) * p) * p⁻¹ = (h.1 : P); group)) }
  ·
    have hγ : ((γ.1 : ↥G₂) : P) • (p⁻¹ • d) = p⁻¹ • d := mem_stabilizer_iff.mp γ.2
    show (p * ((γ.1 : ↥G₂) : P) * p⁻¹) • d = d
    rw [mul_smul, mul_smul, hγ, smul_inv_smul]
  · show p * (p⁻¹ * (h.1 : P) * p) * p⁻¹ ∈ H
    rw [show p * (p⁻¹ * (h.1 : P) * p) * p⁻¹ = (h.1 : P) by group]; exact h.1.2
  · have hh : (h.1 : P) • d = d := mem_stabilizer_iff.mp h.2
    show (p⁻¹ * (h.1 : P) * p) • (p⁻¹ • d) = p⁻¹ • d
    rw [mul_smul, mul_smul, smul_inv_smul, hh]

theorem finiteIndex_of_finite_orbitQuotient_of_finite_stabilizer {H X : Type} [Group H] [MulAction H X]
    (K : Subgroup H) (x₀ : X) [Finite (orbitRel.Quotient ↥K X)] [Finite (stabilizer H x₀)] :
    K.FiniteIndex := by
  classical

  let g : H ⧸ K → orbitRel.Quotient ↥K X :=
    Quotient.lift (fun h : H => (Quotient.mk _ (h⁻¹ • x₀) : orbitRel.Quotient ↥K X)) (by
      intro a b hab
      apply Quotient.sound
      refine ⟨⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab⟩, ?_⟩
      show (a⁻¹ * b) • (b⁻¹ • x₀) = a⁻¹ • x₀
      rw [mul_smul, smul_inv_smul])

  have hfib : ∀ h₁ h₂ : H, g (QuotientGroup.mk h₁) = g (QuotientGroup.mk h₂) →
      ∃ s : stabilizer H x₀, (QuotientGroup.mk h₂ : H ⧸ K) = QuotientGroup.mk ((s : H)⁻¹ * h₁) := by
    intro h₁ h₂ h12
    obtain ⟨k, hk⟩ : ∃ k : ↥K, k • (h₂⁻¹ • x₀) = h₁⁻¹ • x₀ := Quotient.exact h12
    have hk' : (k : H) • (h₂⁻¹ • x₀) = h₁⁻¹ • x₀ := hk
    refine ⟨⟨h₁ * (k : H) * h₂⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, mul_smul, hk', smul_inv_smul]
    · apply Quotient.sound
      refine QuotientGroup.leftRel_apply.mpr ?_
      rw [show h₂⁻¹ * ((h₁ * (k : H) * h₂⁻¹)⁻¹ * h₁) = ((k⁻¹ : ↥K) : H) by
        rw [Subgroup.coe_inv]; group]
      exact (k⁻¹).2

  haveI : Finite (H ⧸ K) := by
    let sec : orbitRel.Quotient ↥K X → H ⧸ K := fun q =>
      if hq : ∃ c : H ⧸ K, g c = q then hq.choose else QuotientGroup.mk 1
    refine Finite.of_surjective (fun sq : stabilizer H x₀ × orbitRel.Quotient ↥K X =>
      Quotient.map' (fun h : H => (sq.1 : H)⁻¹ * h) (fun a b hab => QuotientGroup.leftRel_apply.mpr (by
        rw [show ((sq.1 : H)⁻¹ * a)⁻¹ * ((sq.1 : H)⁻¹ * b) = a⁻¹ * b by group]
        exact QuotientGroup.leftRel_apply.mp hab)) (sec (sq.2))) ?_
    intro c
    induction c using QuotientGroup.induction_on with
    | H h =>
      have hq : ∃ c : H ⧸ K, g c = g (QuotientGroup.mk h) := ⟨_, rfl⟩
      have hsec : sec (g (QuotientGroup.mk h)) = hq.choose := dif_pos hq
      obtain ⟨h₀, hh₀⟩ := Quotient.exists_rep hq.choose
      have hg : g (QuotientGroup.mk h₀) = g (QuotientGroup.mk h) := by
        rw [show (QuotientGroup.mk h₀ : H ⧸ K) = hq.choose from hh₀]; exact hq.choose_spec
      obtain ⟨s, hs⟩ := hfib h₀ h hg
      refine ⟨(s, g (QuotientGroup.mk h)), ?_⟩
      show Quotient.map' _ _ (sec (g (QuotientGroup.mk h))) = QuotientGroup.mk h
      rw [hsec, ← hh₀, hs]
      rfl
  exact Subgroup.finiteIndex_of_finite_quotient

end Skel
end

namespace Skel

def conjEquiv {P : Type} [Group P] (H G₂ : Subgroup P) (p : P) (Γ' : Subgroup ↥G₂)
    (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H)
    (hHG₂ : ∀ h : P, h ∈ H → p⁻¹ * h * p ∈ G₂) : ↥Γ' ≃* ↥H where
  toFun γ := ⟨p * ((γ : ↥G₂) : P) * p⁻¹, (hΓ' (γ : ↥G₂)).1 γ.2⟩
  invFun h := ⟨⟨p⁻¹ * (h : P) * p, hHG₂ _ h.2⟩, (hΓ' _).2 (by
    rw [show p * (p⁻¹ * (h : P) * p) * p⁻¹ = (h : P) by group]; exact h.2)⟩
  left_inv γ := Subtype.ext (Subtype.ext (by
    show p⁻¹ * (p * ((γ : ↥G₂) : P) * p⁻¹) * p = ((γ : ↥G₂) : P); group))
  right_inv h := Subtype.ext (by show p * (p⁻¹ * (h : P) * p) * p⁻¹ = (h : P); group)
  map_mul' γ γ' := Subtype.ext (by
    show p * (((γ * γ' : ↥Γ') : ↥G₂) : P) * p⁻¹ = (p * ((γ : ↥G₂) : P) * p⁻¹) * (p * ((γ' : ↥G₂) : P) * p⁻¹)
    rw [Subgroup.coe_mul, Subgroup.coe_mul]; group)

theorem conjEquiv_apply_coe {P : Type} [Group P] (H G₂ : Subgroup P) (p : P) (Γ' : Subgroup ↥G₂)
    (hΓ' : ∀ x : ↥G₂, x ∈ Γ' ↔ p * (x : P) * p⁻¹ ∈ H)
    (hHG₂ : ∀ h : P, h ∈ H → p⁻¹ * h * p ∈ G₂) (γ : ↥Γ') :
    ((conjEquiv H G₂ p Γ' hΓ' hHG₂ γ : ↥H) : P) = p * ((γ : ↥G₂) : P) * p⁻¹ := rfl

noncomputable def qChar {H : Type} [Group H] {Z : Type} [AddCommGroup Z] [Module ℤ Z] {C : Type} [Field C] [Algebra ℚ C]
    (Kp : IntermediateField ℚ C)
    (Φ : Additive (Abelianization H) →+ Z) (qx : Z →ₗ[ℤ] Additive (↥Kp)ˣ) : H →* Cˣ :=
  (Units.map ((algebraMap ↥Kp C : ↥Kp →+* C) : ↥Kp →* C)).comp
    (AddMonoidHom.toMultiplicative (qx.toAddMonoidHom.comp (Φ.comp (MonoidHom.toAdditive (Abelianization.of (G := H))))))

theorem qChar_apply {H : Type} [Group H] {Z : Type} [AddCommGroup Z] [Module ℤ Z] {C : Type} [Field C] [Algebra ℚ C]
    (Kp : IntermediateField ℚ C)
    (Φ : Additive (Abelianization H) →+ Z) (qx : Z →ₗ[ℤ] Additive (↥Kp)ˣ) (β : H) :
    ((qChar Kp Φ qx β : Cˣ) : C) = (((Additive.toMul (qx (Φ (Additive.ofMul (Abelianization.of β)))) : (↥Kp)ˣ) : ↥Kp) : C) := rfl

noncomputable def qCharInv {H : Type} [Group H] {Z : Type} [AddCommGroup Z] [Module ℤ Z] {C : Type} [Field C] [Algebra ℚ C]
    (Kp : IntermediateField ℚ C)
    (Φ : Additive (Abelianization H) →+ Z) (qx : Z →ₗ[ℤ] Additive (↥Kp)ˣ) : H →* Cˣ :=
  (qChar Kp Φ qx)⁻¹

theorem qCharInv_apply {H : Type} [Group H] {Z : Type} [AddCommGroup Z] [Module ℤ Z] {C : Type} [Field C] [Algebra ℚ C]
    (Kp : IntermediateField ℚ C)
    (Φ : Additive (Abelianization H) →+ Z) (qx : Z →ₗ[ℤ] Additive (↥Kp)ˣ) (β : H) :
    ((qCharInv Kp Φ qx β : Cˣ) : C) = ((((Additive.toMul (qx (Φ (Additive.ofMul (Abelianization.of β)))) : (↥Kp)ˣ) : ↥Kp) : C))⁻¹ := by
  rw [qCharInv, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  rfl

end Skel

noncomputable section
namespace ProjS1

theorem lift_toMul_eq_one_of_mem_closure {H A : Type} [Group H] [CommGroup A] (Q : H →* A) (S : Set H)
    (hS : ∀ g ∈ S, Q g = 1) (x : Additive (Abelianization H))
    (hx : x ∈ AddSubgroup.closure ((fun g : H => Additive.ofMul (Abelianization.of g)) '' S)) :
    Abelianization.lift Q (Additive.toMul x) = 1 := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [toMul_ofMul, Abelianization.lift_apply_of]
    exact hS g hg
  | zero => simp
  | add x y _ _ hx hy => rw [toMul_add, map_mul, hx, hy, one_mul]
  | neg x _ hx => rw [toMul_neg, map_inv, hx, inv_one]

theorem apply_apply_eq_one_of_mem_closure {H A : Type} [Group H] [CommGroup A] (Q : H →* H →* A) (S : Set H)
    (hS : ∀ g ∈ S, ∀ b : H, Q g b = 1) (x : Additive (Abelianization H))
    (hx : x ∈ AddSubgroup.closure ((fun g : H => Additive.ofMul (Abelianization.of g)) '' S))
    (h : H) (hh : Additive.ofMul (Abelianization.of h) = x) (b : H) : Q h b = 1 := by
  have hsuff := lift_toMul_eq_one_of_mem_closure Q S (fun g hg => MonoidHom.ext (hS g hg)) x hx
  rw [← hh, toMul_ofMul, Abelianization.lift_apply_of] at hsuff
  rw [hsuff, MonoidHom.one_apply]

section PUTree

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀] {ϖ : R}
  {K : Type} [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_algebraMap_units_eq_one
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (u : Rˣ) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) = 1 := by
  apply le_antisymm (hint u)
  have h1 : algebraMap K₀ K (algebraMap R K₀ (u : R)) * algebraMap K₀ K (algebraMap R K₀ (↑u⁻¹ : R)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  calc (1 : Γ₀) = Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) *
        Valued.v (algebraMap K₀ K (algebraMap R K₀ (↑u⁻¹ : R))) := by rw [← Valuation.map_mul, h1, Valuation.map_one]
    _ ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) * 1 := mul_le_mul_right (hint _) _
    _ = _ := mul_one _

theorem algebraMap_ne_zero_of_irreducible (hϖ : Irreducible ϖ) : algebraMap R K₀ ϖ ≠ 0 := fun h =>
  hϖ.ne_zero ((IsFractionRing.to_map_eq_zero_iff (K := K₀)).mp h)

theorem v_algebraMap_pos (hϖ : Irreducible ϖ) : 0 < Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) :=
  lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff _).mpr
    ((map_ne_zero _).mpr (algebraMap_ne_zero_of_irreducible hϖ))))

theorem v_algebraMap_lt_one (hϖ : Irreducible ϖ)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) < 1 := by
  by_contra h
  rw [not_lt] at h
  have hϖ0 := algebraMap_ne_zero_of_irreducible (K₀ := K₀) hϖ
  have hle : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)⁻¹) ≤ 1 := by
    rw [map_inv₀, Valuation.map_inv, inv_le_one₀ (v_algebraMap_pos hϖ)]
    exact h
  obtain ⟨b, hb⟩ := hv _ hle
  apply hϖ.not_isUnit
  refine isUnit_iff_exists_inv.mpr ⟨b, ?_⟩
  apply IsFractionRing.injective R K₀
  rw [map_mul, hb, map_one, mul_inv_cancel₀ hϖ0]

theorem exists_v_algebraMap_eq_zpow (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (a : K₀) (ha : a ≠ 0) :
    ∃ k : ℤ, Valued.v (algebraMap K₀ K a) = Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ k := by
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ ha
  refine ⟨k, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, Valuation.map_mul, map_zpow₀,
    v_algebraMap_units_eq_one hint, one_mul]

theorem v_algebraMap_le_or_one_le (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (a : K₀) :
    Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ∨
      1 ≤ Valued.v (algebraMap K₀ K a) := by
  by_cases ha : a = 0
  · left; rw [ha, map_zero, Valuation.map_zero]; exact zero_le'
  obtain ⟨k, hk⟩ := exists_v_algebraMap_eq_zpow hϖ hint a ha
  rw [hk]
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have h1 := (v_algebraMap_lt_one hϖ hv).le
  rcases le_or_gt k 0 with hk0 | hk0
  · exact Or.inr (one_le_zpow_of_nonpos₀ h0 h1 hk0)
  · left
    calc Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ k
        ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ h0 h1 (by omega)
      _ = _ := zpow_one _

theorem exists_pow_le_v_algebraMap_le (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (a : K₀) (ha : a ≠ 0) :
    ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ Valued.v (algebraMap K₀ K a) ∧
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)))⁻¹ ^ N := by
  obtain ⟨k, hk⟩ := exists_v_algebraMap_eq_zpow hϖ hint a ha
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have h1 := (v_algebraMap_lt_one hϖ hv).le
  refine ⟨k.natAbs, ?_, ?_⟩
  · rw [hk, ← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ h0 h1 (Int.le_natAbs)
  · rw [hk, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right_of_le_one₀ h0 h1 (by rw [Int.natCast_natAbs]; exact neg_abs_le k)

def treePseudoUniformizer (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    PseudoUniformizer K₀ K where
  ϖ := algebraMap R K₀ ϖ
  pos := v_algebraMap_pos hϖ
  lt_one := v_algebraMap_lt_one hϖ hv
  scale := exists_pow_le_v_algebraMap_le hϖ hint hv

@[scoped simp] theorem treePseudoUniformizer_ϖ (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    (treePseudoUniformizer hϖ hint hv).ϖ = algebraMap R K₀ ϖ := rfl

end PUTree

section Omega

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem mem_affinoid_of_v_sub_lt (ϖ : Omega.PseudoUniformizer K₀ K) {n : ℕ} {z w : K} (hz : z ∈ Omega.affinoid ϖ n)
    (hw : Valued.v (w - z) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n) : w ∈ Omega.affinoid ϖ n := by
  have hrr : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n :=
    (pow_le_one₀ ϖ.pos.le ϖ.lt_one.le).trans (one_le_pow₀ ((one_le_inv₀ ϖ.pos).2 ϖ.lt_one.le))
  rw [Omega.mem_affinoid_iff'] at hz ⊢
  refine ⟨?_, fun x => ?_⟩
  · have : w = z + (w - z) := by ring
    rw [this]
    exact Valuation.map_add_le _ hz.1 (hw.le.trans hrr)
  · have h1 : Valued.v (w - z) < Valued.v (z - algebraMap K₀ K x) := hw.trans_le (hz.2 x)
    have : w - algebraMap K₀ K x = (z - algebraMap K₀ K x) + (w - z) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ h1]
    exact hz.2 x

theorem exists_mem_upperHalfPlane_forall_pmoebius_ne (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hdisc : Omega.IsDiscrete K ρ)
    {x x' : K} (hx : x ∈ Omega.upperHalfPlane K₀ K) (hx' : x' ∈ Omega.upperHalfPlane K₀ K) :
    ∃ z₁ : K, z₁ ∈ Omega.upperHalfPlane K₀ K ∧ (∀ γ : G, Omega.pmoebius K₀ (ρ γ) x ≠ z₁) ∧
      (∀ γ : G, Omega.pmoebius K₀ (ρ γ) x' ≠ z₁) := by
  classical
  obtain ⟨n, hn⟩ := hex x hx
  obtain ⟨n', hn'⟩ := hex x' hx'
  set N := max n n' with hN
  have hxN : x ∈ Omega.affinoid ϖ N := Omega.affinoid_mono ϖ (le_max_left n n') hn
  have hx'N : x' ∈ Omega.affinoid ϖ N := Omega.affinoid_mono ϖ (le_max_right n n') hn'

  set z : ℕ → K := fun k => x + algebraMap K₀ K ϖ.ϖ ^ (k + N + 1) with hz
  have hzN : ∀ k, z k ∈ Omega.affinoid ϖ N := fun k => by
    refine mem_affinoid_of_v_sub_lt ϖ hxN ?_
    rw [hz]; dsimp only
    rw [add_sub_cancel_left, Valuation.map_pow]
    exact pow_lt_pow_right_of_lt_one₀ ϖ.pos ϖ.lt_one (by omega)
  have hzinj : Function.Injective z := by
    intro k k' h
    rw [hz] at h
    have h' : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (k + N + 1) = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (k' + N + 1) := by
      rw [← Valuation.map_pow, ← Valuation.map_pow]; exact congrArg _ (add_left_cancel h)
    have := pow_right_injective₀ ϖ.pos ϖ.lt_one.ne h'
    omega

  have hfin : {γ : G | Omega.pmoebius K₀ (ρ γ) x ∈ Omega.affinoid ϖ N}.Finite :=
    CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid ϖ ρ hdisc N hxN
  have hfin' : {γ : G | Omega.pmoebius K₀ (ρ γ) x' ∈ Omega.affinoid ϖ N}.Finite :=
    CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid ϖ ρ hdisc N hx'N
  have hbad : {k : ℕ | ∃ γ : G, Omega.pmoebius K₀ (ρ γ) x = z k ∨ Omega.pmoebius K₀ (ρ γ) x' = z k}.Finite := by
    refine Set.Finite.subset ((((hfin.image fun γ => Omega.pmoebius K₀ (ρ γ) x).union
      (hfin'.image fun γ => Omega.pmoebius K₀ (ρ γ) x')).preimage (hzinj.injOn))) ?_
    rintro k ⟨γ, h | h⟩
    · exact Or.inl ⟨γ, by rw [Set.mem_setOf_eq, h]; exact hzN k, h⟩
    · exact Or.inr ⟨γ, by rw [Set.mem_setOf_eq, h]; exact hzN k, h⟩
  obtain ⟨k, -, hk⟩ := Set.Infinite.exists_notMem_finite (Set.infinite_univ (α := ℕ)) hbad
  simp only [Set.mem_setOf_eq, not_exists, not_or] at hk
  exact ⟨z k, Omega.affinoid_subset_upperHalfPlane ϖ N (hzN k), fun γ => (hk γ).1, fun γ => (hk γ).2⟩

end Omega

theorem exists_mem_affinoid_zero
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) [Finite (R ⧸ Ideal.span {ϖ₀})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ₀)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ : Omega.PseudoUniformizer K₀ K) (hϖ : algebraMap R K₀ ϖ₀ = ϖ.ϖ) (hex : Omega.IsExhausted ϖ) :
    ∃ w : K, w ∈ Omega.affinoid ϖ 0 := by

  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K₀ K ϖ.ϖ) (show 0 < 2 by norm_num)
  have h2 : Valued.v y ^ 2 = Valued.v (algebraMap K₀ K ϖ.ϖ) := by rw [← Valuation.map_pow, hy]
  have hy0 : 0 < Valued.v y := by
    rw [Valuation.pos_iff]; rintro rfl
    rw [zero_pow two_ne_zero] at hy; exact ϖ.pos.ne' (by rw [← hy, Valuation.map_zero])
  have hy1 : Valued.v y < 1 := by
    by_contra h; rw [not_lt] at h
    have h' : 1 ≤ Valued.v y ^ 2 := one_le_pow₀ h
    rw [h2] at h'
    exact absurd ϖ.lt_one (not_lt.2 h')
  have hyr : Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v y := by
    rw [← h2, pow_two]
    calc Valued.v y * Valued.v y < Valued.v y * 1 := mul_lt_mul_of_pos_left hy1 hy0
      _ = Valued.v y := mul_one _
  have hyΩ : y ∈ Omega.upperHalfPlane K₀ K := by
    rw [Omega.mem_upperHalfPlane_iff]
    rintro a rfl
    rcases v_algebraMap_le_or_one_le hϖ₀ hint hv a with h | h
    · rw [hϖ] at h; exact absurd hyr (not_lt.2 h)
    · exact absurd hy1 (not_lt.2 h)
  obtain ⟨-, -, w, -, -, -, hw, -⟩ :=
    CerednikDrinfeld.Omega.exists_adj_min_le_v_apply_le_max_of_isUnit R K₀ ϖ₀ hϖ₀ K hint hv hq ϖ hrk hex 1 isUnit_one ⟨y, hyΩ⟩
  exact ⟨w, hw⟩

end ProjS1
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_periodPairing_pullback_eq_periodPairing_pushforward_of_mumfordQuotient_theta.ProjS1"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_periodPairing_pullback_eq_periodPairing_pushforward_of_mumfordQuotient_theta.ProjS1"

theorem Skel.comp_transfer {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    {A B : Type*} [CommGroup A] [CommGroup B] (ϕ : ↥H →* A) (f : A →* B) :
    f.comp ϕ.transfer = (f.comp ϕ).transfer := by
  ext g
  rw [MonoidHom.comp_apply, MonoidHom.transfer_def ϕ default g, MonoidHom.transfer_def (f.comp ϕ) default g]
  unfold Subgroup.leftTransversals.diff
  simp only [map_prod, MonoidHom.comp_apply]

set_option maxHeartbeats 8000000 in
theorem solution

    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)

    (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion] [DecidableEq A.valuation.Completion]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ A.valuation.Completion x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ A.valuation.Completion) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)
    (hϖr : Valued.v (algebraMap K₀ A.valuation.Completion ϖ.ϖ) = Valued.v ((r : ℕ) : A.valuation.Completion))

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    [Mumford.GraphAction PGL(2, K₀) (BruhatTits.tree R₀ K₀)]
    [DecidablePred (· ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)

    (Γd : Subgroup G) (htpd : Γd.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfind : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γd.map ρ)) d))

    (Fd : Type) [Field Fd] [Algebra A.valuation.Completion Fd] [hcurved : IsCurveOver A.valuation.Completion Fd]
    (eFd : Fd ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd))

    (Ed Vd : Type) [Fintype Ed] [Fintype Vd] [DecidableEq Ed] [DecidableEq Vd]
    (Dd : DegeneracyData Ed Vd)
    (eVd : Mumford.QuotVert ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ Vd)
    (eEd : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ Ed)
    (hDad : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dd.a (eEd e) = eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDbd : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dd.b (eEd e) = eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDwd : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (Dd.w (eEd e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γd.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀))]
    (Φd : Additive (Abelianization ↥(Γd.map ρ)) →+ ↥(ribbonKernel Dd))
    (hΦd : ∀ γ : ↥(Γd.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φd (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel Dd)) : Ed → ℤ) (eEd e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (ptd : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion Fd)
    (hpt_fibd : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), ptd z = ptd z' ↔ ∃ γ : ↥(Γd.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_ontod : Function.Surjective ptd)

    (hptd : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : Fd),
        x ∈ (ptd z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFd x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (ptd z).evalAt (eFd.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFd.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (ptd z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (Γc : Subgroup G) (htpc : Γc.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfinc : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γc.map ρ)) d))

    (Fc : Type) [Field Fc] [Algebra A.valuation.Completion Fc] [hcurvec : IsCurveOver A.valuation.Completion Fc]
    (eFc : Fc ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc))

    (Ec Vc : Type) [Fintype Ec] [Fintype Vc] [DecidableEq Ec] [DecidableEq Vc]
    (Dc : DegeneracyData Ec Vc)
    (eVc : Mumford.QuotVert ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ Vc)
    (eEc : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ Ec)
    (hDac : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dc.a (eEc e) = eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDbc : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dc.b (eEc e) = eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDwc : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (Dc.w (eEc e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γc.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀))]
    (Φc : Additive (Abelianization ↥(Γc.map ρ)) →+ ↥(ribbonKernel Dc))
    (hΦc : ∀ γ : ↥(Γc.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φc (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel Dc)) : Ec → ℤ) (eEc e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (ptc : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion Fc)
    (hpt_fibc : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), ptc z = ptc z' ↔ ∃ γ : ↥(Γc.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_ontoc : Function.Surjective ptc)

    (hptc : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : Fc),
        x ∈ (ptc z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFc x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (ptc z).evalAt (eFc.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFc.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (ptc z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (actZd : S →* (↥(ribbonKernel Dd) ≃ₗ[ℤ] ↥(ribbonKernel Dd))) (gald : S →* SemilinearAut A.valuation.Completion Fd)
    (actZc : S →* (↥(ribbonKernel Dc) ≃ₗ[ℤ] ↥(ribbonKernel Dc))) (galc : S →* SemilinearAut A.valuation.Completion Fc)
    (𝒰d : EquivariantUniformization r Dd A hA (Pic0 A.valuation.Completion Fd) S scalar actZd
      ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion Fd) (Pic0 A.valuation.Completion Fd)).comp gald))
    (𝒰c : EquivariantUniformization r Dc A hA (Pic0 A.valuation.Completion Fc) S scalar actZc
      ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion Fc) (Pic0 A.valuation.Completion Fc)).comp galc))
    (hQd : (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γd.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γd.map ρ),
          ((((Additive.toMul (𝒰d.P.Q (Φd (Additive.ofMul (Abelianization.of α))) (Φd (Additive.ofMul (Abelianization.of β))))) :
              (↥𝒰d.K)ˣ) : ↥𝒰d.K) : A.valuation.Completion) * Omega.period (Γd.map ρ).subtype x y α β = 1))
    (hΘd : (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γd.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γd.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γd.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γd.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γd.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : 𝒰d.P.TorusPoints), (∀ γ : ↥(Γd.map ρ), u (Φd (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := Fd),
          (Dv : Divisor A.valuation.Completion Fd) = Finsupp.single (ptd ⟨a, ha⟩) 1 - Finsupp.single (ptd ⟨b, hb⟩) 1 →
          𝒰d.eFull u = Pic0.mk Dv))
    (hQc : (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γc.map ρ),
          ((((Additive.toMul (𝒰c.P.Q (Φc (Additive.ofMul (Abelianization.of α))) (Φc (Additive.ofMul (Abelianization.of β))))) :
              (↥𝒰c.K)ˣ) : ↥𝒰c.K) : A.valuation.Completion) * Omega.period (Γc.map ρ).subtype x y α β = 1))
    (hΘc : (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γc.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γc.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γc.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : 𝒰c.P.TorusPoints), (∀ γ : ↥(Γc.map ρ), u (Φc (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := Fc),
          (Dv : Divisor A.valuation.Completion Fc) = Finsupp.single (ptc ⟨a, ha⟩) 1 - Finsupp.single (ptc ⟨b, hb⟩) 1 →
          𝒰c.eFull u = Pic0.mk Dv))

    (g : G) (hg : ρ g ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) (hArr : Γd ≤ Γc.map (MulAut.conj g).toMonoidHom)
    (φ : Fc →ₐ[A.valuation.Completion] Fd)
    (hφ : ∀ x : Fc, ((eFd (φ x) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd)) : FractionRing (Omega.HolRingOf ϖ ρ)) =
      g • ((eFc x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc)) : FractionRing (Omega.HolRingOf ϖ ρ)))
    (hφC : φ.toRingHom.IsIntegral) (hfinC : FiniteAlong A.valuation.Completion φ) (hsepC : SeparableAlong A.valuation.Completion φ)
    (μ : Dd.FiniteHom Dc)
    (hμV : ∀ v : LT.LatticeTree.Vertex R₀ K₀, μ.mapV (eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) =
      eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) ((ρ g)⁻¹ • v)))
    (hμE : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, ((eEc.symm (μ.mapE (eEd e))).1) = Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀).Dart) ((ρ g)⁻¹ • e.1.out))
    (hdeg : ((μ.degTotal : ℕ)) = finrankAlong A.valuation.Completion φ) :
    ∀ (x : ↥(ribbonKernel Dc)) (y : ↥(ribbonKernel Dd)),
      ((((Additive.toMul (𝒰d.P.Q (μ.pullback x) y)) : (↥𝒰d.K)ˣ) : ↥𝒰d.K) : A.valuation.Completion) =
        ((((Additive.toMul (𝒰c.P.Q x (μ.pushforward y))) : (↥𝒰c.K)ˣ) : ↥𝒰c.K) : A.valuation.Completion) := by

  classical
  intro x y

  have hT : (BruhatTits.tree R₀ K₀).IsTree := CerednikDrinfeld.BruhatTits.tree_isTree R₀ K₀
  have hcb := CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R₀ K₀
  have hadj : ∀ u v : LT.LatticeTree.Vertex R₀ K₀, (BruhatTits.tree R₀ K₀).Adj u v →
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) u ≠ Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) v := by
    have hadj' := (CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
      PGL(2, K₀) (BruhatTits.tree R₀ K₀) hcb.1 hcb.2 (LT.LatticeTree.stdVertex R₀ K₀)).1
    intro u v huv h
    have h1 := hadj' u v huv
    rw [← h] at h1
    exact one_ne_zero (add_left_cancel (h1.symm.trans (add_zero _).symm))
  have hτd : ∀ (g : ↥(Γd.map ρ)) (w : LT.LatticeTree.Vertex R₀ K₀),
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (g • w) = Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w :=
    fun g w => (Mumford.mem_typePreserving_iff (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (g : PGL(2, K₀))).1 (htpd g.2) w
  have hτc : ∀ (g : ↥(Γc.map ρ)) (w : LT.LatticeTree.Vertex R₀ K₀),
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (g • w) = Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w :=
    fun g w => (Mumford.mem_typePreserving_iff (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (g : PGL(2, K₀))).1 (htpc g.2) w

  have haBSd : ∀ e : Ed, eVd.symm (Dd.a e) = Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eEd.symm e).1.out.fst :=
    fun e => eVd.symm_apply_eq.mpr (by have h := hDad (eEd.symm e); rwa [Equiv.apply_symm_apply] at h)
  have hbBSd : ∀ e : Ed, eVd.symm (Dd.b e) = Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eEd.symm e).1.out.snd :=
    fun e => eVd.symm_apply_eq.mpr (by have h := hDbd (eEd.symm e); rwa [Equiv.apply_symm_apply] at h)
  have haBSc : ∀ e : Ec, eVc.symm (Dc.a e) = Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eEc.symm e).1.out.fst :=
    fun e => eVc.symm_apply_eq.mpr (by have h := hDac (eEc.symm e); rwa [Equiv.apply_symm_apply] at h)
  have hbBSc : ∀ e : Ec, eVc.symm (Dc.b e) = Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eEc.symm e).1.out.snd :=
    fun e => eVc.symm_apply_eq.mpr (by have h := hDbc (eEc.symm e); rwa [Equiv.apply_symm_apply] at h)
  have hΦBSd : ∀ γ : ↥(Γd.map ρ), ((Φd (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel Dd)) : Ed → ℤ) =
      Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e : Ed => (eEd.symm e).1) v₀ γ := by
    intro γ; funext e₁
    have h := hΦd γ (eEd.symm e₁)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
    unfold Mumford.pathCycle
    split_ifs <;> rfl
  have hΦBSc : ∀ γ : ↥(Γc.map ρ), ((Φc (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel Dc)) : Ec → ℤ) =
      Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e : Ec => (eEc.symm e).1) v₀ γ := by
    intro γ; funext e₁
    have h := hΦc γ (eEc.symm e₁)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
    unfold Mumford.pathCycle
    split_ifs <;> rfl

  have hHG₂ : ∀ h : PGL(2, K₀), h ∈ Γd.map ρ → (ρ g)⁻¹ * h * ρ g ∈ Γc.map ρ := by
    rintro h ⟨γ, hγ, rfl⟩
    obtain ⟨γ', hγ', hconj⟩ := Subgroup.mem_map.mp (hArr hγ)
    refine ⟨g⁻¹ * γ * g, ?_, by simp [map_mul, map_inv]⟩
    have : g⁻¹ * γ * g = γ' := by
      rw [← hconj]; simp [MulAut.conj_apply, mul_assoc]
    rw [this]; exact hγ'
  let Γ' : Subgroup ↥(Γc.map ρ) :=
    (Γd.map ρ).comap ((MulAut.conj (ρ g)).toMonoidHom.comp (Γc.map ρ).subtype)
  have hΓ' : ∀ x : ↥(Γc.map ρ), x ∈ Γ' ↔ ρ g * (x : PGL(2, K₀)) * (ρ g)⁻¹ ∈ Γd.map ρ := by
    intro x
    simp only [Γ', Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  haveI : Mumford.GraphAction ↥Γ' (BruhatTits.tree R₀ K₀) := Skel.graphAction_subgroup (BruhatTits.tree R₀ K₀) Γ'
  have hp : ∀ w : LT.LatticeTree.Vertex R₀ K₀,
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (ρ g • w) =
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w :=
    (Mumford.mem_typePreserving_iff _ _ _).1 hg

  have hCT :=
    CerednikDrinfeld.Mumford.exists_presentation_conj_apply_eq_of_apply_eq_pathCycle
      (BruhatTits.tree R₀ K₀) hT (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hadj
      (Γd.map ρ) hτd (ρ g) hp (Γc.map ρ) hHG₂ Γ' hΓ'
      Dd eEd.symm eVd.symm haBSd hbBSd v₀ Φd hΦBSd
  obtain ⟨eE', eV', Φ', heE', heV', ha', hb', hΦ', hΦ'conj⟩ := hCT

  have hμE' : ∀ e₁ : Ed,
      ((eEc.symm (μ.mapE e₁)).1 : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀)) =
        Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀).Dart) ((eE' e₁).1).out := by
    intro e₁
    have h1 := hμE (eEd.symm e₁)
    rw [Equiv.apply_symm_apply] at h1
    rw [h1]
    have h2 := heE' e₁
    obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥Γ', γ' • ((ρ g)⁻¹ • (eEd.symm e₁).1.out) = ((eE' e₁).1).out :=
      Quotient.exact ((Quotient.out_eq ((eE' e₁).1)).trans h2)
    refine Quotient.sound ⟨((γ'⁻¹ : ↥Γ') : ↥(Γc.map ρ)), ?_⟩
    rw [← hγ']
    show ((γ'⁻¹ : ↥Γ') : ↥(Γc.map ρ)) • ((γ' : ↥(Γc.map ρ)) • ((ρ g)⁻¹ • (eEd.symm e₁).1.out)) = _
    rw [Subgroup.coe_inv, inv_smul_smul]

  have hPUSH := CerednikDrinfeld.Mumford.finiteHom_pushforward_apply_eq_of_forall_addMonoidHom_apply_eq_pathCycle
    (BruhatTits.tree R₀ K₀) hT (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hτc hadj
    Γ' Dd eE' Dc eEc.symm μ hμE' v₀ Φ' hΦ' Φc hΦBSc

  have hw₂ : ∀ e₂ : Ec, (Dc.w e₂ : ℕ) =
      Nat.card (MulAction.stabilizer ↥(Γc.map ρ) (((eEc.symm e₂).1).out : (BruhatTits.tree R₀ K₀).Dart)) := by
    intro e₂
    have h := hDwc (eEc.symm e₂)
    rwa [Equiv.apply_symm_apply] at h
  have hfinV : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Finite (MulAction.stabilizer ↥(Γc.map ρ) w) :=
    CerednikDrinfeld.BruhatTits.finite_stabilizer_vertex_of_finite_stabilizer_dart R₀ K₀ ↥(Γc.map ρ) hfinc
  haveI : Finite (MulAction.orbitRel.Quotient ↥Γ' (LT.LatticeTree.Vertex R₀ K₀)) := Finite.of_equiv Vd eV'
  haveI : Finite (MulAction.stabilizer ↥(Γc.map ρ) v₀) := hfinV v₀
  haveI hFI : Γ'.FiniteIndex := Skel.finiteIndex_of_finite_orbitQuotient_of_finite_stabilizer Γ' v₀
  have hw₁ : ∀ e₁ : Ed, (Dd.w e₁ : ℕ) =
      Nat.card (MulAction.stabilizer ↥Γ' ((((eE' e₁).1).out : (BruhatTits.tree R₀ K₀).Dart))) := by
    intro e₁

    have h2 := heE' e₁
    obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥Γ', γ' • ((ρ g)⁻¹ • (eEd.symm e₁).1.out) = ((eE' e₁).1).out :=
      Quotient.exact ((Quotient.out_eq ((eE' e₁).1)).trans h2)
    have hw := hDwd (eEd.symm e₁)
    rw [Equiv.apply_symm_apply] at hw
    rw [hw, ← Nat.card_congr (MulAction.stabilizerEquivStabilizer hγ'.symm).toEquiv]
    exact (Skel.card_stabilizer_inv_smul_eq (BruhatTits.tree R₀ K₀) (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂ _).symm
  have hPULL := CerednikDrinfeld.Mumford.finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer
    (BruhatTits.tree R₀ K₀) hT hfinV (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hτc hadj
    Γ' Dd eE' hw₁ Dc eEc.symm hw₂ μ hμE' v₀ Φ' hΦ' Φc hΦBSc

  have hΦonto_c := (CerednikDrinfeld.Mumford.surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle
    (BruhatTits.tree R₀ K₀) hT (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hτc hadj Dc eEc.symm eVc.symm haBSc hbBSc v₀ Φc hΦBSc).1
  have hΦonto_d := (CerednikDrinfeld.Mumford.surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle
    (BruhatTits.tree R₀ K₀) hT (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hτd hadj Dd eEd.symm eVd.symm haBSd hbBSd v₀ Φd hΦBSd).1
  have eαc : ∃ a : ↥(Γc.map ρ), Abelianization.of a = Additive.toMul (hΦonto_c x).choose :=
    QuotientGroup.mk_surjective _
  have hx : x = Φc (Additive.ofMul (Abelianization.of eαc.choose)) := by
    rw [eαc.choose_spec]; exact (hΦonto_c x).choose_spec.symm
  have eβd : ∃ b : ↥(Γd.map ρ), Abelianization.of b = Additive.toMul (hΦonto_d y).choose :=
    QuotientGroup.mk_surjective _
  have hy : y = Φd (Additive.ofMul (Abelianization.of eβd.choose)) := by
    rw [eβd.choose_spec]; exact (hΦonto_d y).choose_spec.symm

  have eβ'' : ∃ b : ↥Γ', ((b : ↥(Γc.map ρ)) : PGL(2, K₀)) = (ρ g)⁻¹ * (eβd.choose : PGL(2, K₀)) * ρ g := by
    refine ⟨⟨⟨(ρ g)⁻¹ * (eβd.choose : PGL(2, K₀)) * ρ g, hHG₂ _ eβd.choose.2⟩, (hΓ' _).2 ?_⟩, rfl⟩
    rw [show ρ g * ((ρ g)⁻¹ * ((eβd.choose : ↥(Γd.map ρ)) : PGL(2, K₀)) * ρ g) * (ρ g)⁻¹ = (eβd.choose : PGL(2, K₀)) by group]
    exact eβd.choose.2

  have eγ₀ : ∃ c : ↥Γ', Abelianization.of c =
      MonoidHom.transfer (Abelianization.of : ↥Γ' →* Abelianization ↥Γ') eαc.choose :=
    QuotientGroup.mk_surjective _

  haveI hAC : IsAlgClosed A.valuation.Completion := ValuationSubring.isAlgClosed_completion_of_liesOverPrime r Fact.out A hA
  have hrk3 := ValuationSubring.valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime r A hA
  have hrk : ∀ x y : A.valuation.Completion, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y := hrk3.2.2
  have hint : ∀ a : R₀, Valued.v (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ a)) ≤ 1 :=
    fun a => (hR₀ _).1 ⟨a, rfl⟩
  have hv : ∀ a : K₀, Valued.v (algebraMap K₀ A.valuation.Completion a) ≤ 1 → IsLocalization.IsInteger R₀ a := by
    intro a ha
    obtain ⟨b, hb⟩ := (hR₀ a).2 ha
    exact ⟨b, hb⟩
  have hq : ∀ ε : _, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ ϖ₀)) ^ N ≤ ε := by
    intro ε hε
    obtain ⟨q, hq⟩ := A.valuation_surjective ε
    have hy : Valued.v ((q : AlgebraicClosure ℚ) : A.valuation.Completion) = ε := by
      rw [← hq]; exact Valued.valuedCompletion_apply _
    have hy0 : ((q : AlgebraicClosure ℚ) : A.valuation.Completion) ≠ 0 := fun h => by
      rw [h, Valuation.map_zero] at hy; exact hε hy.symm
    have hlt : Valued.v (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ ϖ₀)) < 1 := by
      rw [hϖ]; exact ϖ.lt_one
    obtain ⟨N, hN⟩ := hrk _ _ hlt hy0
    exact ⟨N, hy ▸ hN⟩
  haveI hfinq : Finite (R₀ ⧸ Ideal.span {ϖ₀}) := by
    have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).mp hϖ₀
    exact Finite.of_equiv (IsLocalRing.ResidueField R₀) (Ideal.quotEquivOfEq hmax).toEquiv
  haveI : IsDomain ↥(Omega.holRing ϖ) := (Omega.HolRingOf.isDomain_iff ϖ ρ).1 inferInstance
  have hdisc : Omega.IsDiscrete A.valuation.Completion (Γc.map ρ).subtype := by
    refine CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex R₀ K₀ ϖ₀ hϖ₀ A.valuation.Completion hint hv hq
      (Γc.map ρ).subtype ?_
    haveI := hfinV (LT.LatticeTree.stdVertex R₀ K₀)
    exact Set.Finite.subset (s := (MulAction.stabilizer (↥(Γc.map ρ)) (LT.LatticeTree.stdVertex R₀ K₀) : Set _))
      (Set.toFinite _) (fun γ hγ => hγ)

  have ex₁ := ProjS1.exists_mem_affinoid_zero R₀ K₀ ϖ₀ hϖ₀ A.valuation.Completion hint hv hq hrk ϖ hϖ hex
  have hx₁ : ex₁.choose ∈ Omega.upperHalfPlane K₀ A.valuation.Completion := Omega.affinoid_subset_upperHalfPlane ϖ 0 ex₁.choose_spec
  have ey₁ := ProjS1.exists_mem_upperHalfPlane_forall_pmoebius_ne ϖ hex (Γc.map ρ).subtype hdisc hx₁ hx₁
  have hy₁ : ey₁.choose ∈ Omega.upperHalfPlane K₀ A.valuation.Completion := ey₁.choose_spec.1
  have hxy₁ : ∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ ((Γc.map ρ).subtype γ) ex₁.choose ≠ ey₁.choose := ey₁.choose_spec.2.1

  have hxy₁' : ∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) ex₁.choose ≠ ey₁.choose := hxy₁
  have hb' : Omega.pmoebius K₀ ((Γc.map ρ).subtype (eβ''.choose : ↥(Γc.map ρ))) ex₁.choose ∈ Omega.upperHalfPlane K₀ A.valuation.Completion :=
    Omega.pmoebius_mem_upperHalfPlane K₀ hx₁ _
  have hxy₁b : ∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ ((Γc.map ρ).subtype γ)
      (Omega.pmoebius K₀ ((Γc.map ρ).subtype (eβ''.choose : ↥(Γc.map ρ))) ex₁.choose) ≠ ey₁.choose := by
    intro γ
    rw [← Omega.pmoebius_mul K₀ hx₁, ← map_mul]
    exact hxy₁ _

  have he : ∀ γ : ↥Γ', (Γd.map ρ).subtype (Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂ γ) =
      ρ g * ((Γc.map ρ).subtype.comp Γ'.subtype) γ * (ρ g)⁻¹ := fun γ => rfl
  have hpx₁ : Omega.pmoebius K₀ (ρ g) ex₁.choose ∈ Omega.upperHalfPlane K₀ A.valuation.Completion := Omega.pmoebius_mem_upperHalfPlane K₀ hx₁ _
  have hpy₁ : Omega.pmoebius K₀ (ρ g) ey₁.choose ∈ Omega.upperHalfPlane K₀ A.valuation.Completion := Omega.pmoebius_mem_upperHalfPlane K₀ hy₁ _
  have hpxy₁ : ∀ δ : ↥(Γd.map ρ), Omega.pmoebius K₀ (δ : PGL(2, K₀)) (Omega.pmoebius K₀ (ρ g) ex₁.choose) ≠
      Omega.pmoebius K₀ (ρ g) ey₁.choose := by
    intro δ h

    have hδ : (δ : PGL(2, K₀)) = ρ g * (((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂).symm δ : ↥Γ') : ↥(Γc.map ρ)) * (ρ g)⁻¹ := by
      conv_lhs => rw [← (Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂).apply_symm_apply δ]
      rfl
    rw [hδ, ← Omega.pmoebius_mul K₀ hx₁, mul_assoc, inv_mul_cancel, mul_one, Omega.pmoebius_mul K₀ hx₁] at h
    have h2 := congrArg (Omega.pmoebius K₀ (ρ g)⁻¹) h
    rw [← Omega.pmoebius_mul K₀ (Omega.pmoebius_mem_upperHalfPlane K₀ hx₁ _), ← Omega.pmoebius_mul K₀ hy₁,
      inv_mul_cancel, Omega.pmoebius_one, Omega.pmoebius_one] at h2
    exact hxy₁' _ h2

  have hc : ∀ β : ↥(Γc.map ρ),
      (((Skel.qCharInv 𝒰c.K Φc (𝒰c.P.Q (Φc (Additive.ofMul (Abelianization.of (eβ''.choose : ↥(Γc.map ρ))))))) β : (A.valuation.Completion)ˣ) : A.valuation.Completion) =
      Omega.theta (Γc.map ρ).subtype ex₁.choose (Omega.pmoebius K₀ ((Γc.map ρ).subtype (eβ''.choose : ↥(Γc.map ρ))) ex₁.choose)
        ey₁.choose (Omega.pmoebius K₀ ((Γc.map ρ).subtype β) ey₁.choose) := by
    intro β
    have hpin := hQc _ _ hx₁ hy₁ hxy₁' (eβ''.choose : ↥(Γc.map ρ)) β
    rw [Skel.qCharInv_apply]
    exact inv_eq_of_mul_eq_one_right hpin
  have hc' : ∀ γ : ↥Γ',
      ((((Skel.qCharInv 𝒰d.K Φd (𝒰d.P.Q (Φd (Additive.ofMul (Abelianization.of ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eβ''.choose)))))).comp (Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂).toMonoidHom) γ : (A.valuation.Completion)ˣ) : A.valuation.Completion) =
      Omega.theta (((Γc.map ρ).subtype).comp Γ'.subtype) ex₁.choose
        (Omega.pmoebius K₀ ((Γc.map ρ).subtype (eβ''.choose : ↥(Γc.map ρ))) ex₁.choose)
        ey₁.choose (Omega.pmoebius K₀ ((Γc.map ρ).subtype (γ : ↥(Γc.map ρ))) ey₁.choose) := by
    intro γ
    have hpin := hQd _ _ hpx₁ hpy₁ hpxy₁ ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eβ''.choose) ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) γ)
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Skel.qCharInv_apply]
    exact (inv_eq_of_mul_eq_one_right hpin).trans
      (CerednikDrinfeld.Omega.period_pmoebius_pmoebius_of_mulEquiv_of_apply_eq_conj
        (((Γc.map ρ).subtype).comp Γ'.subtype) (Γd.map ρ).subtype (Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) (ρ g) he hx₁ hy₁ eβ''.choose γ)

  have hTR := CerednikDrinfeld.Omega.eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype K₀ A.valuation.Completion ϖ hex
    (Γc.map ρ).subtype hdisc Γ' hx₁ hb' hy₁ hxy₁ hxy₁b ((Skel.qCharInv 𝒰d.K Φd (𝒰d.P.Q (Φd (Additive.ofMul (Abelianization.of ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eβ''.choose)))))).comp (Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂).toMonoidHom) hc' (Skel.qCharInv 𝒰c.K Φc (𝒰c.P.Q (Φc (Additive.ofMul (Abelianization.of (eβ''.choose : ↥(Γc.map ρ))))))) hc

  have key : ∀ (c₂ : ↥Γ' →* (A.valuation.Completion)ˣ) (a : ↥(Γc.map ρ)) (g₀ : ↥Γ'),
      Abelianization.of g₀ = MonoidHom.transfer (Abelianization.of : ↥Γ' →* Abelianization ↥Γ') a →
      MonoidHom.transfer c₂ a = c₂ g₀ := by
    intro c₂ a g₀ hg₀
    have hfac : (Abelianization.lift c₂).comp Abelianization.of = c₂ :=
      MonoidHom.ext fun x => by simp only [MonoidHom.comp_apply, Abelianization.lift_apply_of]
    have h1 : MonoidHom.transfer c₂ a = MonoidHom.transfer ((Abelianization.lift c₂).comp Abelianization.of) a := by
      rw [hfac]
    have h2 : MonoidHom.transfer ((Abelianization.lift c₂).comp Abelianization.of) a =
        ((Abelianization.lift c₂).comp (MonoidHom.transfer (Abelianization.of : ↥Γ' →* Abelianization ↥Γ'))) a := by
      rw [Skel.comp_transfer]
    have h3 : ((Abelianization.lift c₂).comp (MonoidHom.transfer (Abelianization.of : ↥Γ' →* Abelianization ↥Γ'))) a = c₂ g₀ := by
      rw [MonoidHom.comp_apply, ← hg₀, Abelianization.lift_apply_of]
    exact h1.trans (h2.trans h3)
  have hev : (Skel.qCharInv 𝒰c.K Φc (𝒰c.P.Q (Φc (Additive.ofMul (Abelianization.of (eβ''.choose : ↥(Γc.map ρ))))))) eαc.choose = ((Skel.qCharInv 𝒰d.K Φd (𝒰d.P.Q (Φd (Additive.ofMul (Abelianization.of ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eβ''.choose)))))).comp (Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂).toMonoidHom) eγ₀.choose :=
    (DFunLike.congr_fun hTR eαc.choose).trans (key _ _ _ eγ₀.choose_spec)
  have hev' := congrArg Units.val hev
  have hL := Skel.qCharInv_apply 𝒰c.K Φc (𝒰c.P.Q (Φc (Additive.ofMul (Abelianization.of (eβ''.choose : ↥(Γc.map ρ)))))) eαc.choose
  have hR := Skel.qCharInv_apply 𝒰d.K Φd (𝒰d.P.Q (Φd (Additive.ofMul (Abelianization.of ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eβ''.choose))))) ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eγ₀.choose)
  have hM : ((((Skel.qCharInv 𝒰d.K Φd (𝒰d.P.Q (Φd (Additive.ofMul (Abelianization.of ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eβ''.choose)))))).comp (Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂).toMonoidHom) eγ₀.choose : (A.valuation.Completion)ˣ) : A.valuation.Completion) =
      (((Skel.qCharInv 𝒰d.K Φd (𝒰d.P.Q (Φd (Additive.ofMul (Abelianization.of ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eβ''.choose)))))) ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eγ₀.choose) : (A.valuation.Completion)ˣ) : A.valuation.Completion) := rfl
  have hevQ : (((((Additive.toMul (𝒰c.P.Q (Φc (Additive.ofMul (Abelianization.of (eβ''.choose : ↥(Γc.map ρ))))) (Φc (Additive.ofMul (Abelianization.of eαc.choose))))) : (↥𝒰c.K)ˣ) : ↥𝒰c.K) : A.valuation.Completion))⁻¹ =
      (((((Additive.toMul (𝒰d.P.Q (Φd (Additive.ofMul (Abelianization.of ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eβ''.choose)))) (Φd (Additive.ofMul (Abelianization.of ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eγ₀.choose)))))) : (↥𝒰d.K)ˣ) : ↥𝒰d.K) : A.valuation.Completion))⁻¹ :=
    hL.symm.trans (hev'.trans (hM.trans hR))

  have hΦ'e : ∀ γ : ↥Γ', Φ' (Additive.ofMul (Abelianization.of γ)) =
      Φd (Additive.ofMul (Abelianization.of ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) γ))) := fun γ => hΦ'conj γ
  have hβe : eβd.choose = (Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eβ''.choose := Subtype.ext (by
    rw [Skel.conjEquiv_apply_coe, eβ''.choose_spec]; group)
  have hxμ : μ.pullback x = Φd (Additive.ofMul (Abelianization.of ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eγ₀.choose))) :=
    ((congrArg μ.pullback hx).trans (hPULL _)).trans
      ((congrArg (fun t => Φ' (Additive.ofMul t)) eγ₀.choose_spec.symm).trans (hΦ'e _))
  have hy' : y = Φd (Additive.ofMul (Abelianization.of ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eβ''.choose))) :=
    hy.trans (congrArg (fun b : ↥(Γd.map ρ) => Φd (Additive.ofMul (Abelianization.of b))) hβe)
  have hyμ : μ.pushforward y = Φc (Additive.ofMul (Abelianization.of (eβ''.choose : ↥(Γc.map ρ)))) :=
    ((congrArg μ.pushforward hy').trans (congrArg μ.pushforward (hΦ'e _).symm)).trans (hPUSH _)
  have eL : 𝒰d.P.Q (μ.pullback x) y = 𝒰d.P.Q (Φd (Additive.ofMul (Abelianization.of ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eβ''.choose)))) (Φd (Additive.ofMul (Abelianization.of ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eγ₀.choose)))) :=
    (congrArg (fun t => 𝒰d.P.Q t y) hxμ).trans
      ((congrArg (fun t => 𝒰d.P.Q (Φd (Additive.ofMul (Abelianization.of ((Skel.conjEquiv (Γd.map ρ) (Γc.map ρ) (ρ g) Γ' hΓ' hHG₂) eγ₀.choose)))) t) hy').trans (𝒰d.P.Q_symm _ _))
  have eR : 𝒰c.P.Q x (μ.pushforward y) = 𝒰c.P.Q (Φc (Additive.ofMul (Abelianization.of (eβ''.choose : ↥(Γc.map ρ))))) (Φc (Additive.ofMul (Abelianization.of eαc.choose))) :=
    (congrArg (fun t => 𝒰c.P.Q x t) hyμ).trans
      ((congrArg (fun t => 𝒰c.P.Q t (Φc (Additive.ofMul (Abelianization.of (eβ''.choose : ↥(Γc.map ρ)))))) hx).trans (𝒰c.P.Q_symm _ _))
  have gL := congrArg (fun u => ((((Additive.toMul u) : (↥𝒰d.K)ˣ) : ↥𝒰d.K) : A.valuation.Completion)) eL
  have gR := congrArg (fun u => ((((Additive.toMul u) : (↥𝒰c.K)ˣ) : ↥𝒰c.K) : A.valuation.Completion)) eR
  exact gL.trans ((inv_injective hevQ).symm.trans gR.symm)

end S_AlgebraicCurve_Pic0_periodPairing_pullback_eq_periodPairing_pushforward_of_mumfordQuotient_theta
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_periodPairing_pullback_eq_periodPairing_pushforward_of_mumfordQuotient_theta (solution)
