-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ff50eac6-a0a6-577c-b582-d62c1dea8638

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.OrderOfElement
import Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_eq_period_of_isUnit_of_apply_smul_eq_mul_of_forall_isOfFinOrder
import Theorems.Thm_CerednikDrinfeld_Omega_theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder
import Theorems.Thm_CerednikDrinfeld_Omega_dvd_of_forall_ordAt_le
import Theorems.Thm_CerednikDrinfeld_Omega_affinoid_nonempty_of_exists_finset_cover
import Theorems.Thm_CerednikDrinfeld_Omega_eq_one_of_pmoebius_eq_of_mem_affinoid_zero
import Theorems.Thm_CerednikDrinfeld_Omega_smul_stdVertex_eq_of_mem_affinoid_zero
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Theorems.Thm_CerednikDrinfeld_Omega_ord_place_invariantFieldOf_mul_card_stabilizer_eq_ordAt_sub_ordAt_of_cast_card_ne_zero_of_map_le_typePreserving_of_exists_v_le_of_v_card_eq_one
import Theorems.Thm_CerednikDrinfeld_Omega_ordAt_mul
import Theorems.Thm_CerednikDrinfeld_Omega_exists_isThetaPair_ordAt_eq_card
import Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_fracAct_thetaMer_eq
import Theorems.Thm_CerednikDrinfeld_Mumford_div_mem_invariantFieldOf_of_smul_eq_algebraMap_mul
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMer_eq_mk_of_isThetaPair
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_ValuationSubring_isAlgClosed_completion_of_liesOverPrime
import Theorems.Thm_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime
import Theorems.Thm_CerednikDrinfeld_Omega_forall_exists_finset_v_sub_lt_pow_of_finite_quotient
import Theorems.Thm_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one
p2m_attr_erase "simp" "CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford~finite_stabilizer_of_finite_stabilizer_dart AlgebraicCurve ModularCurve"

noncomputable section

namespace ECOmegaD

section Constants

theorem hrk {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∀ x y : A.valuation.Completion, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y :=
  (ValuationSubring.valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime r A hA).2.2

theorem v_coe_algebraicClosure (A : ValuationSubring (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ) :
    Valued.v ((x : A.valuation.Completion)) = A.valuation x := by
  rw [Valued.valuedCompletion_apply]; rfl

theorem exists_v_eq (A : ValuationSubring (AlgebraicClosure ℚ)) (ε : A.ValueGroup) (hε : ε ≠ 0) :
    ∃ y : A.valuation.Completion, y ≠ 0 ∧ Valued.v y = ε := by
  obtain ⟨x, hx⟩ := A.valuation_surjective ε
  refine ⟨((x : AlgebraicClosure ℚ) : A.valuation.Completion), ?_, ?_⟩
  · intro h0
    apply hε
    rw [← hx, ← v_coe_algebraicClosure A x, h0, Valuation.map_zero]
  · rw [← hx, v_coe_algebraicClosure]

variable {C : Type} [Field C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {K₀ : Type} [Field K₀] [Algebra K₀ C]
  {R₀ : Type} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]

theorem hint (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ C x) ≤ 1) :
    ∀ t : R₀, Valued.v (algebraMap K₀ C (algebraMap R₀ K₀ t)) ≤ 1 :=
  fun t => (hR₀ _).mp ⟨t, rfl⟩

theorem hv (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ C x) ≤ 1) :
    ∀ x : K₀, Valued.v (algebraMap K₀ C x) ≤ 1 → IsLocalization.IsInteger R₀ x :=
  fun x hx => by obtain ⟨t, ht⟩ := (hR₀ x).mpr hx; exact ⟨t, ht⟩

theorem finite_quot [Finite (IsLocalRing.ResidueField R₀)] {ϖ₀ : R₀} (hϖ₀ : Irreducible ϖ₀) :
    Finite (R₀ ⧸ Ideal.span {ϖ₀}) := by
  have hmax : IsLocalRing.maximalIdeal R₀ = Ideal.span {ϖ₀} := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ₀
  exact Finite.of_equiv (IsLocalRing.ResidueField R₀) (Ideal.quotEquivOfEq hmax).toEquiv

end Constants

section ConstantsA
variable {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
  (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion]
  (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]

theorem hq (hA : A.LiesOverPrime r) (ϖ : Omega.PseudoUniformizer K₀ A.valuation.Completion) (ϖ₀ : R₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ) :
    ∀ ε : A.ValueGroup, ε ≠ 0 →
      ∃ N : ℕ, Valued.v (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ ϖ₀)) ^ N ≤ ε := by
  intro ε hε
  obtain ⟨y, hy0, hy⟩ := exists_v_eq A ε hε
  obtain ⟨N, hN⟩ := hrk A hA (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ ϖ₀)) y
    (by rw [hϖ]; exact ϖ.lt_one) hy0
  exact ⟨N, by rw [← hy]; exact hN⟩

theorem hfin [Finite (IsLocalRing.ResidueField R₀)] (hA : A.LiesOverPrime r)
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ A.valuation.Completion x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ A.valuation.Completion) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀)
    (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ) : ∀ n : ℕ, ∃ T : Finset K₀, ∀ x : K₀,
    Valued.v (algebraMap K₀ A.valuation.Completion x) ≤ (Valued.v (algebraMap K₀ A.valuation.Completion ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ A.valuation.Completion x - algebraMap K₀ A.valuation.Completion t) <
        (Valued.v (algebraMap K₀ A.valuation.Completion ϖ.ϖ)) ^ n := by
  haveI := finite_quot hϖ₀
  exact CerednikDrinfeld.Omega.forall_exists_finset_v_sub_lt_pow_of_finite_quotient R₀ K₀ ϖ₀ hϖ₀ A.valuation.Completion
    (hint hR₀) (hv hR₀) (hq A K₀ R₀ hA ϖ ϖ₀ hϖ) ϖ

end ConstantsA

section GapC

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

theorem finite_stabilizer_of_finite_stabilizer_dart (w : W)
    (hnbr : (𝒯.neighborSet w).Finite) (hne : (𝒯.neighborSet w).Nonempty)
    (hfin : ∀ d : 𝒯.Dart, Finite (MulAction.stabilizer G d)) : Finite (MulAction.stabilizer G w) := by
  classical
  obtain ⟨u, hu⟩ := hne
  let d₀ : 𝒯.Dart := ⟨(w, u), hu⟩
  haveI : Finite ↥(𝒯.neighborSet w) := hnbr.to_subtype
  haveI := hfin d₀
  have hsec : ∀ u' : ↥(𝒯.neighborSet w), ∃ s : G,
      (∃ g : MulAction.stabilizer G w, (g : G) • u = u') → (s • w = w ∧ s • u = u') := by
    intro u'
    by_cases h : ∃ g : MulAction.stabilizer G w, (g : G) • u = u'
    · obtain ⟨g, hg⟩ := h
      exact ⟨g, fun _ => ⟨g.2, hg⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose σ hσ using hsec
  have hmem : ∀ g : MulAction.stabilizer G w, (g : G) • u ∈ 𝒯.neighborSet w := fun g => by
    rw [SimpleGraph.mem_neighborSet]
    have := GraphAction.smul_adj (𝒯 := 𝒯) (g : G) hu
    rwa [show (g : G) • w = w from g.2] at this
  let F : MulAction.stabilizer G w → ↥(𝒯.neighborSet w) × MulAction.stabilizer G d₀ := fun g =>
    ⟨⟨(g : G) • u, hmem g⟩,
      ⟨(σ ⟨(g : G) • u, hmem g⟩)⁻¹ * g, by
        obtain ⟨hw, hu'⟩ := hσ ⟨(g : G) • u, hmem g⟩ ⟨g, rfl⟩
        rw [MulAction.mem_stabilizer_iff]
        apply SimpleGraph.Dart.ext
        refine Prod.ext ?_ ?_
        · show ((σ ⟨(g : G) • u, hmem g⟩)⁻¹ * g) • w = w
          rw [mul_smul, show (g : G) • w = w from g.2, inv_smul_eq_iff, hw]
        · show ((σ ⟨(g : G) • u, hmem g⟩)⁻¹ * g) • u = u
          rw [mul_smul, inv_smul_eq_iff]
          exact hu'.symm⟩⟩
  refine Finite.of_injective F (fun g g' hgg' => ?_)
  simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hgg'
  obtain ⟨h1, h2⟩ := hgg'
  apply Subtype.ext
  have : (σ ⟨(g : G) • u, hmem g⟩ : G) = σ ⟨(g' : G) • u, hmem g'⟩ := by
    congr 1; exact Subtype.ext h1
  rw [this] at h2
  exact mul_left_cancel h2

theorem smul_neighborSet (g : G) (w : W) : 𝒯.neighborSet (g • w) = (fun x => g • x) '' 𝒯.neighborSet w := by
  ext x
  rw [SimpleGraph.mem_neighborSet, Set.mem_image]
  constructor
  · intro h
    refine ⟨g⁻¹ • x, ?_, smul_inv_smul g x⟩
    rw [SimpleGraph.mem_neighborSet]
    have := GraphAction.smul_adj (𝒯 := 𝒯) g⁻¹ h
    rwa [inv_smul_smul] at this
  · rintro ⟨y, hy, rfl⟩
    rw [SimpleGraph.mem_neighborSet] at hy
    exact GraphAction.smul_adj g hy

end GapC

section Tree

variable (R₀ K₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Field K₀] [Algebra R₀ K₀]
  [IsFractionRing R₀ K₀]

theorem neighborSet_finite_nonempty [Finite (IsLocalRing.ResidueField R₀)] (w : LT.LatticeTree.Vertex R₀ K₀) :
    ((BruhatTits.tree R₀ K₀).neighborSet w).Finite ∧ ((BruhatTits.tree R₀ K₀).neighborSet w).Nonempty := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R₀
  have hϖ0 : algebraMap R₀ K₀ ϖ ≠ 0 := fun h => hϖ.ne_zero ((IsFractionRing.to_map_eq_zero_iff (K := K₀)).mp h)
  let n : GL (Fin 2) K₀ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, algebraMap R₀ K₀ ϖ]
    (by simp [Matrix.det_fin_two, hϖ0])
  let s : R₀ → GL (Fin 2) K₀ := fun t => Matrix.GeneralLinearGroup.mkOfDetNeZero !![algebraMap R₀ K₀ t, 1; 1, 0]
    (by simp [Matrix.det_fin_two])
  obtain ⟨hadj, -, hall, hcong, -⟩ := CerednikDrinfeld.BruhatTits.adj_stdVertex_iff_eq_smul_of_uniformizer R₀ K₀ ϖ hϖ
    n (by simp [n, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]) s (fun t => by simp [s, Matrix.GeneralLinearGroup.val_mkOfDetNeZero])
  haveI : Finite (R₀ ⧸ Ideal.span {ϖ}) := finite_quot hϖ
  have hv₀fin : ((BruhatTits.tree R₀ K₀).neighborSet (LT.LatticeTree.stdVertex R₀ K₀)).Finite := by
    let σ : R₀ ⧸ Ideal.span {ϖ} → R₀ := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}))
    have hσ : ∀ q, Ideal.Quotient.mk (Ideal.span {ϖ}) (σ q) = q :=
      Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}))
    let φ : R₀ ⧸ Ideal.span {ϖ} → LT.LatticeTree.Vertex R₀ K₀ := fun q => (s (σ q) * n) • LT.LatticeTree.stdVertex R₀ K₀
    refine ((Set.finite_range φ).insert (n • LT.LatticeTree.stdVertex R₀ K₀)).subset ?_
    intro y hy
    rw [SimpleGraph.mem_neighborSet] at hy
    rcases hall y hy with h | ⟨t, h⟩
    · exact Set.mem_insert_iff.mpr (Or.inl h)
    · refine Set.mem_insert_iff.mpr (Or.inr ⟨Ideal.Quotient.mk _ t, ?_⟩)
      rw [h]
      show (s (σ (Ideal.Quotient.mk _ t)) * n) • LT.LatticeTree.stdVertex R₀ K₀ = (s t * n) • LT.LatticeTree.stdVertex R₀ K₀
      rw [hcong, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, hσ]
  have hv₀ne : ((BruhatTits.tree R₀ K₀).neighborSet (LT.LatticeTree.stdVertex R₀ K₀)).Nonempty :=
    ⟨_, (SimpleGraph.mem_neighborSet _ _ _).mpr hadj⟩
  obtain ⟨g, hg⟩ := LT.LatticeTree.exists_act_stdVertex_eq R₀ K₀ w
  rw [← CerednikDrinfeld.BruhatTits.gl_smul_def] at hg
  rw [← hg, smul_neighborSet]
  exact ⟨hv₀fin.image _, hv₀ne.image _⟩

theorem finite_stabilizer_vertex [Finite (IsLocalRing.ResidueField R₀)]
    (H : Subgroup PGL(2, K₀)) [GraphAction ↥H (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥H) d))
    (w : LT.LatticeTree.Vertex R₀ K₀) : Finite (MulAction.stabilizer (↥H) w) :=
  finite_stabilizer_of_finite_stabilizer_dart (BruhatTits.tree R₀ K₀) w
    (neighborSet_finite_nonempty R₀ K₀ w).1 (neighborSet_finite_nonempty R₀ K₀ w).2 hfin

end Tree

section Points

variable {K₀ : Type} [Field K₀] {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]

theorem finite_stabilizer_point (ϖ : Omega.PseudoUniformizer K₀ C) (hex : Omega.IsExhausted ϖ)
    (H : Subgroup PGL(2, K₀)) (hdisc : Omega.IsDiscrete C H.subtype) (z : ↥(Omega.upperHalfPlane K₀ C)) :
    Finite (MulAction.stabilizer (↥H) z) := by
  obtain ⟨n, hn⟩ := hex z z.2
  have hfin := CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid ϖ H.subtype hdisc n hn
  have hsub : ((MulAction.stabilizer (↥H) z : Subgroup ↥H) : Set ↥H) ⊆
      {γ : ↥H | Omega.pmoebius K₀ (H.subtype γ) (z : C) ∈ Omega.affinoid ϖ n} := by
    intro γ hγ
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hγ
    show Omega.pmoebius K₀ (γ : PGL(2, K₀)) (z : C) ∈ Omega.affinoid ϖ n
    rw [← Omega.coe_smul_upperHalfPlane, show (γ : PGL(2, K₀)) • z = z from hγ]
    exact hn
  exact (hfin.subset hsub).to_subtype

theorem card_stabilizer_point_ne_zero (ϖ : Omega.PseudoUniformizer K₀ C) (hex : Omega.IsExhausted ϖ)
    (H : Subgroup PGL(2, K₀)) (hdisc : Omega.IsDiscrete C H.subtype) (z : ↥(Omega.upperHalfPlane K₀ C)) :
    (Nat.card (MulAction.stabilizer (↥H) z) : ℤ) ≠ 0 := by
  haveI := finite_stabilizer_point ϖ hex H hdisc z
  exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer (↥H) z)).ne'

theorem card_setOf_smul_eq (H : Subgroup PGL(2, K₀)) {a₀ : C} (ha₀ : a₀ ∈ Omega.upperHalfPlane K₀ C)
    (z : ↥(Omega.upperHalfPlane K₀ C))
    [Finite (MulAction.stabilizer (↥H) z)] [Decidable (∃ γ : ↥H, z = (γ : PGL(2, K₀)) • (⟨a₀, ha₀⟩ : ↥(Omega.upperHalfPlane K₀ C)))] :
    (Nat.card {γ : ↥H // Omega.pmoebius K₀ (H.subtype γ) a₀ = (z : C)} : ℤ) =
      if (∃ γ : ↥H, z = (γ : PGL(2, K₀)) • (⟨a₀, ha₀⟩ : ↥(Omega.upperHalfPlane K₀ C)))
        then (Nat.card (MulAction.stabilizer (↥H) z) : ℤ) else 0 := by
  set a : ↥(Omega.upperHalfPlane K₀ C) := ⟨a₀, ha₀⟩ with ha
  have key : ∀ γ : ↥H, Omega.pmoebius K₀ (H.subtype γ) a₀ = (z : C) ↔ γ • a = z := fun γ => by
    rw [show a₀ = (a : C) from rfl, ← Omega.coe_smul_upperHalfPlane]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  split_ifs with h
  · obtain ⟨γ₀, hγ₀⟩ := h
    have hγ₀' : γ₀ • a = z := hγ₀.symm
    congr 1
    apply Nat.card_congr
    refine ⟨fun γ => ⟨(γ : ↥H) * γ₀⁻¹, ?_⟩, fun g => ⟨(g : ↥H) * γ₀, ?_⟩, fun γ => ?_, fun g => ?_⟩
    · have hinv : γ₀⁻¹ • z = a := by rw [inv_smul_eq_iff]; exact hγ₀
      rw [MulAction.mem_stabilizer_iff, mul_smul, hinv]
      exact (key _).mp γ.2
    · rw [key, mul_smul, hγ₀']; exact g.2
    · apply Subtype.ext; exact inv_mul_cancel_right _ _
    · apply Subtype.ext; exact mul_inv_cancel_right _ _
  · push Not at h
    haveI : IsEmpty {γ : ↥H // Omega.pmoebius K₀ (H.subtype γ) a₀ = (z : C)} :=
      ⟨fun γ => h γ ((key γ).mp γ.2).symm⟩
    rw [Nat.card_of_isEmpty, Nat.cast_zero]

end Points

section QuotFinite

variable {R₀ K₀ : Type} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Field K₀] [Algebra R₀ K₀]
  [IsFractionRing R₀ K₀]

theorem finite_quotEdge (H : Subgroup PGL(2, K₀)) [GraphAction ↥H (BruhatTits.tree R₀ K₀)]
    (htp : H ≤ typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    {E : Type} [Fintype E]
    (eE : {e : QuotEdge ↥H (BruhatTits.tree R₀ K₀) // vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E) :
    Finite (QuotEdge ↥H (BruhatTits.tree R₀ K₀)) := by
  classical
  set 𝒯 := BruhatTits.tree R₀ K₀ with h𝒯
  set v₀ := LT.LatticeTree.stdVertex R₀ K₀ with hv₀
  obtain ⟨hconn, hcol⟩ := CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R₀ K₀
  obtain ⟨hadj, hsmul, ε, hε, hker⟩ :=
    CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter PGL(2, K₀) 𝒯 hconn hcol v₀

  have htype : ∀ (γ : ↥H) (w : LT.LatticeTree.Vertex R₀ K₀), vertexType 𝒯 v₀ ((γ : PGL(2, K₀)) • w) = vertexType 𝒯 v₀ w := by
    intro γ w
    have h0 : vertexType 𝒯 v₀ ((γ : PGL(2, K₀)) • v₀) = 0 := by
      have : (γ : PGL(2, K₀)) ∈ ε.ker := by rw [hker]; exact htp γ.2
      rw [MonoidHom.mem_ker] at this
      rw [← hε, this]; rfl
    rw [hsmul, h0, zero_add]
  haveI : Finite {e : QuotEdge ↥H 𝒯 // vertexType 𝒯 v₀ e.out.fst = 0} := Finite.of_equiv E eE.symm

  let rev : QuotEdge ↥H 𝒯 → QuotEdge ↥H 𝒯 := Quotient.map' SimpleGraph.Dart.symm (fun d d' ⟨γ, hγ⟩ => ⟨γ, by
    rw [← hγ]; exact (smul_dart_symm 𝒯 γ d').symm⟩)
  have hrev : ∀ d : 𝒯.Dart, rev (Quotient.mk _ d) = Quotient.mk _ d.symm := fun d => rfl

  refine Finite.of_surjective (fun x : {e : QuotEdge ↥H 𝒯 // vertexType 𝒯 v₀ e.out.fst = 0} ⊕
      {e : QuotEdge ↥H 𝒯 // vertexType 𝒯 v₀ e.out.fst = 0} => Sum.elim (fun e => e.1) (fun e => rev e.1) x) ?_
  intro q
  by_cases hq : vertexType 𝒯 v₀ q.out.fst = 0
  · exact ⟨Sum.inl ⟨q, hq⟩, rfl⟩
  ·
    have hq' : vertexType 𝒯 v₀ (rev q).out.fst = 0 := by
      obtain ⟨γ, hγ⟩ : ∃ γ : ↥H, γ • q.out.symm = (rev q).out := by
        have h1 : (Quotient.mk (MulAction.orbitRel (↥H) 𝒯.Dart) (rev q).out) = rev q := Quotient.out_eq _
        have h2 : rev q = Quotient.mk _ q.out.symm := by rw [← hrev, Quotient.out_eq]
        exact Quotient.exact (h1.trans h2)
      rw [← hγ]
      show vertexType 𝒯 v₀ ((γ : PGL(2, K₀)) • q.out.snd) = 0
      rw [htype, hadj _ _ q.out.adj]

      generalize vertexType 𝒯 v₀ q.out.fst = t at hq
      fin_cases t
      · exact absurd rfl hq
      · decide
    refine ⟨Sum.inr ⟨rev q, hq'⟩, ?_⟩
    show rev (rev q) = q
    rw [← Quotient.out_eq q, hrev, hrev, SimpleGraph.Dart.symm_symm]

noncomputable scoped instance fintypeQuotEdge_of_finite (H : Subgroup PGL(2, K₀)) [GraphAction ↥H (BruhatTits.tree R₀ K₀)]
    [Finite (QuotEdge ↥H (BruhatTits.tree R₀ K₀))] : Fintype (QuotEdge ↥H (BruhatTits.tree R₀ K₀)) := Fintype.ofFinite _

end QuotFinite

section Frac

theorem prod_mk_eq_mk_prod {R : Type} [CommRing R] {S : Submonoid R} {ι : Type} (s : Finset ι)
    (f : ι → R) (d : ι → ↥S) :
    ∏ i ∈ s, Localization.mk (f i) (d i) = Localization.mk (∏ i ∈ s, f i) (∏ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Localization.mk_one]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi, ih, Localization.mk_mul]

end Frac

section OrdAt

variable {K₀ : Type} [Field K₀] {C : Type} [Field C] [Algebra K₀ C]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀] [CompleteSpace C] [IsAlgClosed C]
  (ϖ : Omega.PseudoUniformizer K₀ C)
  (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
  (hex : Omega.IsExhausted ϖ)
  (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
    Valued.v (algebraMap K₀ C a) ≤ (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ C a - algebraMap K₀ C t) < (Valued.v (algebraMap K₀ C ϖ.ϖ)) ^ n)

include hrk hex hfin in
theorem ordAt_one [IsDomain ↥(Omega.holRing ϖ)] (z : ↥(Omega.upperHalfPlane K₀ C)) : Omega.ordAt ϖ 1 z = 0 := by
  have h := CerednikDrinfeld.Omega.ordAt_mul K₀ C ϖ hrk hex hfin 1 1 one_ne_zero one_ne_zero z
  rw [one_mul] at h
  omega

include hrk hex hfin in
theorem ordAt_prod [IsDomain ↥(Omega.holRing ϖ)] {ι : Type} (s : Finset ι) (F : ι → ↥(Omega.holRing ϖ))
    (hF : ∀ i ∈ s, F i ≠ 0) (z : ↥(Omega.upperHalfPlane K₀ C)) :
    Omega.ordAt ϖ (∏ i ∈ s, F i) z = ∑ i ∈ s, Omega.ordAt ϖ (F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ordAt_one ϖ hrk hex hfin]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      CerednikDrinfeld.Omega.ordAt_mul K₀ C ϖ hrk hex hfin _ _ (hF i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hF j (Finset.mem_insert_of_mem hj))) z,
      ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))]

end OrdAt

section Actions

variable {K₀ : Type} [Field K₀] {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  (ϖ : Omega.PseudoUniformizer K₀ C) {G : Type} [Group G] (ρ : G →* PGL(2, K₀))

theorem fracAct_holRingOf [IsDomain (Omega.HolRingOf ϖ ρ)] (γ : G) (x : FractionRing (Omega.HolRingOf ϖ ρ)) :
    Mumford.fracAct G (Omega.HolRingOf ϖ ρ) γ x =
      @Mumford.fracAct PGL(2, K₀) _ ↥(Omega.holRing ϖ) _ _ (show IsDomain ↥(Omega.holRing ϖ) from ‹_›) (ρ γ) x := by
  unfold Mumford.fracAct
  congr 2
  apply RingEquiv.ext
  intro f
  rfl

end Actions

section Generic

theorem map_prod_eq_algebraMap_inv_prod_mul {K L : Type} [Field K] [CommRing L] [Algebra K L] (φ : L ≃+* L)
    {ι : Type} (s : Finset ι) (θ : ι → L) (k : ι → Kˣ)
    (h : ∀ i ∈ s, φ (θ i) = algebraMap K L (((k i)⁻¹ : Kˣ) : K) * θ i) :
    φ (∏ i ∈ s, θ i) = algebraMap K L (∏ i ∈ s, (k i : K))⁻¹ * ∏ i ∈ s, θ i := by
  rw [map_prod, Finset.prod_congr rfl h, Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, map_prod]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => by rw [Units.val_inv_eq_inv_val])

theorem eq_zero_of_mk_eq_zero {R : Type} [CommRing R] [IsDomain R] {a : R} {s : ↥(nonZeroDivisors R)}
    (h : (Localization.mk a s : Localization (nonZeroDivisors R)) = 0) : a = 0 := by
  rw [← Localization.mk_zero s, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at h
  obtain ⟨c, hc⟩ := h
  simp only [mul_zero] at hc
  exact (mul_eq_zero.mp hc).elim (fun h => absurd h (nonZeroDivisors.coe_ne_zero c)) (fun h =>
    (mul_eq_zero.mp h).elim (fun h => absurd h (nonZeroDivisors.coe_ne_zero _)) id)

end Generic

section Generic2

theorem prod_mk_div_prod_mk {R : Type} [CommRing R] [IsDomain R] {ι κ : Type} (s : Finset ι) (t : Finset κ)
    (F Hh : ι → R) (F' Hh' : κ → R) (hH : ∀ i, Hh i ∈ nonZeroDivisors R) (hH' : ∀ j, Hh' j ∈ nonZeroDivisors R)
    (hF' : ∀ j ∈ t, F' j ≠ 0) (hden : (∏ i ∈ s, Hh i) * ∏ j ∈ t, F' j ∈ nonZeroDivisors R) :
    ((∏ i ∈ s, Localization.mk (F i) ⟨Hh i, hH i⟩) / (∏ j ∈ t, Localization.mk (F' j) ⟨Hh' j, hH' j⟩) : FractionRing R) =
      Localization.mk ((∏ i ∈ s, F i) * ∏ j ∈ t, Hh' j) ⟨(∏ i ∈ s, Hh i) * ∏ j ∈ t, F' j, hden⟩ := by
  rw [prod_mk_eq_mk_prod, prod_mk_eq_mk_prod]
  have hY0 : (Localization.mk (∏ j ∈ t, F' j) (∏ j ∈ t, (⟨Hh' j, hH' j⟩ : ↥(nonZeroDivisors R))) : FractionRing R) ≠ 0 :=
    fun h0 => (Finset.prod_ne_zero_iff.mpr hF') (eq_zero_of_mk_eq_zero h0)
  rw [div_eq_iff hY0, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, Submonoid.coe_finset_prod]
  ring

end Generic2

section ThetaQuot

variable {K₀ : Type} [Field K₀] {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀] [CompleteSpace C]
  (ϖ : Omega.PseudoUniformizer K₀ C) (hex : Omega.IsExhausted ϖ)
  (H : Subgroup PGL(2, K₀)) (hdisc : Omega.IsDiscrete C H.subtype)

include hex hdisc in

theorem mk_mem_invariantFieldOf_of_prod_theta_eq [IsDomain ↥(Omega.holRing ϖ)]
    {n m : ℕ} (a b z : Fin n → C) (a' b' z' : Fin m → C)
    (ha : ∀ i, a i ∈ Omega.upperHalfPlane K₀ C) (hb : ∀ i, b i ∈ Omega.upperHalfPlane K₀ C)
    (hz : ∀ i, z i ∈ Omega.upperHalfPlane K₀ C)
    (ha' : ∀ j, a' j ∈ Omega.upperHalfPlane K₀ C) (hb' : ∀ j, b' j ∈ Omega.upperHalfPlane K₀ C)
    (hz' : ∀ j, z' j ∈ Omega.upperHalfPlane K₀ C)
    (hza : ∀ i (γ : ↥H), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (a i) ≠ z i)
    (hzb : ∀ i (γ : ↥H), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (b i) ≠ z i)
    (hza' : ∀ j (γ : ↥H), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (a' j) ≠ z' j)
    (hzb' : ∀ j (γ : ↥H), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (b' j) ≠ z' j)
    (hmult : ∀ β : ↥H,
      ∏ i, Omega.theta H.subtype (a i) (b i) (z i) (Omega.pmoebius K₀ (β : PGL(2, K₀)) (z i)) =
        ∏ j, Omega.theta H.subtype (a' j) (b' j) (z' j) (Omega.pmoebius K₀ (β : PGL(2, K₀)) (z' j)))
    (F Hh : Fin n → ↥(Omega.holRing ϖ)) (F' Hh' : Fin m → ↥(Omega.holRing ϖ))
    (hpair : ∀ i, Omega.IsThetaPair ϖ H.subtype (a i) (b i) (z i) (F i) (Hh i))
    (hpair' : ∀ j, Omega.IsThetaPair ϖ H.subtype (a' j) (b' j) (z' j) (F' j) (Hh' j))
    (hF0' : ∀ j, F' j ≠ 0)
    (hden : (∏ i, Hh i) * ∏ j, F' j ∈ nonZeroDivisors ↥(Omega.holRing ϖ)) :
    (Localization.mk ((∏ i, F i) * ∏ j, Hh' j) ⟨(∏ i, Hh i) * ∏ j, F' j, hden⟩ : Omega.merField ϖ) ∈
      Mumford.invariantFieldOf C PGL(2, K₀) ↥(Omega.holRing ϖ) H := by
  classical
  letI iField : Field (Omega.merField ϖ) := inferInstance
  letI iCR : CommRing (Omega.merField ϖ) := iField.toCommRing
  letI iAlg : Algebra C (Omega.merField ϖ) := inferInstance

  have haut := fun (x y w : C) (hx : x ∈ Omega.upperHalfPlane K₀ C) (hy : y ∈ Omega.upperHalfPlane K₀ C)
      (hw : w ∈ Omega.upperHalfPlane K₀ C) (hxa : ∀ γ : ↥H, Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ w)
      (hyb : ∀ γ : ↥H, Omega.pmoebius K₀ (γ : PGL(2, K₀)) y ≠ w) =>
    CerednikDrinfeld.Omega.exists_monoidHom_fracAct_thetaMer_eq K₀ C ϖ hex H.subtype hdisc hx hy hw hxa hyb
  choose c hc hcact using fun i => haut (a i) (b i) (z i) (ha i) (hb i) (hz i) (hza i) (hzb i)
  choose c' hc' hcact' using fun j => haut (a' j) (b' j) (z' j) (ha' j) (hb' j) (hz' j) (hza' j) (hzb' j)
  have hcc : ∀ β : ↥H, ∏ i, ((c i β : Cˣ) : C) = ∏ j, ((c' j β : Cˣ) : C) := fun β => by
    simp only [hc, hc']
    exact hmult β

  have hθ : ∀ i, Omega.thetaMer ϖ H.subtype (a i) (b i) (z i) = Localization.mk (F i) ⟨Hh i, (hpair i).1⟩ :=
    fun i => CerednikDrinfeld.Omega.thetaMer_eq_mk_of_isThetaPair ϖ H.subtype (a i) (b i) (z i) (F i) (Hh i) (hpair i)
  have hθ' : ∀ j, Omega.thetaMer ϖ H.subtype (a' j) (b' j) (z' j) = Localization.mk (F' j) ⟨Hh' j, (hpair' j).1⟩ :=
    fun j => CerednikDrinfeld.Omega.thetaMer_eq_mk_of_isThetaPair ϖ H.subtype (a' j) (b' j) (z' j) (F' j) (Hh' j) (hpair' j)
  have hXY := prod_mk_div_prod_mk (R := ↥(Omega.holRing ϖ)) Finset.univ Finset.univ F Hh F' Hh'
    (fun i => (hpair i).1) (fun j => (hpair' j).1) (fun j _ => hF0' j) hden
  rw [← hXY, ← Finset.prod_congr rfl (fun i _ => hθ i), ← Finset.prod_congr rfl (fun j _ => hθ' j)]
  let uP : PGL(2, K₀) → C := fun δ => if hδ : δ ∈ H then (∏ i, ((c i ⟨δ, hδ⟩ : Cˣ) : C))⁻¹ else 1
  apply CerednikDrinfeld.Mumford.div_mem_invariantFieldOf_of_smul_eq_algebraMap_mul C PGL(2, K₀) ↥(Omega.holRing ϖ) H uP
  · intro δ hδ
    rw [Mumford.frac_smul_def]
    simp only [uP, dif_pos hδ]
    exact map_prod_eq_algebraMap_inv_prod_mul _ _ _ (fun i => c i ⟨δ, hδ⟩) (fun i _ => hcact i ⟨δ, hδ⟩)
  · intro δ hδ
    rw [Mumford.frac_smul_def]
    simp only [uP, dif_pos hδ]
    rw [hcc ⟨δ, hδ⟩]
    exact map_prod_eq_algebraMap_inv_prod_mul _ _ _ (fun j => c' j ⟨δ, hδ⟩) (fun j _ => hcact' j ⟨δ, hδ⟩)

end ThetaQuot

section Transport

variable {K₀ : Type} [Field K₀] {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  (ϖ : Omega.PseudoUniformizer K₀ C) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (Γ : Subgroup G)

theorem mem_invariantFieldOf_of_mem_map [IsDomain ↥(Omega.holRing ϖ)] [IsDomain (Omega.HolRingOf ϖ ρ)]
    (x : Omega.merField ϖ) (hx : x ∈ Mumford.invariantFieldOf C PGL(2, K₀) ↥(Omega.holRing ϖ) (Γ.map ρ)) :
    (show FractionRing (Omega.HolRingOf ϖ ρ) from x) ∈ Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ := by
  rw [Mumford.mem_invariantFieldOf_iff]
  intro γ hγ
  rw [Mumford.frac_smul_def, fracAct_holRingOf ϖ ρ]
  have := (Mumford.mem_invariantFieldOf_iff C PGL(2, K₀) ↥(Omega.holRing ϖ) (Γ.map ρ) x).mp hx (ρ γ)
    (Subgroup.mem_map_of_mem ρ hγ)
  rw [Mumford.frac_smul_def] at this
  exact this

end Transport

section DivisorStep

theorem ordAt_prod_mul_eq_of_divisor_eq_ord
    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion] [DecidableEq A.valuation.Completion]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ A.valuation.Completion x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ A.valuation.Completion) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)] [IsAlgClosed A.valuation.Completion]
    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))
    (htameV : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) w) : ℕ) : A.valuation.Completion) = 1)
    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC]
    (eFC : FC ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ))
    {E V : Type} [Fintype E] [Fintype V]
    (eV : Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ V)
    (eE : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E)
    (pt : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion FC)
    (hpt_fib : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), pt z = pt z' ↔ ∃ γ : ↥(Γ.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))
    (hdisc : Omega.IsDiscrete A.valuation.Completion (Γ.map ρ).subtype)
    {n : ℕ} (a b : Fin n → A.valuation.Completion)
    (ha : ∀ i, a i ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : ∀ i, b i ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
    (F Hh : Fin n → ↥(Omega.holRing ϖ)) (hF0 : ∀ i, F i ≠ 0) (hH0 : ∀ i, Hh i ≠ 0)
    (hord : ∀ i (w : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)),
      Omega.ordAt ϖ (F i) w = Nat.card {γ : ↥(Γ.map ρ) // Omega.pmoebius K₀ ((Γ.map ρ).subtype γ) (a i) = (w : A.valuation.Completion)} ∧
      Omega.ordAt ϖ (Hh i) w = Nat.card {γ : ↥(Γ.map ρ) // Omega.pmoebius K₀ ((Γ.map ρ).subtype γ) (b i) = (w : A.valuation.Completion)})
    (g₁ g₂ : ↥(Omega.holRing ϖ)) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ∈ nonZeroDivisors ↥(Omega.holRing ϖ))
    (hmem : (show FractionRing (Omega.HolRingOf ϖ ρ) from Localization.mk g₁ ⟨g₂, hg₂⟩) ∈
      Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)
    (hdivg : ∀ v : Place A.valuation.Completion FC,
      ((∑ i, (Finsupp.single (pt ⟨a i, ha i⟩) 1 - Finsupp.single (pt ⟨b i, hb i⟩) 1)) : Divisor A.valuation.Completion FC) v =
        v.ord (eFC.symm ⟨_, hmem⟩))
    (w : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) :
    Omega.ordAt ϖ ((∏ i, F i) * g₂) w = Omega.ordAt ϖ ((∏ i, Hh i) * g₁) w := by
  classical
  haveI hdom : IsDomain ↥(Omega.holRing ϖ) := (show IsDomain ↥(Omega.holRing ϖ) from ‹IsDomain (Omega.HolRingOf ϖ ρ)›)
  have hrk' := ECOmegaD.hrk A hA
  have hfin' := ECOmegaD.hfin A K₀ R₀ hA hR₀ ϖ ϖ₀ hϖ₀ hϖ
  haveI : Fintype (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) := Fintype.ofEquiv V eV.symm
  haveI : Finite (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)) := finite_quotEdge (Γ.map ρ) htp eE
  haveI : Fintype (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)) := Fintype.ofFinite _
  haveI hstw : Finite (MulAction.stabilizer ↥(Γ.map ρ) w) := finite_stabilizer_point ϖ hex (Γ.map ρ) hdisc w
  have hN := card_stabilizer_point_ne_zero ϖ hex (Γ.map ρ) hdisc w
  have hval : ∀ ε : A.ValueGroup, ε ≠ 0 → ∃ y : A.valuation.Completion, y ≠ 0 ∧ Valued.v y ≤ ε := fun ε hε => by
    obtain ⟨y, hy0, hy⟩ := ECOmegaD.exists_v_eq A ε hε
    exact ⟨y, hy0, hy.le⟩
  have htame : ((Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) w) : ℕ) : A.valuation.Completion) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := MulAction.stabilizer ↥(Γ.map ρ) w)).ne'
  have hg₂0 : g₂ ≠ 0 := nonZeroDivisors.ne_zero hg₂
  have hord₀ := CerednikDrinfeld.Omega.ord_place_invariantFieldOf_mul_card_stabilizer_eq_ordAt_sub_ordAt_of_cast_card_ne_zero_of_map_le_typePreserving_of_exists_v_le_of_v_card_eq_one
    K₀ A.valuation.Completion hrk' hval R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex G ρ Γ htp hfin htameV FC eFC pt hpt w htame
    (show Omega.HolRingOf ϖ ρ from g₁) (show Omega.HolRingOf ϖ ρ from g₂) hg₁ hg₂ hmem

  have cnt : ∀ {x : A.valuation.Completion} (hx : x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
      (Nat.card {γ : ↥(Γ.map ρ) // Omega.pmoebius K₀ ((Γ.map ρ).subtype γ) x = (w : A.valuation.Completion)} : ℤ) =
        if pt ⟨x, hx⟩ = pt w then (Nat.card (MulAction.stabilizer ↥(Γ.map ρ) w) : ℤ) else 0 := by
    intro x hx
    rw [card_setOf_smul_eq (Γ.map ρ) hx w]
    by_cases hp : ∃ γ : ↥(Γ.map ρ), w = (γ : PGL(2, K₀)) • (⟨x, hx⟩ : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion))
    · rw [if_pos hp, if_pos ((hpt_fib _ _).mpr hp)]
    · rw [if_neg hp, if_neg (fun h' => hp ((hpt_fib _ _).mp h'))]

  have hD := hdivg (pt w)
  have key : ((∑ i, Omega.ordAt ϖ (F i) w : ℕ) : ℤ) - ((∑ i, Omega.ordAt ϖ (Hh i) w : ℕ) : ℤ) =
      (Omega.ordAt ϖ g₁ w : ℤ) - (Omega.ordAt ϖ g₂ w : ℤ) := by
    rw [← show (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from (show Omega.HolRingOf ϖ ρ from g₁)) w : ℤ) = Omega.ordAt ϖ g₁ w from rfl,
      ← show (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from (show Omega.HolRingOf ϖ ρ from g₂)) w : ℤ) = Omega.ordAt ϖ g₂ w from rfl,
      ← hord₀, ← hD]
    simp only [Finsupp.sub_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
    push_cast
    simp only [(fun i => (hord i w).1), (fun i => (hord i w).2), cnt (ha _), cnt (hb _)]
    rw [Finset.sum_mul]
    simp only [sub_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_sub_distrib]

  have h1 : Omega.ordAt ϖ ((∏ i, F i) * g₂) w = ∑ i, Omega.ordAt ϖ (F i) w + Omega.ordAt ϖ g₂ w := by
    rw [CerednikDrinfeld.Omega.ordAt_mul K₀ A.valuation.Completion ϖ hrk' hex hfin' _ _
      (Finset.prod_ne_zero_iff.mpr fun i _ => hF0 i) hg₂0 w, ordAt_prod ϖ hrk' hex hfin' _ _ (fun i _ => hF0 i) w]
  have h2 : Omega.ordAt ϖ ((∏ i, Hh i) * g₁) w = ∑ i, Omega.ordAt ϖ (Hh i) w + Omega.ordAt ϖ g₁ w := by
    rw [CerednikDrinfeld.Omega.ordAt_mul K₀ A.valuation.Completion ϖ hrk' hex hfin' _ _
      (Finset.prod_ne_zero_iff.mpr fun i _ => hH0 i) hg₁ w, ordAt_prod ϖ hrk' hex hfin' _ _ (fun i _ => hH0 i) w]
  rw [h1, h2]
  omega

end DivisorStep

namespace AbelConverse

variable {K₀ : Type} [Field K₀] {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀] [CompleteSpace C] [IsAlgClosed C]
  (ϖ : Omega.PseudoUniformizer K₀ C)
  (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
  (hex : Omega.IsExhausted ϖ)
  (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
    Valued.v (algebraMap K₀ C a) ≤ (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ C a - algebraMap K₀ C t) < (Valued.v (algebraMap K₀ C ϖ.ϖ)) ^ n)

include hrk hex hfin in

theorem exists_isUnit_mul_eq_of_forall_ordAt_eq [IsDomain ↥(Omega.holRing ϖ)] (F H : ↥(Omega.holRing ϖ))
    (hF : F ≠ 0) (hH : H ≠ 0) (h : ∀ z : ↥(Omega.upperHalfPlane K₀ C), Omega.ordAt ϖ F z = Omega.ordAt ϖ H z) :
    ∃ u : ↥(Omega.holRing ϖ), IsUnit u ∧ u * H = F := by
  obtain ⟨u, hu⟩ := CerednikDrinfeld.Omega.dvd_of_forall_ordAt_le K₀ C ϖ hrk hex hfin F H hH (fun z => (h z).ge)
  obtain ⟨w, hw⟩ := CerednikDrinfeld.Omega.dvd_of_forall_ordAt_le K₀ C ϖ hrk hex hfin H F hF (fun z => (h z).le)
  have huw : u * w = 1 := by
    have : H * (u * w) = H * 1 := by rw [mul_one, ← mul_assoc, ← hu, ← hw]
    exact mul_left_cancel₀ hH this
  exact ⟨u, IsUnit.of_mul_eq_one w huw, by rw [mul_comm, ← hu]⟩

include hfin in

theorem exists_mem_affinoid_zero : ∃ w : C, w ∈ Omega.affinoid ϖ 0 :=
  CerednikDrinfeld.Omega.affinoid_nonempty_of_exists_finset_cover K₀ C ϖ 0 (hfin 0)

theorem apply_smul_eq_mul_of_fracAct_eq [IsDomain ↥(Omega.holRing ϖ)] (u : ↥(Omega.holRing ϖ)) (δ : PGL(2, K₀)) (k : Cˣ)
    (h : Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) δ (algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) u) =
      algebraMap C (Omega.merField ϖ) ((k⁻¹ : Cˣ) : C) * algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) u)
    (z : ↥(Omega.upperHalfPlane K₀ C)) :
    (u : ↥(Omega.upperHalfPlane K₀ C) → C) (δ • z) = (k : C) * (u : ↥(Omega.upperHalfPlane K₀ C) → C) z := by
  rw [Mumford.fracAct_algebraMap] at h
  have h2 : algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) (δ • u) =
      algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) (((k⁻¹ : Cˣ) : C) • u) := by
    rw [h, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply C ↥(Omega.holRing ϖ) (Omega.merField ϖ)]
  have h3 : δ • u = ((k⁻¹ : Cˣ) : C) • u := IsFractionRing.injective ↥(Omega.holRing ϖ) (Omega.merField ϖ) h2
  have h4 := congrArg (fun f : ↥(Omega.holRing ϖ) => (f : ↥(Omega.upperHalfPlane K₀ C) → C) (δ • z)) h3
  simp only [Omega.coe_smul_holRing_apply, inv_smul_smul] at h4
  have h5 : ((((k⁻¹ : Cˣ) : C) • u : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ C) → C) (δ • z) =
      ((k⁻¹ : Cˣ) : C) * (u : ↥(Omega.upperHalfPlane K₀ C) → C) (δ • z) := by
    rw [Algebra.smul_def, Subring.coe_mul, Pi.mul_apply, Omega.algebraMap_holRing_apply]
  rw [h5, Units.val_inv_eq_inv_val] at h4
  rw [h4, ← mul_assoc, mul_inv_cancel₀ k.ne_zero, one_mul]

include hex in

theorem prod_multiplier_eq_one_of_isOfFinOrder [IsDomain ↥(Omega.holRing ϖ)] (H : Subgroup PGL(2, K₀))
    (hdisc : Omega.IsDiscrete C H.subtype) {n : ℕ} (a b z : Fin n → C)
    (ha : ∀ i, a i ∈ Omega.upperHalfPlane K₀ C) (hb : ∀ i, b i ∈ Omega.upperHalfPlane K₀ C)
    (hz : ∀ i, z i ∈ Omega.upperHalfPlane K₀ C)
    (hza : ∀ i (γ : ↥H), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (a i) ≠ z i)
    (hzb : ∀ i (γ : ↥H), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (b i) ≠ z i)
    (c : Fin n → (↥H →* Cˣ))
    (hc : ∀ i (β : ↥H), ((c i β : Cˣ) : C) = Omega.theta H.subtype (a i) (b i) (z i) (Omega.pmoebius K₀ (H.subtype β) (z i)))
    (γ : ↥H) (hγ : IsOfFinOrder γ) : (∏ i, c i) γ = 1 := by
  rw [MonoidHom.finset_prod_apply]
  refine Finset.prod_eq_one (fun i _ => Units.ext ?_)
  rw [hc, Units.val_one]
  exact CerednikDrinfeld.Omega.theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder K₀ C ϖ hex H.subtype hdisc
    (ha i) (hb i) (hz i) (hza i) (hzb i) γ hγ

theorem ne_of_type (H : Subgroup PGL(2, K₀)) : True := trivial

end AbelConverse

end ECOmegaD
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one.ECOmegaD"

theorem ECOmegaD.AbelConverse.map_algebraMap_eq_of_mul_eq
    {C M : Type} [Field C] [CommRing M] [IsDomain M] [Algebra C M] [Algebra C (FractionRing M)]
    (φ : FractionRing M ≃+* FractionRing M)
    (hφC : ∀ c : C, φ (algebraMap C (FractionRing M) c) = algebraMap C (FractionRing M) c)
    {n : ℕ} (F H : Fin n → M) (g₁ g₂ u : M)
    (hH : ∀ i, H i ∈ nonZeroDivisors M) (hg₁ : g₁ ∈ nonZeroDivisors M) (hg₂ : g₂ ∈ nonZeroDivisors M)
    (hu : u * ((∏ i, H i) * g₁) = (∏ i, F i) * g₂)
    (c : Fin n → Cˣ)
    (hθ : ∀ i, φ (Localization.mk (F i) ⟨H i, hH i⟩) =
      algebraMap C (FractionRing M) (((c i)⁻¹ : Cˣ) : C) * Localization.mk (F i) ⟨H i, hH i⟩)
    (hinv : φ (Localization.mk g₁ ⟨g₂, hg₂⟩) = Localization.mk g₁ ⟨g₂, hg₂⟩) :
    φ (algebraMap M (FractionRing M) u) =
      algebraMap C (FractionRing M) (((∏ i, c i)⁻¹ : Cˣ) : C) * algebraMap M (FractionRing M) u := by
  have hne : ∀ m : M, m ∈ nonZeroDivisors M → algebraMap M (FractionRing M) m ≠ 0 := fun m hm =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
  have hmk : ∀ (a b : M) (hb : b ∈ nonZeroDivisors M),
      (Localization.mk a ⟨b, hb⟩ : FractionRing M) = algebraMap M (FractionRing M) a / algebraMap M (FractionRing M) b := by
    intro a b hb
    rw [Localization.mk_eq_mk', IsFractionRing.mk'_eq_div]
  have hden : (∏ i, algebraMap M (FractionRing M) (H i)) * algebraMap M (FractionRing M) g₁ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hne _ (hH i)) (hne _ hg₁)
  have huF : algebraMap M (FractionRing M) u =
      (∏ i, algebraMap M (FractionRing M) (F i) / algebraMap M (FractionRing M) (H i)) *
        (algebraMap M (FractionRing M) g₂ / algebraMap M (FractionRing M) g₁) := by
    rw [Finset.prod_div_distrib, div_mul_div_comm, eq_div_iff hden]
    have h := congrArg (algebraMap M (FractionRing M)) hu
    simpa only [map_mul, map_prod] using h
  have hθ' : ∀ i, φ (algebraMap M (FractionRing M) (F i) / algebraMap M (FractionRing M) (H i)) =
      algebraMap C (FractionRing M) (((c i)⁻¹ : Cˣ) : C) *
        (algebraMap M (FractionRing M) (F i) / algebraMap M (FractionRing M) (H i)) := fun i => by
    simpa only [hmk] using hθ i
  have hinv' : φ (algebraMap M (FractionRing M) g₂ / algebraMap M (FractionRing M) g₁) =
      algebraMap M (FractionRing M) g₂ / algebraMap M (FractionRing M) g₁ := by
    have h := hinv
    rw [hmk] at h
    rw [← inv_div, map_inv₀, h, inv_div]
  rw [huF, map_mul, map_prod]
  simp_rw [hθ', hinv']
  rw [Finset.prod_mul_distrib, ← map_prod]
  simp only [Units.val_inv_eq_inv_val, Units.coe_prod, Finset.prod_inv_distrib, mul_assoc]

namespace ECOmegaD
namespace AbelConverse

theorem exists_multiplier_of_unit
    {K₀ : Type} [Field K₀] {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀] [CompleteSpace C] [IsAlgClosed C]
    (ϖ : Omega.PseudoUniformizer K₀ C) (hex : Omega.IsExhausted ϖ) [IsDomain ↥(Omega.holRing ϖ)]
    (H : Subgroup PGL(2, K₀)) (hdisc : Omega.IsDiscrete C H.subtype)
    {n : ℕ} (a b z : Fin n → C)
    (ha : ∀ i, a i ∈ Omega.upperHalfPlane K₀ C) (hb : ∀ i, b i ∈ Omega.upperHalfPlane K₀ C)
    (hz : ∀ i, z i ∈ Omega.upperHalfPlane K₀ C)
    (hza : ∀ i (γ : ↥H), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (a i) ≠ z i)
    (hzb : ∀ i (γ : ↥H), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (b i) ≠ z i)
    (F Hh : Fin n → ↥(Omega.holRing ϖ)) (hpair : ∀ i, Omega.IsThetaPair ϖ H.subtype (a i) (b i) (z i) (F i) (Hh i))
    (g₁ g₂ u : ↥(Omega.holRing ϖ)) (hg₁ : g₁ ∈ nonZeroDivisors ↥(Omega.holRing ϖ)) (hg₂ : g₂ ∈ nonZeroDivisors ↥(Omega.holRing ϖ))
    (hu : u * ((∏ i, Hh i) * g₁) = (∏ i, F i) * g₂)
    (hinv : ∀ γ : ↥H, Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) (γ : PGL(2, K₀)) (Localization.mk g₁ ⟨g₂, hg₂⟩) =
      Localization.mk g₁ ⟨g₂, hg₂⟩) :
    ∃ χ : ↥H →* Cˣ,
      (∀ β : ↥H, ((χ β : Cˣ) : C) = ∏ i, Omega.theta H.subtype (a i) (b i) (z i) (Omega.pmoebius K₀ (β : PGL(2, K₀)) (z i))) ∧
      (∀ (γ : ↥H) (w : ↥(Omega.upperHalfPlane K₀ C)),
        (u : ↥(Omega.upperHalfPlane K₀ C) → C) ((γ : PGL(2, K₀)) • w) = ((χ γ : Cˣ) : C) * (u : ↥(Omega.upperHalfPlane K₀ C) → C) w) ∧
      (∀ γ : ↥H, IsOfFinOrder γ → χ γ = 1) := by
  classical

  have haut := fun (x y w : C) (hx : x ∈ Omega.upperHalfPlane K₀ C) (hy : y ∈ Omega.upperHalfPlane K₀ C)
      (hw : w ∈ Omega.upperHalfPlane K₀ C) (hxa : ∀ γ : ↥H, Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ w)
      (hyb : ∀ γ : ↥H, Omega.pmoebius K₀ (γ : PGL(2, K₀)) y ≠ w) =>
    CerednikDrinfeld.Omega.exists_monoidHom_fracAct_thetaMer_eq K₀ C ϖ hex H.subtype hdisc hx hy hw hxa hyb
  choose c hc hcact using fun i => haut (a i) (b i) (z i) (ha i) (hb i) (hz i) (hza i) (hzb i)
  have hθ : ∀ i, Omega.thetaMer ϖ H.subtype (a i) (b i) (z i) = Localization.mk (F i) ⟨Hh i, (hpair i).1⟩ :=
    fun i => CerednikDrinfeld.Omega.thetaMer_eq_mk_of_isThetaPair ϖ H.subtype (a i) (b i) (z i) (F i) (Hh i) (hpair i)
  refine ⟨∏ i, c i, fun β => ?_, fun γ w => ?_, fun γ hγ => ?_⟩
  · rw [MonoidHom.finset_prod_apply, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => hc i β
  ·
    have h5 := ECOmegaD.AbelConverse.map_algebraMap_eq_of_mul_eq (C := C) (M := ↥(Omega.holRing ϖ))
      (Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) (γ : PGL(2, K₀)))
      (fun x => by
        rw [IsScalarTower.algebraMap_apply C ↥(Omega.holRing ϖ) (FractionRing ↥(Omega.holRing ϖ)), Mumford.fracAct_algebraMap,
          Mumford.smul_algebraMap_const_M])
      F Hh g₁ g₂ u (fun i => (hpair i).1) hg₁ hg₂ hu (fun i => c i γ)
      (fun i => by rw [← hθ i]; exact hcact i γ) (hinv γ)
    have hA3 := apply_smul_eq_mul_of_fracAct_eq ϖ u (γ : PGL(2, K₀)) (∏ i, c i γ) h5 w
    rw [hA3, MonoidHom.finset_prod_apply]
  · rw [MonoidHom.finset_prod_apply]
    refine Finset.prod_eq_one (fun i _ => Units.ext ?_)
    rw [hc, Units.val_one]
    exact CerednikDrinfeld.Omega.theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder K₀ C ϖ hex H.subtype hdisc
      (ha i) (hb i) (hz i) (hza i) (hzb i) γ hγ

end ECOmegaD.AbelConverse
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one.ECOmegaD"
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one.ECOmegaD"

namespace ECOmegaD

theorem fracAct_eq_of_mem_invariantFieldOf
    {K₀ : Type} [Field K₀] {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : Omega.PseudoUniformizer K₀ C) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (Γ : Subgroup G)
    [IsDomain ↥(Omega.holRing ϖ)] [IsDomain (Omega.HolRingOf ϖ ρ)]
    (x : Omega.merField ϖ) (hx : (show FractionRing (Omega.HolRingOf ϖ ρ) from x) ∈ Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ)
    (γ : ↥(Γ.map ρ)) :
    Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) (γ : PGL(2, K₀)) x = x := by
  obtain ⟨γ', hγ', hγeq⟩ := Subgroup.mem_map.mp γ.2
  have := (Mumford.mem_invariantFieldOf_iff C G (Omega.HolRingOf ϖ ρ) Γ _).mp hx γ' hγ'
  rw [Mumford.frac_smul_def, fracAct_holRingOf ϖ ρ, hγeq] at this
  exact this

end ECOmegaD
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one.ECOmegaD"

open ECOmegaD in
set_option maxHeartbeats 1600000 in
theorem solution

    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (ι : ↥(A.decompositionSubgroup ℚ) →* S) (hι : ∀ τ, scalar (ι τ) = τ)

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

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))
    (htame : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) w) : ℕ) : A.valuation.Completion) = 1)

    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC] [hcurve : IsCurveOver A.valuation.Completion FC]
    (eFC : FC ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ))
    (hfg : ∃ x : FC, Transcendental A.valuation.Completion x ∧ FiniteDimensional (IntermediateField.adjoin A.valuation.Completion ({x} : Set FC)) FC)

    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (eV : Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ V)
    (eE : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E)
    (hDa : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.a (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDb : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.b (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDw : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (D.w (eE e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γ.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)
    (Φ : Additive (Abelianization ↥(Γ.map ρ)) →+ ↥(ribbonKernel D))
    (hΦ : ∀ γ : ↥(Γ.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φ (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel D)) : E → ℤ) (eE e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (pt : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion FC)
    (hpt_fib : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), pt z = pt z' ↔ ∃ γ : ↥(Γ.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_onto : Function.Surjective pt)

    (hpt : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (galFC : S →* SemilinearAut A.valuation.Completion FC)
    (hgalFC_base : ∀ (σ : S) (c : A.valuation.Completion), SemilinearAut.baseAut (galFC σ) c = (scalar σ) • c)
    (hgal : ∀ σ : S, ∃ (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion),
      n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) ∧ (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))))
    (πV : S →* Equiv.Perm V) (πE : S →* Equiv.Perm E) (sgn : S →* ℤˣ)
    (hπV : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ v : LT.LatticeTree.Vertex R₀ K₀, πV σ (eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (ρ n • v)))
    (hπE : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
        (ρ n ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = 1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out))) ∧
        (ρ n ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = -1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out).symm)))
    (hπ_width : ∀ σ e, D.w (πE σ e) = D.w e)
    (hsgn_pos : ∀ σ e, sgn σ = 1 → D.a (πE σ e) = πV σ (D.a e) ∧ D.b (πE σ e) = πV σ (D.b e))
    (hsgn_neg : ∀ σ e, sgn σ = -1 → D.a (πE σ e) = πV σ (D.b e) ∧ D.b (πE σ e) = πV σ (D.a e))
    (hπ_inertia : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → πV (ι τ) = 1 ∧ πE (ι τ) = 1 ∧ sgn (ι τ) = 1)
    (actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)))
    (hactZ : ∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E), (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e)
    (n : ℕ) (a b z : Fin n → A.valuation.Completion)
    (ha : ∀ i, a i ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : ∀ i, b i ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
    (hz : ∀ i, z i ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
    (hza : ∀ i (γ : ↥(Γ.map ρ)), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (a i) ≠ z i) (hzb : ∀ i (γ : ↥(Γ.map ρ)), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (b i) ≠ z i)
    (hprin : Divisor.IsPrincipal (K := A.valuation.Completion) (F := FC)
      (∑ i, (Finsupp.single (pt ⟨a i, ha i⟩) 1 - Finsupp.single (pt ⟨b i, hb i⟩) 1) : Divisor A.valuation.Completion FC)) :
    ∃ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion ∧ y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion ∧
      (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) ∧
      ∃ α : ↥(Γ.map ρ), ∀ β : ↥(Γ.map ρ),
        ∏ i, Omega.theta (Γ.map ρ).subtype (a i) (b i) (z i) (Omega.pmoebius K₀ (β : PGL(2, K₀)) (z i)) =
          Omega.period (Γ.map ρ).subtype x y α β := by
  classical

  haveI hAC : IsAlgClosed A.valuation.Completion :=
    ValuationSubring.isAlgClosed_completion_of_liesOverPrime r (Fact.out) A hA
  haveI hdom : IsDomain ↥(Omega.holRing ϖ) := (show IsDomain ↥(Omega.holRing ϖ) from ‹IsDomain (Omega.HolRingOf ϖ ρ)›)
  have hrk' := ECOmegaD.hrk A hA
  have hfin' := ECOmegaD.hfin A K₀ R₀ hA hR₀ ϖ ϖ₀ hϖ₀ hϖ
  haveI hstabv : ∀ v : LT.LatticeTree.Vertex R₀ K₀, Finite (MulAction.stabilizer ↥(Γ.map ρ) v) :=
    fun v => ECOmegaD.finite_stabilizer_vertex R₀ K₀ (Γ.map ρ) hfin v
  have hdisc : Omega.IsDiscrete A.valuation.Completion (Γ.map ρ).subtype := by
    haveI := ECOmegaD.finite_quot hϖ₀
    haveI := hstabv (LT.LatticeTree.stdVertex R₀ K₀)
    refine CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex R₀ K₀ ϖ₀ hϖ₀ A.valuation.Completion
      (ECOmegaD.hint hR₀) (ECOmegaD.hv hR₀) (ECOmegaD.hq A K₀ R₀ hA ϖ ϖ₀ hϖ) (Γ.map ρ).subtype ?_
    have : Finite {γ : ↥(Γ.map ρ) | (Γ.map ρ).subtype γ • LT.LatticeTree.stdVertex R₀ K₀ = LT.LatticeTree.stdVertex R₀ K₀} :=
      Finite.of_injective (fun x => (⟨x.1, x.2⟩ : MulAction.stabilizer ↥(Γ.map ρ) (LT.LatticeTree.stdVertex R₀ K₀)))
        (fun x y h => Subtype.ext (congrArg Subtype.val h))
    exact Set.toFinite _

  have hdiv := fun (x y w : A.valuation.Completion) (hx : x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
      (hy : y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hw : w ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
      (hxa : ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ w)
      (hyb : ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) y ≠ w) =>
    CerednikDrinfeld.Omega.exists_isThetaPair_ordAt_eq_card K₀ A.valuation.Completion ϖ hrk' hex hfin'
      (Γ.map ρ).subtype hdisc hx hy hw hxa hyb
  choose F Hh hpair hord using fun i => hdiv (a i) (b i) (z i) (ha i) (hb i) (hz i) (hza i) (hzb i)

  have hF0 : ∀ i, F i ≠ 0 := fun i h0 => by
    obtain ⟨γ, hγ⟩ := ((hpair i).2.2.1 ⟨z i, hz i⟩).mp (by rw [h0]; rfl)
    exact hza i γ hγ
  have hH0 : ∀ i, Hh i ≠ 0 := fun i h0 => by
    obtain ⟨γ, hγ⟩ := ((hpair i).2.1 ⟨z i, hz i⟩).mp (by rw [h0]; rfl)
    exact hzb i γ hγ

  obtain ⟨gFC, hgFC0, hdivg⟩ := hprin
  obtain ⟨⟨g₁, g₂⟩, hg12⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (Omega.HolRingOf ϖ ρ))
    ((eFC gFC : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))
  have hrep : ((eFC gFC : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) :
      FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g₁ ⟨g₂.1, g₂.2⟩ := by
    rw [Localization.mk_eq_mk']; exact hg12.symm
  have hmem : (show FractionRing (Omega.HolRingOf ϖ ρ) from Localization.mk g₁ ⟨g₂.1, g₂.2⟩) ∈
      Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ := by
    have := (eFC gFC).2
    rw [hrep] at this
    exact this
  have hg₁ : (show ↥(Omega.holRing ϖ) from g₁) ≠ 0 := by
    intro h0
    apply hgFC0
    have h1 : ((eFC gFC : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) :
        FractionRing (Omega.HolRingOf ϖ ρ)) = 0 := by
      rw [hrep, show g₁ = 0 from h0, Localization.mk_zero]
    have h2 : eFC gFC = 0 := Subtype.ext h1
    exact (map_eq_zero_iff _ eFC.injective).mp h2
  have hg₂0 : (show ↥(Omega.holRing ϖ) from g₂.1) ≠ 0 := nonZeroDivisors.ne_zero g₂.2
  have heq : eFC.symm ⟨_, hmem⟩ = gFC := by
    rw [AlgEquiv.symm_apply_eq]
    exact Subtype.ext hrep.symm
  have hdivg' : ∀ v : Place A.valuation.Completion FC,
      ((∑ i, (Finsupp.single (pt ⟨a i, ha i⟩) 1 - Finsupp.single (pt ⟨b i, hb i⟩) 1)) : Divisor A.valuation.Completion FC) v =
        v.ord (eFC.symm ⟨_, hmem⟩) := fun v => by rw [heq]; exact hdivg v

  have hOrd := ECOmegaD.ordAt_prod_mul_eq_of_divisor_eq_ord A hA K₀ R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex G ρ Γ htp hfin htame FC eFC eV eE pt hpt_fib hpt
    hdisc a b ha hb F Hh hF0 hH0 hord (show ↥(Omega.holRing ϖ) from g₁) (show ↥(Omega.holRing ϖ) from g₂.1) hg₁ g₂.2 hmem hdivg'

  obtain ⟨u, hu, hueq⟩ := ECOmegaD.AbelConverse.exists_isUnit_mul_eq_of_forall_ordAt_eq ϖ hrk' hex hfin'
    ((∏ i, F i) * (show ↥(Omega.holRing ϖ) from g₂.1)) ((∏ i, Hh i) * (show ↥(Omega.holRing ϖ) from g₁))
    (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hF0 i) hg₂0)
    (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hH0 i) hg₁) hOrd

  have hinv := fun γ : ↥(Γ.map ρ) => ECOmegaD.fracAct_eq_of_mem_invariantFieldOf ϖ ρ Γ _ hmem γ
  obtain ⟨χ, hχv, haut, hχ1⟩ := ECOmegaD.AbelConverse.exists_multiplier_of_unit ϖ hex (Γ.map ρ) hdisc a b z ha hb hz hza hzb
    F Hh hpair (show ↥(Omega.holRing ϖ) from g₁) (show ↥(Omega.holRing ϖ) from g₂.1) u
    (mem_nonZeroDivisors_of_ne_zero hg₁) g₂.2 hueq hinv

  haveI := ECOmegaD.finite_quot hϖ₀
  haveI : Finite (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) := Finite.of_equiv _ eV.symm
  have hActs : Mumford.ActsThrough (LT.LatticeTree.Vertex R₀ K₀) (Γ.map ρ).subtype := fun g w => rfl
  obtain ⟨hconn, hcol⟩ := CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R₀ K₀
  obtain ⟨hadj1, -, -⟩ := CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
    ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) hconn hcol (LT.LatticeTree.stdVertex R₀ K₀)
  have hτ : ∀ (g : ↥(Γ.map ρ)) (w : LT.LatticeTree.Vertex R₀ K₀),
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (g • w) =
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w := fun g w => htp g.2 w
  have hadj : ∀ u w : LT.LatticeTree.Vertex R₀ K₀, (BruhatTits.tree R₀ K₀).Adj u w →
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) u ≠
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w := by
    intro u w huw h
    have h1 := hadj1 u w huw
    rw [← h] at h1
    have h2 : (1 : ZMod 2) = 0 := add_left_cancel (h1.symm.trans (add_zero _).symm)
    exact absurd h2 (by decide)
  obtain ⟨w₀, hw₀⟩ := ECOmegaD.AbelConverse.exists_mem_affinoid_zero ϖ hfin'
  have hw₀Ω := Omega.affinoid_subset_upperHalfPlane ϖ 0 hw₀
  obtain ⟨nM, hn⟩ : ∃ nM : GL (Fin 2) K₀, nM = LT.LatticeTree.diagSnd (LT.LatticeTree.unitOfNeZero (K := K₀) hϖ₀.ne_zero) :=
    ⟨_, rfl⟩
  have hnadj : (BruhatTits.tree R₀ K₀).Adj (LT.LatticeTree.stdVertex R₀ K₀) (nM • LT.LatticeTree.stdVertex R₀ K₀) := by
    rw [BruhatTits.tree_adj_iff, hn]
    refine ⟨(LT.LatticeTree.stdVertex_ne_act_diagSnd (R := R₀) (K := K₀) hϖ₀).symm,
      Or.inl ⟨LT.LatticeTree.stdLattice R₀ K₀, LT.LatticeTree.latticeMap _ (LT.LatticeTree.stdLattice R₀ K₀),
        LT.LatticeTree.isFullLattice_stdLattice, LT.LatticeTree.isFullLattice_stdLattice.map _, rfl, rfl,
        LT.LatticeTree.adjacentLattice_stdLattice_diagSnd (R := R₀) (K := K₀) hϖ₀⟩⟩
  have hsep : Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) ((1 : GL (Fin 2) K₀) • LT.LatticeTree.stdVertex R₀ K₀) ≠
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (nM • LT.LatticeTree.stdVertex R₀ K₀) := by
    rw [one_smul]; exact hadj _ _ hnadj

  obtain ⟨α, hα⟩ :=
    CerednikDrinfeld.Omega.exists_forall_eq_period_of_isUnit_of_apply_smul_eq_mul_of_forall_isOfFinOrder R₀ K₀ ϖ₀ hϖ₀
      A.valuation.Completion (ECOmegaD.hint hR₀) (ECOmegaD.hv hR₀) (ECOmegaD.hq A K₀ R₀ hA ϖ ϖ₀ hϖ) hrk' ϖ hex
      (Γ.map ρ).subtype hActs (Γ.map ρ).subtype_injective hstabv
      (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hτ hadj
      1 nM hw₀ hw₀ hsep u hu χ haut hχ1 htame

  have hbase : ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk nM) w₀) ≠
      Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk 1) w₀ := by
    intro γ hγ
    obtain ⟨gγ, hgγ⟩ := Matrix.ProjGenLinGroup.mk_surjective (γ : PGL(2, K₀))
    rw [← hgγ, ← Omega.pmoebius_mul K₀ hw₀Ω, ← map_mul] at hγ
    have hred := CerednikDrinfeld.Omega.smul_stdVertex_eq_of_mem_affinoid_zero R₀ K₀ ϖ₀ hϖ₀ A.valuation.Completion
      (ECOmegaD.hint hR₀) (ECOmegaD.hv hR₀) ϖ (x := Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk 1) w₀) (gγ * nM) 1
      (by rw [← hγ, ← Omega.pmoebius_mul K₀ hw₀Ω, inv_mul_cancel, Omega.pmoebius_one]; exact hw₀)
      (by rw [← Omega.pmoebius_mul K₀ hw₀Ω, inv_mul_cancel, Omega.pmoebius_one]; exact hw₀)
    have hτγ := hτ γ (nM • LT.LatticeTree.stdVertex R₀ K₀)
    rw [Subgroup.smul_def, ← hgγ, BruhatTits.pgl_mk_smul, ← mul_smul, hred] at hτγ
    exact hsep hτγ
  refine ⟨Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk nM) w₀, Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk 1) w₀,
    Omega.pmoebius_mem_upperHalfPlane K₀ hw₀Ω _, Omega.pmoebius_mem_upperHalfPlane K₀ hw₀Ω _, hbase, α, fun β => ?_⟩
  rw [← hα β]
  exact (hχv β).symm

end
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one.ECOmegaD"

end S_AlgebraicCurve_Pic0_exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one (solution)
