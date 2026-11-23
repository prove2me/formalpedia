-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:09.108204+00:00
-- url     : https://prove2.me/theorems/0d3b8cce-6ee9-4f5a-b254-c787efc3faf8
-- title:
--   T2 Space General Linear Group
-- statement:
--   Definitions and structural lemmas for T2 Space General Linear Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/T2SpaceGeneralLinearGroup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_Model_measurableEmbedding_val
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology
open scoped NNReal ENNReal Pointwise
noncomputable section
namespace GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem mem_KO_iff (g : GL n k) :
    g ∈ KO k n ↔ (∀ i j, g.val i j ∈ 𝒪[k]) ∧ ∀ i j, (g⁻¹).val i j ∈ 𝒪[k] := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨fun i j => (u.val i j).2, fun i j => ?_⟩
    rw [← map_inv]; exact ((u⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    have inj : Function.Injective ((algebraMap 𝒪[k] k).mapMatrix (m := n)) :=
      fun A B h => by ext i j; exact congrFun (congrFun h i) j
    let A : Matrix n n 𝒪[k] := fun i j => ⟨g.val i j, h1 i j⟩
    let B : Matrix n n 𝒪[k] := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
    have hA : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
    have hB : (algebraMap 𝒪[k] k).mapMatrix B = (g⁻¹).val := rfl
    refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
    · rw [map_mul, hA, hB, map_one, Units.mul_inv]
    · rw [map_mul, hA, hB, map_one, Units.inv_mul]
theorem isEmbedding_val_GL : IsEmbedding (fun g : GL n k => g.val) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  refine Units.isEmbedding_val_mk' (f := fun A : Matrix n n k => A⁻¹) (fun A hA => ?_) fun u => by simp
  refine (continuousAt_matrix_inv A ?_).continuousWithinAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
instance t2Space_general_linear_group : T2Space (GL n k) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  infer_instance
instance secondCountable_GL : SecondCountableTopology (GL n k) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have : SecondCountableTopology (Matrix n n k) := inferInstanceAs (SecondCountableTopology (n → n → k))
  exact isEmbedding_val_GL.secondCountableTopology
instance locallyCompact_GL : LocallyCompactSpace (GL n k) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have : LocallyCompactSpace (Matrix n n k) := inferInstanceAs (LocallyCompactSpace (n → n → k))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace
omit [DecidableEq n] in
theorem isOpen_intMatrix {m : Type*} [Fintype m] : IsOpen {A : Matrix m n k | ∀ i j, A i j ∈ 𝒪[k]} := by
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact isOpen_int.preimage (f := fun A : Matrix m n k => A i j) (by fun_prop)
omit [DecidableEq n] [Fintype n] in
theorem isCompact_intMatrix {m : Type*} : IsCompact {A : Matrix m n k | ∀ i j, A i j ∈ 𝒪[k]} := by
  have h : IsCompact (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : n => (𝒪[k] : Set k)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int
  have e : {A : Matrix m n k | ∀ i j, A i j ∈ 𝒪[k]} =
      (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : n => (𝒪[k] : Set k)) :=
    Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
  rw [e]; exact h
theorem isOpen_KO : IsOpen (KO k n : Set (GL n k)) := by
  have h1 := (isOpen_intMatrix (k := k) (m := n) (n := n)).preimage (Units.continuous_val (M := Matrix n n k))
  have h2 := (isOpen_intMatrix (k := k) (m := n) (n := n)).preimage (Units.continuous_coe_inv (M := Matrix n n k))
  convert h1.inter h2 using 1
  exact Set.ext mem_KO_iff
theorem isCompact_KO : IsCompact (KO k n : Set (GL n k)) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have hK := isCompact_intMatrix (k := k) (m := n) (n := n)
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [SetLike.mem_coe, mem_KO_iff, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def diagGL (c : n → kˣ) : GL n k :=
  ⟨diagonal fun i => (c i : k), diagonal fun i => ((c i)⁻¹ : kˣ), by simp [diagonal_mul_diagonal],
    by simp [diagonal_mul_diagonal]⟩
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
@[simp] theorem diagGL_val (c : n → kˣ) : (diagGL c).val = diagonal fun i => (c i : k) := rfl
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def diagHom : (n → kˣ) →* GL n k where
  toFun := diagGL
  map_one' := Units.ext (by simp)
  map_mul' c c' := Units.ext (by simp [diagonal_mul_diagonal])
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem hom_eq_one_of_center (Δ : GL n k →* ℝ≥0) (hc : ∀ g, (∀ h, g * h = h * g) → Δ g = 1) (g : GL n k) :
    Δ g = 1 := by
  have pos : ∀ g, Δ g ≠ 0 := fun g => ((Group.isUnit g).map Δ).ne_zero
  have conj : ∀ x y p : GL n k, p * x = y * p → Δ x = Δ y := fun x y p h => by
    have := congrArg Δ h
    rw [map_mul, map_mul, mul_comm] at this
    exact mul_right_cancel₀ (pos p) this
  have hdiag : ∀ c : n → kˣ, Δ (diagGL c) = 1 := fun c => by
    have h1 : ∀ σ : Equiv.Perm n, Δ (diagGL c) = Δ (diagGL (c ∘ σ)) := fun σ =>
      conj _ _ (Matrix.GeneralLinearGroup.mkOfDetNeZero (σ.permMatrix k) (by
        rw [Matrix.det_permutation]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h])) (Units.ext (by
        ext i j
        simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, diagGL_val, mul_diagonal,
          diagonal_mul, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
          Option.some.injEq, Function.comp]
        split_ifs with h <;> simp [h]))
    have h2 : Δ (diagHom (∏ σ : Equiv.Perm n, c ∘ σ)) = 1 := hc _ fun h => Units.ext (by
      rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
      · exact Subsingleton.elim _ _
      have : (∏ σ : Equiv.Perm n, c ∘ σ) = fun _ => ∏ σ : Equiv.Perm n, c (σ i₀) := by
        funext i
        rw [Finset.prod_apply]
        exact (Fintype.prod_equiv (Equiv.mulRight (Equiv.swap i₀ i)) _ _ fun σ => by simp)
      rw [this]
      simp only [diagHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, diagGL_val, ← smul_one_eq_diagonal]
      simp)
    rw [← MonoidHom.comp_apply, map_prod] at h2
    have h3 : ∏ σ : Equiv.Perm n, Δ (diagGL c) = 1 := by
      rw [← h2]; exact Finset.prod_congr rfl fun σ _ => h1 σ
    rw [Finset.prod_const] at h3
    exact (pow_eq_one_iff_of_nonneg zero_le (Finset.card_ne_zero.2 Finset.univ_nonempty)).1 h3
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ g : GL n k, g.val = M → Δ g = 1) g.val g.det_ne_zero ?_ ?_ ?_ g rfl
  · intro D hD g hg
    rw [det_diagonal, Finset.prod_ne_zero_iff] at hD
    rw [show g = diagGL fun i => Units.mk0 (D i) (hD i (Finset.mem_univ _)) from Units.ext hg]
    exact hdiag _
  · rintro ⟨i, j, hij, c⟩ g hg
    have hinv : (g⁻¹).val = transvection i j (-c) := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [hg, TransvectionStruct.toMatrix_mk, transvection_mul_transvection_same _ _ hij]
      simp
    have h1 : Δ g = Δ g⁻¹ := conj _ _ (diagGL fun l => if l = i then -1 else 1) (Units.ext (by
      ext a b
      rw [Units.val_mul, Units.val_mul, hinv, hg, TransvectionStruct.toMatrix_mk]
      simp only [diagGL_val, mul_diagonal, diagonal_mul, transvection, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply]
      clear conj hdiag hc pos hinv hg
      simp only [apply_ite (Units.val : kˣ → k), Units.val_neg, Units.val_one]
      split_ifs <;> first | (exfalso; grind) | ring))
    have h2 : Δ g ^ 2 = 1 := by
      rw [pow_two]; nth_rewrite 2 [h1]; rw [← map_mul, mul_inv_cancel, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h2
  · intro A B hA hB pA pB g hg
    rw [show g = Matrix.GeneralLinearGroup.mkOfDetNeZero A hA * Matrix.GeneralLinearGroup.mkOfDetNeZero B hB from
      Units.ext hg, map_mul, pA _ rfl, pB _ rfl, one_mul]
variable [MeasurableSpace k] [BorelSpace k]
instance borel_GL : BorelSpace (GL n k) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have hB : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  exact (measurableEmbedding_val n).borelSpace isEmbedding_val_GL.isInducing
instance isMulRightInvariant_of_haar (μ : Measure (GL n k)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h : Measure.modularCharacter g = 1 := by
    refine hom_eq_one_of_center Measure.modularCharacter (fun z hz => ?_) g
    have h1 := Measure.map_right_mul_eq_modularCharacterFun_smul μ z
    rw [show (fun x => x * z) = fun x => z * x from funext fun x => (hz x).symm,
      Measure.IsMulLeftInvariant.map_mul_left_eq_self] at h1
    have h2 := congrArg (fun m : Measure (GL n k) => m (KO k n)) h1
    have hne : μ (KO k n) ≠ 0 := (isOpen_KO.measure_pos μ ⟨1, one_mem _⟩).ne'
    have hnt : μ (KO k n) ≠ ⊤ := isCompact_KO.measure_lt_top.ne
    simp only [Measure.coe_nnreal_smul_apply] at h2
    have h3 : (Measure.modularCharacterFun z : ℝ≥0∞) = 1 :=
      (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
    exact_mod_cast h3
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g, show Measure.modularCharacterFun g = 1 from h, one_smul]
def haarVol (J : Subgroup (GL n k)) : Measure (GL n k) :=
  ((Measure.haar : Measure (GL n k)) J)⁻¹ • Measure.haar
theorem haar_ne_zero_ne_top (μ : Measure (GL n k)) [μ.IsHaarMeasure] {J : Subgroup (GL n k)}
    (ho : IsOpen (J : Set (GL n k))) (hK : J ≤ KO k n) : μ J ≠ 0 ∧ μ J ≠ ⊤ :=
  ⟨(ho.measure_pos μ ⟨1, one_mem _⟩).ne', ((measure_mono hK).trans_lt isCompact_KO.measure_lt_top).ne⟩
theorem isHaarMeasure_haarVol {J : Subgroup (GL n k)} (ho : IsOpen (J : Set (GL n k))) (hK : J ≤ KO k n) :
    (haarVol J).IsHaarMeasure :=
  have h := haar_ne_zero_ne_top Measure.haar ho hK
  Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 h.2) (ENNReal.inv_ne_top.2 h.1)
instance isHaarMeasure_haarVol_KO : (haarVol (KO k n)).IsHaarMeasure := isHaarMeasure_haarVol isOpen_KO le_rfl
end GlobalTheory.SplitFlip


