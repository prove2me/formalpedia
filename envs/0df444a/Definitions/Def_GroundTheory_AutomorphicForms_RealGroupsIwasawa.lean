-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
-- name    : GroundTheory_AutomorphicForms_RealGroupsIwasawa
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:45.973798+00:00
-- url     : https://prove2.me/theorems/b5dac571-ff8c-413d-aff3-d2c2b6c35c7f
-- title:
--   Real Groups Iwasawa
-- statement:
--   Definitions and structural lemmas for Real Groups Iwasawa, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsIwasawa.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open Matrix
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]
theorem mul_apply_self_of_isUpperTriangular {A B : Matrix n n 𝕜} (hA : A.IsUpperTriangular)
    (hB : B.IsUpperTriangular) (i : n) : (A * B) i i = A i i * B i i := by
  rw [mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h
theorem isUpperTriangular_conjTranspose_iff {A : Matrix n n 𝕜} :
    Aᴴ.IsUpperTriangular ↔ A.IsLowerTriangular := by
  constructor
  · intro h i j hij
    have := h (i := j) (j := i) (OrderDual.toDual_lt_toDual.1 hij)
    simpa [conjTranspose_apply] using this
  · intro h i j hij
    have := h (show OrderDual.toDual i < OrderDual.toDual j from hij)
    simp [conjTranspose_apply, this]
theorem eq_one_of_mem_unitaryGroup_of_isUpperTriangular {t : Matrix n n 𝕜}
    (ht : t ∈ unitaryGroup n 𝕜) (hu : t.IsUpperTriangular) (hpos : ∀ i, 0 < t i i) : t = 1 := by
  have h1 : tᴴ * t = 1 := ht.1
  let : Invertible t := invertibleOfLeftInverse t tᴴ h1
  have hinv : t⁻¹ = tᴴ := inv_eq_left_inv h1
  have hinvU : t⁻¹.IsUpperTriangular := blockTriangular_inv_of_blockTriangular hu
  rw [hinv, isUpperTriangular_conjTranspose_iff] at hinvU
  have hdiag : ∀ i j, i ≠ j → t i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hinvU (show OrderDual.toDual j < OrderDual.toDual i from h)
    · exact hu h
  have hii : ∀ i, t i i = 1 := by
    intro i
    have e := congrFun (congrFun h1 i) i
    rw [mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hdiag k i hk, mul_zero])
      (fun h => absurd (Finset.mem_univ i) h), one_apply_eq, conjTranspose_apply] at e
    obtain ⟨hre, him⟩ := RCLike.pos_iff.1 (hpos i)
    have hr : t i i = (RCLike.re (t i i) : 𝕜) := by
      rw [← RCLike.re_add_im (t i i), him]; simp
    rw [hr, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, ← RCLike.ofReal_one,
      RCLike.ofReal_inj] at e
    rw [hr, ← RCLike.ofReal_one, RCLike.ofReal_inj]
    nlinarith
  ext i j
  by_cases h : i = j
  · subst h; rw [hii, one_apply_eq]
  · rw [hdiag i j h, one_apply_ne h]
section Existence
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
theorem exists_isUpperTriangular_conjTranspose_mul_self {S : Matrix n n 𝕜} (hS : S.PosDef) :
    ∃ R : Matrix n n 𝕜, R.IsUpperTriangular ∧ Rᴴ * R = S := by
  have hLi : (LDL.lowerInv hS).IsLowerTriangular := fun i j hij =>
    LDL.lowerInv_triangular hS (OrderDual.toDual_lt_toDual.1 hij)
  have hL : (LDL.lower hS).IsLowerTriangular := blockTriangular_inv_of_blockTriangular hLi
  have hD : (LDL.diag hS).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact hS.mul_mul_conjTranspose_same
      (vecMul_injective_iff_isUnit.2 (isUnit_of_invertible (LDL.lowerInv hS)))
  have hpos : ∀ i, 0 < LDL.diagEntries hS i := fun i => by
    simpa [LDL.diag] using hD.diag_pos (i := i)
  set d : n → ℝ := fun i => RCLike.re (LDL.diagEntries hS i)
  have hd : ∀ i, LDL.diagEntries hS i = (d i : 𝕜) := fun i => by
    obtain ⟨_, him⟩ := RCLike.pos_iff.1 (hpos i)
    rw [← RCLike.re_add_im (LDL.diagEntries hS i), him]; simp [d]
  have hd0 : ∀ i, 0 ≤ d i := fun i => (RCLike.pos_iff.1 (hpos i)).1.le
  refine ⟨diagonal (fun i => (Real.sqrt (d i) : 𝕜)) * (LDL.lower hS)ᴴ,
    (blockTriangular_diagonal _).mul (isUpperTriangular_conjTranspose_iff.2 hL), ?_⟩
  have hsq : (diagonal (fun i => (Real.sqrt (d i) : 𝕜)))ᴴ * diagonal (fun i => (Real.sqrt (d i) : 𝕜))
      = LDL.diag hS := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, LDL.diag]
    congr 1; funext i
    rw [hd i, Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul,
      Real.mul_self_sqrt (hd0 i)]
  rw [conjTranspose_mul, conjTranspose_conjTranspose]
  calc LDL.lower hS * (diagonal fun i => (Real.sqrt (d i) : 𝕜))ᴴ *
        (diagonal (fun i => (Real.sqrt (d i) : 𝕜)) * (LDL.lower hS)ᴴ)
      = LDL.lower hS * ((diagonal fun i => (Real.sqrt (d i) : 𝕜))ᴴ *
        diagonal (fun i => (Real.sqrt (d i) : 𝕜))) * (LDL.lower hS)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = S := by rw [hsq, LDL.lower_conj_diag]
end Existence
section Existence2
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
theorem star_mul_self_norm_div {x : 𝕜} (hx : x ≠ 0) :
    star ((‖x‖ : 𝕜) / x) * ((‖x‖ : 𝕜) / x) = 1 := by
  rw [star_div₀, RCLike.star_def, RCLike.conj_ofReal, div_mul_div_comm, RCLike.conj_mul, ← sq]
  exact div_self (pow_ne_zero 2 (by simpa using hx))
theorem exists_cholesky {S : Matrix n n 𝕜} (hS : S.PosDef) :
    ∃ B : Matrix n n 𝕜, ∃ a : n → ℝ, B.IsUpperTriangular ∧ (∀ i, 0 < a i) ∧
      (∀ i, B i i = a i) ∧ Bᴴ * B = S := by
  obtain ⟨R, hR, hRS⟩ := exists_isUpperTriangular_conjTranspose_mul_self hS
  have hdet : S.det ≠ 0 := (isUnit_iff_isUnit_det S).1 hS.isUnit |>.ne_zero
  have hRi : ∀ i, R i i ≠ 0 := by
    have : R.det ≠ 0 := by
      intro h; apply hdet; rw [← hRS, det_mul, h, mul_zero]
    rw [det_of_isUpperTriangular hR] at this
    exact fun i => Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ i)
  refine ⟨diagonal (fun i => (‖R i i‖ : 𝕜) / R i i) * R, fun i => ‖R i i‖,
    (blockTriangular_diagonal _).mul hR, fun i => norm_pos_iff.2 (hRi i), fun i => ?_, ?_⟩
  · rw [diagonal_mul, div_mul_cancel₀ _ (hRi i)]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _)ᴴ,
      diagonal_conjTranspose, diagonal_mul_diagonal]
    have : (fun i => (star (fun i => (‖R i i‖ : 𝕜) / R i i)) i * ((‖R i i‖ : 𝕜) / R i i)) =
        fun _ => 1 := funext fun i => star_mul_self_norm_div (hRi i)
    rw [this, diagonal_one, Matrix.one_mul, hRS]
theorem exists_KAN (g : GL n 𝕜) :
    ∃ k : unitaryGroup n 𝕜, ∃ a : n → ℝ, (∀ i, 0 < a i) ∧ ∃ u : Matrix n n 𝕜,
      u.IsUpperTriangular ∧ (∀ i, u i i = 1) ∧
        (g : Matrix n n 𝕜) = (k : Matrix n n 𝕜) * diagonal (fun i => (a i : 𝕜)) * u := by
  obtain ⟨B, a, hB, ha, hBd, hBS⟩ := exists_cholesky (posDef_conjTranspose_mul_self_GL g)
  have hBdet : IsUnit B.det := by
    rw [det_of_isUpperTriangular hB]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by
      rw [hBd i]; exact_mod_cast (ha i).ne')
  have hau : diagonal (fun i => (a i : 𝕜)) * (diagonal (fun i => ((a i : 𝕜))⁻¹) * B) = B := by
    rw [← Matrix.mul_assoc, diagonal_mul_diagonal]
    have : (fun i => (a i : 𝕜) * (a i : 𝕜)⁻¹) = fun _ => 1 :=
      funext fun i => mul_inv_cancel₀ (by exact_mod_cast (ha i).ne')
    rw [this, diagonal_one, Matrix.one_mul]
  have hk : (g : Matrix n n 𝕜) * B⁻¹ ∈ unitaryGroup n 𝕜 := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_mul,
      conjTranspose_nonsing_inv]
    calc Bᴴ⁻¹ * (g : Matrix n n 𝕜)ᴴ * ((g : Matrix n n 𝕜) * B⁻¹)
        = Bᴴ⁻¹ * ((g : Matrix n n 𝕜)ᴴ * g) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Bᴴ⁻¹ * Bᴴ * (B * B⁻¹) := by rw [← hBS]; simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.nonsing_inv_mul _ (by rw [det_conjTranspose]; exact hBdet.star),
          Matrix.mul_nonsing_inv _ hBdet, Matrix.one_mul]
  refine ⟨⟨_, hk⟩, a, ha, diagonal (fun i => ((a i : 𝕜))⁻¹) * B,
    (blockTriangular_diagonal _).mul hB, fun i => ?_, ?_⟩
  · rw [diagonal_mul, hBd i, inv_mul_cancel₀ (by exact_mod_cast (ha i).ne')]
  · rw [Matrix.mul_assoc, hau]
    show (g : Matrix n n 𝕜) = (g : Matrix n n 𝕜) * B⁻¹ * B
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBdet, Matrix.mul_one]
end Existence2
section Uniqueness
theorem isUnit_det_diagonal_mul_of_unitriangular {a : n → ℝ} (ha : ∀ i, 0 < a i)
    {u : Matrix n n 𝕜} (hu : u.IsUpperTriangular) (hu1 : ∀ i, u i i = 1) :
    IsUnit (diagonal (fun i => (a i : 𝕜)) * u).det := by
  rw [det_of_isUpperTriangular ((blockTriangular_diagonal _).mul hu)]
  exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by
    rw [diagonal_mul, hu1, mul_one]; exact_mod_cast (ha i).ne')
theorem KAN_unique {k k' : unitaryGroup n 𝕜} {a a' : n → ℝ} {u u' : Matrix n n 𝕜}
    (ha : ∀ i, 0 < a i) (ha' : ∀ i, 0 < a' i) (hu : u.IsUpperTriangular)
    (hu' : u'.IsUpperTriangular) (hu1 : ∀ i, u i i = 1) (hu1' : ∀ i, u' i i = 1)
    (h : (k : Matrix n n 𝕜) * diagonal (fun i => (a i : 𝕜)) * u =
      (k' : Matrix n n 𝕜) * diagonal (fun i => (a' i : 𝕜)) * u') :
    k = k' ∧ a = a' ∧ u = u' := by
  set B := diagonal (fun i => (a i : 𝕜)) * u with hBdef
  set B' := diagonal (fun i => (a' i : 𝕜)) * u' with hB'def
  have hB : B.IsUpperTriangular := (blockTriangular_diagonal _).mul hu
  have hB' : B'.IsUpperTriangular := (blockTriangular_diagonal _).mul hu'
  have hBd : ∀ i, B i i = a i := fun i => by rw [hBdef, diagonal_mul, hu1, mul_one]
  have hBd' : ∀ i, B' i i = a' i := fun i => by rw [hB'def, diagonal_mul, hu1', mul_one]
  have hBu : IsUnit B.det := isUnit_det_diagonal_mul_of_unitriangular ha hu hu1
  have hk' : star (k' : Matrix n n 𝕜) * k' = 1 := mem_unitaryGroup_iff'.1 k'.2
  have h2 : (k : Matrix n n 𝕜) * B = k' * B' := by
    simpa only [hBdef, hB'def, Matrix.mul_assoc] using h
  set t := star (k' : Matrix n n 𝕜) * k with ht
  have htB : t * B = B' := by
    rw [ht, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, hk', Matrix.one_mul]
  have htB' : t = B' * B⁻¹ := by
    rw [← htB, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.mul_one]
  have htU : t.IsUpperTriangular := by
    rw [htB']
    let : Invertible B := invertibleOfIsUnitDet B hBu
    exact hB'.mul (blockTriangular_inv_of_blockTriangular hB)
  have htmem : t ∈ unitaryGroup n 𝕜 := Submonoid.mul_mem _ (Unitary.star_mem k'.2) k.2
  have htpos : ∀ i, 0 < t i i := by
    intro i
    have e := congrFun (congrFun htB i) i
    rw [mul_apply_self_of_isUpperTriangular htU hB, hBd, hBd'] at e
    have hai : (a i : 𝕜) ≠ 0 := by exact_mod_cast (ha i).ne'
    have : t i i = ((a' i / a i : ℝ) : 𝕜) := by
      rw [RCLike.ofReal_div, ← e, mul_div_cancel_right₀ _ hai]
    rw [this]
    exact RCLike.ofReal_pos.2 (div_pos (ha' i) (ha i))
  have ht1 := eq_one_of_mem_unitaryGroup_of_isUpperTriangular htmem htU htpos
  have hkk : k = k' := by
    apply Subtype.ext
    have hk'' : (k' : Matrix n n 𝕜) * star (k' : Matrix n n 𝕜) = 1 := mem_unitaryGroup_iff.1 k'.2
    calc (k : Matrix n n 𝕜) = (k' : Matrix n n 𝕜) * (star (k' : Matrix n n 𝕜) * k) := by
          rw [← Matrix.mul_assoc, hk'', Matrix.one_mul]
      _ = k' := by rw [← ht, ht1, Matrix.mul_one]
  have hBB : B = B' := by rw [← htB, ht1, Matrix.one_mul]
  have haa : a = a' := funext fun i => by
    have := congrFun (congrFun hBB i) i
    rw [hBd, hBd'] at this
    exact_mod_cast this
  refine ⟨hkk, haa, ?_⟩
  subst haa
  have hinv : diagonal (fun i => ((a i : 𝕜))⁻¹) * diagonal (fun i => (a i : 𝕜)) = 1 := by
    rw [diagonal_mul_diagonal]
    have : (fun i => ((a i : 𝕜))⁻¹ * (a i : 𝕜)) = fun _ => 1 :=
      funext fun i => inv_mul_cancel₀ (by exact_mod_cast (ha i).ne')
    rw [this, diagonal_one]
  calc u = diagonal (fun i => ((a i : 𝕜))⁻¹) * B := by
        rw [hBdef, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    _ = diagonal (fun i => ((a i : 𝕜))⁻¹) * B' := by rw [hBB]
    _ = u' := by rw [hB'def, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
end Uniqueness
section Homeomorph
open scoped Matrix.Norms.L2Operator Topology
open Filter Set
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
variable (n) in

abbrev PosDiag := {a : n → ℝ // ∀ i, 0 < a i}
abbrev UpperUnitriangular (n 𝕜 : Type*) [RCLike 𝕜] [LinearOrder n] :=
  {u : Matrix n n 𝕜 // u.IsUpperTriangular ∧ ∀ i, u i i = 1}
theorem isUnit_det_iwasawa (x : unitaryGroup n 𝕜 × PosDiag n × UpperUnitriangular n 𝕜) :
    IsUnit ((x.1 : Matrix n n 𝕜) * diagonal (fun i => (x.2.1.1 i : 𝕜)) * x.2.2.1).det := by
  rw [Matrix.mul_assoc, det_mul]
  exact (UnitaryGroup.det_isUnit x.1).mul
    (isUnit_det_diagonal_mul_of_unitriangular x.2.1.2 x.2.2.2.1 x.2.2.2.2)
noncomputable def iwasawaMul (x : unitaryGroup n 𝕜 × PosDiag n × UpperUnitriangular n 𝕜) :
    GL n 𝕜 :=
  ⟨(x.1 : Matrix n n 𝕜) * diagonal (fun i => (x.2.1.1 i : 𝕜)) * x.2.2.1,
    ((x.1 : Matrix n n 𝕜) * diagonal (fun i => (x.2.1.1 i : 𝕜)) * x.2.2.1)⁻¹,
    mul_nonsing_inv _ (isUnit_det_iwasawa x), nonsing_inv_mul _ (isUnit_det_iwasawa x)⟩
@[simp] theorem coe_iwasawaMul (x : unitaryGroup n 𝕜 × PosDiag n × UpperUnitriangular n 𝕜) :
    ((iwasawaMul x : GL n 𝕜) : Matrix n n 𝕜) =
      (x.1 : Matrix n n 𝕜) * diagonal (fun i => (x.2.1.1 i : 𝕜)) * x.2.2.1 := rfl
theorem iwasawaMul_surjective : Function.Surjective (iwasawaMul (n := n) (𝕜 := 𝕜)) := by
  intro g
  obtain ⟨k, a, ha, u, hu, hu1, h⟩ := exists_KAN g
  exact ⟨(k, ⟨a, ha⟩, ⟨u, hu, hu1⟩), Units.ext h.symm⟩
theorem iwasawaMul_injective : Function.Injective (iwasawaMul (n := n) (𝕜 := 𝕜)) := by
  rintro ⟨k, ⟨a, ha⟩, ⟨u, hu, hu1⟩⟩ ⟨k', ⟨a', ha'⟩, ⟨u', hu', hu1'⟩⟩ h
  obtain ⟨h1, h2, h3⟩ := KAN_unique ha ha' hu hu' hu1 hu1' (congrArg Units.val h)
  subst h1 h2 h3; rfl
noncomputable def iwasawaEquiv : unitaryGroup n 𝕜 × PosDiag n × UpperUnitriangular n 𝕜 ≃ GL n 𝕜 :=
  Equiv.ofBijective iwasawaMul ⟨iwasawaMul_injective, iwasawaMul_surjective⟩
theorem isCompact_unitaryGroup : IsCompact (unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := by
  have : ProperSpace (Matrix n n 𝕜) := FiniteDimensional.proper 𝕜 _
  refine Metric.isCompact_of_isClosed_isBounded isClosed_unitary ?_
  refine (Metric.isBounded_iff_subset_closedBall (0 : Matrix n n 𝕜)).2 ⟨‖(1 : Matrix n n 𝕜)‖, ?_⟩
  intro U hU
  rw [Metric.mem_closedBall, dist_zero_right]
  have := CStarRing.norm_mem_unitary_mul (1 : Matrix n n 𝕜) hU
  rw [Matrix.mul_one] at this
  exact this.le
instance : CompactSpace (unitaryGroup n 𝕜) :=
  isCompact_iff_compactSpace.1 isCompact_unitaryGroup
end Homeomorph
section Homeomorph2
open scoped Matrix.Norms.L2Operator Topology
open Filter Set
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
noncomputable def iwasawaK (g : GL n 𝕜) : unitaryGroup n 𝕜 := (iwasawaEquiv.symm g).1
theorem iwasawaEquiv_symm_spec (g : GL n 𝕜) :
    (g : Matrix n n 𝕜) = ((iwasawaEquiv.symm g).1 : Matrix n n 𝕜) *
      diagonal (fun i => ((iwasawaEquiv.symm g).2.1.1 i : 𝕜)) * (iwasawaEquiv.symm g).2.2.1 := by
  conv_lhs => rw [← iwasawaEquiv.apply_symm_apply g]
  rfl
theorem iwasawaK_conjTranspose_mul (g : GL n 𝕜) :
    ((iwasawaK g : Matrix n n 𝕜))ᴴ * g =
      diagonal (fun i => ((iwasawaEquiv.symm g).2.1.1 i : 𝕜)) * (iwasawaEquiv.symm g).2.2.1 := by
  have hk : ((iwasawaK g : Matrix n n 𝕜))ᴴ * iwasawaK g = 1 := (iwasawaK g).2.1
  conv_lhs => rw [iwasawaEquiv_symm_spec g]
  rw [iwasawaK, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← iwasawaK, hk, Matrix.one_mul]
def iwasawaClosedSet : Set (unitaryGroup n 𝕜 × GL n 𝕜) :=
  {p | ((p.1 : Matrix n n 𝕜)ᴴ * p.2).IsUpperTriangular ∧
    ∀ i, 0 ≤ RCLike.re (((p.1 : Matrix n n 𝕜)ᴴ * p.2) i i) ∧
      RCLike.im (((p.1 : Matrix n n 𝕜)ᴴ * p.2) i i) = 0}
theorem isClosed_iwasawaClosedSet : IsClosed (iwasawaClosedSet (n := n) (𝕜 := 𝕜)) := by
  have hc : Continuous (fun p : unitaryGroup n 𝕜 × GL n 𝕜 => (p.1 : Matrix n n 𝕜)ᴴ * p.2) :=
    (continuous_subtype_val.comp continuous_fst).matrix_conjTranspose.mul
      (Units.continuous_val.comp continuous_snd)
  have h1 : IsClosed (⋂ i, ⋂ j, {p : unitaryGroup n 𝕜 × GL n 𝕜 |
      j < i → ((p.1 : Matrix n n 𝕜)ᴴ * p.2) i j = 0}) := by
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    by_cases h : j < i
    · simp only [h, forall_const]
      exact isClosed_eq (hc.matrix_elem i j) continuous_const
    · simp only [h, IsEmpty.forall_iff, ofPred_true, isClosed_univ]
  have h2 : IsClosed (⋂ i, ({p : unitaryGroup n 𝕜 × GL n 𝕜 |
      0 ≤ RCLike.re (((p.1 : Matrix n n 𝕜)ᴴ * p.2) i i)} ∩
      {p | RCLike.im (((p.1 : Matrix n n 𝕜)ᴴ * p.2) i i) = 0})) := by
    refine isClosed_iInter fun i => IsClosed.inter ?_ ?_
    · exact isClosed_le continuous_const (RCLike.continuous_re.comp (hc.matrix_elem i i))
    · exact isClosed_eq (RCLike.continuous_im.comp (hc.matrix_elem i i)) continuous_const
  have e : iwasawaClosedSet (n := n) (𝕜 := 𝕜) = (⋂ i, ⋂ j, {p : unitaryGroup n 𝕜 × GL n 𝕜 |
      j < i → ((p.1 : Matrix n n 𝕜)ᴴ * p.2) i j = 0}) ∩ (⋂ i, ({p : unitaryGroup n 𝕜 × GL n 𝕜 |
      0 ≤ RCLike.re (((p.1 : Matrix n n 𝕜)ᴴ * p.2) i i)} ∩
      {p | RCLike.im (((p.1 : Matrix n n 𝕜)ᴴ * p.2) i i) = 0})) := by
    ext p
    simp only [iwasawaClosedSet, mem_iInter, mem_ofPred_eq, mem_inter_iff, IsUpperTriangular,
      BlockTriangular, id]
  rw [e]
  exact h1.inter h2
theorem mem_iwasawaClosedSet (g : GL n 𝕜) : (iwasawaK g, g) ∈ iwasawaClosedSet (n := n) := by
  refine ⟨?_, fun i => ?_⟩
  · show ((iwasawaK g : Matrix n n 𝕜)ᴴ * g).IsUpperTriangular
    rw [iwasawaK_conjTranspose_mul]
    exact (blockTriangular_diagonal _).mul (iwasawaEquiv.symm g).2.2.2.1
  · show 0 ≤ RCLike.re (((iwasawaK g : Matrix n n 𝕜)ᴴ * g) i i) ∧ _
    rw [iwasawaK_conjTranspose_mul, diagonal_mul, (iwasawaEquiv.symm g).2.2.2.2 i, mul_one]
    simp only [RCLike.ofReal_re, RCLike.ofReal_im, and_true]
    exact ((iwasawaEquiv.symm g).2.1.2 i).le
theorem eq_iwasawaK_of_mem {y : unitaryGroup n 𝕜} {g : GL n 𝕜}
    (h : (y, g) ∈ iwasawaClosedSet (n := n)) : y = iwasawaK g := by
  obtain ⟨hU, hpos⟩ := h
  set R := (y : Matrix n n 𝕜)ᴴ * g with hR
  have hyy : (y : Matrix n n 𝕜) * (y : Matrix n n 𝕜)ᴴ = 1 := y.2.2
  have hRdet : R.det ≠ 0 := by
    rw [hR, det_mul]
    exact mul_ne_zero (by rw [det_conjTranspose]; exact (UnitaryGroup.det_isUnit y).star.ne_zero)
      ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  have hRi : ∀ i, R i i ≠ 0 := by
    rw [det_of_isUpperTriangular hU] at hRdet
    exact fun i => Finset.prod_ne_zero_iff.1 hRdet i (Finset.mem_univ i)
  set a : n → ℝ := fun i => RCLike.re (R i i)
  have hRa : ∀ i, R i i = (a i : 𝕜) := fun i => by
    rw [← RCLike.re_add_im (R i i), (hpos i).2]; simp [a]
  have ha : ∀ i, 0 < a i := fun i => lt_of_le_of_ne (hpos i).1 (fun h => hRi i (by
    rw [hRa i, ← h]; simp))
  have hinv : diagonal (fun i => (a i : 𝕜)) * diagonal (fun i => ((a i : 𝕜))⁻¹) = 1 := by
    rw [diagonal_mul_diagonal]
    have : (fun i => (a i : 𝕜) * ((a i : 𝕜))⁻¹) = fun _ => 1 :=
      funext fun i => mul_inv_cancel₀ (by exact_mod_cast (ha i).ne')
    rw [this, diagonal_one]
  have hu : (diagonal (fun i => ((a i : 𝕜))⁻¹) * R).IsUpperTriangular :=
    (blockTriangular_diagonal _).mul hU
  have hu1 : ∀ i, (diagonal (fun i => ((a i : 𝕜))⁻¹) * R) i i = 1 := fun i => by
    rw [diagonal_mul, hRa i, inv_mul_cancel₀ (by exact_mod_cast (ha i).ne')]
  have hg : iwasawaMul (y, ⟨a, ha⟩, ⟨_, hu, hu1⟩) = g := by
    apply Units.ext
    rw [coe_iwasawaMul]
    show (y : Matrix n n 𝕜) * diagonal (fun i => (a i : 𝕜)) *
      (diagonal (fun i => ((a i : 𝕜))⁻¹) * R) = g
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), hinv, Matrix.one_mul, hR,
      ← Matrix.mul_assoc, hyy, Matrix.one_mul]
  have : iwasawaEquiv.symm g = (y, ⟨a, ha⟩, ⟨_, hu, hu1⟩) := by
    rw [Equiv.symm_apply_eq]; exact hg.symm
  rw [iwasawaK, this]
theorem continuous_iwasawaK : Continuous (iwasawaK : GL n 𝕜 → unitaryGroup n 𝕜) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  apply tendsto_nhds_of_unique_mapClusterPt
  intro y hy
  apply eq_iwasawaK_of_mem
  have hsub : range (fun g : GL n 𝕜 => (iwasawaK g, g)) ⊆ iwasawaClosedSet (n := n) := by
    rintro _ ⟨g, rfl⟩; exact mem_iwasawaClosedSet g
  apply isClosed_iwasawaClosedSet.closure_subset_iff.2 hsub
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 ht
  obtain ⟨g, hgU, hgV⟩ := ((mapClusterPt_iff_frequently.1 hy) U hU).and_eventually hV |>.exists
  exact ⟨(iwasawaK g, g), hUV ⟨hgU, hgV⟩, g, rfl⟩
end Homeomorph2
section Homeomorph3
open scoped Matrix.Norms.L2Operator Topology
open Filter Set
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
theorem iwasawaEquiv_symm_A (g : GL n 𝕜) (i : n) :
    (iwasawaEquiv.symm g).2.1.1 i = RCLike.re ((((iwasawaK g : Matrix n n 𝕜))ᴴ * g) i i) := by
  rw [iwasawaK_conjTranspose_mul, diagonal_mul, (iwasawaEquiv.symm g).2.2.2.2 i, mul_one,
    RCLike.ofReal_re]
theorem iwasawaEquiv_symm_N (g : GL n 𝕜) :
    (iwasawaEquiv.symm g).2.2.1 = diagonal (fun i => (((iwasawaEquiv.symm g).2.1.1 i : 𝕜))⁻¹) *
      (((iwasawaK g : Matrix n n 𝕜))ᴴ * g) := by
  rw [iwasawaK_conjTranspose_mul, ← Matrix.mul_assoc, diagonal_mul_diagonal]
  have : (fun i => (((iwasawaEquiv.symm g).2.1.1 i : 𝕜))⁻¹ * ((iwasawaEquiv.symm g).2.1.1 i : 𝕜)) =
      fun _ => 1 := funext fun i => inv_mul_cancel₀ (by exact_mod_cast ((iwasawaEquiv.symm g).2.1.2 i).ne')
  rw [this, diagonal_one, Matrix.one_mul]
noncomputable def iwasawaHomeomorph :
    unitaryGroup n 𝕜 × PosDiag n × UpperUnitriangular n 𝕜 ≃ₜ GL n 𝕜 where
  toEquiv := iwasawaEquiv
  continuous_toFun := by
    have hM : Continuous (fun x : unitaryGroup n 𝕜 × PosDiag n × UpperUnitriangular n 𝕜 =>
        (x.1 : Matrix n n 𝕜) * diagonal (fun i => (x.2.1.1 i : 𝕜)) * x.2.2.1) :=
      ((continuous_subtype_val.comp continuous_fst).mul (Continuous.matrix_diagonal
        (continuous_pi fun i => RCLike.continuous_ofReal.comp
          ((continuous_apply i).comp (continuous_subtype_val.comp
            (continuous_fst.comp continuous_snd)))))).mul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
    refine Units.continuous_iff.2 ⟨hM, ?_⟩
    exact continuousOn_matrix_inv.comp_continuous hM
      (fun x => (isUnit_iff_isUnit_det _).2 (isUnit_det_iwasawa x))
  continuous_invFun := by
    have hK : Continuous (iwasawaK : GL n 𝕜 → unitaryGroup n 𝕜) := continuous_iwasawaK
    have hR : Continuous (fun g : GL n 𝕜 => ((iwasawaK g : Matrix n n 𝕜))ᴴ * g) :=
      (continuous_subtype_val.comp hK).matrix_conjTranspose.mul Units.continuous_val
    have ha : Continuous fun g : GL n 𝕜 => (iwasawaEquiv.symm g).2.1.1 := by
      have e : (fun g : GL n 𝕜 => (iwasawaEquiv.symm g).2.1.1) =
          fun g i => RCLike.re ((((iwasawaK g : Matrix n n 𝕜))ᴴ * g) i i) :=
        funext fun g => funext fun i => iwasawaEquiv_symm_A g i
      rw [e]
      exact continuous_pi fun i => RCLike.continuous_re.comp (hR.matrix_elem i i)
    have hu : Continuous fun g : GL n 𝕜 => (iwasawaEquiv.symm g).2.2.1 := by
      have e := funext (iwasawaEquiv_symm_N (n := n) (𝕜 := 𝕜))
      rw [e]
      refine Continuous.mul (Continuous.matrix_diagonal (continuous_pi fun i => ?_)) hR
      refine Continuous.inv₀ (RCLike.continuous_ofReal.comp ((continuous_apply i).comp ha)) ?_
      intro g
      exact_mod_cast ((iwasawaEquiv.symm g).2.1.2 i).ne'
    exact hK.prodMk ((ha.subtype_mk _).prodMk (hu.subtype_mk _))
end Homeomorph3
end GroundTheory.Automorphic


