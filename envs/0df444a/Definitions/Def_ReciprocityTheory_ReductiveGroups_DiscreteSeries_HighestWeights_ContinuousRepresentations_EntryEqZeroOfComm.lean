-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_EntryEqZeroOfComm
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_EntryEqZeroOfComm
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:58:47.157796+00:00
-- url     : https://prove2.me/theorems/55db778b-f520-40c0-8475-f074a2b77a27
-- title:
--   Entry Eq Zero Of Comm
-- statement:
--   Definitions and structural lemmas for Entry Eq Zero Of Comm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/EntryEqZeroOfComm.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Theorems.Thm_Formalism_REAL_isCompactInvariant_compactSpan
import Theorems.Thm_Formalism_REAL_kIrr
import Theorems.Thm_Formalism_REAL_mem_compactSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
namespace PieceCon
variable {n : ℕ}
theorem entry_eq_zero_of_comm {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : Y * Jm ε = Jm ε * Y) {a b : Fin n} (hab : ε a ≠ ε b) : Y a b = 0 := by
  have h := congrFun (congrFun hY a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  cases ha : ε a <;> cases hb : ε b
  · exact absurd (ha.trans hb.symm) hab
  · rw [ha, hb] at h; simp only [Bool.false_eq_true, if_false, if_true] at h
    linear_combination h / 2
  · rw [ha, hb] at h; simp only [Bool.false_eq_true, if_false, if_true] at h
    linear_combination -h / 2
  · exact absurd (ha.trans hb.symm) hab
theorem single_block {ε : Fin n → Bool} {a b : Fin n} (hab : ε a = ε b) :
    ∀ i j, ε i ≠ ε j → Matrix.single a b (1 : ℂ) i j = 0 := by
  intro i j hij
  rw [Matrix.single_apply]
  split_ifs with h
  · exact absurd (h.1 ▸ h.2 ▸ hab) hij
  · rfl
def blockPart (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := Matrix.of fun a b => if ε a = ε b then X a b else 0
  map_add' X Y := by
    ext a b; simp only [Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c X := by
    ext a b; simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp
theorem blockPart_eq {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ a b, ε a ≠ ε b → X a b = 0) : blockPart ε X = X := by
  ext a b
  simp only [blockPart, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  split_ifs with h
  · rfl
  · exact (hX a b h).symm
section Cut
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
def cut (W : Submodule ℂ V) : (V →L[ℂ] V) →L[ℂ] (W →L[ℂ] W) :=
  (ContinuousLinearMap.compL ℂ W V W W.orthogonalProjectionOnto).comp
    ((ContinuousLinearMap.compL ℂ W V V).flip W.subtypeL)
theorem cut_apply (W : Submodule ℂ V) (A : V →L[ℂ] V) (v : W) :
    cut W A v = W.orthogonalProjectionOnto (A v) := rfl
theorem cut_apply_mem (W : Submodule ℂ V) (A : V →L[ℂ] V) (v : W) (h : A v ∈ W) :
    ((cut W A v : W) : V) = A v := by
  rw [cut_apply]
  exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := W) ⟨A v, h⟩)
theorem cut_mul (W : Submodule ℂ V) (A B : V →L[ℂ] V) (hB : ∀ v ∈ W, B v ∈ W) :
    cut W (A * B) = cut W A * cut W B := by
  ext1 v
  show cut W (A * B) v = cut W A (cut W B v)
  rw [cut_apply, cut_apply, cut_apply_mem W B v (hB v v.2)]
  rfl
theorem cut_one (W : Submodule ℂ V) : cut W 1 = 1 := by
  ext1 v
  apply Subtype.ext
  rw [cut_apply_mem W 1 v v.2]
  rfl
end Cut
section Piece
variable {ε : Fin n → Bool} (R : KRep ε)
theorem op_mul (k k' : KG ε) : R.op (k * k') = R.op k * R.op k' := by
  simp [KRep.op, map_mul]
theorem op_one : R.op 1 = 1 := by
  simp [KRep.op, map_one]
theorem op_inv (k : KG ε) : R.op k⁻¹ = star (R.op k) := by
  simp [KRep.op, map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
theorem dτ_mem {W : Submodule ℂ R.V} (hW : Formalism.REAL.KStable ε R.units W)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : ∀ a b, ε a ≠ ε b → X a b = 0) :
    ∀ v ∈ W, R.dτ X v ∈ W := by
  intro v hv
  rw [Matrix.matrix_eq_sum_single X, map_sum, _root_.sum_apply]
  refine W.sum_mem fun a _ => ?_
  rw [map_sum, _root_.sum_apply]
  refine W.sum_mem fun b _ => ?_
  by_cases hab : ε a = ε b
  · have e : Matrix.single a b (X a b) = X a b • Matrix.single a b 1 := by
      ext i j; simp [Matrix.single_apply]
    rw [e, map_smul, _root_.smul_apply]
    exact W.smul_mem _ (hW a b hab v hv)
  · have e : Matrix.single a b (X a b) = 0 := by
      rw [hX a b hab]; ext i j; simp [Matrix.single_apply]
    rw [e, map_zero, _root_.zero_apply]
    exact W.zero_mem
variable {W : Submodule ℂ R.V} (hτ : ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W)
include hτ
theorem star_cut (k : KG ε) : star (cut W (R.op k)) = cut W (R.op k⁻¹) := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  rw [Submodule.coe_inner, Submodule.coe_inner, cut_apply_mem W _ u (hτ _ u u.2),
    cut_apply_mem W _ v (hτ _ v v.2), op_inv, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
theorem cut_mem_unitary (k : KG ε) : cut W (R.op k) ∈ unitary (W →L[ℂ] W) := by
  rw [Unitary.mem_iff, star_cut R hτ, ← cut_mul W _ _ (hτ k), ← cut_mul W _ _ (hτ k⁻¹),
    ← op_mul, ← op_mul, inv_mul_cancel, mul_inv_cancel, op_one, cut_one]
  exact ⟨rfl, rfl⟩
def tauW : KG ε →* unitary (W →L[ℂ] W) where
  toFun k := ⟨cut W (R.op k), cut_mem_unitary R hτ k⟩
  map_one' := Subtype.ext (by simp only [op_one, cut_one]; rfl)
  map_mul' k k' := Subtype.ext (by
    simp only [op_mul]
    exact cut_mul W _ _ (hτ k'))
theorem tauW_coe (k : KG ε) : ((tauW R hτ k : unitary (W →L[ℂ] W)) : W →L[ℂ] W) = cut W (R.op k) :=
  rfl
theorem tauW_cont : Continuous (tauW R hτ) := by
  have h : Continuous fun k : KG ε => cut W (R.op k) :=
    (cut W).continuous.comp (continuous_subtype_val.comp R.cont)
  exact h.subtype_mk _
end Piece
end PieceCon
open PieceCon in

def pieceKType {n : ℕ} {ε : Fin n → Bool} (R : KRep ε)
    (hS : KRepStableStatement) (hR : KRepRelStatement) (μ : Fin n → ℝ) (x : R.V) (hx : x ≠ 0)
    (hhi : Formalism.REAL.KHighest ε R.units μ x) : KType ε μ :=
  let W := Formalism.REAL.kSpan ε R.units x
  have hK : Formalism.REAL.KStable ε R.units W := Formalism.REAL.isCompactInvariant_compactSpan x
  have hτ : ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W := (hS n ε R W).mpr hK
  have hxW : x ∈ W := Formalism.REAL.mem_compactSpan x
  { V := W
    τ := tauW R hτ
    cont := tauW_cont R hτ
    irred := by
      intro W' hW'
      set S : Submodule ℂ R.V := W'.map W.subtype with hSdef
      have hSτ : ∀ k : KG ε, ∀ v ∈ S, R.op k v ∈ S := by
        intro k v hv
        obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
        refine Submodule.mem_map.mpr ⟨(tauW R hτ k : W →L[ℂ] W) u, hW' k u hu, ?_⟩
        rw [tauW_coe]
        exact cut_apply_mem W _ u (hτ k u u.2)
      have hSK : Formalism.REAL.KStable ε R.units S := (hS n ε R S).mp hSτ
      have hle : S ≤ W := Submodule.map_subtype_le W W'
      have hinj := Submodule.map_injective_of_injective W.injective_subtype
      rcases Formalism.REAL.kIrr R.V n ε R.units μ x inferInstance (hR n ε R).1 (hR n ε R).2 hhi S hle hSK
        with h | h
      · left
        apply hinj
        rw [Submodule.map_bot]
        exact h
      · right
        apply hinj
        rw [Submodule.map_subtype_top]
        exact h
    dτ := (cut W).toLinearMap ∘ₗ R.dτ ∘ₗ blockPart ε
    hasDeriv := by
      intro X hX γ hγ
      have hb : blockPart ε X = X := blockPart_eq fun a b h => entry_eq_zero_of_comm hX.2 h
      have hd := ((cut W).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (R.hasDeriv X hX γ hγ)
      show HasDerivAt (fun t => cut W (R.op (γ t))) (cut W (R.dτ (blockPart ε X))) 0
      rw [hb]
      simpa [Function.comp_def] using hd
    w := ⟨((‖x‖⁻¹ : ℝ) : ℂ) • x, W.smul_mem _ hxW⟩
    w_norm := by
      rw [Submodule.coe_norm]
      show ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    w_wt := by
      intro a
      apply Subtype.ext
      have hb : blockPart ε (Matrix.single a a 1) = Matrix.single a a 1 :=
        blockPart_eq (single_block rfl)
      show ((cut W (R.dτ (blockPart ε (Matrix.single a a 1))) _ : W) : R.V) = _
      rw [hb, cut_apply_mem W _ _ (dτ_mem R hK (single_block rfl) _ (W.smul_mem _ hxW))]
      simp only [map_smul, Submodule.coe_smul]
      have h1 : R.dτ (Matrix.single a a 1) x = ((μ a : ℝ) : ℂ) • x := hhi.1 a
      rw [h1, smul_comm]
    w_hw := by
      intro a b hab hε
      apply Subtype.ext
      have hb : blockPart ε (Matrix.single a b 1) = Matrix.single a b 1 :=
        blockPart_eq (single_block hε)
      show ((cut W (R.dτ (blockPart ε (Matrix.single a b 1))) _ : W) : R.V) = _
      rw [hb, cut_apply_mem W _ _ (dτ_mem R hK (single_block hε) _ (W.smul_mem _ hxW))]
      simp only [map_smul, Submodule.coe_zero]
      have h1 : R.dτ (Matrix.single a b 1) x = 0 := hhi.2 a b hab hε
      rw [h1, smul_zero] }
end ReciprocityTheory.ChartRestriction.DS.HW


