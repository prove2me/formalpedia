-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
-- name    : LeanPool_OrderClosures_BanLat_Substructures_Ideal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:26:27.35556+00:00
-- url     : https://prove2.me/theorems/45708429-42a2-4604-8091-e832782af6c9
-- title:
--   Ideal
-- statement:
--   Definitions and structural lemmas for Ideal, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Theorems.Thm_IsVLArchimedean_eq_zero_of_nonneg_of_forall_nsmul_le
public import Theorems.Thm_LLexpr_NormalForm_eval_add
public import Theorems.Thm_LLexpr_NormalForm_eval_inf
public import Theorems.Thm_LLexpr_NormalForm_eval_negate
public import Theorems.Thm_LLexpr_NormalForm_eval_smul
public import Theorems.Thm_LLexpr_NormalForm_eval_sup
public import Theorems.Thm_LLexpr_NormalForm_eval_var
public import Theorems.Thm_LLexpr_NormalForm_eval_zero
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_add
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
public import Theorems.Thm_LLexpr_eval_add
public import Theorems.Thm_LLexpr_eval_inf
public import Theorems.Thm_LLexpr_eval_reindexExpr
public import Theorems.Thm_LLexpr_eval_smul
public import Theorems.Thm_LLexpr_eval_sup
public import Theorems.Thm_LLexpr_eval_var
public import Theorems.Thm_LLexpr_eval_zero
public import Theorems.Thm_LLexpr_normalize_eval
public import Theorems.Thm_NormedVectorLattice_continuous_inf
public import Theorems.Thm_NormedVectorLattice_continuous_sup
public import Theorems.Thm_NormedVectorLattice_lipschitzWith_abs
public import Theorems.Thm_P2M_abs_smul__56c684b926d9
public import Theorems.Thm_VectorSublattice_abs_mem
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_abs_eq_zero_iff_zero
attribute [local simp] LLexpr.NormalForm.eval_add
attribute [local simp] LLexpr.NormalForm.eval_inf
attribute [local simp] LLexpr.NormalForm.eval_negate
attribute [local simp] LLexpr.NormalForm.eval_smul
attribute [local simp] LLexpr.NormalForm.eval_sup
attribute [local simp] LLexpr.NormalForm.eval_var
attribute [local simp] LLexpr.NormalForm.eval_zero
attribute [local simp] LLexpr.SupLinearCombination.eval_add
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
attribute [local simp] LLexpr.SupLinearCombination.eval_smul
attribute [local simp] LLexpr.SupLinearCombination.eval_sup
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.normalize_eval
attribute [local simp] VectorSublattice.coe_toSubmodule
attribute [local simp] VectorSublattice.mem_bot
attribute [local simp] VectorSublattice.mem_top


set_option autoImplicit true
@[expose] public section
@[expose] public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
structure OrderIdeal (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X]
    extends VectorSublattice X where
  solid' : ∀ {x y : X}, x ∈ carrier → 0 ≤ y → y ≤ x → y ∈ carrier
namespace OrderIdeal
instance : SetLike (OrderIdeal X) X where
  coe J := J.carrier
  coe_injective p q h := by
    cases p; cases q; congr
    exact SetLike.ext' h
instance : PartialOrder (OrderIdeal X) := .ofSetLike (OrderIdeal X) X
variable (J : OrderIdeal X)
theorem solid {x y : X} (hx : x ∈ J) (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    y ∈ J :=
  J.solid' hx hy0 hyx
theorem sup_mem {x y : X} (hx : x ∈ J) (hy : y ∈ J) :
    x ⊔ y ∈ J :=
  J.toVectorSublattice.sup_mem hx hy
theorem inf_mem {x y : X} (hx : x ∈ J) (hy : y ∈ J) :
    x ⊓ y ∈ J :=
  J.toVectorSublattice.inf_mem hx hy
theorem abs_mem {x : X} (hx : x ∈ J) : |x| ∈ J :=
  J.toVectorSublattice.abs_mem hx
theorem mem_of_abs_mem {x : X} (h : |x| ∈ J) : x ∈ J := by
  have hpos : x⁺ ∈ J := J.solid h (posPart_nonneg x) (sup_le (le_abs_self x) (abs_nonneg x))
  have hneg : x⁻ ∈ J := J.solid h (negPart_nonneg x) (sup_le (neg_le_abs x) (abs_nonneg x))
  have := J.toSubmodule.sub_mem hpos hneg
  rwa [posPart_sub_negPart] at this
def ofSolid (M : Submodule ℝ X)
    (h : ∀ x y : X, x ∈ M → |y| ≤ |x| → y ∈ M) :
    OrderIdeal X where
  toSubmodule := M
  sup_mem' := fun {x y} hx hy => by
    have hax : |x| ∈ M := h x (|x|) hx (abs_of_nonneg (abs_nonneg x)).le
    have hay : |y| ∈ M := h y (|y|) hy (abs_of_nonneg (abs_nonneg y)).le
    have hab : |x| + |y| ∈ M := M.add_mem hax hay
    apply h (|x| + |y|) (x ⊔ y) hab
    rw [abs_of_nonneg (add_nonneg (abs_nonneg x) (abs_nonneg y))]
    apply sup_le
    · exact sup_le
        (le_trans (le_abs_self x) (le_add_of_nonneg_right (abs_nonneg y)))
        (le_trans (le_abs_self y) (le_add_of_nonneg_left (abs_nonneg x)))
    · calc -(x ⊔ y) = (-x) ⊓ (-y) := neg_sup x y
        _ ≤ -x := inf_le_left
        _ ≤ |x| := neg_le_abs x
        _ ≤ |x| + |y| := le_add_of_nonneg_right (abs_nonneg y)
  solid' := fun {x y} hx hy0 hyx =>
    h x y hx (by rwa [abs_of_nonneg hy0, abs_of_nonneg (le_trans hy0 hyx)])
protected def inf (J₁ J₂ : OrderIdeal X) : OrderIdeal X where
  toSubmodule := J₁.toSubmodule ⊓ J₂.toSubmodule
  sup_mem' := fun hx hy =>
    ⟨J₁.sup_mem hx.1 hy.1, J₂.sup_mem hx.2 hy.2⟩
  solid' := fun hx hy0 hyx =>
    ⟨J₁.solid hx.1 hy0 hyx, J₂.solid hx.2 hy0 hyx⟩
instance : InfSet (OrderIdeal X) where
  sInf S :=
    { toSubmodule := InfSet.sInf ((fun J : OrderIdeal X => J.toSubmodule) '' S)
      sup_mem' := fun {x y} hx hy => by
        have hx' := (Submodule.mem_sInf).mp hx
        have hy' := (Submodule.mem_sInf).mp hy
        refine (Submodule.mem_sInf).mpr ?_
        rintro _ ⟨J, hJ, rfl⟩
        exact J.sup_mem (hx' _ ⟨J, hJ, rfl⟩) (hy' _ ⟨J, hJ, rfl⟩)
      solid' := fun {x y} hx hy0 hyx => by
        have hx' := (Submodule.mem_sInf).mp hx
        refine (Submodule.mem_sInf).mpr ?_
        rintro _ ⟨J, hJ, rfl⟩
        exact J.solid (hx' _ ⟨J, hJ, rfl⟩) hy0 hyx }
@[simp] theorem mem_sInf {S : Set (OrderIdeal X)} {x : X} :
    x ∈ (InfSet.sInf S : OrderIdeal X) ↔ ∀ J ∈ S, x ∈ J := by
  change x ∈ InfSet.sInf ((fun J : OrderIdeal X => J.toSubmodule) '' S) ↔ _
  rw [Submodule.mem_sInf]
  exact ⟨fun h J hJ => h _ ⟨J, hJ, rfl⟩, by rintro h _ ⟨J, hJ, rfl⟩; exact h J hJ⟩
def generated (s : Set X) : OrderIdeal X :=
  InfSet.sInf {J : OrderIdeal X | s ⊆ (J : Set X)}
def generatedAux (s : Set X) : OrderIdeal X :=
  ofSolid
    { carrier := {x : X | ∃ (t : Finset X) (c : X → ℝ),
        (∀ y ∈ t, y ∈ s) ∧ (∀ y ∈ t, 0 ≤ c y) ∧ |x| ≤ ∑ y ∈ t, c y • |y|}
      add_mem' := by
        classical
        rintro x x' ⟨t, c, hts, hc, hxle⟩ ⟨t', c', ht's, hc', hx'le⟩
        refine ⟨t ∪ t',
          fun y => (if y ∈ t then c y else 0) + (if y ∈ t' then c' y else 0),
          ?_, ?_, ?_⟩
        · intro y hy
          rcases Finset.mem_union.mp hy with h | h
          · exact hts y h
          · exact ht's y h
        · intro y _
          refine add_nonneg ?_ ?_
          · split_ifs with h
            · exact hc y h
            · exact le_rfl
          · split_ifs with h
            · exact hc' y h
            · exact le_rfl
        · have h1 : ∑ y ∈ t, c y • |y| =
              ∑ y ∈ t ∪ t', (if y ∈ t then c y else 0) • |y| := by
            rw [show ∑ y ∈ t, c y • |y| =
                ∑ y ∈ t, (if y ∈ t then c y else 0) • |y| from
              Finset.sum_congr rfl (fun y hy => by rw [if_pos hy])]
            exact Finset.sum_subset Finset.subset_union_left
              (fun y _ hy => by rw [if_neg hy, zero_smul])
          have h2 : ∑ y ∈ t', c' y • |y| =
              ∑ y ∈ t ∪ t', (if y ∈ t' then c' y else 0) • |y| := by
            rw [show ∑ y ∈ t', c' y • |y| =
                ∑ y ∈ t', (if y ∈ t' then c' y else 0) • |y| from
              Finset.sum_congr rfl (fun y hy => by rw [if_pos hy])]
            exact Finset.sum_subset Finset.subset_union_right
              (fun y _ hy => by rw [if_neg hy, zero_smul])
          calc |x + x'|
              ≤ |x| + |x'| := abs_add_le _ _
            _ ≤ (∑ y ∈ t, c y • |y|) + (∑ y ∈ t', c' y • |y|) :=
                add_le_add hxle hx'le
            _ = (∑ y ∈ t ∪ t', (if y ∈ t then c y else 0) • |y|) +
                (∑ y ∈ t ∪ t', (if y ∈ t' then c' y else 0) • |y|) := by
                rw [h1, h2]
            _ = ∑ y ∈ t ∪ t', ((if y ∈ t then c y else 0) +
                  (if y ∈ t' then c' y else 0)) • |y| := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun y _ => ?_
                rw [add_smul]
      zero_mem' := ⟨∅, fun _ => 0, by simp, by simp, by simp⟩
      smul_mem' := by
        rintro r x ⟨t, c, hts, hc, hxle⟩
        refine ⟨t, fun y => |r| * c y, hts,
          fun y hy => mul_nonneg (abs_nonneg _) (hc y hy), ?_⟩
        rw [abs_smul']
        calc |r| • |x|
            ≤ |r| • ∑ y ∈ t, c y • |y| :=
              smul_le_smul_of_nonneg_left hxle (abs_nonneg _)
          _ = ∑ y ∈ t, (|r| * c y) • |y| := by
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [smul_smul] }
    (fun x y ⟨t, c, hts, hc, hxle⟩ hyx_abs =>
      ⟨t, c, hts, hc, le_trans hyx_abs hxle⟩)
def principal (a : X) : OrderIdeal X where
  toSubmodule :=
    { carrier := {x : X | ∃ c : ℝ, 0 ≤ c ∧ |x| ≤ c • |a|}
      add_mem' := fun {x y} ⟨cx, hcx, hx⟩ ⟨cy, hcy, hy⟩ =>
        ⟨cx + cy, add_nonneg hcx hcy, by
          calc |x + y| ≤ |x| + |y| := abs_add_le x y
            _ ≤ cx • |a| + cy • |a| := add_le_add hx hy
            _ = (cx + cy) • |a| := (add_smul cx cy |a|).symm⟩
      zero_mem' := ⟨0, le_rfl, by simp⟩
      smul_mem' := fun r x ⟨c, hc, hx⟩ =>
        ⟨|r| * c, mul_nonneg (abs_nonneg r) hc, by
          rw [abs_smul' x r]
          calc |r| • |x| ≤ |r| • (c • |a|) :=
                smul_le_smul_of_nonneg_left hx (abs_nonneg r)
            _ = (|r| * c) • |a| := smul_smul |r| c |a|⟩ }
  sup_mem' := fun {x y} ⟨cx, hcx, hx⟩ ⟨cy, hcy, hy⟩ =>
    ⟨cx + cy, add_nonneg hcx hcy, by
      have : |x ⊔ y| ≤ |x| + |y| := by
        apply sup_le
        · exact sup_le
            (le_trans (le_abs_self x) (le_add_of_nonneg_right (abs_nonneg y)))
            (le_trans (le_abs_self y) (le_add_of_nonneg_left (abs_nonneg x)))
        · calc -(x ⊔ y) = (-x) ⊓ (-y) := neg_sup x y
            _ ≤ -x := inf_le_left
            _ ≤ |x| := neg_le_abs x
            _ ≤ |x| + |y| := le_add_of_nonneg_right (abs_nonneg y)
      calc |x ⊔ y| ≤ |x| + |y| := this
        _ ≤ cx • |a| + cy • |a| := add_le_add hx hy
        _ = (cx + cy) • |a| := (add_smul cx cy |a|).symm⟩
  solid' := fun {x y} ⟨c, hc, hx⟩ hy0 hyx =>
    ⟨c, hc, le_trans (by rw [abs_of_nonneg hy0]; exact le_trans hyx (le_abs_self x)) hx⟩
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
noncomputable def gaugeNorm (a x : X) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ |x| ≤ c • |a|}
variable (a : X)
theorem gaugeNorm_nonneg (x : X) : 0 ≤ gaugeNorm a x := by
  unfold gaugeNorm
  by_cases h : {c : ℝ | 0 ≤ c ∧ |x| ≤ c • |a|}.Nonempty
  · exact le_csInf h fun _ ⟨hc, _⟩ => hc
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]
theorem gaugeNorm_zero : gaugeNorm a 0 = 0 := by
  apply le_antisymm
  · exact csInf_le ⟨0, fun _ ⟨hd, _⟩ => hd⟩ ⟨le_rfl, by simp⟩
  · exact gaugeNorm_nonneg a 0
theorem gaugeNorm_bddBelow (x : X) :
    BddBelow {c : ℝ | 0 ≤ c ∧ |x| ≤ c • |a|} :=
  ⟨0, fun _ ⟨hc, _⟩ => hc⟩
theorem gaugeNorm_add_le {x y : X} (hx : x ∈ principal a) (hy : y ∈ principal a) :
    gaugeNorm a (x + y) ≤ gaugeNorm a x + gaugeNorm a y := by
  -- Bound `gaugeNorm a (x + y) - cy` for each admissible bound `cy` of `y`.
  have step1 : ∀ cy, cy ∈ {c : ℝ | 0 ≤ c ∧ |y| ≤ c • |a|} →
      gaugeNorm a (x + y) - cy ≤ gaugeNorm a x := by
    intro cy ⟨hcy, hcy_le⟩
    apply le_csInf hx
    intro cx ⟨hcx, hcx_le⟩
    have : cx + cy ∈ {c : ℝ | 0 ≤ c ∧ |x + y| ≤ c • |a|} :=
      ⟨add_nonneg hcx hcy, le_trans (abs_add_le x y)
        (by rw [add_smul]; exact add_le_add hcx_le hcy_le)⟩
    exact sub_le_iff_le_add.mpr (csInf_le (gaugeNorm_bddBelow a (x + y)) this)
  -- Then take the infimum over admissible bounds of `y`.
  have step2 : gaugeNorm a (x + y) - gaugeNorm a x ≤ gaugeNorm a y :=
    le_csInf hy (fun cy hcy => by linarith [step1 cy hcy])
  linarith
theorem gaugeNorm_div_mem {r : ℝ} (hr_pos : 0 < |r|) {x : X} {c : ℝ}
    (hc : 0 ≤ c) (hle : |r| • |x| ≤ c • |a|) :
    c / |r| ∈ {c : ℝ | 0 ≤ c ∧ |x| ≤ c • |a|} := by
  refine ⟨div_nonneg hc hr_pos.le, ?_⟩
  have := smul_le_smul_of_nonneg_left hle (inv_nonneg.mpr hr_pos.le)
  rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hr_pos), one_smul, smul_smul] at this
  rwa [div_eq_inv_mul]
theorem gaugeNorm_smul (r : ℝ) (x : X) :
    gaugeNorm a (r • x) = |r| * gaugeNorm a x := by
  by_cases hr : r = 0
  · simp [hr, gaugeNorm_zero]
  · have hr_pos : (0 : ℝ) < |r| := abs_pos.mpr hr
    -- S_x nonempty ↔ S_{rx} nonempty (when r ≠ 0)
    by_cases hne : {c : ℝ | 0 ≤ c ∧ |x| ≤ c • |a|}.Nonempty
    · apply le_antisymm
      · -- ≤: gaugeNorm(rx)/|r| ≤ gaugeNorm(x), then multiply
        suffices h : gaugeNorm a (r • x) / |r| ≤ gaugeNorm a x from
          (div_le_iff₀ hr_pos).mp h |>.trans (le_of_eq (mul_comm _ _))
        apply le_csInf hne
        intro d ⟨hd, hle⟩
        rw [div_le_iff₀ hr_pos]
        exact (csInf_le (gaugeNorm_bddBelow a (r • x))
          ⟨mul_nonneg hr_pos.le hd, by
            rw [abs_smul' x r, mul_smul]
            exact smul_le_smul_of_nonneg_left hle hr_pos.le⟩).trans (le_of_eq (mul_comm _ _))
      · -- ≥: for any c in S_{rx}, c/|r| ∈ S_x, so gaugeNorm(x) ≤ c/|r|
        obtain ⟨d, hd, hle⟩ := hne
        have hne_rx : {c : ℝ | 0 ≤ c ∧ |r • x| ≤ c • |a|}.Nonempty :=
          ⟨|r| * d, mul_nonneg hr_pos.le hd, by
            rw [abs_smul' x r, mul_smul]
            exact smul_le_smul_of_nonneg_left hle hr_pos.le⟩
        apply le_csInf hne_rx
        intro c ⟨hc, hle'⟩
        calc |r| * gaugeNorm a x
            ≤ |r| * (c / |r|) :=
              mul_le_mul_of_nonneg_left
                (csInf_le (gaugeNorm_bddBelow a x) (gaugeNorm_div_mem a hr_pos hc
                  (by rwa [abs_smul' x r] at hle'))) hr_pos.le
          _ = c := by field_simp
    · -- Both S_x and S_{rx} empty: both sides are 0
      have hne2 : ¬{c : ℝ | 0 ≤ c ∧ |r • x| ≤ c • |a|}.Nonempty := by
        intro ⟨c, hc, hle⟩
        exact hne ⟨c / |r|, gaugeNorm_div_mem a hr_pos hc
          (by rwa [abs_smul' x r] at hle)⟩
      simp only [gaugeNorm, Set.not_nonempty_iff_eq_empty.mp hne,
        Set.not_nonempty_iff_eq_empty.mp hne2, Real.sInf_empty, mul_zero]
theorem abs_le_gaugeNorm_smul_abs [IsVLArchimedean X] {x : X}
    (hx : x ∈ principal a) : |x| ≤ gaugeNorm a x • |a| := by
  suffices h : (|x| - gaugeNorm a x • |a|)⁺ = 0 by
    have := le_posPart (|x| - gaugeNorm a x • |a|)
    rw [h] at this; exact sub_nonpos.mp this
  apply IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le (y := |a|) (posPart_nonneg _)
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · have hne : {c : ℝ | 0 ≤ c ∧ |x| ≤ c • |a|}.Nonempty := hx
    have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hlt : gaugeNorm a x < gaugeNorm a x + 1 / ↑n :=
      lt_add_of_pos_right _ (div_pos one_pos hn_pos)
    obtain ⟨c, ⟨_, hcle⟩, hc_lt⟩ := exists_lt_of_csInf_lt hne hlt
    have hstep : |x| - gaugeNorm a x • |a| ≤ (1 / (↑n : ℝ)) • |a| := by
      calc |x| - gaugeNorm a x • |a|
          ≤ c • |a| - gaugeNorm a x • |a| := sub_le_sub_right hcle _
        _ = (c - gaugeNorm a x) • |a| := (sub_smul c (gaugeNorm a x) |a|).symm
        _ ≤ (1 / ↑n) • |a| :=
            smul_le_smul_of_nonneg_right (by linarith) (abs_nonneg a)
    have hpos_le : (|x| - gaugeNorm a x • |a|)⁺ ≤ (1 / (↑n : ℝ)) • |a| :=
      sup_le hstep (smul_nonneg (div_nonneg one_pos.le hn_pos.le) (abs_nonneg a))
    calc n • (|x| - gaugeNorm a x • |a|)⁺
        ≤ n • ((1 / (↑n : ℝ)) • |a|) :=
          nsmul_le_nsmul hpos_le (smul_nonneg (div_nonneg one_pos.le hn_pos.le)
            (abs_nonneg a)) le_rfl
      _ = ((↑n : ℝ) * (1 / ↑n)) • |a| := by
          rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      _ = |a| := by rw [mul_one_div_cancel (ne_of_gt hn_pos), one_smul]
theorem gaugeNorm_mono_abs {x y : X} (hy : y ∈ principal a) (h : |x| ≤ |y|) :
    gaugeNorm a x ≤ gaugeNorm a y := by
  -- S_y ⊆ S_x, so sInf S_x ≤ sInf S_y
  apply le_csInf hy
  intro c ⟨hc, hle⟩
  exact csInf_le (gaugeNorm_bddBelow a x) ⟨hc, le_trans h hle⟩
theorem gaugeNorm_eq_zero_iff [IsVLArchimedean X] {x : X}
    (hx : x ∈ principal a) : gaugeNorm a x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have := abs_le_gaugeNorm_smul_abs a hx
    rw [h, zero_smul] at this
    exact (abs_eq_zero_iff_zero x).mp (le_antisymm this (abs_nonneg x))
  · intro h; rw [h]; exact gaugeNorm_zero a
abbrev principalSubmodule (a : X) : Submodule ℝ X :=
  (principal a).toSubmodule
noncomputable instance instNormPrincipal (a : X) :
    Norm ↥(principalSubmodule a) where
  norm x := gaugeNorm a x.1
noncomputable instance instLatticePrincipal (a : X) :
    Lattice ↥(principalSubmodule a) where
  sup x y := ⟨x.1 ⊔ y.1, (principal a).sup_mem x.2 y.2⟩
  inf x y := ⟨x.1 ⊓ y.1, (principal a).inf_mem x.2 y.2⟩
  le_sup_left := fun x y => show x.1 ≤ x.1 ⊔ y.1 from le_sup_left
  le_sup_right := fun x y => show y.1 ≤ x.1 ⊔ y.1 from le_sup_right
  sup_le := fun x y z h1 h2 => show x.1 ⊔ y.1 ≤ z.1 from sup_le h1 h2
  inf_le_left := fun x y => show x.1 ⊓ y.1 ≤ x.1 from inf_le_left
  inf_le_right := fun x y => show x.1 ⊓ y.1 ≤ y.1 from inf_le_right
  le_inf := fun x y z h1 h2 => show x.1 ≤ y.1 ⊓ z.1 from le_inf h1 h2
instance instIsOrderedAddMonoidPrincipal (a : X) :
    @IsOrderedAddMonoid ↥(principalSubmodule a)
      inferInstance (instLatticePrincipal a).toPartialOrder.toPreorder where
  add_le_add_left := fun x y (h : x.1 ≤ y.1) z =>
    show x.1 + z.1 ≤ y.1 + z.1 from add_le_add_left h _
@[reducible]
noncomputable def principalNormedAddCommGroup [IsVLArchimedean X]
    (a : X) :
    NormedAddCommGroup ↥(principalSubmodule a) :=
  NormedAddCommGroup.ofCore (𝕜 := ℝ) {
    toCore := {
      norm_nonneg := fun x => gaugeNorm_nonneg a x.1
      norm_smul := fun r x => gaugeNorm_smul a r x.1
      norm_triangle := fun x y => gaugeNorm_add_le a x.2 y.2
    }
    norm_eq_zero_iff := fun x => (gaugeNorm_eq_zero_iff a x.2).trans
      ⟨fun h => Subtype.ext h, fun h => congr_arg Subtype.val h⟩
  }
@[reducible]
noncomputable def principalVectorLattice (a : X) :
    @VectorLattice ↥(principalSubmodule a) inferInstance
      (instLatticePrincipal a)
      (instIsOrderedAddMonoidPrincipal a) where
  toModule := (principalSubmodule a).module
  smul_le_smul_of_nonneg_left := by
    intro c hc x y hxy
    change c • x.1 ≤ c • y.1
    exact smul_le_smul_of_nonneg_left hxy hc
@[reducible]
noncomputable def principalNormedVectorLattice [IsVLArchimedean X]
    (a : X) :
    @NormedVectorLattice ↥(principalSubmodule a)
      (principalNormedAddCommGroup a)
      (instLatticePrincipal a)
      (instIsOrderedAddMonoidPrincipal a) := by
  letI : NormedAddCommGroup ↥(principalSubmodule a) := principalNormedAddCommGroup a
  letI : Lattice ↥(principalSubmodule a) := instLatticePrincipal a
  letI : IsOrderedAddMonoid ↥(principalSubmodule a) := instIsOrderedAddMonoidPrincipal a
  letI : VectorLattice ↥(principalSubmodule a) := principalVectorLattice a
  let solidNorm : HasSolidNorm ↥(principalSubmodule a) := {
    solid := by
      intro x y h
      change gaugeNorm a x.1 ≤ gaugeNorm a y.1
      exact gaugeNorm_mono_abs a y.2 h
  }
  let normSmul : NormSMulClass ℝ ↥(principalSubmodule a) := {
    norm_smul := by
      intro r x
      change gaugeNorm a (r • x.1) = ‖r‖ * gaugeNorm a x.1
      rw [gaugeNorm_smul a r x.1, Real.norm_eq_abs]
  }
  exact @NormedVectorLattice.mk ↥(principalSubmodule a)
    (principalNormedAddCommGroup a)
    (instLatticePrincipal a)
    (instIsOrderedAddMonoidPrincipal a)
    (principalVectorLattice a)
    solidNorm
    normSmul
theorem sum_pos_mem (J₁ J₂ : OrderIdeal X) {v u₁ u₂ : X}
    (hu₁ : u₁ ∈ J₁) (hu₂ : u₂ ∈ J₂) (hu₁0 : 0 ≤ u₁) (hu₂0 : 0 ≤ u₂)
    (hv0 : 0 ≤ v) (hvle : v ≤ u₁ + u₂) :
    v ∈ J₁.toSubmodule + J₂.toSubmodule := by
  have hv₁ : v ⊓ u₁ ∈ J₁ := J₁.solid hu₁ (le_inf hv0 hu₁0) inf_le_right
  have heq : v - v ⊓ u₁ = (v - u₁)⁺ := by
    rw [inf_eq_sub_posPart_sub]; abel
  have hv₂ : v - v ⊓ u₁ ∈ J₂ := by
    rw [heq]
    exact J₂.solid hu₂ (posPart_nonneg _)
      (sup_le (sub_le_iff_le_add'.mpr hvle) hu₂0)
  refine Submodule.mem_sup.mpr ⟨v ⊓ u₁, hv₁, v - v ⊓ u₁, hv₂, ?_⟩
  abel
def sum (J₁ J₂ : OrderIdeal X) : OrderIdeal X :=
  ofSolid (J₁.toSubmodule + J₂.toSubmodule) <| by
    intro x y hx hyx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
    -- `|y| ≤ |x₁| + |x₂|`; split `y⁺` and `y⁻` separately using `sum_pos_mem`.
    have habs : |y| ≤ |x₁| + |x₂| := le_trans hyx (abs_add_le x₁ x₂)
    have h_pos_le : y⁺ ≤ |x₁| + |x₂| :=
      le_trans (sup_le (le_abs_self y) (abs_nonneg y)) habs
    have h_neg_le : y⁻ ≤ |x₁| + |x₂| :=
      le_trans (sup_le (neg_le_abs y) (abs_nonneg y)) habs
    have hpos : y⁺ ∈ J₁.toSubmodule + J₂.toSubmodule :=
      sum_pos_mem J₁ J₂ (J₁.abs_mem hx₁) (J₂.abs_mem hx₂)
        (abs_nonneg _) (abs_nonneg _) (posPart_nonneg _) h_pos_le
    have hneg : y⁻ ∈ J₁.toSubmodule + J₂.toSubmodule :=
      sum_pos_mem J₁ J₂ (J₁.abs_mem hx₁) (J₂.abs_mem hx₂)
        (abs_nonneg _) (abs_nonneg _) (negPart_nonneg _) h_neg_le
    have := (J₁.toSubmodule + J₂.toSubmodule).sub_mem hpos hneg
    rwa [posPart_sub_negPart] at this
@[simp]
theorem sum_toSubmodule (J₁ J₂ : OrderIdeal X) :
    (sum J₁ J₂).toSubmodule = J₁.toSubmodule + J₂.toSubmodule := rfl
theorem exists_sum_decomp (J₁ J₂ : OrderIdeal X) {z : X}
    (hz : z ∈ J₁.toSubmodule + J₂.toSubmodule) :
    ∃ a b : X, a ∈ J₁ ∧ b ∈ J₂ ∧ a + b = z ∧ |a| ≤ |z| ∧ |b| ≤ |z| := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hz
  have habs : |u₁ + u₂| ≤ |u₁| + |u₂| := abs_add_le u₁ u₂
  -- Positive part split
  have hxp_le : (u₁ + u₂)⁺ ≤ |u₁| + |u₂| :=
    le_trans (sup_le (le_abs_self _) (abs_nonneg _)) habs
  let ap := (u₁ + u₂)⁺ ⊓ |u₁|
  have hap_nn : 0 ≤ ap := le_inf (posPart_nonneg _) (abs_nonneg _)
  have hap_le_xp : ap ≤ (u₁ + u₂)⁺ := inf_le_left
  have hap_mem : ap ∈ J₁ := J₁.solid (J₁.abs_mem hu₁) hap_nn inf_le_right
  let bp := (u₁ + u₂)⁺ - ap
  have hbp_eq : bp = ((u₁ + u₂)⁺ - |u₁|)⁺ := by
    change (u₁ + u₂)⁺ - (u₁ + u₂)⁺ ⊓ |u₁| = ((u₁ + u₂)⁺ - |u₁|)⁺
    rw [inf_eq_sub_posPart_sub]; abel
  have hbp_nn : 0 ≤ bp := by rw [hbp_eq]; exact posPart_nonneg _
  have hbp_le_xp : bp ≤ (u₁ + u₂)⁺ := sub_le_self _ hap_nn
  have hbp_mem : bp ∈ J₂ := by
    rw [hbp_eq]
    exact J₂.solid (J₂.abs_mem hu₂) (posPart_nonneg _)
      (sup_le (sub_le_iff_le_add'.mpr hxp_le) (abs_nonneg _))
  have hab_p_sum : ap + bp = (u₁ + u₂)⁺ := by
    change ap + ((u₁ + u₂)⁺ - ap) = _
    abel
  -- Negative part split
  have hxn_le : (u₁ + u₂)⁻ ≤ |u₁| + |u₂| :=
    le_trans (sup_le (neg_le_abs _) (abs_nonneg _)) habs
  let an := (u₁ + u₂)⁻ ⊓ |u₁|
  have han_nn : 0 ≤ an := le_inf (negPart_nonneg _) (abs_nonneg _)
  have han_le_xn : an ≤ (u₁ + u₂)⁻ := inf_le_left
  have han_mem : an ∈ J₁ := J₁.solid (J₁.abs_mem hu₁) han_nn inf_le_right
  let bn := (u₁ + u₂)⁻ - an
  have hbn_eq : bn = ((u₁ + u₂)⁻ - |u₁|)⁺ := by
    change (u₁ + u₂)⁻ - (u₁ + u₂)⁻ ⊓ |u₁| = ((u₁ + u₂)⁻ - |u₁|)⁺
    rw [inf_eq_sub_posPart_sub]; abel
  have hbn_nn : 0 ≤ bn := by rw [hbn_eq]; exact posPart_nonneg _
  have hbn_le_xn : bn ≤ (u₁ + u₂)⁻ := sub_le_self _ han_nn
  have hbn_mem : bn ∈ J₂ := by
    rw [hbn_eq]
    exact J₂.solid (J₂.abs_mem hu₂) (posPart_nonneg _)
      (sup_le (sub_le_iff_le_add'.mpr hxn_le) (abs_nonneg _))
  have hab_n_sum : an + bn = (u₁ + u₂)⁻ := by
    change an + ((u₁ + u₂)⁻ - an) = _
    abel
  -- Assemble
  refine ⟨ap - an, bp - bn,
    J₁.toSubmodule.sub_mem hap_mem han_mem,
    J₂.toSubmodule.sub_mem hbp_mem hbn_mem, ?_, ?_, ?_⟩
  · calc ap - an + (bp - bn)
        = (ap + bp) - (an + bn) := by abel
      _ = (u₁ + u₂)⁺ - (u₁ + u₂)⁻ := by rw [hab_p_sum, hab_n_sum]
      _ = u₁ + u₂ := posPart_sub_negPart _
  · calc |ap - an|
        = |ap + (-an)| := by rw [sub_eq_add_neg]
      _ ≤ |ap| + |(-an)| := abs_add_le _ _
      _ = ap + an := by rw [abs_of_nonneg hap_nn, abs_neg, abs_of_nonneg han_nn]
      _ ≤ (u₁ + u₂)⁺ + (u₁ + u₂)⁻ := add_le_add hap_le_xp han_le_xn
      _ = |u₁ + u₂| := posPart_add_negPart _
  · calc |bp - bn|
        = |bp + (-bn)| := by rw [sub_eq_add_neg]
      _ ≤ |bp| + |(-bn)| := abs_add_le _ _
      _ = bp + bn := by rw [abs_of_nonneg hbp_nn, abs_neg, abs_of_nonneg hbn_nn]
      _ ≤ (u₁ + u₂)⁺ + (u₁ + u₂)⁻ := add_le_add hbp_le_xp hbn_le_xn
      _ = |u₁ + u₂| := posPart_add_negPart _
instance : Top (OrderIdeal X) where
  top :=
    { toSubmodule := ⊤
      sup_mem' := fun _ _ => Submodule.mem_top
      solid' := fun _ _ _ => Submodule.mem_top }
@[simp] theorem mem_top {x : X} : x ∈ (⊤ : OrderIdeal X) := Submodule.mem_top
instance : Bot (OrderIdeal X) where
  bot :=
    { toSubmodule := ⊥
      sup_mem' := fun {x y} hx hy => by
        have hx' : x = 0 := (Submodule.mem_bot ℝ).mp hx
        have hy' : y = 0 := (Submodule.mem_bot ℝ).mp hy
        rw [hx', hy', sup_idem]; exact Submodule.zero_mem _
      solid' := fun {x y} hx hy0 hyx => by
        have hx' : x = 0 := (Submodule.mem_bot ℝ).mp hx
        rw [hx'] at hyx
        exact (Submodule.mem_bot ℝ).mpr (le_antisymm hyx hy0) }
@[simp] theorem mem_bot {x : X} : x ∈ (⊥ : OrderIdeal X) ↔ x = 0 :=
  Submodule.mem_bot ℝ
instance : CompleteLattice (OrderIdeal X) where
  __ := (inferInstance : PartialOrder (OrderIdeal X))
  sup := sum
  inf := OrderIdeal.inf
  top := ⊤
  bot := ⊥
  sInf := sInf
  sSup S := sInf {K : OrderIdeal X | ∀ I ∈ S, I ≤ K}
  le_top := fun _ _ _ => Submodule.mem_top
  bot_le := fun J x hx => by
    have hx' : x ∈ (⊥ : Submodule ℝ X) := hx
    have : x = 0 := (Submodule.mem_bot ℝ).mp hx'
    exact this ▸ J.toSubmodule.zero_mem
  le_sup_left := fun J₁ J₂ x hx =>
    Submodule.mem_sup.mpr ⟨x, hx, 0, J₂.toSubmodule.zero_mem, add_zero x⟩
  le_sup_right := fun J₁ J₂ x hx =>
    Submodule.mem_sup.mpr ⟨0, J₁.toSubmodule.zero_mem, x, hx, zero_add x⟩
  sup_le := fun J₁ J₂ K hJ₁ hJ₂ x hx => by
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
    exact K.toSubmodule.add_mem (hJ₁ hx₁) (hJ₂ hx₂)
  inf_le_left := fun _ _ _ hx => hx.1
  inf_le_right := fun _ _ _ hx => hx.2
  le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩
  isLUB_sSup := fun S => by
    refine ⟨?_, ?_⟩
    · intro J hJ x hx
      rw [mem_sInf]
      intro K hK
      exact hK J hJ hx
    · intro J hJ x hx
      rw [mem_sInf] at hx
      exact hx J hJ
  isGLB_sInf := fun S => by
    refine ⟨?_, ?_⟩
    · intro J hJ x hx
      rw [mem_sInf] at hx
      exact hx J hJ
    · intro J hJ x hx
      rw [mem_sInf]
      intro K hK
      exact hJ hK hx
@[simp] theorem sup_toSubmodule (J₁ J₂ : OrderIdeal X) :
    (J₁ ⊔ J₂).toSubmodule = J₁.toSubmodule + J₂.toSubmodule := rfl
@[simp] theorem inf_toSubmodule (J₁ J₂ : OrderIdeal X) :
    (J₁ ⊓ J₂).toSubmodule = J₁.toSubmodule ⊓ J₂.toSubmodule := rfl
section Closure
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]
theorem topologicalClosure_solid (J : OrderIdeal X) :
    ∀ x y : X, x ∈ J.toSubmodule.topologicalClosure → |y| ≤ |x| →
      y ∈ J.toSubmodule.topologicalClosure := by
  intro x y hx hy_abs
  have hx' : x ∈ closure (J.toSubmodule : Set X) := by
    rwa [← Submodule.topologicalClosure_coe]
  obtain ⟨xn, hxn_mem, hxn_lim⟩ := mem_closure_iff_seq_limit.mp hx'
  -- Truncated sequence yₙ = (y ⊔ -|xₙ|) ⊓ |xₙ|, which lies in J and converges to y.
  set yn : ℕ → X := fun n => (y ⊔ (-|xn n|)) ⊓ |xn n| with hyn_def
  have habs_nn : ∀ n, (0 : X) ≤ |xn n| := fun _ => abs_nonneg _
  have hyn_mem : ∀ n, yn n ∈ J.toSubmodule := by
    intro n
    have habs_mem : |xn n| ∈ J := J.abs_mem (hxn_mem n)
    have h_le : yn n ≤ |xn n| := inf_le_right
    have h_neg_le : -|xn n| ≤ |xn n| :=
      le_trans (neg_nonpos_of_nonneg (habs_nn n)) (habs_nn n)
    have h_ge : -|xn n| ≤ yn n := le_inf le_sup_right h_neg_le
    have h_abs_yn : |yn n| ≤ |xn n| := by
      rw [abs_le']; exact ⟨h_le, by rwa [neg_le]⟩
    have : |yn n| ∈ J := J.solid habs_mem (abs_nonneg _) h_abs_yn
    exact J.mem_of_abs_mem this
  -- Continuity of `|·|`, `⊔`, `⊓` makes `yn → y`.
  have hcont_abs : Continuous (|·| : X → X) :=
    NormedVectorLattice.lipschitzWith_abs.continuous
  have habs_tendsto : Filter.Tendsto (fun n => |xn n|) Filter.atTop (nhds |x|) :=
    (hcont_abs.tendsto _).comp hxn_lim
  have hneg_tendsto : Filter.Tendsto (fun n => -|xn n|) Filter.atTop (nhds (-|x|)) :=
    habs_tendsto.neg
  have hsup_tendsto :
      Filter.Tendsto (fun n => y ⊔ (-|xn n|)) Filter.atTop (nhds (y ⊔ (-|x|))) :=
    (NormedVectorLattice.continuous_sup.tendsto _).comp
      (tendsto_const_nhds.prodMk_nhds hneg_tendsto)
  have hyn_tendsto :
      Filter.Tendsto yn Filter.atTop (nhds ((y ⊔ (-|x|)) ⊓ |x|)) :=
    (NormedVectorLattice.continuous_inf.tendsto _).comp
      (hsup_tendsto.prodMk_nhds habs_tendsto)
  have h_le_abs : y ≤ |x| := le_trans (le_abs_self y) hy_abs
  have h_neg_le : -|x| ≤ y := by rw [neg_le]; exact le_trans (neg_le_abs y) hy_abs
  have hy_eq : (y ⊔ (-|x|)) ⊓ |x| = y := by
    rw [sup_eq_left.mpr h_neg_le, inf_eq_left.mpr h_le_abs]
  rw [hy_eq] at hyn_tendsto
  have hy_in_closure : y ∈ closure (J.toSubmodule : Set X) :=
    mem_closure_of_tendsto hyn_tendsto (Filter.Eventually.of_forall hyn_mem)
  rwa [← Submodule.topologicalClosure_coe] at hy_in_closure
def topologicalClosure (J : OrderIdeal X) : OrderIdeal X :=
  ofSolid J.toSubmodule.topologicalClosure (topologicalClosure_solid J)
@[simp]
theorem topologicalClosure_toSubmodule (J : OrderIdeal X) :
    (topologicalClosure J).toSubmodule = J.toSubmodule.topologicalClosure := rfl
end Closure
end OrderIdeal
structure ClosedOrderIdeal (X : Type*) [NormedAddCommGroup X]
    [Lattice X] [IsOrderedAddMonoid X] [BanachLattice X]
    extends OrderIdeal X where
  isClosed' : IsClosed (toOrderIdeal : Set X)
namespace ClosedOrderIdeal
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]
instance : SetLike (ClosedOrderIdeal X) X where
  coe J := J.toOrderIdeal
  coe_injective p q h := by
    cases p; cases q; congr
    exact SetLike.coe_injective h
theorem isClosed (J : ClosedOrderIdeal X) : IsClosed (J : Set X) :=
  J.isClosed'
instance : PartialOrder (ClosedOrderIdeal X) :=
  .ofSetLike (ClosedOrderIdeal X) X
def inf (J₁ J₂ : ClosedOrderIdeal X) : ClosedOrderIdeal X where
  toOrderIdeal := J₁.toOrderIdeal ⊓ J₂.toOrderIdeal
  isClosed' := J₁.isClosed.inter J₂.isClosed
theorem exists_sum_decomp_norm (J₁ J₂ : OrderIdeal X) {z : X}
    (hz : z ∈ J₁.toSubmodule + J₂.toSubmodule) :
    ∃ a b : X, a ∈ J₁ ∧ b ∈ J₂ ∧ a + b = z ∧ ‖a‖ ≤ ‖z‖ ∧ ‖b‖ ≤ ‖z‖ := by
  obtain ⟨a, b, ha, hb, hsum, habs_a, habs_b⟩ := OrderIdeal.exists_sum_decomp J₁ J₂ hz
  refine ⟨a, b, ha, hb, hsum, ?_, ?_⟩
  · rw [← norm_abs_eq_norm z]; exact norm_le_norm_of_abs_le_abs (by rwa [abs_abs])
  · rw [← norm_abs_eq_norm z]; exact norm_le_norm_of_abs_le_abs (by rwa [abs_abs])
theorem isClosed_sum {J₁ J₂ : OrderIdeal X}
    (h₁ : IsClosed (J₁ : Set X)) (h₂ : IsClosed (J₂ : Set X)) :
    IsClosed ((OrderIdeal.sum J₁ J₂ : OrderIdeal X) : Set X) := by
  rw [← isSeqClosed_iff_isClosed]
  intro z_seq z hz_mem hz_lim
  -- Extract a subsequence whose consecutive distances are summable.
  have hCauchy : CauchySeq z_seq := hz_lim.cauchySeq
  obtain ⟨φ, hφ_mono, hφ_sum⟩ :=
    Metric.exists_subseq_summable_dist_of_cauchySeq z_seq hCauchy
  -- The subsequence still converges to z.
  have hsub_lim : Filter.Tendsto (z_seq ∘ φ) Filter.atTop (nhds z) :=
    hz_lim.comp hφ_mono.tendsto_atTop
  -- Differences along the subsequence.
  set w : ℕ → X := fun k => z_seq (φ (k + 1)) - z_seq (φ k) with hw_def
  have hw_norm : ∀ k, ‖w k‖ = dist (z_seq (φ (k + 1))) (z_seq (φ k)) := by
    intro k; rw [hw_def, dist_eq_norm]
  have hw_summable : Summable fun k => ‖w k‖ := by
    simpa [hw_norm] using hφ_sum
  have hw_mem : ∀ k, w k ∈ J₁.toSubmodule + J₂.toSubmodule := fun k =>
    (J₁.toSubmodule + J₂.toSubmodule).sub_mem (hz_mem _) (hz_mem _)
  -- Decompose each difference with norm bounds.
  choose a b ha hb hab ha_norm hb_norm using
    fun k => exists_sum_decomp_norm J₁ J₂ (hw_mem k)
  have ha_summable : Summable fun k => ‖a k‖ :=
    hw_summable.of_nonneg_of_le (fun _ => norm_nonneg _) ha_norm
  have hb_summable : Summable fun k => ‖b k‖ :=
    hw_summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb_norm
  have ha_sum : Summable a := ha_summable.of_norm
  have hb_sum : Summable b := hb_summable.of_norm
  obtain ⟨A, hA_hasSum⟩ := ha_sum
  obtain ⟨B, hB_hasSum⟩ := hb_sum
  -- The partial sums of `a` live in the closed ideal `J₁`, hence so does `A`.
  have hA_mem : A ∈ J₁ :=
    h₁.mem_of_tendsto hA_hasSum
      (Filter.Eventually.of_forall fun s =>
        J₁.toSubmodule.sum_mem (fun k _ => ha k))
  have hB_mem : B ∈ J₂ :=
    h₂.mem_of_tendsto hB_hasSum
      (Filter.Eventually.of_forall fun s =>
        J₂.toSubmodule.sum_mem (fun k _ => hb k))
  -- `w k = a k + b k`, so `HasSum w (A + B)`.
  have hw_hasSum : HasSum w (A + B) := by
    have : HasSum (fun k => a k + b k) (A + B) := hA_hasSum.add hB_hasSum
    convert this using 1
    funext k; exact (hab k).symm
  -- Telescoping: partial sums of `w` tend to `z - z_seq (φ 0)`.
  have htelescope : Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, w k) Filter.atTop
      (nhds (z - z_seq (φ 0))) := by
    have hsum_eq : ∀ n, (∑ k ∈ Finset.range n, w k)
        = z_seq (φ n) - z_seq (φ 0) := by
      intro n
      simpa [hw_def] using
        Finset.sum_range_sub (fun k => z_seq (φ k)) n
    simp only [hsum_eq]
    exact hsub_lim.sub_const _
  -- Identify the two limits of the partial sums.
  have hAB_eq : A + B = z - z_seq (φ 0) :=
    tendsto_nhds_unique hw_hasSum.tendsto_sum_nat htelescope
  have hz_eq : z = z_seq (φ 0) + (A + B) := by rw [hAB_eq]; abel
  change z ∈ (J₁.toSubmodule + J₂.toSubmodule : Submodule ℝ X)
  rw [hz_eq]
  exact (J₁.toSubmodule + J₂.toSubmodule).add_mem
    (hz_mem (φ 0))
    (Submodule.mem_sup.mpr ⟨A, hA_mem, B, hB_mem, rfl⟩)
def sup (J₁ J₂ : ClosedOrderIdeal X) : ClosedOrderIdeal X where
  toOrderIdeal := OrderIdeal.sum J₁.toOrderIdeal J₂.toOrderIdeal
  isClosed' := isClosed_sum J₁.isClosed J₂.isClosed
def sInf (S : Set (ClosedOrderIdeal X)) : ClosedOrderIdeal X where
  toOrderIdeal := InfSet.sInf ((fun J : ClosedOrderIdeal X => J.toOrderIdeal) '' S)
  isClosed' := by
    have h : ((InfSet.sInf ((fun J : ClosedOrderIdeal X => J.toOrderIdeal) '' S) :
        OrderIdeal X) : Set X) =
        ⋂ J ∈ S, (J : Set X) := by
      ext x
      rw [Set.mem_iInter₂]
      exact OrderIdeal.mem_sInf.trans
        ⟨fun h J hJ => h _ ⟨J, hJ, rfl⟩, by rintro h _ ⟨J, hJ, rfl⟩; exact h J hJ⟩
    rw [show ((InfSet.sInf ((fun J : ClosedOrderIdeal X => J.toOrderIdeal) '' S) :
        OrderIdeal X) : Set X) =
        ⋂ J ∈ S, (J : Set X) from h]
    exact isClosed_biInter fun J _ => J.isClosed
instance : Lattice (ClosedOrderIdeal X) where
  sup := sup
  inf := inf
  le_sup_left := fun J₁ J₂ x hx => by
    change x ∈ OrderIdeal.sum J₁.toOrderIdeal J₂.toOrderIdeal
    exact Submodule.mem_sup.mpr ⟨x, hx, 0, J₂.toSubmodule.zero_mem, add_zero x⟩
  le_sup_right := fun J₁ J₂ x hx => by
    change x ∈ OrderIdeal.sum J₁.toOrderIdeal J₂.toOrderIdeal
    exact Submodule.mem_sup.mpr ⟨0, J₁.toSubmodule.zero_mem, x, hx, zero_add x⟩
  sup_le := fun J₁ J₂ K hJ₁ hJ₂ x hx => by
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
    exact K.toSubmodule.add_mem (hJ₁ hx₁) (hJ₂ hx₂)
  inf_le_left := fun _ _ _ hx => hx.1
  inf_le_right := fun _ _ _ hx => hx.2
  le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩
instance : InfSet (ClosedOrderIdeal X) where
  sInf := sInf
end ClosedOrderIdeal


