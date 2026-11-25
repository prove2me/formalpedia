-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
-- name    : GroundTheory_PAdicHodge_FieldOfNormsRing
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T09:04:28.146583+00:00
-- url     : https://prove2.me/theorems/9ff603b0-5705-55d5-aec8-771b41ae68cf
-- title:
--   Field Of Norms Ring
-- statement:
--   Definitions and structural lemmas for Field Of Norms Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsRing.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_mem
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_mul
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_one
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_zero
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_nrm_N
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_nrm_N_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_nrm_N_sub_N_le
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_nrm_N_sub_N_le_mul
import Theorems.Thm_GroundTheory_PAdicHodge_continuous_nrm
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_le_nrm_iff
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_mul
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_mul_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_neg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_sub_le_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower___lt_one_de857b87b125
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower___nonneg_2e425604b7b3
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower_nrm_N_add_sub_le___484fd36eb6a8
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower_nrm_N_sub_N_le___999ce6594f0e
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_nrm_sub_le_of_le__5fdbf955fbfb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.PAdicHodge.NormTower.N_one
attribute [local simp] GroundTheory.PAdicHodge.NormTower.N_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_eq_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_neg
attribute [local simp] GroundTheory.PAdicHodge.nrm_one
attribute [local simp] GroundTheory.PAdicHodge.nrm_zero


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
namespace NormTower
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}
  (t : NormTower K Ω p)
section Composite
def Nto (i : ℕ) : ℕ → Ω → Ω
  | 0 => id
  | j + 1 => fun y ↦ Nto i j (t.N (i + j) y)
@[simp]
theorem Nto_zero (i : ℕ) (y : Ω) : t.Nto i 0 y = y := rfl
theorem Nto_succ (i j : ℕ) (y : Ω) : t.Nto i (j + 1) y = t.Nto i j (t.N (i + j) y) := rfl
theorem Nto_succ' (i j : ℕ) (y : Ω) : t.Nto i (j + 1) y = t.N i (t.Nto (i + 1) j y) := by
  induction j generalizing y with
  | zero => simp [Nto]
  | succ j ih =>
    rw [Nto_succ, ih, Nto_succ, show i + (j + 1) = i + 1 + j by omega]
theorem Nto_mem (i : ℕ) {j : ℕ} {y : Ω} (hy : y ∈ t.E (i + j)) : t.Nto i j y ∈ t.E i := by
  induction j generalizing y with
  | zero => exact hy
  | succ j ih => exact ih (t.N_mem (i + j) hy)
@[simp]
theorem Nto_one (i j : ℕ) : t.Nto i j 1 = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Nto_succ, t.N_one, ih]
@[simp]
theorem Nto_zero' (i j : ℕ) : t.Nto i j 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Nto_succ, t.N_zero, ih]
def D (i j : ℕ) : ℕ :=
  ∏ m ∈ Finset.range j, p ^ t.k (i + m)
theorem D_succ (i j : ℕ) : t.D i (j + 1) = t.D i j * p ^ t.k (i + j) := by
  rw [D, Finset.prod_range_succ]; rfl
theorem nrm_Nto (i j : ℕ) (y : Ω) : nrm K (t.Nto i j y) = nrm K y ^ t.D i j := by
  induction j generalizing y with
  | zero => simp [D]
  | succ j ih => rw [Nto_succ, ih, t.nrm_N, D_succ, ← pow_mul, mul_comm]
theorem nrm_Nto_le_one (i j : ℕ) {y : Ω} (hy : nrm K y ≤ 1) : nrm K (t.Nto i j y) ≤ 1 := by
  rw [nrm_Nto]; exact pow_le_one₀ (nrm_nonneg _) hy
theorem nrm_Nto_sub_Nto_le_ρ (i : ℕ) {j : ℕ} {a b : Ω} (ha : a ∈ t.E (i + j)) (hb : b ∈ t.E (i + j))
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) (hab : nrm K (a - b) ≤ t.ρ) :
    nrm K (t.Nto i j a - t.Nto i j b) ≤ t.ρ := by
  induction j generalizing a b with
  | zero => exact hab
  | succ j ih =>
    exact ih (t.N_mem _ ha) (t.N_mem _ hb) (t.nrm_N_le_one _ ha1) (t.nrm_N_le_one _ hb1)
      (t.nrm_N_sub_N_le_ρ _ ha hb ha1 hb1 hab)
def cnt (i j : ℕ) : ℕ :=
  ((Finset.range j).filter fun m ↦ t.k (i + m) ≠ 0).card
theorem cnt_succ (i j : ℕ) : t.cnt i (j + 1) = t.cnt i j + if t.k (i + j) ≠ 0 then 1 else 0 := by
  simp only [cnt, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rw [add_zero]
theorem cnt_mono (i : ℕ) : Monotone (t.cnt i) := by
  intro j j' h
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))
theorem exists_le_cnt (i M : ℕ) : ∃ j, M ≤ t.cnt i j := by
  induction M with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ M ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨m, hm, hk⟩ := t.frequently_ne_zero (i + j)
    refine ⟨m - i + 1, ?_⟩
    rw [cnt_succ, if_pos (by rwa [show i + (m - i) = m by omega])]
    have := t.cnt_mono i (show j ≤ m - i by omega)
    omega
theorem nrm_Nto_sub_Nto_le (i : ℕ) {j : ℕ} {a b : Ω} (ha : a ∈ t.E (i + j)) (hb : b ∈ t.E (i + j))
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) {s : ℝ} (hs : s ≤ t.ρ) (hab : nrm K (a - b) ≤ s) :
    nrm K (t.Nto i j a - t.Nto i j b) ≤ t.ρ ^ t.cnt i j * s := by
  induction j generalizing a b s with
  | zero => simpa [cnt] using hab
  | succ j ih =>
    simp only [Nto_succ]
    have hs0 : 0 ≤ s := (nrm_nonneg _).trans hab
    by_cases hk : t.k (i + j) ≠ 0
    · have h1 := t.nrm_N_sub_N_le_mul (i + j) hk ha hb ha1 hb1 hs hab
      have hs' : t.ρ * s ≤ t.ρ :=
        (mul_le_of_le_one_left hs0 t.ρ_lt_one.le).trans hs
      refine (ih (t.N_mem _ ha) (t.N_mem _ hb) (t.nrm_N_le_one _ ha1) (t.nrm_N_le_one _ hb1)
        hs' h1).trans (le_of_eq ?_)
      rw [cnt_succ, if_pos hk, pow_succ]; ring
    · have h1 := t.nrm_N_sub_N_le (i + j) ha hb ha1 hb1 hs hab
      refine (ih (t.N_mem _ ha) (t.N_mem _ hb) (t.nrm_N_le_one _ ha1) (t.nrm_N_le_one _ hb1)
        hs h1).trans (le_of_eq ?_)
      rw [cnt_succ, if_neg hk, add_zero]
end Composite
section Families
def IsFam (z : ℕ → Ω) : Prop :=
  ∀ n, z n ∈ t.E n ∧ t.N n (z (n + 1)) = z n
def IsIntFam (z : ℕ → Ω) : Prop :=
  t.IsFam z ∧ ∀ n, nrm K (z n) ≤ 1
variable {t}
theorem IsFam.Nto_eq {z : ℕ → Ω} (hz : t.IsFam z) (i j : ℕ) : t.Nto i j (z (i + j)) = z i := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Nto_succ, ← add_assoc, (hz (i + j)).2, ih]
theorem intFam_ext {z z' : ℕ → Ω} (hz : t.IsIntFam z) (hz' : t.IsIntFam z')
    (h : ∀ n, nrm K (z n - z' n) ≤ t.ρ) : z = z' := by
  funext i
  rw [← sub_eq_zero, ← nrm_eq_zero (K := K)]
  refine le_antisymm ?_ (nrm_nonneg _)
  have hle : ∀ M : ℕ, nrm K (z i - z' i) ≤ t.ρ ^ M := by
    intro M
    obtain ⟨j, hj⟩ := t.exists_le_cnt i M
    rw [← hz.1.Nto_eq i j, ← hz'.1.Nto_eq i j]
    refine (t.nrm_Nto_sub_Nto_le i (hz.1 _).1 (hz'.1 _).1 (hz.2 _) (hz'.2 _) le_rfl
      (h _)).trans ?_
    calc t.ρ ^ t.cnt i j * t.ρ ≤ t.ρ ^ t.cnt i j * 1 :=
          mul_le_mul_of_nonneg_left t.ρ_lt_one.le (pow_nonneg t.ρ_nonneg _)
      _ = t.ρ ^ t.cnt i j := mul_one _
      _ ≤ t.ρ ^ M := pow_le_pow_of_le_one t.ρ_nonneg t.ρ_lt_one.le hj
  exact ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one t.ρ_nonneg t.ρ_lt_one) hle
variable (t)
def intSet (n : ℕ) : Set Ω :=
  {y | y ∈ t.E n ∧ nrm K y ≤ 1}
theorem isCompact_intSet (n : ℕ) : IsCompact (t.intSet n) := by
  haveI := t.finiteDimensional n
  have hc := IsNonarchimedeanLocalField.isCompact_closedBall (t.E n) 1
  have : t.intSet n = Subtype.val '' {x : t.E n | valuation (t.E n) x ≤ 1} := by
    ext y
    simp only [intSet, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hy, hy1⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      rw [← map_one (valuation (t.E n)), ← (valuation (t.E n)).vle_iff_le,
        ← IntermediateField.coe_vle_coe_iff]
      rw [← nrm_le_nrm_iff (K := K)]
      simpa using hy1
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      rw [← map_one (valuation (t.E n)), ← (valuation (t.E n)).vle_iff_le,
        ← IntermediateField.coe_vle_coe_iff, ← nrm_le_nrm_iff (K := K)] at hx
      simpa using hx
  rw [this]
  exact hc.image continuous_subtype_val
theorem continuous_N (n : ℕ) : Continuous (t.N n) :=
  continuous_finsetProd _ fun σ _ ↦ continuous_algEquiv_of_isAlgebraic σ
theorem nrm_Nto_sub_le_of_cong {a : ℕ → Ω} (ha : ∀ n, a n ∈ t.E n) (ha1 : ∀ n, nrm K (a n) ≤ 1)
    (hcong : ∀ n, nrm K (t.N n (a (n + 1)) - a n) ≤ t.ρ) (i j : ℕ) :
    nrm K (t.Nto i j (a (i + j)) - a i) ≤ t.ρ := by
  induction j with
  | zero => simp [t.ρ_nonneg]
  | succ j ih =>
    rw [Nto_succ, ← add_assoc]
    have h1 := t.nrm_Nto_sub_Nto_le_ρ i (t.N_mem _ (ha _)) (ha (i + j))
      (t.nrm_N_le_one _ (ha1 _)) (ha1 _) (hcong _)
    exact nrm_sub_le_of_le' h1 ih
theorem exists_intFam {a : ℕ → Ω} (ha : ∀ n, a n ∈ t.E n) (ha1 : ∀ n, nrm K (a n) ≤ 1)
    (hcong : ∀ n, nrm K (t.N n (a (n + 1)) - a n) ≤ t.ρ) :
    ∃ z, t.IsIntFam z ∧ ∀ n, nrm K (z n - a n) ≤ t.ρ := by

  let S : ℕ → Set (ℕ → Ω) := fun m ↦
    {z | (∀ n < m, nrm K (t.N n (z (n + 1)) - z n) ≤ 0) ∧ ∀ n ≤ m, nrm K (z n - a n) ≤ t.ρ}
  have hP : IsCompact {z : ℕ → Ω | ∀ n, z n ∈ t.intSet n} :=
    isCompact_pi_infinite t.isCompact_intSet
  have hcont : ∀ n, Continuous fun z : ℕ → Ω ↦ nrm K (t.N n (z (n + 1)) - z n) := fun n ↦
    (continuous_nrm K Ω).comp (((t.continuous_N n).comp (continuous_apply _)).sub
      (continuous_apply _))
  have hcont' : ∀ n, Continuous fun z : ℕ → Ω ↦ nrm K (z n - a n) := fun n ↦
    (continuous_nrm K Ω).comp ((continuous_apply _).sub continuous_const)
  have hcl : ∀ m, IsClosed (S m) := by
    intro m
    have e : S m = (⋂ n ∈ {n | n < m}, {z : ℕ → Ω | nrm K (t.N n (z (n + 1)) - z n) ≤ 0}) ∩
        ⋂ n ∈ {n | n ≤ m}, {z : ℕ → Ω | nrm K (z n - a n) ≤ t.ρ} := by
      ext z; simp [S]
    rw [e]
    exact (isClosed_biInter fun n _ ↦ isClosed_le (hcont n) continuous_const).inter
      (isClosed_biInter fun n _ ↦ isClosed_le (hcont' n) continuous_const)
  have hanti : ∀ {m m'}, m ≤ m' → S m' ⊆ S m := fun hmm' z hz ↦
    ⟨fun n hn ↦ hz.1 n (by omega), fun n hn ↦ hz.2 n (by omega)⟩
  have hne : ∀ m, ({z : ℕ → Ω | ∀ n, z n ∈ t.intSet n} ∩ S m).Nonempty := by
    intro m
    refine ⟨fun n ↦ if n ≤ m then t.Nto n (m - n) (a m) else a n, ?_, ?_, ?_⟩
    · intro n
      dsimp only
      split_ifs with h
      · have ham : a m ∈ t.E (n + (m - n)) := by rw [Nat.add_sub_cancel' h]; exact ha m
        exact ⟨t.Nto_mem n ham, t.nrm_Nto_le_one _ _ (ha1 m)⟩
      · exact ⟨ha n, ha1 n⟩
    · intro n hn
      simp only [if_pos hn.le, if_pos (show n + 1 ≤ m by omega)]
      rw [← Nto_succ', show m - n = m - (n + 1) + 1 by omega]
      simp
    · intro n hn
      simp only [if_pos hn]
      have := t.nrm_Nto_sub_le_of_cong ha ha1 hcong n (m - n)
      rwa [Nat.add_sub_cancel' hn] at this
  obtain ⟨z, hzP, hz⟩ := hP.inter_iInter_nonempty S hcl fun u ↦ by
    obtain ⟨z, hzP, hzS⟩ := hne (u.sup id)
    refine ⟨z, hzP, Set.mem_iInter₂.mpr fun m hm ↦ hanti (Finset.le_sup (f := id) hm) hzS⟩
  rw [Set.mem_iInter] at hz
  refine ⟨z, ⟨fun n ↦ ⟨(hzP n).1, ?_⟩, fun n ↦ (hzP n).2⟩, fun n ↦ (hz n).2 n le_rfl⟩
  have := (hz (n + 1)).1 n (Nat.lt_succ_self n)
  rw [← sub_eq_zero, ← nrm_eq_zero (K := K)]
  exact le_antisymm this (nrm_nonneg _)
end Families
section Ring
def Plus : Type _ :=
  {z : ℕ → Ω // t.IsIntFam z}
namespace Plus
variable {t}
theorem mem (x : t.Plus) (n : ℕ) : x.1 n ∈ t.E n := (x.2.1 n).1
theorem nrm_le (x : t.Plus) (n : ℕ) : nrm K (x.1 n) ≤ 1 := x.2.2 n
theorem N_eq (x : t.Plus) (n : ℕ) : t.N n (x.1 (n + 1)) = x.1 n := (x.2.1 n).2
theorem eq_of_cong {x y : t.Plus} (h : ∀ n, nrm K (x.1 n - y.1 n) ≤ t.ρ) : x = y :=
  Subtype.ext (intFam_ext x.2 y.2 h)
instance : Zero t.Plus :=
  ⟨⟨fun _ ↦ 0, fun n ↦ ⟨zero_mem _, t.N_zero n⟩, fun n ↦ by simp⟩⟩
instance : One t.Plus :=
  ⟨⟨fun _ ↦ 1, fun n ↦ ⟨one_mem _, t.N_one n⟩, fun n ↦ by simp⟩⟩
instance : Mul t.Plus :=
  ⟨fun x y ↦ ⟨fun n ↦ x.1 n * y.1 n, fun n ↦ ⟨mul_mem (x.mem n) (y.mem n),
    by rw [t.N_mul, x.N_eq, y.N_eq]⟩, fun n ↦ nrm_mul_le_one (x.nrm_le n) (y.nrm_le n)⟩⟩
@[simp] theorem zero_val (n : ℕ) : (0 : t.Plus).1 n = 0 := rfl
@[simp] theorem one_val (n : ℕ) : (1 : t.Plus).1 n = 1 := rfl
@[simp] theorem mul_val (x y : t.Plus) (n : ℕ) : (x * y).1 n = x.1 n * y.1 n := rfl
theorem exists_add (x y : t.Plus) :
    ∃ z, t.IsIntFam z ∧ ∀ n, nrm K (z n - (x.1 n + y.1 n)) ≤ t.ρ :=
  t.exists_intFam (fun n ↦ add_mem (x.mem n) (y.mem n))
    (fun n ↦ nrm_add_le_one (x.nrm_le n) (y.nrm_le n)) fun n ↦ by
      have := t.nrm_N_add_sub_le_ρ n (x.mem (n + 1)) (y.mem (n + 1)) (x.nrm_le _) (y.nrm_le _)
      rw [x.N_eq, y.N_eq] at this
      rwa [sub_add_eq_sub_sub]
theorem exists_neg (x : t.Plus) : ∃ z, t.IsIntFam z ∧ ∀ n, nrm K (z n - -x.1 n) ≤ t.ρ :=
  t.exists_intFam (fun n ↦ neg_mem (x.mem n)) (fun n ↦ by simpa using x.nrm_le n) fun n ↦ by
    have := t.nrm_N_add_sub_le_ρ n (neg_mem (x.mem (n + 1))) (x.mem (n + 1))
      (by simpa using x.nrm_le (n + 1)) (x.nrm_le _)
    rw [neg_add_cancel, t.N_zero, x.N_eq] at this
    rw [sub_neg_eq_add, ← nrm_neg]
    convert this using 2; ring
instance : Add t.Plus :=
  ⟨fun x y ↦ ⟨(exists_add x y).choose, (exists_add x y).choose_spec.1⟩⟩
instance : Neg t.Plus :=
  ⟨fun x ↦ ⟨(exists_neg x).choose, (exists_neg x).choose_spec.1⟩⟩
theorem add_cong (x y : t.Plus) (n : ℕ) : nrm K ((x + y).1 n - (x.1 n + y.1 n)) ≤ t.ρ :=
  (exists_add x y).choose_spec.2 n
theorem neg_cong (x : t.Plus) (n : ℕ) : nrm K ((-x).1 n - -x.1 n) ≤ t.ρ :=
  (exists_neg x).choose_spec.2 n
theorem cong4 {a b c d e : Ω} (h1 : nrm K a ≤ t.ρ) (h2 : nrm K b ≤ t.ρ)
    (h3 : nrm K c ≤ t.ρ) (h4 : nrm K d ≤ t.ρ) (he : e = a + b - c - d) : nrm K e ≤ t.ρ := by
  rw [he]
  exact nrm_sub_le_of_le (nrm_sub_le_of_le (nrm_add_le_of_le h1 h2) h3) h4
instance instCommRing : CommRing t.Plus where
  add_assoc x y z := eq_of_cong fun n ↦
    cong4 (add_cong (x + y) z n) (add_cong x y n) (add_cong y z n) (add_cong x (y + z) n) (by ring)
  zero_add x := eq_of_cong fun n ↦ by
    have := add_cong 0 x n; simpa using this
  add_zero x := eq_of_cong fun n ↦ by
    have := add_cong x 0 n; simpa using this
  add_comm x y := eq_of_cong fun n ↦
    cong4 (add_cong x y n) (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg) (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg)
      (add_cong y x n) (by ring)
  neg_add_cancel x := eq_of_cong fun n ↦ by
    have h1 := add_cong (-x) x n
    have h2 := neg_cong x n
    exact cong4 h1 h2 (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg) (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg)
      (by rw [zero_val]; ring)
  nsmul := nsmulRec
  zsmul := zsmulRec
  left_distrib x y z := eq_of_cong fun n ↦ by
    have h1 := add_cong y z n
    have h2 := add_cong (x * y) (x * z) n
    have h1' : nrm K (x.1 n * (y + z).1 n - x.1 n * (y.1 n + z.1 n)) ≤ t.ρ := by
      rw [← mul_sub, nrm_mul]
      exact (mul_le_of_le_one_left (nrm_nonneg _) (x.nrm_le n)).trans h1
    exact cong4 h1' (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg) (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg) h2
      (by simp; ring)
  right_distrib x y z := eq_of_cong fun n ↦ by
    have h1 := add_cong x y n
    have h2 := add_cong (x * z) (y * z) n
    have h1' : nrm K ((x + y).1 n * z.1 n - (x.1 n + y.1 n) * z.1 n) ≤ t.ρ := by
      rw [← sub_mul, nrm_mul]
      exact (mul_le_of_le_one_right (nrm_nonneg _) (z.nrm_le n)).trans h1
    exact cong4 h1' (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg) (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg) h2
      (by simp; ring)
  zero_mul x := Subtype.ext (funext fun n ↦ by simp)
  mul_zero x := Subtype.ext (funext fun n ↦ by simp)
  mul_assoc x y z := Subtype.ext (funext fun n ↦ by simp [mul_assoc])
  one_mul x := Subtype.ext (funext fun n ↦ by simp)
  mul_one x := Subtype.ext (funext fun n ↦ by simp)
  mul_comm x y := Subtype.ext (funext fun n ↦ by simp [mul_comm])
end Plus
end Ring
end NormTower
end GroundTheory.PAdicHodge


