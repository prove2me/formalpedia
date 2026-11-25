-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:28.575736+00:00
-- url     : https://prove2.me/theorems/47ff2764-a1e4-463b-acf2-6593ae5109b2
-- title:
--   Smul One Le And Le Smul One Iff Eigenvalues
-- statement:
--   Definitions and structural lemmas for Smul One Le And Le Smul One Iff Eigenvalues, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Theorems.Thm_GlobalTheory_inv_le_inv_of_posDef_of_le
import Theorems.Thm_GlobalTheory_inv_real_smul_of_posDef
import Theorems.Thm_GlobalTheory_le_re_trace_smul_one_of_posSemidef
import Theorems.Thm_GlobalTheory_norm_sq_apply_le_of_posSemidef
import Theorems.Thm_GlobalTheory_posDef_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
namespace GlobalTheory
section Weight
variable {κ X : Type*}
noncomputable def lwP₂ (S : Finset κ) (z : κ → ℂ) : ℝ :=
  1 + ∑ j ∈ S, |Real.log ‖z j‖|
def coordDivisor (S : Finset κ) (w : X → κ → ℂ) : Set X :=
  {x | ∃ j ∈ S, w x j = 0}
theorem one_le_logWeight (S : Finset κ) (z : κ → ℂ) : 1 ≤ lwP₂ S z :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
theorem logWeight_pos (S : Finset κ) (z : κ → ℂ) : 0 < lwP₂ S z :=
  one_pos.trans_le (one_le_logWeight S z)
theorem mul_logWeight_pow_le (S : Finset κ) (z : κ → ℂ) {C C' : ℝ} {N N' : ℕ} (hC : C ≤ C')
    (hC' : 0 ≤ C') (hN : N ≤ N') : C * lwP₂ S z ^ N ≤ C' * lwP₂ S z ^ N' :=
  mul_le_mul hC (pow_le_pow_right₀ (one_le_logWeight S z) hN)
    (pow_nonneg (logWeight_pos S z).le _) hC'
end Weight
section Polydisc
variable {ι : Type*}
end Polydisc
section Growth
variable {κ κ' X X' E F : Type*} [TopologicalSpace X] [TopologicalSpace X']
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
def HasLogGrowth (S : Finset κ) (w : X → κ → ℂ) (U : Set X) (f : X → E) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ x ∈ K, x ∉ coordDivisor S w →
    ‖f x‖ ≤ C * lwP₂ S (w x) ^ N
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
namespace HasLogGrowth
theorem exists_one_le {f : X → E} (hf : HasLogGrowth S w U f) {K : Set X} (hKU : K ⊆ U)
    (hK : IsCompact K) : ∃ (C : ℝ) (N : ℕ), 1 ≤ C ∧ ∀ x ∈ K, x ∉ coordDivisor S w →
      ‖f x‖ ≤ C * lwP₂ S (w x) ^ N := by
  obtain ⟨C, N, h⟩ := hf K hKU hK
  exact ⟨max C 1, N, le_max_right _ _, fun x hx hB => (h x hx hB).trans
    (mul_logWeight_pow_le _ _ (le_max_left _ _) (zero_le_one.trans (le_max_right _ _)) le_rfl)⟩
theorem mono {f : X → E} (hf : HasLogGrowth S w U f) {V : Set X} (hV : V ⊆ U) :
    HasLogGrowth S w V f :=
  fun K hK => hf K (hK.trans hV)
theorem of_norm_le {f : X → E} {g : X → F} (hg : HasLogGrowth S w U g)
    (h : ∀ x ∈ U, x ∉ coordDivisor S w → ‖f x‖ ≤ ‖g x‖) : HasLogGrowth S w U f := by
  intro K hKU hK
  obtain ⟨C, N, hC⟩ := hg K hKU hK
  exact ⟨C, N, fun x hx hB => (h x (hKU hx) hB).trans (hC x hx hB)⟩
theorem of_le {f : X → E} {g : X → ℝ} (hg : HasLogGrowth S w U g)
    (h : ∀ x ∈ U, x ∉ coordDivisor S w → ‖f x‖ ≤ g x) : HasLogGrowth S w U f :=
  hg.of_norm_le fun x hx hB => (h x hx hB).trans (le_abs_self _)
theorem congr {f g : X → E} (hg : HasLogGrowth S w U g)
    (h : ∀ x ∈ U, x ∉ coordDivisor S w → f x = g x) : HasLogGrowth S w U f :=
  hg.of_norm_le fun x hx hB => by rw [h x hx hB]
theorem norm {f : X → E} (hf : HasLogGrowth S w U f) : HasLogGrowth S w U fun x => ‖f x‖ :=
  hf.of_norm_le fun _ _ _ => (norm_norm _).le
theorem of_continuousOn {f : X → E} (hf : ContinuousOn f U) : HasLogGrowth S w U f := by
  intro K hKU hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hf.mono hKU)
  exact ⟨C, 0, fun x hx _ => by simpa using hC x hx⟩
theorem const (c : E) : HasLogGrowth S w U fun _ => c :=
  of_continuousOn continuousOn_const
theorem lwP₂ : HasLogGrowth S w U fun x => lwP₂ S (w x) :=
  fun _ _ _ => ⟨1, 1, fun x _ _ => by simp [abs_of_pos (logWeight_pos S (w x))]⟩
theorem add {f g : X → E} (hf : HasLogGrowth S w U f) (hg : HasLogGrowth S w U g) :
    HasLogGrowth S w U fun x => f x + g x := by
  intro K hKU hK
  obtain ⟨C, N, hC1, hC⟩ := hf.exists_one_le hKU hK
  obtain ⟨D, M, hD1, hD⟩ := hg.exists_one_le hKU hK
  refine ⟨C + D, max N M, fun x hx hB => (norm_add_le _ _).trans ?_⟩
  rw [add_mul]
  exact add_le_add
    ((hC x hx hB).trans (mul_logWeight_pow_le _ _ le_rfl (by linarith) (le_max_left _ _)))
    ((hD x hx hB).trans (mul_logWeight_pow_le _ _ le_rfl (by linarith) (le_max_right _ _)))
theorem sum {α : Type*} {s : Finset α} {f : α → X → E} (hf : ∀ a ∈ s, HasLogGrowth S w U (f a)) :
    HasLogGrowth S w U fun x => ∑ a ∈ s, f a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))
theorem mul {R : Type*} [SeminormedRing R] {f g : X → R} (hf : HasLogGrowth S w U f)
    (hg : HasLogGrowth S w U g) : HasLogGrowth S w U fun x => f x * g x := by
  intro K hKU hK
  obtain ⟨C, N, hC1, hC⟩ := hf.exists_one_le hKU hK
  obtain ⟨D, M, hD1, hD⟩ := hg.exists_one_le hKU hK
  refine ⟨C * D, N + M, fun x hx hB => (norm_mul_le _ _).trans ?_⟩
  rw [pow_add, mul_mul_mul_comm]
  exact mul_le_mul (hC x hx hB) (hD x hx hB) (norm_nonneg _) ((norm_nonneg _).trans (hC x hx hB))
theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] {c : X → 𝕜} {f : X → E}
    (hc : HasLogGrowth S w U c) (hf : HasLogGrowth S w U f) :
    HasLogGrowth S w U fun x => c x • f x :=
  (hc.norm.mul hf.norm).of_le fun _ _ _ => (norm_smul _ _).le
theorem prod {R α : Type*} [SeminormedCommRing R] {s : Finset α} {f : α → X → R}
    (hf : ∀ a ∈ s, HasLogGrowth S w U (f a)) : HasLogGrowth S w U fun x => ∏ a ∈ s, f a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).mul
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))
theorem star {f : X → ℂ} (hf : HasLogGrowth S w U f) : HasLogGrowth S w U fun x => star (f x) :=
  hf.of_norm_le fun _ _ _ => (norm_star _).le
end HasLogGrowth
def IsUnitMulMonomialOn (S : Finset κ) (v : X' → κ → ℂ) (S' : Finset κ') (w' : X' → κ' → ℂ)
    (U' : Set X') : Prop :=
  ∀ j ∈ S, ∃ (u : X' → ℂ) (m : κ' → ℕ), ContinuousOn u U' ∧
    ∀ x ∈ U', u x ≠ 0 ∧ v x j = u x * ∏ i ∈ S', w' x i ^ m i
namespace IsUnitMulMonomialOn
variable {S' : Finset κ'} {w' : X' → κ' → ℂ} {U' : Set X'} {v : X' → κ → ℂ}
end IsUnitMulMonomialOn
end Growth
section Scalar
variable {κ κ' X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
def IsLogBoundedScalar (S : Finset κ) (w : X → κ → ℂ) (U : Set X) (g : X → ℝ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ x ∈ K, x ∉ coordDivisor S w →
    (C * lwP₂ S (w x) ^ N)⁻¹ ≤ g x ∧ g x ≤ C * lwP₂ S (w x) ^ N
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X} {g g' : X → ℝ}
theorem IsLogBoundedScalar.pos (hg : IsLogBoundedScalar S w U g) {x : X} (hx : x ∈ U)
    (hB : x ∉ coordDivisor S w) : 0 < g x := by
  obtain ⟨C, N, hC, h⟩ := hg {x} (singleton_subset_iff.2 hx) isCompact_singleton
  exact (inv_pos.2 (mul_pos hC (pow_pos (logWeight_pos _ _) _))).trans_le (h x rfl hB).1
theorem isLogBoundedScalar_iff : IsLogBoundedScalar S w U g ↔
    (∀ x ∈ U, x ∉ coordDivisor S w → 0 < g x) ∧ HasLogGrowth S w U g ∧
      HasLogGrowth S w U fun x => (g x)⁻¹ := by
  refine ⟨fun h => ⟨fun x => h.pos, fun K hKU hK => ?_, fun K hKU hK => ?_⟩,
    fun ⟨h0, h1, h2⟩ K hKU hK => ?_⟩
  · obtain ⟨C, N, -, h'⟩ := h K hKU hK
    exact ⟨C, N, fun x hx hB => by
      rw [Real.norm_of_nonneg (h.pos (hKU hx) hB).le]; exact (h' x hx hB).2⟩
  · obtain ⟨C, N, hC, h'⟩ := h K hKU hK
    exact ⟨C, N, fun x hx hB => by
      rw [Real.norm_of_nonneg (inv_pos.2 (h.pos (hKU hx) hB)).le]
      exact inv_le_of_inv_le₀ (mul_pos hC (pow_pos (logWeight_pos _ _) _)) (h' x hx hB).1⟩
  · obtain ⟨C, N, hC, h⟩ := (h1.norm.add h2.norm).exists_one_le hKU hK
    refine ⟨C, N, by linarith, fun x hx hB => ?_⟩
    have hp := h0 x (hKU hx) hB
    have hi := inv_pos.2 hp
    have h3 := (le_abs_self _).trans (h x hx hB)
    rw [Real.norm_of_nonneg hp.le, Real.norm_of_nonneg hi.le] at h3
    exact ⟨inv_le_of_inv_le₀ hp (by linarith), by linarith⟩
namespace IsLogBoundedScalar
theorem hasLogGrowth (hg : IsLogBoundedScalar S w U g) : HasLogGrowth S w U g :=
  (isLogBoundedScalar_iff.1 hg).2.1
theorem hasLogGrowth_inv (hg : IsLogBoundedScalar S w U g) :
    HasLogGrowth S w U fun x => (g x)⁻¹ :=
  (isLogBoundedScalar_iff.1 hg).2.2
theorem congr (hg : IsLogBoundedScalar S w U g) (h : ∀ x ∈ U, x ∉ coordDivisor S w → g' x = g x) :
    IsLogBoundedScalar S w U g' := by
  intro K hKU hK
  obtain ⟨C, N, hC, h'⟩ := hg K hKU hK
  exact ⟨C, N, hC, fun x hx hB => h x (hKU hx) hB ▸ h' x hx hB⟩
theorem of_continuousOn (hg : ContinuousOn g U) (h0 : ∀ x ∈ U, 0 < g x) :
    IsLogBoundedScalar S w U g :=
  isLogBoundedScalar_iff.2 ⟨fun x hx _ => h0 x hx, .of_continuousOn hg,
    .of_continuousOn (hg.inv₀ fun x hx => (h0 x hx).ne')⟩
theorem const {c : ℝ} (hc : 0 < c) : IsLogBoundedScalar S w U fun _ => c :=
  of_continuousOn continuousOn_const fun _ _ => hc
theorem lwP₂ : IsLogBoundedScalar S w U fun x => lwP₂ S (w x) :=
  fun _ _ _ => ⟨1, 1, one_pos, fun x _ _ => by
    have := one_le_logWeight S (w x)
    simpa using (inv_le_one_of_one_le₀ this).trans this⟩
theorem mul (hg : IsLogBoundedScalar S w U g) (hg' : IsLogBoundedScalar S w U g') :
    IsLogBoundedScalar S w U fun x => g x * g' x :=
  isLogBoundedScalar_iff.2 ⟨fun _ hx hB => mul_pos (hg.pos hx hB) (hg'.pos hx hB),
    hg.hasLogGrowth.mul hg'.hasLogGrowth,
    (hg.hasLogGrowth_inv.mul hg'.hasLogGrowth_inv).congr fun _ _ _ => mul_inv _ _⟩
theorem inv (hg : IsLogBoundedScalar S w U g) : IsLogBoundedScalar S w U fun x => (g x)⁻¹ :=
  isLogBoundedScalar_iff.2 ⟨fun _ hx hB => inv_pos.2 (hg.pos hx hB), hg.hasLogGrowth_inv,
    hg.hasLogGrowth.congr fun _ _ _ => inv_inv _⟩
theorem prod {α : Type*} {s : Finset α} {f : α → X → ℝ}
    (hf : ∀ a ∈ s, IsLogBoundedScalar S w U (f a)) :
    IsLogBoundedScalar S w U fun x => ∏ a ∈ s, f a x :=
  isLogBoundedScalar_iff.2 ⟨fun _ hx hB => Finset.prod_pos fun a ha => (hf a ha).pos hx hB,
    .prod fun a ha => (hf a ha).hasLogGrowth,
    (HasLogGrowth.prod (f := fun a x => (f a x)⁻¹) fun a ha => (hf a ha).hasLogGrowth_inv).congr
      fun _ _ _ => (Finset.prod_inv_distrib _).symm⟩
end IsLogBoundedScalar
end Scalar
section Entries
variable {κ X l m n : Type*} [TopologicalSpace X]
def HasLogGrowthEntries (S : Finset κ) (w : X → κ → ℂ) (U : Set X) (A : X → Matrix m n ℂ) : Prop :=
  ∀ i j, HasLogGrowth S w U fun x => A x i j
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
namespace HasLogGrowthEntries
theorem congr {A A' : X → Matrix m n ℂ} (hA : HasLogGrowthEntries S w U A)
    (h : ∀ x ∈ U, x ∉ coordDivisor S w → A' x = A x) : HasLogGrowthEntries S w U A' :=
  fun i j => (hA i j).congr fun x hx hB => by rw [h x hx hB]
theorem mul [Fintype m] {A : X → Matrix l m ℂ} {A' : X → Matrix m n ℂ}
    (hA : HasLogGrowthEntries S w U A) (hA' : HasLogGrowthEntries S w U A') :
    HasLogGrowthEntries S w U fun x => A x * A' x :=
  fun i j => .sum (f := fun k x => A x i k * A' x k j) fun k _ => (hA i k).mul (hA' k j)
theorem submatrix {m' n' : Type*} {A : X → Matrix m n ℂ} (hA : HasLogGrowthEntries S w U A)
    (r : m' → m) (c : n' → n) : HasLogGrowthEntries S w U fun x => (A x).submatrix r c :=
  fun i j => hA (r i) (c j)
theorem det [Fintype n] [DecidableEq n] {A : X → Matrix n n ℂ}
    (hA : HasLogGrowthEntries S w U A) : HasLogGrowth S w U fun x => (A x).det := by
  simp only [Matrix.det_apply']
  exact .sum (f := fun (σ : Equiv.Perm n) x => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A x (σ i) i)
    fun σ _ => (HasLogGrowth.const _).mul
      (.prod (f := fun i x => A x (σ i) i) fun i _ => hA (σ i) i)
theorem trace [Fintype n] {A : X → Matrix n n ℂ} (hA : HasLogGrowthEntries S w U A) :
    HasLogGrowth S w U fun x => (A x).trace :=
  .sum (f := fun i x => A x i i) fun i _ => hA i i
end HasLogGrowthEntries
end Entries
section MatrixLemmas
variable {m n : Type*}
theorem real_smul_one_le_real_smul_one [DecidableEq n] {a b : ℝ} (h : a ≤ b) :
    a • (1 : Matrix n n ℂ) ≤ b • (1 : Matrix n n ℂ) := by
  rw [Matrix.le_iff, ← sub_smul]
  exact PosSemidef.one.smul (sub_nonneg.2 h)
theorem inv_smul_one_le_and_le_smul_one_mono [DecidableEq n] {G : Matrix n n ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (h : a⁻¹ • (1 : Matrix n n ℂ) ≤ G ∧ G ≤ a • (1 : Matrix n n ℂ)) :
    b⁻¹ • (1 : Matrix n n ℂ) ≤ G ∧ G ≤ b • (1 : Matrix n n ℂ) :=
  ⟨(real_smul_one_le_real_smul_one (inv_anti₀ ha hab)).trans h.1,
    h.2.trans (real_smul_one_le_real_smul_one hab)⟩
theorem norm_apply_le_of_le_smul_one [DecidableEq n] {G : Matrix n n ℂ} (hG : G.PosSemidef)
    {a : ℝ} (h : G ≤ a • (1 : Matrix n n ℂ)) (i j : n) : ‖G i j‖ ≤ a := by
  have h1 : ∀ k, (G k k).re ≤ a := fun k => by
    have := (Complex.nonneg_iff.1 ((Matrix.le_iff.1 h).diag_nonneg (i := k))).1
    simpa using this
  have h0 : ∀ k, 0 ≤ (G k k).re := fun k => (Complex.nonneg_iff.1 (hG.diag_nonneg (i := k))).1
  have h2 : ‖G i j‖ ^ 2 ≤ (G i i).re * (G j j).re := norm_sq_apply_le_of_posSemidef hG i j
  have ha : 0 ≤ a := (h0 i).trans (h1 i)
  refine abs_le_of_sq_le_sq' (h2.trans ?_) ha |>.2
  rw [sq]
  exact mul_le_mul (h1 i) (h1 j) (h0 j) ha
variable [Fintype n] [DecidableEq n]
theorem inv_smul_one_le_inv_and_inv_le_smul_one {G : Matrix n n ℂ} {a : ℝ} (ha : 0 < a)
    (h : a⁻¹ • (1 : Matrix n n ℂ) ≤ G ∧ G ≤ a • (1 : Matrix n n ℂ)) :
    a⁻¹ • (1 : Matrix n n ℂ) ≤ G⁻¹ ∧ G⁻¹ ≤ a • (1 : Matrix n n ℂ) := by
  have h0 : (a⁻¹ • (1 : Matrix n n ℂ)).PosDef := PosDef.one.smul (inv_pos.2 ha)
  have h1 := inv_le_inv_of_posDef_of_le (posDef_of_le h0 h.1) h.2
  have h2 := inv_le_inv_of_posDef_of_le h0 h.1
  rw [inv_real_smul_of_posDef PosDef.one ha.ne', inv_one] at h1
  rw [inv_real_smul_of_posDef PosDef.one (inv_pos.2 ha).ne', inv_one, inv_inv] at h2
  exact ⟨h1, h2⟩
variable [Fintype m] [DecidableEq m]
theorem posDef_fromBlocks_zero {A : Matrix m m ℂ} {D : Matrix n n ℂ} (hA : A.PosDef)
    (hD : D.PosDef) : (fromBlocks A 0 0 D).PosDef := by
  let _ := hA.isUnit.invertible
  have h := (PosDef.fromBlocks₁₁ (0 : Matrix m n ℂ) D hA).2 (by simpa using hD.posSemidef)
  rw [conjTranspose_zero] at h
  rw [h.posDef_iff_det_ne_zero, det_fromBlocks_zero₂₁]
  exact mul_ne_zero hA.det_pos.ne' hD.det_pos.ne'
noncomputable def schurComplement₁₁ (G : Matrix (m ⊕ n) (m ⊕ n) ℂ) : Matrix n n ℂ :=
  G.toBlocks₂₂ - G.toBlocks₂₁ * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂
noncomputable def schurComplement₂₂ (G : Matrix (m ⊕ n) (m ⊕ n) ℂ) : Matrix m m ℂ :=
  G.toBlocks₁₁ - G.toBlocks₁₂ * G.toBlocks₂₂⁻¹ * G.toBlocks₂₁
theorem schurComplement₁₁_eq_inv {G : Matrix (m ⊕ n) (m ⊕ n) ℂ} (hG : G.PosDef) :
    schurComplement₁₁ G = (G⁻¹.submatrix Sum.inr Sum.inr)⁻¹ := by
  have h11 : (G.toBlocks₁₁).PosDef := hG.submatrix Sum.inl_injective
  let _ := h11.isUnit.invertible
  let _ := hG.isUnit.invertible
  have h := mul_inv_of_invertible G
  rw [← fromBlocks_toBlocks G⁻¹] at h
  nth_rw 1 [← fromBlocks_toBlocks G] at h
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h
  obtain ⟨-, h12, -, h22⟩ := h
  refine (inv_eq_left_inv ?_).symm
  change schurComplement₁₁ G * G⁻¹.toBlocks₂₂ = 1
  have h3 : G.toBlocks₁₂ * G⁻¹.toBlocks₂₂ = -(G.toBlocks₁₁ * G⁻¹.toBlocks₁₂) :=
    eq_neg_of_add_eq_zero_right h12
  rw [schurComplement₁₁, Matrix.sub_mul, Matrix.mul_assoc, h3, Matrix.mul_neg, Matrix.mul_assoc,
    ← Matrix.mul_assoc (G.toBlocks₁₁⁻¹), inv_mul_of_invertible, Matrix.one_mul, sub_neg_eq_add,
    add_comm, h22]
end MatrixLemmas
section PiKronecker
variable {α : Type*} [Fintype α] {l n o : α → Type*}
noncomputable def piKronecker (A : ∀ a, Matrix (l a) (n a) ℂ) : Matrix (∀ a, l a) (∀ a, n a) ℂ :=
  Matrix.of fun i j => ∏ a, A a (i a) (j a)
variable [DecidableEq α] [∀ a, Fintype (n a)]
variable [∀ a, DecidableEq (n a)]
end PiKronecker
section Compound
variable {l n o : Type*} [LinearOrder l] [LinearOrder n] [LinearOrder o]
noncomputable def compoundMatrix (k : ℕ) (A : Matrix l n ℂ) :
    Matrix (Set.powersetCard l k) (Set.powersetCard n k) ℂ :=
  Matrix.of fun I J => (A.submatrix (subsetEnum I) (subsetEnum J)).det
variable [Fintype n]
end Compound
section LogBounded
variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']
def IsLogBounded [DecidableEq n] (S : Finset κ) (w : X → κ → ℂ) (U : Set X)
    (G : X → Matrix n n ℂ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ x ∈ K, x ∉ coordDivisor S w →
    (C * lwP₂ S (w x) ^ N)⁻¹ • (1 : Matrix n n ℂ) ≤ G x ∧
      G x ≤ (C * lwP₂ S (w x) ^ N) • (1 : Matrix n n ℂ)
variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}
theorem IsLogBounded.posDef (hG : IsLogBounded S w U G) {x : X} (hx : x ∈ U)
    (hB : x ∉ coordDivisor S w) : (G x).PosDef := by
  obtain ⟨C, N, hC, h⟩ := hG {x} (singleton_subset_iff.2 hx) isCompact_singleton
  exact posDef_of_le (PosDef.one.smul (inv_pos.2 (mul_pos hC (pow_pos (logWeight_pos _ _) _))))
    (h x rfl hB).1
namespace IsLogBounded
theorem congr (hG : IsLogBounded S w U G) (h : ∀ x ∈ U, x ∉ coordDivisor S w → G' x = G x) :
    IsLogBounded S w U G' := by
  intro K hKU hK
  obtain ⟨C, N, hC, h'⟩ := hG K hKU hK
  exact ⟨C, N, hC, fun x hx hB => h x (hKU hx) hB ▸ h' x hx hB⟩
theorem of_le {g : X → ℝ} (hg : HasLogGrowth S w U g)
    (h : ∀ x ∈ U, x ∉ coordDivisor S w → 0 < g x ∧
      (g x)⁻¹ • (1 : Matrix n n ℂ) ≤ G x ∧ G x ≤ g x • (1 : Matrix n n ℂ)) :
    IsLogBounded S w U G := by
  intro K hKU hK
  obtain ⟨C, N, hC, h'⟩ := hg.exists_one_le hKU hK
  exact ⟨C, N, by linarith, fun x hx hB => inv_smul_one_le_and_le_smul_one_mono
    (h x (hKU hx) hB).1 ((le_abs_self _).trans (h' x hx hB)) (h x (hKU hx) hB).2⟩
theorem hasLogGrowthEntries (hG : IsLogBounded S w U G) : HasLogGrowthEntries S w U G := by
  intro i j K hKU hK
  obtain ⟨C, N, -, h⟩ := hG K hKU hK
  exact ⟨C, N, fun x hx hB =>
    norm_apply_le_of_le_smul_one (hG.posDef (hKU hx) hB).posSemidef (h x hx hB).2 i j⟩
theorem submatrix (hG : IsLogBounded S w U G) {e : m → n} (he : Function.Injective e) :
    IsLogBounded S w U fun x => (G x).submatrix e e := by
  intro K hKU hK
  obtain ⟨C, N, hC, h⟩ := hG K hKU hK
  refine ⟨C, N, hC, fun x hx hB => ⟨?_, ?_⟩⟩
  · simpa [Matrix.le_iff, submatrix_sub, submatrix_smul, submatrix_one e he] using
      (Matrix.le_iff.1 (h x hx hB).1).submatrix e
  · simpa [Matrix.le_iff, submatrix_sub, submatrix_smul, submatrix_one e he] using
      (Matrix.le_iff.1 (h x hx hB).2).submatrix e
variable [Fintype n]
theorem inv (hG : IsLogBounded S w U G) : IsLogBounded S w U fun x => (G x)⁻¹ := by
  intro K hKU hK
  obtain ⟨C, N, hC, h⟩ := hG K hKU hK
  exact ⟨C, N, hC, fun x hx hB => inv_smul_one_le_inv_and_inv_le_smul_one
    (mul_pos hC (pow_pos (logWeight_pos _ _) _)) (h x hx hB)⟩
theorem hasLogGrowthEntries_inv (hG : IsLogBounded S w U G) :
    HasLogGrowthEntries S w U fun x => (G x)⁻¹ :=
  hG.inv.hasLogGrowthEntries
theorem of_trace (h0 : ∀ x ∈ U, x ∉ coordDivisor S w → (G x).PosDef)
    (h1 : HasLogGrowth S w U fun x => (G x).trace)
    (h2 : HasLogGrowth S w U fun x => (G x)⁻¹.trace) : IsLogBounded S w U G := by
  refine of_le (((HasLogGrowth.const (1 : ℝ)).add h1.norm).add h2.norm) fun x hx hB => ?_
  have hp : 0 < 1 + ‖(G x).trace‖ + ‖(G x)⁻¹.trace‖ := by positivity
  have hG := h0 x hx hB
  let _ := hG.isUnit.invertible
  refine ⟨hp, ?_, (le_re_trace_smul_one_of_posSemidef hG.posSemidef).trans
    (real_smul_one_le_real_smul_one ?_)⟩
  · have h3 : (G x)⁻¹ ≤ (1 + ‖(G x).trace‖ + ‖(G x)⁻¹.trace‖) • (1 : Matrix n n ℂ) :=
      (le_re_trace_smul_one_of_posSemidef hG.inv.posSemidef).trans
        (real_smul_one_le_real_smul_one (by
          linarith [RCLike.re_le_norm (G x)⁻¹.trace, norm_nonneg (G x).trace]))
    have h4 := inv_le_inv_of_posDef_of_le hG.inv h3
    rwa [inv_real_smul_of_posDef PosDef.one hp.ne', inv_one, inv_inv_of_invertible] at h4
  · linarith [RCLike.re_le_norm (G x).trace, norm_nonneg (G x)⁻¹.trace]
end IsLogBounded
variable [Fintype n]
theorem isLogBounded_iff_entries : IsLogBounded S w U G ↔
    (∀ x ∈ U, x ∉ coordDivisor S w → (G x).PosDef) ∧ HasLogGrowthEntries S w U G ∧
      HasLogGrowthEntries S w U fun x => (G x)⁻¹ :=
  ⟨fun h => ⟨fun _ => h.posDef, h.hasLogGrowthEntries, h.hasLogGrowthEntries_inv⟩,
    fun ⟨h0, h1, h2⟩ => .of_trace h0 h1.trace h2.trace⟩
namespace IsLogBounded
end IsLogBounded
namespace IsLogBounded
variable [Fintype m]
theorem fromBlocks (hH : IsLogBounded S w U H) (hG : IsLogBounded S w U G) :
    IsLogBounded S w U fun x => Matrix.fromBlocks (H x) 0 0 (G x) := by
  have key : ∀ {H : X → Matrix m m ℂ} {G : X → Matrix n n ℂ}, IsLogBounded S w U H →
      IsLogBounded S w U G →
        HasLogGrowthEntries S w U fun x => Matrix.fromBlocks (H x) 0 0 (G x) := by
    rintro H G hH hG (i | i) (j | j)
    exacts [hH.hasLogGrowthEntries i j, .const 0, .const 0, hG.hasLogGrowthEntries i j]
  refine isLogBounded_iff_entries.2 ⟨fun x hx hB =>
    posDef_fromBlocks_zero (hH.posDef hx hB) (hG.posDef hx hB), key hH hG,
    (key hH.inv hG.inv).congr fun x hx hB => inv_eq_left_inv ?_⟩
  let _ := (hH.posDef hx hB).isUnit.invertible
  let _ := (hG.posDef hx hB).isUnit.invertible
  simp [fromBlocks_multiply]
theorem schurComplement₁₁ {G : X → Matrix (m ⊕ n) (m ⊕ n) ℂ} (hG : IsLogBounded S w U G) :
    IsLogBounded S w U fun x => schurComplement₁₁ (G x) :=
  (hG.inv.submatrix Sum.inr_injective).inv.congr fun _ hx hB =>
    schurComplement₁₁_eq_inv (hG.posDef hx hB)
end IsLogBounded
end LogBounded
section Examples
example : lwP₂ (Finset.univ : Finset (Fin 2)) ![(Real.exp (-1) : ℝ), (Real.exp 2 : ℝ)] = 4 := by
  simp only [lwP₂, Fin.sum_univ_two, cons_val_zero, cons_val_one, Complex.norm_real,
    Real.norm_eq_abs, Real.abs_exp, Real.log_exp]
  norm_num
example : schurComplement₁₁ (fromBlocks !![2] !![Complex.I] !![-Complex.I] !![1]) = !![1 / 2] := by
  ext i j
  fin_cases i; fin_cases j
  simp [schurComplement₁₁, Matrix.mul_apply, Matrix.inv_def]
  ring_nf
  simp
  norm_num
end Examples
end GlobalTheory


