-- Prove2me | solution 1 for ApproxSyzygies.Smoothed.proposition_4_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T22:27:38.861924+00:00
-- url     : https://prove2.me/submissions/9c04565c-340c-437e-b273-152da1d95a34

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Anticoncentration
import Theorems.Thm_ApproxSyzygies_Smoothed_lemma_4_7

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Module

namespace ApproxSyzygies.Smoothed.Dev.P48

open ApproxSyzygies.Smoothed

section Frame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A frame: pairwise orthogonal vectors, each of norm `0` or `1`. -/
def IsFrame {k : ℕ} (v : Fin k → E) : Prop :=
  (∀ a b, inner ℝ (v a) (v b) = if a = b then inner ℝ (v a) (v a) else 0) ∧
    ∀ a, ‖v a‖ = 0 ∨ ‖v a‖ = 1

/-- The projection `∑ₐ ⟪vₐ, g⟫ vₐ`. -/
noncomputable def proj {k : ℕ} (v : Fin k → E) (g : E) : E :=
  ∑ a, inner ℝ (v a) g • v a

lemma proj_mem {k : ℕ} (v : Fin k → E) (g : E) : proj v g ∈ Submodule.span ℝ (Set.range v) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

lemma inner_sub_proj {k : ℕ} {v : Fin k → E} (hv : IsFrame v) (g : E) (a : Fin k) :
    inner ℝ (v a) (g - proj v g) = 0 := by
  rw [inner_sub_right, proj, inner_sum]
  rw [Finset.sum_congr rfl (fun b _ => by rw [inner_smul_right, hv.1 a b])]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rcases hv.2 a with h | h
  · rw [norm_eq_zero.1 h]; simp
  · rw [real_inner_self_eq_norm_sq, h]; ring

lemma inner_sub_proj_of_mem {k : ℕ} {v : Fin k → E} (hv : IsFrame v) (g : E) {z : E}
    (hz : z ∈ Submodule.span ℝ (Set.range v)) : inner ℝ z (g - proj v g) = 0 := by
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact inner_sub_proj hv g a
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

lemma norm_sub_proj_le {k : ℕ} {v : Fin k → E} (hv : IsFrame v) (g : E) {z : E}
    (hz : z ∈ Submodule.span ℝ (Set.range v)) : ‖g - proj v g‖ ≤ ‖g - z‖ := by
  have hmem : proj v g - z ∈ Submodule.span ℝ (Set.range v) :=
    Submodule.sub_mem _ (proj_mem v g) hz
  have h0 : inner ℝ (g - proj v g) (proj v g - z) = 0 := by
    rw [real_inner_comm]; exact inner_sub_proj_of_mem hv g hmem
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real h0
  have he : g - proj v g + (proj v g - z) = g - z := by abel
  rw [he] at h
  have : ‖g - proj v g‖ ^ 2 ≤ ‖g - z‖ ^ 2 := by nlinarith [norm_nonneg (proj v g - z)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

lemma norm_proj_le {k : ℕ} {v : Fin k → E} (hv : IsFrame v) (g : E) : ‖proj v g‖ ≤ ‖g‖ := by
  have h0 : inner ℝ (proj v g) (g - proj v g) = 0 := inner_sub_proj_of_mem hv g (proj_mem v g)
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real h0
  have he : proj v g + (g - proj v g) = g := by abel
  rw [he] at h
  have : ‖proj v g‖ ^ 2 ≤ ‖g‖ ^ 2 := by nlinarith [norm_nonneg (g - proj v g)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

lemma proj_eq_self {k : ℕ} {v : Fin k → E} (hv : IsFrame v) {g : E}
    (hg : g ∈ Submodule.span ℝ (Set.range v)) : proj v g = g := by
  have h := norm_sub_proj_le hv g hg
  rw [sub_self, norm_zero] at h
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h)).symm

lemma proj_of_isEmpty {k : ℕ} (hk : k = 0) (v : Fin k → E) (g : E) : proj v g = 0 := by
  subst hk; simp [proj]

lemma continuous_proj {X : Type*} [TopologicalSpace X] {k : ℕ} {v : X → Fin k → E} {g : X → E}
    (hv : Continuous v) (hg : Continuous g) : Continuous fun x => proj (v x) (g x) := by
  unfold proj
  refine continuous_finsetSum _ fun a _ => ?_
  have hva : Continuous fun x => v x a := (continuous_apply a).comp hv
  exact (hva.inner hg).smul hva

lemma isFrame_of_orthonormal {k : ℕ} {v : Fin k → E} (hv : Orthonormal ℝ v) : IsFrame v := by
  classical
  refine ⟨fun a b => ?_, fun a => Or.inr (hv.1 a)⟩
  rw [orthonormal_iff_ite.1 hv a b, orthonormal_iff_ite.1 hv a a]
  by_cases h : a = b <;> simp [h]

lemma isFrame_zero {k : ℕ} : IsFrame (fun _ : Fin k => (0 : E)) :=
  ⟨fun a b => by split_ifs <;> simp, fun _ => Or.inl norm_zero⟩

lemma isClosed_isFrame (k : ℕ) : IsClosed {v : Fin k → E | IsFrame v} := by
  have h1 : IsClosed {v : Fin k → E |
      ∀ a b, inner ℝ (v a) (v b) = if a = b then inner ℝ (v a) (v a) else 0} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
    have ha : Continuous fun v : Fin k → E => v a := continuous_apply a
    have hb : Continuous fun v : Fin k → E => v b := continuous_apply b
    split_ifs
    · exact isClosed_eq (ha.inner hb) (ha.inner ha)
    · exact isClosed_eq (ha.inner hb) continuous_const
  have h2 : IsClosed {v : Fin k → E | ∀ a, ‖v a‖ = 0 ∨ ‖v a‖ = 1} := by
    simp only [Set.ofPred_forall, Set.ofPred_or]
    refine isClosed_iInter fun a => ?_
    have ha : Continuous fun v : Fin k → E => ‖v a‖ := (continuous_apply a).norm
    exact (isClosed_eq ha continuous_const).union (isClosed_eq ha continuous_const)
  exact h1.inter h2

lemma isCompact_isFrame [FiniteDimensional ℝ E] (k : ℕ) :
    IsCompact {v : Fin k → E | IsFrame v} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_isFrame k) ?_
  refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun v hv => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  rcases hv.2 a with h | h <;> rw [h]; exact zero_le_one

end Frame

/-- Projection of a closed set along a compact factor is closed. -/
lemma isClosed_exists_mem_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} (hK : IsCompact K) {F : Set (X × Y)} (hF : IsClosed F) :
    IsClosed {y | ∃ x ∈ K, (x, y) ∈ F} := by
  have := isCompact_iff_compactSpace.mp hK
  have hc : Continuous fun p : K × Y => ((p.1 : X), p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have h := isClosedMap_snd_of_compactSpace (X := K) (Y := Y) _ (hF.preimage hc)
  convert h using 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage, Prod.exists]
  constructor
  · rintro ⟨x, hx, hxy⟩; exact ⟨⟨x, hx⟩, y, hxy, rfl⟩
  · rintro ⟨x, y', hxy, rfl⟩; exact ⟨x, x.2, hxy⟩

section Tens

variable {ι κ : Type} [Fintype ι] [Fintype κ]

lemma norm_tens (u : EuclideanSpace ℝ ι) (w : EuclideanSpace ℝ κ) :
    ‖tens u w‖ = ‖u‖ * ‖w‖ := by
  have h : ‖tens u w‖ ^ 2 = (‖u‖ * ‖w‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp [tens, mul_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

lemma tens_sub (u : EuclideanSpace ℝ ι) (w w' : EuclideanSpace ℝ κ) :
    tens u w - tens u w' = tens u (w - w') := by
  ext p; simp [tens, mul_sub]

lemma continuous_tens {X : Type*} [TopologicalSpace X] {u : X → EuclideanSpace ℝ ι}
    {w : X → EuclideanSpace ℝ κ} (hu : Continuous u) (hw : Continuous w) :
    Continuous fun x => tens (u x) (w x) := by
  unfold tens
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => ?_)
  exact ((PiLp.continuous_apply 2 _ p.1).comp hu).mul ((PiLp.continuous_apply 2 _ p.2).comp hw)

end Tens

end ApproxSyzygies.Smoothed.Dev.P48
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Module

namespace ApproxSyzygies.Smoothed.Dev.P48

open ApproxSyzygies.Smoothed

variable {m L : ℕ} {ι : Fin L → Fin m → Type} [∀ ℓ i, Fintype (ι ℓ i)]
  {κ : Fin m → Type} [∀ i, Fintype (κ i)]

/-- The ambient space `W = ⨁ᵢ Wᵢ`. -/
abbrev Wsp (κ : Fin m → Type) [∀ i, Fintype (κ i)] : Type :=
  PiLp 2 fun i => EuclideanSpace ℝ (κ i)

/-- The data of block `ℓ`: the vectors `ζᵢ` and the images `Cᵢ(b_k)` of a basis of `G₀`. -/
abbrev Dat (ι : Fin L → Fin m → Type) [∀ ℓ i, Fintype (ι ℓ i)] (κ : Fin m → Type)
    [∀ i, Fintype (κ i)] (d : ℕ) (ℓ : Fin L) : Type :=
  (∀ i, EuclideanSpace ℝ (ι ℓ i)) × (∀ i, Fin d → EuclideanSpace ℝ (ι ℓ i × κ i))

/-- The residual `‖ζᵢ ⊗ hᵢ + Cᵢ(Π h)‖` written through the data. -/
noncomputable def res {d : ℕ} (bW : Fin d → Wsp κ) {ℓ : Fin L} (t : Dat ι κ d ℓ) (i : Fin m)
    (h : Wsp κ) : ℝ :=
  ‖tens (t.1 i) (h i) + ∑ k, inner ℝ (bW k) h • t.2 i k‖

/-- One shrinking step from `span v` to `span v'`. -/
def Step {d : ℕ} (Q : ℝ) (bW : Fin d → Wsp κ) {ℓ : Fin L} (t : Dat ι κ d ℓ) {k k' : ℕ}
    (v : Fin k → Wsp κ) (v' : Fin k' → Wsp κ) : Prop :=
  ∀ g : Wsp κ, ∃ i, ‖proj v g - proj v' (proj v g)‖ ≤ Q * res bW t i (proj v g)

/-- The first `j` steps can be carried out. -/
def Good (kk : Fin (L + 1) → ℕ) (Q : ℝ) (bW : Fin (kk 0) → Wsp κ) (j : ℕ)
    (θ : ∀ ℓ, Dat ι κ (kk 0) ℓ) : Prop :=
  ∃ V : (j : Fin (L + 1)) → Fin (kk j) → Wsp κ, (∀ j, IsFrame (V j)) ∧ V 0 = bW ∧
    ∀ ℓ : Fin L, ℓ.val < j → Step Q bW (θ ℓ) (V ℓ.castSucc) (V ℓ.succ)

lemma continuous_res {X : Type*} [TopologicalSpace X] {d : ℕ} (bW : Fin d → Wsp κ) {ℓ : Fin L}
    {t : X → Dat ι κ d ℓ} {h : X → Wsp κ} (ht : Continuous t) (hh : Continuous h) (i : Fin m) :
    Continuous fun x => res bW (t x) i (h x) := by
  unfold res
  refine Continuous.norm (Continuous.add ?_ ?_)
  · exact continuous_tens ((continuous_apply i).comp (continuous_fst.comp ht))
      ((PiLp.continuous_apply 2 _ i).comp hh)
  · refine continuous_finsetSum _ fun k _ => ?_
    exact ((Continuous.inner (𝕜 := ℝ) continuous_const hh)).smul
      ((continuous_apply k).comp ((continuous_apply i).comp (continuous_snd.comp ht)))

lemma good_congr (kk : Fin (L + 1) → ℕ) (Q : ℝ) (bW : Fin (kk 0) → Wsp κ) (j : ℕ)
    {θ θ' : ∀ ℓ, Dat ι κ (kk 0) ℓ} (h : ∀ ℓ : Fin L, ℓ.val < j → θ ℓ = θ' ℓ) :
    Good kk Q bW j θ ↔ Good kk Q bW j θ' := by
  constructor
  · rintro ⟨V, h1, h2, h3⟩
    exact ⟨V, h1, h2, fun ℓ hℓ => h ℓ hℓ ▸ h3 ℓ hℓ⟩
  · rintro ⟨V, h1, h2, h3⟩
    exact ⟨V, h1, h2, fun ℓ hℓ => (h ℓ hℓ).symm ▸ h3 ℓ hℓ⟩

lemma good_zero (kk : Fin (L + 1) → ℕ) (Q : ℝ) (bW : Fin (kk 0) → Wsp κ) (hb : IsFrame bW)
    (θ : ∀ ℓ, Dat ι κ (kk 0) ℓ) : Good kk Q bW 0 θ := by
  classical
  refine ⟨Function.update (fun j => fun _ => 0) 0 bW, fun j => ?_, by simp, fun ℓ h => absurd h
    (Nat.not_lt_zero _)⟩
  by_cases hj : j = 0
  · subst hj; simpa using hb
  · rw [Function.update_of_ne hj]; exact isFrame_zero

lemma isClosed_good (kk : Fin (L + 1) → ℕ) (Q : ℝ) (bW : Fin (kk 0) → Wsp κ) (j : ℕ) :
    IsClosed {θ : ∀ ℓ, Dat ι κ (kk 0) ℓ | Good kk Q bW j θ} := by
  set K : Set ((j : Fin (L + 1)) → Fin (kk j) → Wsp κ) :=
    (Set.pi Set.univ fun j => {v | IsFrame v}) ∩ {V | V 0 = bW} with hK
  have hKc : IsCompact K :=
    (isCompact_univ_pi fun j => isCompact_isFrame _).inter_right
      (isClosed_eq (continuous_apply 0) continuous_const)
  set F : Set (((j : Fin (L + 1)) → Fin (kk j) → Wsp κ) × (∀ ℓ, Dat ι κ (kk 0) ℓ)) :=
    {p | ∀ ℓ : Fin L, ℓ.val < j → Step Q bW (p.2 ℓ) (p.1 ℓ.castSucc) (p.1 ℓ.succ)} with hF
  have hFc : IsClosed F := by
    rw [hF]
    simp only [Step, Set.ofPred_forall, Set.ofPred_exists]
    refine isClosed_iInter fun ℓ => isClosed_iInter fun _ => isClosed_iInter fun g =>
      isClosed_iUnion_of_finite fun i => ?_
    have hv : Continuous fun p : ((j : Fin (L + 1)) → Fin (kk j) → Wsp κ) ×
        (∀ ℓ, Dat ι κ (kk 0) ℓ) => p.1 ℓ.castSucc := (continuous_apply _).comp continuous_fst
    have hv' : Continuous fun p : ((j : Fin (L + 1)) → Fin (kk j) → Wsp κ) ×
        (∀ ℓ, Dat ι κ (kk 0) ℓ) => p.1 ℓ.succ := (continuous_apply _).comp continuous_fst
    have hpg := continuous_proj hv continuous_const (g := fun _ => g)
    exact isClosed_le (Continuous.norm (hpg.sub (continuous_proj hv' hpg)))
      (continuous_const.mul (continuous_res bW ((continuous_apply ℓ).comp continuous_snd) hpg i))
  convert isClosed_exists_mem_compact hKc hFc using 1
  ext θ
  simp only [Set.mem_ofPred_eq, Good, hK, hF, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
    forall_true_left]
  constructor
  · rintro ⟨V, h1, h2, h3⟩; exact ⟨V, ⟨h1, h2⟩, h3⟩
  · rintro ⟨V, ⟨h1, h2⟩, h3⟩; exact ⟨V, h1, h2, h3⟩

/-- The iterates `g⁽ʲ⁾`. -/
noncomputable def gseq {kk : Fin (L + 1) → ℕ} (V : (j : Fin (L + 1)) → Fin (kk j) → Wsp κ)
    (g : Wsp κ) : ℕ → Wsp κ
  | 0 => proj (V 0) g
  | j + 1 => if h : j + 1 < L + 1 then proj (V ⟨j + 1, h⟩) (gseq V g j) else gseq V g j

lemma iterate {kk : Fin (L + 1) → ℕ} {Q β η : ℝ} {bW : Fin (kk 0) → Wsp κ}
    {θ : ∀ ℓ, Dat ι κ (kk 0) ℓ} (hQ : 0 ≤ Q) (hβ : 0 ≤ β)
    (V : (j : Fin (L + 1)) → Fin (kk j) → Wsp κ) (hV0 : V 0 = bW)
    (hst : ∀ ℓ : Fin L, Step Q bW (θ ℓ) (V ℓ.castSucc) (V ℓ.succ))
    (hlast : kk (Fin.last L) = 0) (g : Wsp κ) (hg : proj bW g = g)
    (hres : ∀ ℓ i, res bW (θ ℓ) i g ≤ η)
    (hlip : ∀ ℓ i x, res bW (θ ℓ) i x ≤ res bW (θ ℓ) i g + β * ‖x - g‖) :
    β * ‖g‖ + η ≤ η * (1 + β * Q) ^ L := by
  have key : ∀ j : ℕ, (hj : j ≤ L) →
      (∃ g', gseq V g j = proj (V ⟨j, Nat.lt_succ_of_le hj⟩) g') ∧
        β * ‖g - gseq V g j‖ + η ≤ η * (1 + β * Q) ^ j := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨⟨g, rfl⟩, ?_⟩
      have : gseq V g 0 = g := by simp only [gseq, hV0, hg]
      rw [this]; simp
    | succ j ih =>
      intro hj
      obtain ⟨⟨g', hg'⟩, hb⟩ := ih (by omega)
      have hdef : gseq V g (j + 1) = proj (V ⟨j + 1, by omega⟩) (gseq V g j) := by
        simp only [gseq, dif_pos (show j + 1 < L + 1 by omega)]
      refine ⟨⟨gseq V g j, hdef⟩, ?_⟩
      set ℓ : Fin L := ⟨j, by omega⟩
      obtain ⟨i, hi⟩ := hst ℓ g'
      have e1 : (ℓ.castSucc : Fin (L + 1)) = ⟨j, by omega⟩ := rfl
      have e2 : (ℓ.succ : Fin (L + 1)) = ⟨j + 1, by omega⟩ := rfl
      rw [e1, e2, ← hg', ← hdef] at hi
      set x := gseq V g j
      have hstep : ‖x - gseq V g (j + 1)‖ ≤ Q * (η + β * ‖g - x‖) := by
        refine hi.trans (mul_le_mul_of_nonneg_left ?_ hQ)
        rw [← norm_neg (g - x), neg_sub]
        exact (hlip ℓ i x).trans (by linarith [hres ℓ i])
      have htri : ‖g - gseq V g (j + 1)‖ ≤ ‖g - x‖ + ‖x - gseq V g (j + 1)‖ := by
        have := norm_add_le (g - x) (x - gseq V g (j + 1))
        rwa [sub_add_sub_cancel] at this
      have hs := norm_nonneg (g - x)
      calc β * ‖g - gseq V g (j + 1)‖ + η
          ≤ β * (‖g - x‖ + Q * (η + β * ‖g - x‖)) + η := by
            gcongr; exact htri.trans (by linarith)
        _ = (1 + β * Q) * (β * ‖g - x‖ + η) := by ring
        _ ≤ (1 + β * Q) * (η * (1 + β * Q) ^ j) := by
            gcongr
        _ = η * (1 + β * Q) ^ (j + 1) := by ring
  obtain ⟨⟨g', hg'⟩, hb⟩ := key L le_rfl
  have h0 : gseq V g L = 0 := by
    rw [hg']; exact proj_of_isEmpty hlast _ _
  rwa [h0, sub_zero] at hb

/-- The deterministic dimension sequence. -/
noncomputable def kseq (d : ℕ) (n : ℕ → Fin m → ℕ) : ℕ → ℕ
  | 0 => d
  | j + 1 => min (kseq d n j) ⌊2 * ∑ i, (kseq d n j : ℝ) / (n j i : ℝ)⌋₊

lemma kseq_le (d : ℕ) (n : ℕ → Fin m → ℕ) (j : ℕ) :
    (kseq d n j : ℝ) ≤ d * ∏ t ∈ Finset.range j, (2 * ∑ i, (1 : ℝ) / (n t i : ℝ)) := by
  induction j with
  | zero => simp [kseq]
  | succ j ih =>
    have ha : 0 ≤ 2 * ∑ i, (1 : ℝ) / (n j i : ℝ) := by positivity
    calc (kseq d n (j + 1) : ℝ) ≤ ⌊2 * ∑ i, (kseq d n j : ℝ) / (n j i : ℝ)⌋₊ := by
          simp [kseq]
      _ ≤ 2 * ∑ i, (kseq d n j : ℝ) / (n j i : ℝ) := Nat.floor_le (by positivity)
      _ = (kseq d n j : ℝ) * (2 * ∑ i, (1 : ℝ) / (n j i : ℝ)) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ (d * ∏ t ∈ Finset.range j, (2 * ∑ i, (1 : ℝ) / (n t i : ℝ))) *
            (2 * ∑ i, (1 : ℝ) / (n j i : ℝ)) := mul_le_mul_of_nonneg_right ih ha
      _ = d * ∏ t ∈ Finset.range (j + 1), (2 * ∑ i, (1 : ℝ) / (n t i : ℝ)) := by
          rw [Finset.prod_range_succ]; ring

end ApproxSyzygies.Smoothed.Dev.P48
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Module

namespace ApproxSyzygies.Smoothed.Dev.P48

open ApproxSyzygies.Smoothed

section Pad

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An orthonormal family padded with zeros. -/
noncomputable def pad {r : ℕ} (k : ℕ) (e : Fin r → E) : Fin k → E :=
  fun a => if h : a.val < r then e ⟨a.val, h⟩ else 0

lemma isFrame_pad {r : ℕ} (k : ℕ) {e : Fin r → E} (he : Orthonormal ℝ e) : IsFrame (pad k e) := by
  classical
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · unfold pad
    by_cases ha : a.val < r <;> by_cases hb : b.val < r
    · simp only [ha, hb, dif_pos]
      rw [orthonormal_iff_ite.1 he, orthonormal_iff_ite.1 he]
      by_cases hab : a = b
      · subst hab; simp
      · have : (⟨a.val, ha⟩ : Fin r) ≠ ⟨b.val, hb⟩ := fun h => hab (Fin.ext (Fin.mk.inj h))
        simp [hab, this]
    · have hab : a ≠ b := fun h => hb (h ▸ ha)
      simp [ha, hb, hab]
    · simp [ha, hb]
    · simp [ha, hb]
  · unfold pad
    by_cases ha : a.val < r
    · simp only [ha, dif_pos]; exact Or.inr (he.1 _)
    · simp only [ha, dif_neg, not_false_eq_true, norm_zero, true_or]

lemma mem_span_pad {r k : ℕ} (hrk : r ≤ k) (e : Fin r → E) (c : Fin r) :
    e c ∈ Submodule.span ℝ (Set.range (pad k e)) := by
  refine Submodule.subset_span ⟨⟨c.val, lt_of_lt_of_le c.2 hrk⟩, ?_⟩
  simp [pad, c.2]

end Pad

variable {m L : ℕ} {ι : Fin L → Fin m → Type} [∀ ℓ i, Fintype (ι ℓ i)]
  {κ : Fin m → Type} [∀ i, Fintype (κ i)]

lemma indep_coord {β : Fin m → Type} [∀ i, MeasurableSpace (β i)] (μ : ∀ i, Measure (β i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin m) :
    Indep (MeasurableSpace.comap (fun y : ∀ j, β j => y i) inferInstance)
      (MeasurableSpace.comap (fun (y : ∀ j, β j) (j : {j : Fin m // j ≠ i}) => y j) inferInstance)
      (Measure.pi μ) := by
  have hind : iIndepFun (fun j (y : ∀ j, β j) => y j) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  rw [iIndepFun_iff_iIndep] at hind
  have h := indep_iSup_of_disjoint (fun j => (measurable_pi_apply j).comap_le) hind
    (S := {i}) (T := {i}ᶜ) (Set.disjoint_singleton_left.2 (fun h => h rfl))
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · exact le_iSup₂ (f := fun j (_ : j ∈ ({i} : Set (Fin m))) =>
      MeasurableSpace.comap (fun y : ∀ j, β j => y j) inferInstance) i rfl
  · show MeasurableSpace.comap _ MeasurableSpace.pi ≤ _
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun j => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂ (f := fun j (_ : j ∈ ({i}ᶜ : Set (Fin m))) =>
      MeasurableSpace.comap (fun y : ∀ j, β j => y j) inferInstance) j.val j.2

/-- For a fixed past at which the first `ℓ` steps succeed, the block-`ℓ` values at which step
`ℓ` fails have probability at most `m e^{-γ}`: Lemma 4.7 on the product space. -/
lemma section_bound (hm : 0 < m) (kk : Fin (L + 1) → ℕ) (Q η₀ γ : ℝ)
    (bW : Fin (kk 0) → Wsp κ) (ℓ : Fin L)
    (θ₀ : ∀ ℓ, Dat ι κ (kk 0) ℓ) (hgood : Good kk Q bW ℓ.val θ₀)
    (ν : ∀ i, ProbabilityMeasure (EuclideanSpace ℝ (ι ℓ i)))
    (hsa : ∀ i, SubspaceAnticonc (1 / 4) η₀ γ (ν i : Measure (EuclideanSpace ℝ (ι ℓ i))))
    (hdim : ∀ i, 4 ≤ Fintype.card (ι ℓ i))
    (Φ : ∀ i, Fin (kk 0) → ((j : {j : Fin m // j ≠ i}) → EuclideanSpace ℝ (ι ℓ j)) →
      EuclideanSpace ℝ (ι ℓ i × κ i))
    (hΦ : ∀ i k, Measurable (Φ i k))
    (hk : ∀ r : ℕ, r ≤ kk ℓ.castSucc →
      (r : ℝ) ≤ 2 * ∑ i, (kk ℓ.castSucc : ℝ) / (Fintype.card (ι ℓ i) : ℝ) → r ≤ kk ℓ.succ)
    (hQ : Real.sqrt (∑ i, ((Fintype.card (ι ℓ i) : ℝ)) ^ 2) / η₀ ≤ Q) :
    (Measure.pi fun i => (ν i : Measure (EuclideanSpace ℝ (ι ℓ i))))
      {y | ¬ Good kk Q bW (ℓ.val + 1)
        (Function.update θ₀ ℓ (y, fun i k => Φ i k (fun j => y j)))}
      ≤ ENNReal.ofReal (m * Real.exp (-γ)) := by
  classical
  obtain ⟨V, hVf, hV0, hVst⟩ := hgood
  set G : Submodule ℝ (Wsp κ) := Submodule.span ℝ (Set.range (V ℓ.castSucc)) with hGdef
  have hG : finrank ℝ G ≤ kk ℓ.castSucc := by
    have := finrank_range_le_card (R := ℝ) (V ℓ.castSucc)
    simpa [Set.finrank] using this
  set μ := Measure.pi fun i => (ν i : Measure (EuclideanSpace ℝ (ι ℓ i))) with hμ
  let Cl : ∀ i, (∀ j, EuclideanSpace ℝ (ι ℓ j)) → (G →ₗ[ℝ] EuclideanSpace ℝ (ι ℓ i × κ i)) :=
    fun i y =>
    { toFun := fun h => ∑ k, inner ℝ (bW k) (h : Wsp κ) • Φ i k (fun j => y j)
      map_add' := fun a b => by
        simp only [Submodule.coe_add, inner_add_right, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul, inner_smul_right, mul_smul, RingHom.id_apply,
          Finset.smul_sum] }
  let C : ∀ i, (∀ j, EuclideanSpace ℝ (ι ℓ j)) → (G →L[ℝ] EuclideanSpace ℝ (ι ℓ i × κ i)) :=
    fun i y => LinearMap.toContinuousLinearMap (Cl i y)
  have hCapp : ∀ i y (h : G), C i y h = ∑ k, inner ℝ (bW k) (h : Wsp κ) • Φ i k (fun j => y j) :=
    fun _ _ _ => rfl
  have hind : iIndepFun (fun i (y : ∀ j, EuclideanSpace ℝ (ι ℓ j)) => y i) μ :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hsa' : ∀ i, SubspaceAnticonc (1 / 4) η₀ γ
      (μ.map fun y : ∀ j, EuclideanSpace ℝ (ι ℓ j) => y i) := by
    intro i
    have := (measurePreserving_eval (fun i => (ν i : Measure (EuclideanSpace ℝ (ι ℓ i)))) i).map_eq
    rw [hμ]
    convert hsa i
  have h47 := lemma_4_7 (ι := ι ℓ) (κ := κ) G (kk ℓ.castSucc) hG η₀ γ μ
    (fun i y => y i) (fun i => measurable_pi_apply i) hind hsa' hdim C
    (fun i => MeasurableSpace.comap
      (fun (y : ∀ j, EuclideanSpace ℝ (ι ℓ j)) (j : {j : Fin m // j ≠ i}) => y j) inferInstance)
    (fun i => (measurable_pi_lambda _ fun j => measurable_pi_apply _).comap_le)
    (fun i g => by
      simp only [hCapp]
      have hm' : Measurable fun z : ((j : {j : Fin m // j ≠ i}) → EuclideanSpace ℝ (ι ℓ j)) =>
          ∑ k, inner ℝ (bW k) (g : Wsp κ) • Φ i k z :=
        Finset.measurable_sum _ fun k _ => by have := hΦ i k; fun_prop
      exact hm'.comp (comap_measurable _))
    (fun i => indep_coord _ i)
  refine le_trans (measure_mono ?_) h47
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy ⊢
  intro hex
  apply hy
  obtain ⟨G', hG'G, hG'dim, hG'⟩ := hex
  set r := finrank ℝ G'
  let e : Fin r → Wsp κ := fun c => ((stdOrthonormalBasis ℝ G') c : Wsp κ)
  have he : Orthonormal ℝ e := (stdOrthonormalBasis ℝ G').orthonormal.comp_linearIsometry G'.subtypeₗᵢ
  have hr : r ≤ kk ℓ.succ := by
    refine hk r ((Submodule.finrank_mono hG'G).trans hG) ?_
    exact hG'dim
  set v' : Fin (kk ℓ.succ) → Wsp κ := pad (kk ℓ.succ) e
  have hv' : IsFrame v' := isFrame_pad _ he
  have hG'sp : ∀ z ∈ G', z ∈ Submodule.span ℝ (Set.range v') := by
    intro z hz
    have hsum := congrArg Subtype.val ((stdOrthonormalBasis ℝ G').sum_repr ⟨z, hz⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    rw [← hsum]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (mem_span_pad hr e c)
  refine ⟨Function.update V ℓ.succ v', fun j => ?_, ?_, fun ℓ' hℓ' => ?_⟩
  · by_cases hj : j = ℓ.succ
    · subst hj; rw [Function.update_self]; exact hv'
    · rw [Function.update_of_ne hj]; exact hVf j
  · rw [Function.update_of_ne (Fin.succ_ne_zero ℓ).symm]; exact hV0
  · have hcs : ℓ'.castSucc ≠ ℓ.succ := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    rw [Function.update_of_ne hcs]
    rcases eq_or_ne ℓ' ℓ with rfl | hne
    · rw [Function.update_self, Function.update_self]
      intro g
      set h := proj (V ℓ'.castSucc) g
      have hmem : h ∈ G := proj_mem _ g
      obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ
        (fun i => res bW (ℓ := ℓ') (y, fun i k => Φ i k (fun j => y j)) i h)
        ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      refine ⟨i₀, ?_⟩
      set η := res bW (ℓ := ℓ') (y, fun i k => Φ i k (fun j => y j)) i₀ h
      have hη : 0 ≤ η := norm_nonneg _
      have hb := hG' η ⟨h, hmem⟩ (fun i => hi₀ i (Finset.mem_univ _))
      have h1 : ‖h - proj v' h‖ ≤ Metric.infDist h G' := by
        refine (Metric.le_infDist ⟨0, G'.zero_mem⟩).2 fun z hz => ?_
        rw [dist_eq_norm]
        exact norm_sub_proj_le hv' h (hG'sp z hz)
      refine h1.trans (hb.trans ?_)
      rw [mul_div_assoc, mul_comm Q]
      exact mul_le_mul_of_nonneg_left hQ hη
    · have hs : ℓ'.succ ≠ ℓ.succ := fun h => hne (Fin.succ_inj.1 h)
      rw [Function.update_of_ne hs, Function.update_of_ne hne]
      have hlt : ℓ'.val < ℓ.val := by
        have : ℓ'.val ≠ ℓ.val := fun h => hne (Fin.ext h)
        omega
      exact hVst ℓ' hlt

end ApproxSyzygies.Smoothed.Dev.P48
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Module

namespace ApproxSyzygies.Smoothed.Dev.P48

open ApproxSyzygies.Smoothed

variable {m L : ℕ} {ι : Fin L → Fin m → Type} [∀ ℓ i, Fintype (ι ℓ i)]
  {κ : Fin m → Type} [∀ i, Fintype (κ i)]

/-- The data `θ(ω)` of all blocks. -/
noncomputable def theta {G₀ : Submodule ℝ (Wsp κ)} {d : ℕ} (bG : Fin d → G₀) {Ω : Type}
    (ζ : ∀ ℓ i, Ω → EuclideanSpace ℝ (ι ℓ i))
    (C : ∀ ℓ i, Ω → (G₀ →L[ℝ] EuclideanSpace ℝ (ι ℓ i × κ i))) (ω : Ω) :
    ∀ ℓ, Dat ι κ d ℓ :=
  fun ℓ => (fun i => ζ ℓ i ω, fun i k => C ℓ i ω (bG k))

lemma prob_step (hm : 0 < m) (G₀ : Submodule ℝ (Wsp κ)) (kk : Fin (L + 1) → ℕ) (Q η₀ γ : ℝ)
    (bG : Fin (kk 0) → G₀) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ζ : ∀ ℓ i, Ω → EuclideanSpace ℝ (ι ℓ i)) (hζ : ∀ ℓ i, Measurable (ζ ℓ i)) (ℓ : Fin L)
    (hcond : ∀ᵐ x ∂(P.map fun ω (ℓ' : {ℓ' : Fin L // ℓ' < ℓ}) (i : Fin m) => ζ ℓ' i ω),
        ∃ ν : ∀ i, ProbabilityMeasure (EuclideanSpace ℝ (ι ℓ i)),
          (∀ i, SubspaceAnticonc (1 / 4) η₀ γ (ν i : Measure (EuclideanSpace ℝ (ι ℓ i)))) ∧
          condDistrib (fun ω (i : Fin m) => ζ ℓ i ω)
              (fun ω (ℓ' : {ℓ' : Fin L // ℓ' < ℓ}) (i : Fin m) => ζ ℓ' i ω) P x =
            Measure.pi fun i => (ν i : Measure (EuclideanSpace ℝ (ι ℓ i))))
    (hdim : ∀ i, 4 ≤ Fintype.card (ι ℓ i))
    (C : ∀ ℓ i, Ω → (G₀ →L[ℝ] EuclideanSpace ℝ (ι ℓ i × κ i)))
    (hCmeas : ∀ ℓ i (g : G₀),
      Measurable[MeasurableSpace.comap
          (fun ω => ((fun (ℓ' : {ℓ' : Fin L // ℓ' < ℓ}) (j : Fin m) => ζ ℓ' j ω),
            (fun j : {j : Fin m // j ≠ i} => ζ ℓ j ω))) inferInstance]
        fun ω => C ℓ i ω g)
    (hk : ∀ r : ℕ, r ≤ kk ℓ.castSucc →
      (r : ℝ) ≤ 2 * ∑ i, (kk ℓ.castSucc : ℝ) / (Fintype.card (ι ℓ i) : ℝ) → r ≤ kk ℓ.succ)
    (hQ : Real.sqrt (∑ i, ((Fintype.card (ι ℓ i) : ℝ)) ^ 2) / η₀ ≤ Q) :
    P ({ω | Good kk Q (fun k => (bG k : Wsp κ)) ℓ.val (theta bG ζ C ω)} \
        {ω | Good kk Q (fun k => (bG k : Wsp κ)) (ℓ.val + 1) (theta bG ζ C ω)})
      ≤ ENNReal.ofReal (m * Real.exp (-γ)) := by
  classical
  set bW : Fin (kk 0) → Wsp κ := fun k => (bG k : Wsp κ)
  set past : Ω → ((ℓ' : {ℓ' : Fin L // ℓ' < ℓ}) → (i : Fin m) → EuclideanSpace ℝ (ι ℓ' i)) :=
    fun ω ℓ' i => ζ ℓ' i ω with hpast
  set block : Ω → ((i : Fin m) → EuclideanSpace ℝ (ι ℓ i)) := fun ω i => ζ ℓ i ω with hblock
  have hpastm : Measurable past :=
    measurable_pi_lambda _ fun ℓ' => measurable_pi_lambda _ fun i => hζ ℓ'.1 i
  have hblockm : Measurable block := measurable_pi_lambda _ fun i => hζ ℓ i
  -- the past data as a function of `past`
  set θlt : Ω → ∀ ℓ', Dat ι κ (kk 0) ℓ' :=
    fun ω ℓ' => if ℓ' < ℓ then theta bG ζ C ω ℓ' else 0 with hθlt
  have hθltm : Measurable[MeasurableSpace.comap past inferInstance] θlt := by
    let _ : MeasurableSpace Ω := MeasurableSpace.comap past inferInstance
    refine measurable_pi_lambda _ fun ℓ' => ?_
    by_cases h : ℓ' < ℓ
    · simp only [hθlt, h, if_true, theta]
      refine Measurable.prodMk ?_ ?_
      · refine measurable_pi_lambda _ fun i => ?_
        have : (fun ω => ζ ℓ' i ω) = (fun x : ((ℓ' : {ℓ' : Fin L // ℓ' < ℓ}) → (i : Fin m) →
            EuclideanSpace ℝ (ι ℓ' i)) => x ⟨ℓ', h⟩ i) ∘ past := rfl
        rw [this]
        exact ((measurable_pi_apply _).comp (measurable_pi_apply _)).comp (comap_measurable _)
      · refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun k => ?_
        refine (hCmeas ℓ' i (bG k)).mono ?_ le_rfl
        have : (fun ω => ((fun (ℓ'' : {ℓ'' : Fin L // ℓ'' < ℓ'}) (j : Fin m) => ζ ℓ'' j ω),
            (fun j : {j : Fin m // j ≠ i} => ζ ℓ' j ω))) =
            (fun x : ((ℓ' : {ℓ' : Fin L // ℓ' < ℓ}) → (i : Fin m) → EuclideanSpace ℝ (ι ℓ' i)) =>
              ((fun (ℓ'' : {ℓ'' : Fin L // ℓ'' < ℓ'}) (j : Fin m) =>
                x ⟨ℓ''.1, lt_trans ℓ''.2 h⟩ j),
              (fun j : {j : Fin m // j ≠ i} => x ⟨ℓ', h⟩ j))) ∘ past := rfl
        rw [this, ← MeasurableSpace.comap_comp]
        refine MeasurableSpace.comap_mono (Measurable.comap_le ?_)
        refine Measurable.prodMk ?_ ?_
        · exact measurable_pi_lambda _ fun ℓ'' => measurable_pi_lambda _ fun j =>
            (measurable_pi_apply _).comp (measurable_pi_apply _)
        · exact measurable_pi_lambda _ fun j =>
            (measurable_pi_apply _).comp (measurable_pi_apply _)
    · simp only [hθlt, h, if_false]
      exact measurable_const
  have : ∀ ℓ', BorelSpace (Dat ι κ (kk 0) ℓ') := fun ℓ' => inferInstance
  have : ∀ ℓ', SecondCountableTopology (Dat ι κ (kk 0) ℓ') := fun ℓ' => inferInstance
  have : ∀ ℓ', StandardBorelSpace (Dat ι κ (kk 0) ℓ') := fun ℓ' => inferInstance
  obtain ⟨Ψ₁, hΨ₁, hΨ₁eq⟩ := hθltm.exists_eq_measurable_comp
  have hΦex := fun i k => (hCmeas ℓ i (bG k)).exists_eq_measurable_comp
  choose Φ hΦ hΦeq using hΦex
  set Ψ : ((ℓ' : {ℓ' : Fin L // ℓ' < ℓ}) → (i : Fin m) → EuclideanSpace ℝ (ι ℓ' i)) ×
      ((i : Fin m) → EuclideanSpace ℝ (ι ℓ i)) → ∀ ℓ', Dat ι κ (kk 0) ℓ' :=
    fun p => Function.update (Ψ₁ p.1) ℓ (p.2, fun i k => Φ i k (p.1, fun j => p.2 j)) with hΨ
  have hΨm : Measurable Ψ := by
    refine measurable_update'.comp ((hΨ₁.comp measurable_fst).prodMk ?_)
    refine measurable_snd.prodMk (measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun k => ?_)
    exact (hΦ i k).comp (measurable_fst.prodMk
      (measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp measurable_snd))
  set S := Ψ ⁻¹' ({θ | Good kk Q bW ℓ.val θ} \ {θ | Good kk Q bW (ℓ.val + 1) θ}) with hS
  have hSm : MeasurableSet S :=
    hΨm ((isClosed_good kk Q bW _).measurableSet.diff (isClosed_good kk Q bW _).measurableSet)
  -- agreement of the data
  have hagree : ∀ ω, ∀ ℓ' : Fin L, ℓ'.val < ℓ.val + 1 →
      theta bG ζ C ω ℓ' = Ψ (past ω, block ω) ℓ' := by
    intro ω ℓ' hℓ'
    rcases eq_or_ne ℓ' ℓ with rfl | hne
    · simp only [hΨ, Function.update_self, theta]
      congr 1
      funext i k
      exact congrFun (hΦeq i k) ω
    · simp only [hΨ, Function.update_of_ne hne]
      have hlt : ℓ' < ℓ := by
        have : ℓ'.val ≠ ℓ.val := fun h => hne (Fin.ext h)
        exact Fin.lt_def.2 (by omega)
      have := congrFun (congrFun hΨ₁eq ω) ℓ'
      simp only [Function.comp_apply, hθlt, hlt, if_true] at this
      exact this
  have hset : {ω | Good kk Q bW ℓ.val (theta bG ζ C ω)} \
      {ω | Good kk Q bW (ℓ.val + 1) (theta bG ζ C ω)} = (fun ω => (past ω, block ω)) ⁻¹' S := by
    ext ω
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_preimage, hS]
    rw [good_congr kk Q bW ℓ.val (fun ℓ' h => hagree ω ℓ' (by omega)),
      good_congr kk Q bW (ℓ.val + 1) (fun ℓ' h => hagree ω ℓ' h)]
  rw [hset, ← Measure.map_apply (hpastm.prodMk hblockm) hSm,
    ← compProd_map_condDistrib hblockm.aemeasurable, Measure.compProd_apply hSm]
  have hprob : IsProbabilityMeasure (P.map past) := Measure.isProbabilityMeasure_map hpastm.aemeasurable
  calc ∫⁻ x, condDistrib block past P x (Prod.mk x ⁻¹' S) ∂(P.map past)
      ≤ ∫⁻ _, ENNReal.ofReal (m * Real.exp (-γ)) ∂(P.map past) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hcond] with x ⟨ν, hν, hcd⟩
        rw [hcd]
        by_cases hx : Good kk Q bW ℓ.val (Ψ₁ x)
        · refine le_trans (measure_mono ?_)
            (section_bound hm kk Q η₀ γ bW ℓ (Ψ₁ x) hx ν hν hdim
              (fun i k z => Φ i k (x, z))
              (fun i k => (hΦ i k).comp measurable_prodMk_left) hk hQ)
          intro y hy
          simp only [Set.mem_preimage, hS, Set.mem_sdiff, Set.mem_ofPred_eq] at hy
          exact hy.2
        · have : Prod.mk x ⁻¹' S = ∅ := by
            ext y
            simp only [Set.mem_preimage, hS, Set.mem_sdiff, Set.mem_ofPred_eq,
              Set.mem_empty_iff_false, iff_false, not_and, not_not]
            intro hy
            refine absurd ((good_congr kk Q bW ℓ.val (θ' := Ψ₁ x) fun ℓ' h => ?_).1 hy) hx
            simp only [hΨ]
            exact Function.update_of_ne (fun e => by rw [e] at h; omega) _ _
          rw [this, measure_empty]; exact zero_le
    _ = ENNReal.ofReal (m * Real.exp (-γ)) := by
        rw [lintegral_const, measure_univ, mul_one]

end ApproxSyzygies.Smoothed.Dev.P48
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed.Dev.P48

open ApproxSyzygies.Smoothed

variable {m L : ℕ} {ι : Fin L → Fin m → Type} [∀ ℓ i, Fintype (ι ℓ i)]
  {κ : Fin m → Type} [∀ i, Fintype (κ i)]

/-- The projection onto `G₀` as an element of `G₀`. -/
noncomputable def pG {G₀ : Submodule ℝ (Wsp κ)} {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ G₀)
    (x : Wsp κ) : G₀ :=
  ∑ k, inner ℝ (b k : Wsp κ) x • b k

lemma coe_pG {G₀ : Submodule ℝ (Wsp κ)} {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ G₀)
    (x : Wsp κ) : (pG b x : Wsp κ) = proj (fun k => (b k : Wsp κ)) x := by
  simp [pG, proj]

lemma pG_coe {G₀ : Submodule ℝ (Wsp κ)} {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ G₀) (g : G₀) :
    pG b g = g := b.sum_repr' g

lemma pG_sub {G₀ : Submodule ℝ (Wsp κ)} {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ G₀)
    (x y : Wsp κ) : pG b x - pG b y = pG b (x - y) := by
  simp [pG, inner_sub_right, sub_smul, Finset.sum_sub_distrib]

lemma isFrame_basis {G₀ : Submodule ℝ (Wsp κ)} {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ G₀) :
    IsFrame (fun k => (b k : Wsp κ)) :=
  isFrame_of_orthonormal (b.orthonormal.comp_linearIsometry G₀.subtypeₗᵢ)

lemma mem_span_basis {G₀ : Submodule ℝ (Wsp κ)} {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ G₀)
    (g : G₀) : (g : Wsp κ) ∈ Submodule.span ℝ (Set.range fun k => (b k : Wsp κ)) := by
  rw [← pG_coe b g, coe_pG]
  exact proj_mem _ _

lemma res_apply {G₀ : Submodule ℝ (Wsp κ)} {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ G₀)
    {ℓ : Fin L} (z : ∀ i, EuclideanSpace ℝ (ι ℓ i))
    (C : ∀ i, G₀ →L[ℝ] EuclideanSpace ℝ (ι ℓ i × κ i)) (i : Fin m) (x : Wsp κ) :
    res (fun k => (b k : Wsp κ)) (ℓ := ℓ) ((z, fun i k => C i (b k)) : Dat ι κ d ℓ) i x =
      ‖tens (z i) (x i) + C i (pG b x)‖ := by
  simp [res, pG, map_sum, map_smul]

lemma res_lip {G₀ : Submodule ℝ (Wsp κ)} {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ G₀)
    {ℓ : Fin L} (z : ∀ i, EuclideanSpace ℝ (ι ℓ i))
    (C : ∀ i, G₀ →L[ℝ] EuclideanSpace ℝ (ι ℓ i × κ i)) (i : Fin m) (x y : Wsp κ) :
    res (fun k => (b k : Wsp κ)) (ℓ := ℓ) ((z, fun i k => C i (b k)) : Dat ι κ d ℓ) i x ≤
      res (fun k => (b k : Wsp κ)) (ℓ := ℓ) ((z, fun i k => C i (b k)) : Dat ι κ d ℓ) i y +
        (‖z i‖ + ‖C i‖) * ‖x - y‖ := by
  rw [res_apply, res_apply]
  have hd : tens (z i) (x i) + C i (pG b x) - (tens (z i) (y i) + C i (pG b y)) =
      tens (z i) ((x - y) i) + C i (pG b (x - y)) := by
    rw [← pG_sub, map_sub, PiLp.sub_apply, ← tens_sub]; abel
  have h1 := norm_sub_norm_le (tens (z i) (x i) + C i (pG b x)) (tens (z i) (y i) + C i (pG b y))
  rw [hd] at h1
  have h2 : ‖tens (z i) ((x - y) i) + C i (pG b (x - y))‖ ≤ (‖z i‖ + ‖C i‖) * ‖x - y‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_tens, add_mul]
    refine add_le_add (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ _) (norm_nonneg _)) ?_
    refine (C i).le_opNorm_of_le ?_
    have : ‖pG b (x - y)‖ = ‖(pG b (x - y) : Wsp κ)‖ := rfl
    rw [this, coe_pG]
    exact norm_proj_le (isFrame_basis b) _
  linarith

end ApproxSyzygies.Smoothed.Dev.P48

namespace ApproxSyzygies.Smoothed

open ApproxSyzygies.Smoothed.Dev.P48 in
theorem chk_proposition_4_8 {m L : ℕ} {ι : Fin L → Fin m → Type} [∀ ℓ i, Fintype (ι ℓ i)]
    {κ : Fin m → Type} [∀ i, Fintype (κ i)]
    (G₀ : Submodule ℝ (PiLp 2 fun i => EuclideanSpace ℝ (κ i))) (NG : ℕ)
    (hG : Module.finrank ℝ G₀ ≤ NG) (η₀ γ β : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ζ : ∀ ℓ i, Ω → EuclideanSpace ℝ (ι ℓ i)) (hζ : ∀ ℓ i, Measurable (ζ ℓ i))
    (hcond : ∀ ℓ : Fin L,
      ∀ᵐ x ∂(P.map fun ω (ℓ' : {ℓ' : Fin L // ℓ' < ℓ}) (i : Fin m) => ζ ℓ' i ω),
        ∃ ν : ∀ i, ProbabilityMeasure (EuclideanSpace ℝ (ι ℓ i)),
          (∀ i, SubspaceAnticonc (1 / 4) η₀ γ (ν i : Measure (EuclideanSpace ℝ (ι ℓ i)))) ∧
          condDistrib (fun ω (i : Fin m) => ζ ℓ i ω)
              (fun ω (ℓ' : {ℓ' : Fin L // ℓ' < ℓ}) (i : Fin m) => ζ ℓ' i ω) P x =
            Measure.pi fun i => (ν i : Measure (EuclideanSpace ℝ (ι ℓ i))))
    (hdim : ∀ ℓ i, 4 ≤ Fintype.card (ι ℓ i))
    (C : ∀ ℓ i, Ω → (G₀ →L[ℝ] EuclideanSpace ℝ (ι ℓ i × κ i)))
    (hCmeas : ∀ ℓ i (g : G₀),
      Measurable[MeasurableSpace.comap
          (fun ω => ((fun (ℓ' : {ℓ' : Fin L // ℓ' < ℓ}) (j : Fin m) => ζ ℓ' j ω),
            (fun j : {j : Fin m // j ≠ i} => ζ ℓ j ω))) inferInstance]
        fun ω => C ℓ i ω g)
    (hprod : (NG : ℝ) * ∏ ℓ, (2 * ∑ i, (1 : ℝ) / (Fintype.card (ι ℓ i) : ℝ)) < 1)
    (hβ1 : 1 ≤ β)
    (hβ : ∀ᵐ ω ∂P, ∀ ℓ i, ‖ζ ℓ i ω‖ + ‖C ℓ i ω‖ ≤ β) :
    P {ω | ¬ ∀ (η : ℝ), 0 ≤ η → ∀ g : G₀,
          (∀ ℓ i, ‖tens (ζ ℓ i ω) ((g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) i) +
              C ℓ i ω g‖ ≤ η) →
          ∀ i, ‖(g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) i‖ ≤
            η * (1 + β * (⨆ ℓ : Fin L,
              Real.sqrt (∑ i, ((Fintype.card (ι ℓ i) : ℝ)) ^ 2) / η₀)) ^ L}
      ≤ ENNReal.ofReal (m * L * Real.exp (-γ)) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    refine le_trans (measure_mono (t := ∅) ?_) (by simp)
    intro ω hω
    exact hω (fun η _ g _ i => i.elim0)
  set d := Module.finrank ℝ G₀ with hd
  set n : ℕ → Fin m → ℕ := fun j i => if h : j < L then Fintype.card (ι ⟨j, h⟩ i) else 1 with hn
  set kk : Fin (L + 1) → ℕ := fun j => kseq d n j.val with hkk
  have hkk0 : kk 0 = d := by simp [hkk, kseq]
  let bGb : OrthonormalBasis (Fin (kk 0)) ℝ G₀ :=
    (stdOrthonormalBasis ℝ G₀).reindex (finCongr hkk0.symm)
  set bW : Fin (kk 0) → PiLp 2 (fun i => EuclideanSpace ℝ (κ i)) := fun k => (bGb k : _) with hbW
  have hbWf : IsFrame bW := isFrame_basis bGb
  set Q := ⨆ ℓ : Fin L, Real.sqrt (∑ i, ((Fintype.card (ι ℓ i) : ℝ)) ^ 2) / η₀ with hQ
  have hQle : ∀ ℓ : Fin L, Real.sqrt (∑ i, ((Fintype.card (ι ℓ i) : ℝ)) ^ 2) / η₀ ≤ Q :=
    by
    intro ℓ
    rw [hQ]
    exact le_ciSup (f := fun ℓ : Fin L => Real.sqrt (∑ i, ((Fintype.card (ι ℓ i) : ℝ)) ^ 2) / η₀)
      (Set.finite_range _).bddAbove ℓ
  have hQ0 : 0 ≤ Q := by
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL; simp [hQ]
    · have hpm : Measurable fun ω (ℓ' : {ℓ' : Fin L // ℓ' < ⟨0, hL⟩}) (i : Fin m) => ζ ℓ' i ω :=
        measurable_pi_lambda _ fun ℓ' => measurable_pi_lambda _ fun i => hζ ℓ'.1 i
      have := Measure.isProbabilityMeasure_map (μ := P) hpm.aemeasurable
      obtain ⟨x, ν, hν, -⟩ := (hcond ⟨0, hL⟩).exists
      have hη₀ := (hν ⟨0, hm⟩).2.1
      exact (div_nonneg (Real.sqrt_nonneg _) hη₀.le).trans (hQle ⟨0, hL⟩)
  have hnℓ : ∀ ℓ : Fin L, ∀ i, n ℓ.val i = Fintype.card (ι ℓ i) := fun ℓ i => by simp [hn, ℓ.2]
  have hk : ∀ ℓ : Fin L, ∀ r : ℕ, r ≤ kk ℓ.castSucc →
      (r : ℝ) ≤ 2 * ∑ i, (kk ℓ.castSucc : ℝ) / (Fintype.card (ι ℓ i) : ℝ) → r ≤ kk ℓ.succ := by
    intro ℓ r h1 h2
    show r ≤ kseq d n (ℓ.val + 1)
    simp only [kseq]
    refine le_min h1 (Nat.le_floor ?_)
    simp only [hnℓ]
    exact h2
  have hlast : kk (Fin.last L) = 0 := by
    have h1 := kseq_le d n L
    have hp : ∏ t ∈ Finset.range L, (2 * ∑ i, (1 : ℝ) / (n t i : ℝ)) =
        ∏ ℓ : Fin L, (2 * ∑ i, (1 : ℝ) / (Fintype.card (ι ℓ i) : ℝ)) := by
      rw [← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl fun ℓ _ => ?_
      simp only [hnℓ]
    have hnn : 0 ≤ ∏ ℓ : Fin L, (2 * ∑ i, (1 : ℝ) / (Fintype.card (ι ℓ i) : ℝ)) :=
      Finset.prod_nonneg fun _ _ => by positivity
    have : (kseq d n L : ℝ) < 1 := by
      calc (kseq d n L : ℝ) ≤ d * ∏ ℓ : Fin L, (2 * ∑ i, (1 : ℝ) / (Fintype.card (ι ℓ i) : ℝ)) := by
            rw [← hp]; exact h1
        _ ≤ NG * ∏ ℓ : Fin L, (2 * ∑ i, (1 : ℝ) / (Fintype.card (ι ℓ i) : ℝ)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hG) hnn
        _ < 1 := hprod
    show kseq d n L = 0
    exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast this)
  set θ := theta (⇑bGb) ζ C with hθ
  have hstep : ∀ ℓ : Fin L, P ({ω | Good kk Q bW ℓ.val (θ ω)} \
      {ω | Good kk Q bW (ℓ.val + 1) (θ ω)}) ≤ ENNReal.ofReal (m * Real.exp (-γ)) :=
    fun ℓ => prob_step hm G₀ kk Q η₀ γ bGb P ζ hζ ℓ (hcond ℓ) (hdim ℓ) C hCmeas (hk ℓ) (hQle ℓ)
  have hA : ∀ j : ℕ, j ≤ L → P {ω | ¬ Good kk Q bW j (θ ω)} ≤
      j * ENNReal.ofReal (m * Real.exp (-γ)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp [good_zero kk Q bW hbWf]
    | succ j ih =>
      intro hj
      calc P {ω | ¬ Good kk Q bW (j + 1) (θ ω)}
          ≤ P ({ω | ¬ Good kk Q bW j (θ ω)} ∪ ({ω | Good kk Q bW j (θ ω)} \
              {ω | Good kk Q bW (j + 1) (θ ω)})) := by
            refine measure_mono fun ω h => ?_
            by_cases hg : Good kk Q bW j (θ ω)
            · exact Or.inr ⟨hg, h⟩
            · exact Or.inl hg
        _ ≤ P {ω | ¬ Good kk Q bW j (θ ω)} + P ({ω | Good kk Q bW j (θ ω)} \
              {ω | Good kk Q bW (j + 1) (θ ω)}) := measure_union_le _ _
        _ ≤ j * ENNReal.ofReal (m * Real.exp (-γ)) + ENNReal.ofReal (m * Real.exp (-γ)) :=
            add_le_add (ih (by omega)) (hstep ⟨j, by omega⟩)
        _ = (j + 1 : ℕ) * ENNReal.ofReal (m * Real.exp (-γ)) := by push_cast; ring
  have hnull : P {ω | ¬ ∀ ℓ i, ‖ζ ℓ i ω‖ + ‖C ℓ i ω‖ ≤ β} = 0 := ae_iff.1 hβ
  refine le_trans (measure_mono (t := {ω | ¬ Good kk Q bW L (θ ω)} ∪
    {ω | ¬ ∀ ℓ i, ‖ζ ℓ i ω‖ + ‖C ℓ i ω‖ ≤ β}) ?_) ?_
  · intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
    obtain ⟨⟨V, -, hV0, hVst⟩, hβω⟩ := hcon
    apply hω
    intro η hη g hres i
    have hit := iterate (θ := θ ω) (Q := Q) (β := β) (η := η) hQ0 (by linarith) V hV0 (fun ℓ => hVst ℓ ℓ.2) hlast
      (g : PiLp 2 fun i => EuclideanSpace ℝ (κ i))
      (proj_eq_self hbWf (mem_span_basis bGb g))
      (fun ℓ i => by
        have := res_apply bGb (fun i => ζ ℓ i ω) (C ℓ · ω) i g
        rw [pG_coe] at this
        exact (le_of_eq this).trans (hres ℓ i))
      (fun ℓ i x => (res_lip bGb (fun i => ζ ℓ i ω) (C ℓ · ω) i x g).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hβω ℓ i) (norm_nonneg _))))
    have h1 := PiLp.norm_apply_le (g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)) i
    have h2 : ‖(g : PiLp 2 fun i => EuclideanSpace ℝ (κ i))‖ ≤
        β * ‖(g : PiLp 2 fun i => EuclideanSpace ℝ (κ i))‖ :=
      le_mul_of_one_le_left (norm_nonneg _) hβ1
    linarith
  · calc P ({ω | ¬ Good kk Q bW L (θ ω)} ∪ {ω | ¬ ∀ ℓ i, ‖ζ ℓ i ω‖ + ‖C ℓ i ω‖ ≤ β})
        ≤ P {ω | ¬ Good kk Q bW L (θ ω)} + P {ω | ¬ ∀ ℓ i, ‖ζ ℓ i ω‖ + ‖C ℓ i ω‖ ≤ β} :=
          measure_union_le _ _
      _ ≤ L * ENNReal.ofReal (m * Real.exp (-γ)) := by rw [hnull, add_zero]; exact hA L le_rfl
      _ = ENNReal.ofReal (m * L * Real.exp (-γ)) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1; ring

end ApproxSyzygies.Smoothed
end

theorem solution : type_of% @ApproxSyzygies.Smoothed.chk_proposition_4_8 := @ApproxSyzygies.Smoothed.chk_proposition_4_8
