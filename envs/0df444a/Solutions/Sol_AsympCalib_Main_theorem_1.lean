-- Prove2me | solution 1 for AsympCalib.Main.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T08:46:17.92971+00:00
-- url     : https://prove2.me/submissions/465c4ccf-ca07-49dc-a2e8-c85310ac491a

import Mathlib
import Definitions.Def_AsympCalib_Main_Setting


noncomputable section
open Finset
open AsympCalib.Main CalibratedCE.Forecast
namespace ACProof

lemma regret_gridPt_nonneg (k : ℕ) (i : Fin (k+1)) : 0 ≤ gridPt k i := by
  unfold gridPt
  positivity

lemma regret_gridPt_le_one {k : ℕ} (hk : 0 < k) (i : Fin (k+1)) : gridPt k i ≤ 1 := by
  unfold gridPt
  apply (div_le_one (by exact_mod_cast hk : (0:ℝ)<k)).2
  exact_mod_cast Nat.le_of_lt_succ i.isLt

lemma positive_square_step (s d : ℝ) :
    (max 0 (s+d))^2 ≤ (max 0 s)^2 + 2*(max 0 s)*d+d^2 := by
  by_cases hs : 0 ≤ s <;> by_cases hd : 0 ≤ s+d
  · simp only [max_eq_right hs, max_eq_right hd]
    nlinarith
  · simp only [max_eq_right hs, max_eq_left (le_of_not_ge hd)]
    nlinarith [sq_nonneg (s+d)]
  · simp only [max_eq_left (le_of_not_ge hs), max_eq_right hd]
    nlinarith
  · simp only [max_eq_left (le_of_not_ge hs), max_eq_left (le_of_not_ge hd)]
    nlinarith [sq_nonneg d]

lemma dist_coordinate_le_one {m : ℕ} {p : Fin m → ℝ} (hp : IsDist p) (i : Fin m) :
    p i ≤ 1 := by
  rw [← hp.2]
  exact single_le_sum (fun j _ => hp.1 j) (mem_univ i)

lemma dist_square_sum_le_one {m : ℕ} {p : Fin m → ℝ} (hp : IsDist p) :
    ∑ i, (p i)^2 ≤ 1 := by
  calc
    ∑ i, (p i)^2 ≤ ∑ i, p i := by
      apply sum_le_sum
      intro i _
      nlinarith [hp.1 i, dist_coordinate_le_one hp i]
    _ = 1 := hp.2

lemma brier_bounds {k : ℕ} (hk : 0<k) {X : ℕ → ℝ} {s : ℕ}
    (hX : 0≤X s ∧ X s≤1) (i : Fin (k+1)) :
    0 ≤ brierLoss k X s i ∧ brierLoss k X s i ≤ 1 := by
  have h0 := regret_gridPt_nonneg k i
  have h1 := regret_gridPt_le_one hk i
  unfold brierLoss
  constructor
  · positivity
  · nlinarith [sq_nonneg (X s-gridPt k i)]

lemma regret_linear_cancel {m : ℕ} (L p : Fin m → ℝ) (R : Fin m → Fin m → ℝ)
    (hflow : ∀ i, p i*(∑ j,R i j)=∑ j,p j*R j i) :
    ∑ i, ∑ j, R i j*p i*(L i-L j) = 0 := by
  have heq : (∑ i, ∑ j, R i j*p i*(L i-L j)) =
      (∑ i,L i*(p i*(∑ j,R i j))) - (∑ j,L j*(∑ i,p i*R i j)) := by
    simp_rw [mul_sub, sum_sub_distrib]
    congr 1
    · apply sum_congr rfl
      intro i _
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    · rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
  rw [heq]
  simp_rw [hflow]
  exact sub_self _

lemma regret_increment_square {k : ℕ} (hk : 0<k) (X : ℕ→ℝ)
    (μ : ℕ→Fin (k+1)→ℝ) (s : ℕ) (hX : 0≤X s ∧ X s≤1) (hμ : IsDist (μ s)) :
    (∑ i, ∑ j, (μ s i*(brierLoss k X s i-brierLoss k X s j))^2) ≤ (k+1:ℕ) := by
  have hm : (0:ℝ) ≤ (k+1:ℕ) := by positivity
  calc
    (∑ i, ∑ j, (μ s i*(brierLoss k X s i-brierLoss k X s j))^2)
      ≤ ∑ i, ∑ _j : Fin (k+1), (μ s i)^2 := by
        apply sum_le_sum
        intro i _
        apply sum_le_sum
        intro j _
        have hi := brier_bounds hk hX i
        have hj := brier_bounds hk hX j
        have hd : (brierLoss k X s i-brierLoss k X s j)^2 ≤ 1 := by nlinarith
        rw [mul_pow]
        nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg (μ s i))]
    _ = (k+1:ℕ)*(∑ i,(μ s i)^2) := by simp [← mul_sum]
    _ ≤ (k+1:ℕ)*1 := mul_le_mul_of_nonneg_left (dist_square_sum_le_one hμ) hm
    _ = (k+1:ℕ) := mul_one _


lemma regret_square_bound {k : ℕ} (hk : 0<k) (X : ℕ→ℝ)
    (μ : ℕ→Fin (k+1)→ℝ) (t : ℕ)
    (hX : ∀ s<t, 0≤X s ∧ X s≤1) (hμ : ∀ s<t, IsDist (μ s))
    (hcon : ∀ s<t, Conservation k X μ s) :
    (∑ i, ∑ j, (Rg (brierLoss k X) μ t i j)^2) ≤ (k+1:ℕ)*(t:ℝ) := by
  induction t with
  | zero => simp [Rg, S]
  | succ t ih =>
    have ih' := ih (fun s hs => hX s (Nat.lt_trans hs (Nat.lt_succ_self t)))
      (fun s hs => hμ s (Nat.lt_trans hs (Nat.lt_succ_self t)))
      (fun s hs => hcon s (Nat.lt_trans hs (Nat.lt_succ_self t)))
    have hstep (i j : Fin (k+1)) :
        (Rg (brierLoss k X) μ (t+1) i j)^2 ≤
          (Rg (brierLoss k X) μ t i j)^2 +
          2*(Rg (brierLoss k X) μ t i j)*
            (μ t i*(brierLoss k X t i-brierLoss k X t j)) +
          (μ t i*(brierLoss k X t i-brierLoss k X t j))^2 := by
      simpa only [Rg, S, sum_range_succ] using
        positive_square_step (S (brierLoss k X) μ t i j)
          (μ t i*(brierLoss k X t i-brierLoss k X t j))
    have hc := regret_linear_cancel (brierLoss k X t) (μ t)
      (Rg (brierLoss k X) μ t) (hcon t (Nat.lt_succ_self t))
    have hs := regret_increment_square hk X μ t (hX t (Nat.lt_succ_self t))
      (hμ t (Nat.lt_succ_self t))
    calc
      (∑ i, ∑ j, (Rg (brierLoss k X) μ (t+1) i j)^2) ≤
          ∑ i, ∑ j, ((Rg (brierLoss k X) μ t i j)^2 +
          2*(Rg (brierLoss k X) μ t i j)*
            (μ t i*(brierLoss k X t i-brierLoss k X t j)) +
          (μ t i*(brierLoss k X t i-brierLoss k X t j))^2) :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => hstep i j
      _ = (∑ i, ∑ j, (Rg (brierLoss k X) μ t i j)^2) +
          2*(∑ i, ∑ j, Rg (brierLoss k X) μ t i j*μ t i*
            (brierLoss k X t i-brierLoss k X t j)) +
          (∑ i, ∑ j, (μ t i*(brierLoss k X t i-brierLoss k X t j))^2) := by
        simp_rw [sum_add_distrib, mul_sum]
        congr 2
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        ring
      _ ≤ (k+1:ℕ)*(t:ℝ)+(k+1:ℕ) := by rw [hc]; linarith
      _ = (k+1:ℕ)*((t+1:ℕ):ℝ) := by push_cast; ring


lemma nearest_grid {k : ℕ} (hk : 0<k) (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1) :
    ∃ j : Fin (k+1), |q-gridPt k j|≤1/(2*(k:ℝ)) := by
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  let z : ℤ := round (q*(k:ℝ))
  have hz : 0≤z := by
    dsimp [z]
    rw [round_eq]
    apply Int.floor_nonneg.mpr
    positivity
  have hzR : (z:ℝ)≤q*(k:ℝ)+1/2 := round_le_add_half _
  have hzlt : z < (k:ℤ)+1 := by
    have : (z:ℝ)<(k:ℝ)+1 := by nlinarith
    exact_mod_cast this
  have hzN : z.toNat<k+1 := by omega
  refine ⟨⟨z.toNat,hzN⟩, ?_⟩
  have hcast : (z.toNat:ℝ)=(z:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hz
  have ha := abs_sub_round (q*(k:ℝ))
  change |q-(z.toNat:ℝ)/(k:ℝ)|≤_
  rw [hcast]
  have he : q-(z:ℝ)/(k:ℝ)=(q*(k:ℝ)-(z:ℝ))/(k:ℝ) := by field_simp
  rw [he]
  rw [abs_div, abs_of_pos hkR]
  apply (div_le_iff₀ hkR).2
  calc
    |q*(k:ℝ)-(z:ℝ)| ≤ 1/2 := ha
    _ = 1/(2*(k:ℝ))*(k:ℝ) := by field_simp

lemma weighted_counts_bounds {k : ℕ} (X : ℕ→ℝ) (μ : ℕ→Fin (k+1)→ℝ) (t : ℕ)
    (hX : ∀ s<t, 0≤X s ∧ X s≤1) (hμ : ∀ s<t, IsDist (μ s))
    (i : Fin (k+1)) :
    0≤nTilde k μ t i ∧ 0≤(∑ s∈range t,μ s i*X s) ∧
    (∑ s∈range t,μ s i*X s)≤nTilde k μ t i := by
  refine ⟨sum_nonneg (fun s hs => (hμ s (mem_range.mp hs)).1 i), ?_, ?_⟩
  · exact sum_nonneg fun s hs => mul_nonneg ((hμ s (mem_range.mp hs)).1 i) (hX s (mem_range.mp hs)).1
  · apply sum_le_sum
    intro s hs
    exact mul_le_of_le_one_right ((hμ s (mem_range.mp hs)).1 i) (hX s (mem_range.mp hs)).2

lemma weighted_counts_sum {k : ℕ} (μ : ℕ→Fin (k+1)→ℝ) (t : ℕ)
    (hμ : ∀ s<t, IsDist (μ s)) : ∑ i,nTilde k μ t i=(t:ℝ) := by
  unfold nTilde
  rw [sum_comm]
  calc
    ∑ s∈range t,∑ i,μ s i = ∑ _s∈range t,(1:ℝ) := by
      apply sum_congr rfl
      intro s hs
      exact (hμ s (mem_range.mp hs)).2
    _ = (t:ℝ) := by simp

lemma brier_regret_identity {k : ℕ} (X : ℕ→ℝ) (μ : ℕ→Fin (k+1)→ℝ) (t : ℕ)
    (hX : ∀ s<t, 0≤X s ∧ X s≤1) (hμ : ∀ s<t, IsDist (μ s))
    (i j : Fin (k+1)) :
    S (brierLoss k X) μ t i j = nTilde k μ t i *
      ((rhoTilde k X μ t i-gridPt k i)^2-(rhoTilde k X μ t i-gridPt k j)^2) := by
  let a := nTilde k μ t i
  let b := ∑ s∈range t,μ s i*X s
  have hb := weighted_counts_bounds X μ t hX hμ i
  have hexp : S (brierLoss k X) μ t i j =
      a*((gridPt k i)^2-(gridPt k j)^2)+2*b*(gridPt k j-gridPt k i) := by
    unfold S brierLoss
    dsimp [a,b,nTilde]
    simp_rw [mul_sum, sum_mul]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro s _
    ring
  change _ = a*((b/a-gridPt k i)^2-(b/a-gridPt k j)^2)
  rw [hexp]
  by_cases ha : a=0
  · have hb0 : b=0 := by change 0≤a ∧ 0≤b ∧ b≤a at hb; linarith
    rw [ha,hb0]
    simp
  · field_simp
    ring

lemma regret_single_bound {k : ℕ} (hk : 0<k) (X : ℕ→ℝ)
    (μ : ℕ→Fin (k+1)→ℝ) (t : ℕ)
    (hX : ∀ s<t, 0≤X s ∧ X s≤1) (hμ : ∀ s<t, IsDist (μ s))
    (hcon : ∀ s<t, Conservation k X μ s) (i j : Fin (k+1)) :
    Rg (brierLoss k X) μ t i j≤Real.sqrt ((k+1:ℕ)*(t:ℝ)) := by
  have h := regret_square_bound hk X μ t hX hμ hcon
  have h1 : (Rg (brierLoss k X) μ t i j)^2≤∑ j,(Rg (brierLoss k X) μ t i j)^2 :=
    single_le_sum (fun _ _ => sq_nonneg _) (mem_univ j)
  have h2 : (∑ j,(Rg (brierLoss k X) μ t i j)^2)≤
      ∑ i,∑ j,(Rg (brierLoss k X) μ t i j)^2 :=
    single_le_sum (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (mem_univ i)
  have hr := Real.sq_sqrt (show (0:ℝ)≤(k+1:ℕ)*(t:ℝ) by positivity)
  have hn := Real.sqrt_nonneg ((k+1:ℕ)*(t:ℝ))
  nlinarith

lemma weighted_bin_bound {k : ℕ} (hk : 0<k) (X : ℕ→ℝ)
    (μ : ℕ→Fin (k+1)→ℝ) (t : ℕ)
    (hX : ∀ s<t, 0≤X s ∧ X s≤1) (hμ : ∀ s<t, IsDist (μ s))
    (hcon : ∀ s<t, Conservation k X μ s) (i : Fin (k+1)) :
    nTilde k μ t i*(rhoTilde k X μ t i-gridPt k i)^2≤
      Real.sqrt ((k+1:ℕ)*(t:ℝ))+nTilde k μ t i/(4*(k:ℝ)^2) := by
  have hb := weighted_counts_bounds X μ t hX hμ i
  have hr0 : 0≤rhoTilde k X μ t i := div_nonneg hb.2.1 hb.1
  have hr1 : rhoTilde k X μ t i≤1 := by
    by_cases ha : nTilde k μ t i=0
    · simp [rhoTilde,ha]
    · exact (div_le_one (lt_of_le_of_ne hb.1 (Ne.symm ha))).2 hb.2.2
  obtain ⟨j,hj⟩ := nearest_grid hk (rhoTilde k X μ t i) hr0 hr1
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hsq : (rhoTilde k X μ t i-gridPt k j)^2≤1/(4*(k:ℝ)^2) := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by positivity : (0:ℝ)≤1/(2*(k:ℝ)))).2 hj
    rw [sq_abs] at h
    have he : (1/(2*(k:ℝ)))^2=1/(4*(k:ℝ)^2) := by ring
    rwa [he] at h
  have hs := regret_single_bound hk X μ t hX hμ hcon i j
  have hi := brier_regret_identity X μ t hX hμ i j
  have hle : S (brierLoss k X) μ t i j≤Rg (brierLoss k X) μ t i j := le_max_right _ _
  have hm := mul_le_mul_of_nonneg_left hsq hb.1
  simp only [mul_one_div] at hm
  nlinarith

lemma weighted_score_bound {k : ℕ} (hk : 0<k) (X : ℕ→ℝ)
    (μ : ℕ→Fin (k+1)→ℝ) (t : ℕ)
    (hX : ∀ s<t, 0≤X s ∧ X s≤1) (hμ : ∀ s<t, IsDist (μ s))
    (hcon : ∀ s<t, Conservation k X μ s) (ht : 0<t) :
    CTilde k X μ t≤((k+1:ℕ):ℝ)*Real.sqrt ((k+1:ℕ)*(t:ℝ))/(t:ℝ)+1/(4*(k:ℝ)^2) := by
  have htR : (0:ℝ)<t := by exact_mod_cast ht
  have hs := sum_le_sum (s:=univ) fun i _ => weighted_bin_bound hk X μ t hX hμ hcon i
  have hc := weighted_counts_sum μ t hμ
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,← sum_div,hc] at hs
  unfold CTilde
  have he : (∑ i,nTilde k μ t i/(t:ℝ)*(rhoTilde k X μ t i-gridPt k i)^2)=
      (∑ i,nTilde k μ t i*(rhoTilde k X μ t i-gridPt k i)^2)/(t:ℝ) := by
    rw [sum_div]
    apply sum_congr rfl
    intro i _
    ring
  rw [he]
  apply (div_le_iff₀ htR).2
  calc
    _ ≤ ((k+1:ℕ):ℝ)*Real.sqrt ((k+1:ℕ)*(t:ℝ))+(t:ℝ)/(4*(k:ℝ)^2) := hs
    _ = _ := by field_simp

end ACProof


noncomputable section
namespace ACProof

def scoreTerm (p a b : ℝ) : ℝ := a * (b / a - p) ^ 2

lemma scoreTerm_nonneg {p a b : ℝ} (ha : 0 ≤ a) : 0 ≤ scoreTerm p a b :=
  mul_nonneg ha (sq_nonneg _)

lemma scoreTerm_ge_affine {p a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    a * (p ^ 2 - u ^ 2) + 2 * b * (u - p) ≤ scoreTerm p a b := by
  rcases ha.eq_or_lt with h | h
  · have h0 : a = 0 := h.symm
    have hb0 : b = 0 := le_antisymm (h0 ▸ hba) hb
    simp [scoreTerm, h0, hb0]
  · have heq : scoreTerm p a b - (a * (p ^ 2 - u ^ 2) + 2 * b * (u - p)) =
        a * (b / a - u) ^ 2 := by
      unfold scoreTerm
      field_simp
      ring
    linarith [mul_nonneg h.le (sq_nonneg (b / a - u))]

lemma scoreTerm_eq_affine {p a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    scoreTerm p a b = a * (p ^ 2 - (b / a) ^ 2) + 2 * b * (b / a - p) := by
  rcases ha.eq_or_lt with h | h
  · have h0 : a = 0 := h.symm
    have hb0 : b = 0 := le_antisymm (h0 ▸ hba) hb
    simp [scoreTerm, h0, hb0]
  · unfold scoreTerm
    field_simp
    ring

lemma mul_le_abs_of_abs_le_one (x y : ℝ) (hy : |y| ≤ 1) : x * y ≤ |x| := by
  calc
    x * y ≤ |x * y| := le_abs_self _
    _ = |x| * |y| := abs_mul _ _
    _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    _ = |x| := mul_one _

lemma scoreTerm_sub_le {p a b c d : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hb : 0 ≤ b) (hba : b ≤ a) (hd : 0 ≤ d) (hdc : d ≤ c) :
    scoreTerm p a b - scoreTerm p c d ≤ |a-c| + 2 * |b-d| := by
  have ha : 0 ≤ a := hb.trans hba
  have hc : 0 ≤ c := hd.trans hdc
  have hq : 0 ≤ b/a := div_nonneg hb ha
  have hq1 : b/a ≤ 1 := by
    rcases ha.eq_or_lt with h | h
    · simp [h.symm]
    · exact (div_le_one h).2 hba
  have hdiff : |b/a-p| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hsquare : |p^2-(b/a)^2| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg p, sq_nonneg (b/a)]
  have h1 := mul_le_abs_of_abs_le_one (a-c) (p^2-(b/a)^2) hsquare
  have h2 := mul_le_abs_of_abs_le_one (b-d) (b/a-p) hdiff
  have h3 := scoreTerm_ge_affine (p:=p) (u:=b/a) hc hd hdc
  rw [scoreTerm_eq_affine ha hb hba]
  nlinarith

lemma scoreTerm_lipschitz {p a b c d : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hb : 0 ≤ b) (hba : b ≤ a) (hd : 0 ≤ d) (hdc : d ≤ c) :
    |scoreTerm p a b - scoreTerm p c d| ≤ |a-c| + 2 * |b-d| := by
  rw [abs_le]
  constructor
  · have h := scoreTerm_sub_le hp hp1 hd hdc hb hba
    rw [abs_sub_comm c a, abs_sub_comm d b] at h
    linarith
  · exact scoreTerm_sub_le hp hp1 hb hba hd hdc

end ACProof


noncomputable section
open scoped BigOperators
open AsympCalib.Main CalibratedCE.Forecast
namespace ACProof
abbrev Code (k t : ℕ) := Fin t → (Fin (k+1) × Fin 2)
def decode {k t : ℕ} (w : Code k t) : History :=
  List.ofFn fun s => (gridVec k (w s).1, (w s).2)
def snocCode {k t : ℕ} (w : Code k t) (i : Fin (k+1)) (x : Fin 2) : Code k (t+1) :=
  Fin.snoc w (i,x)
@[simp] theorem decode_length {k t : ℕ} (w : Code k t) : (decode w).length = t := by simp [decode]
@[simp] theorem decode_snoc {k t : ℕ} (w : Code k t) (i : Fin (k+1)) (x : Fin 2) :
    decode (snocCode w i x) = decode w ++ [(gridVec k i,x)] := by
  unfold decode
  rw [List.ofFn_succ_last]
  simp only [snocCode, Fin.snoc_castSucc, Fin.snoc_last]
@[simp] theorem gridVec_one (k : ℕ) (i : Fin (k+1)) : gridVec k i 1 = gridPt k i := by simp [gridVec]
theorem gridPt_nonneg (k : ℕ) (i : Fin (k+1)) : 0 ≤ gridPt k i := by unfold gridPt; positivity
theorem gridPt_le_one (k : ℕ) (hk : 0<k) (i : Fin (k+1)) : gridPt k i ≤ 1 := by
  apply (div_le_one (by exact_mod_cast hk)).2
  exact_mod_cast (Nat.le_of_lt_succ i.isLt)
theorem gridVec_injective {k : ℕ} (hk : 0<k) : Function.Injective (gridVec k) := by
  intro i j h
  have h' := congrFun h 1
  simp only [gridVec_one, gridPt] at h'
  have hk' : (k:ℝ) ≠ 0 := by positivity
  have : (i:ℝ) = (j:ℝ) := (div_left_inj' hk').mp h'
  apply Fin.ext
  exact_mod_cast this

def codedLaw {k : ℕ} (σ : History → PMF (Fin (k+1))) (A : History → PMF (Fin 2)) :
    (t : ℕ) → PMF (Code k t)
  | 0 => PMF.pure (fun i => Fin.elim0 i)
  | t+1 => (codedLaw σ A t).bind fun w => (σ (decode w)).bind fun i =>
      (A (decode w)).map fun x => snocCode w i x

theorem codedLaw_map {k : ℕ} (σ : History → PMF (Fin (k+1))) (A : History → PMF (Fin 2)) (t : ℕ) :
    (codedLaw σ A t).map decode = histLaw (forecaster k σ) A t := by
  induction t with
  | zero => simp [codedLaw, histLaw, PMF.pure_map, decode]
  | succ t ih =>
    rw [codedLaw, PMF.map_bind, histLaw, ← ih, PMF.bind_map]
    congr 1
    funext w
    simp only [Function.comp_apply, forecaster, PMF.bind_map, PMF.map_bind,
      PMF.map_comp, Function.comp_def, decode_snoc]

def mean {k : ℕ} (σ : History → PMF (Fin (k+1))) (A : History → PMF (Fin 2)) (t : ℕ)
    (f : Code k t → ℝ) : ℝ := ∑ w, (codedLaw σ A t w).toReal * f w

def count {k t : ℕ} (w : Code k t) (i : Fin (k+1)) : ℝ :=
  ∑ s, if (w s).1=i then 1 else 0
def wetCount {k t : ℕ} (w : Code k t) (i : Fin (k+1)) : ℝ :=
  ∑ s, if (w s).1=i ∧ (w s).2=1 then 1 else 0
def weightedCount {k t : ℕ} (σ : History → PMF (Fin (k+1))) (w : Code k t) (i : Fin (k+1)) : ℝ :=
  nTilde k (muH σ (decode w)) t i
def weightedWet {k t : ℕ} (σ : History → PMF (Fin (k+1))) (w : Code k t) (i : Fin (k+1)) : ℝ :=
  ∑ s ∈ Finset.range t, muH σ (decode w) s i * outcomeR (decode w) s
def actualScore {k t : ℕ} (w : Code k t) : ℝ := calibScore2Hj (decode w) 1

@[simp] theorem count_snoc {k t : ℕ} (w : Code k t) (j i : Fin (k+1)) (x : Fin 2) :
    count (snocCode w j x) i = count w i + if j=i then 1 else 0 := by
  simp [count, snocCode, Fin.sum_univ_castSucc]
@[simp] theorem wetCount_snoc {k t : ℕ} (w : Code k t) (j i : Fin (k+1)) (x : Fin 2) :
    wetCount (snocCode w j x) i = wetCount w i + if j=i ∧ x=1 then 1 else 0 := by
  simp [wetCount, snocCode, Fin.sum_univ_castSucc]
theorem count_nonneg {k t : ℕ} (w : Code k t) (i : Fin (k+1)) : 0 ≤ count w i := by
  unfold count; positivity
theorem wetCount_nonneg {k t : ℕ} (w : Code k t) (i : Fin (k+1)) : 0 ≤ wetCount w i := by
  unfold wetCount; positivity
theorem wetCount_le_count {k t : ℕ} (w : Code k t) (i : Fin (k+1)) : wetCount w i ≤ count w i := by
  apply Finset.sum_le_sum
  intro s _; split_ifs <;> simp_all

theorem sum_count {k t : ℕ} (w : Code k t) : ∑ i, count w i = (t:ℝ) := by
  unfold count
  rw [Finset.sum_comm]
  simp

theorem length_filter_ofFn {α : Type*} (p : α → Bool) {t : ℕ} (f : Fin t → α) :
    ((List.ofFn f).filter p).length = ∑ s, if p (f s) then 1 else 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.ofFn_succ_last, List.filter_append, List.length_append, Fin.sum_univ_castSucc]
    rw [ih]
    cases h : p (f (Fin.last t)) <;> simp [h]

theorem native_count {k t : ℕ} (hk : 0<k) (w : Code k t) (i : Fin (k+1)) :
    (NH (decode w) (gridVec k i):ℝ) = count w i := by
  classical
  simp only [NH, decode, length_filter_ofFn]
  simp [count, (gridVec_injective hk).eq_iff]
theorem native_wet {k t : ℕ} (hk : 0<k) (w : Code k t) (i : Fin (k+1)) :
    (((decode w).filter (fun e => e.1=gridVec k i ∧ e.2=1)).length:ℝ) = wetCount w i := by
  classical
  simp only [decode, length_filter_ofFn]
  simp [wetCount, (gridVec_injective hk).eq_iff]
theorem native_rho {k t : ℕ} (hk : 0<k) (w : Code k t) (i : Fin (k+1)) :
    rhoH (decode w) (gridVec k i) 1 = wetCount w i / count w i := by
  unfold rhoH
  split_ifs with h
  · have hc : count w i=0 := by rw [← native_count hk]; simp [h]
    simp [hc]
  · rw [native_count hk, native_wet hk]
theorem actualScore_eq_sum {k t : ℕ} (hk : 0<k) (w : Code k t) :
    actualScore w = (∑ i, count w i * (wetCount w i/count w i-gridPt k i)^2)/(t:ℝ) := by
  classical
  have hsub : ((decode w).map Prod.fst).toFinset ⊆ Finset.univ.image (gridVec k) := by
    intro p hp
    simp only [List.mem_toFinset, List.mem_map] at hp
    obtain ⟨e, he, rfl⟩ := hp
    simp only [decode, List.mem_ofFn] at he
    obtain ⟨s, rfl⟩ := he
    exact Finset.mem_image.mpr ⟨(w s).1, Finset.mem_univ _, rfl⟩
  unfold actualScore calibScore2Hj
  rw [Finset.sum_subset hsub]
  · rw [Finset.sum_image]
    · simp only [native_rho hk, native_count hk, gridVec_one, decode_length]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _; ring
    · intro i _ j _ h; exact gridVec_injective hk h
  · intro p _ hp
    have hn : NH (decode w) p = 0 := by
      unfold NH
      apply List.length_eq_zero_iff.mpr
      apply List.filter_eq_nil_iff.mpr
      intro e he
      have : e.1 ≠ p := by
        intro h
        apply hp
        simp only [List.mem_toFinset, List.mem_map]
        exact ⟨e,he,h⟩
      simpa using this
    simp [hn]

theorem actualScore_nonneg {k t : ℕ} (hk : 0<k) (w : Code k t) : 0 ≤ actualScore w := by
  rw [actualScore_eq_sum hk]
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg fun i _ => mul_nonneg (count_nonneg w i) (sq_nonneg _)

theorem actualScore_le_one {k t : ℕ} (hk : 0<k) (w : Code k t) : actualScore w ≤ 1 := by
  rw [actualScore_eq_sum hk]
  by_cases ht : t=0
  · simp [ht]
  apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero ht)).2
  rw [← sum_count w]
  apply Finset.sum_le_sum
  intro i _
  have hc := count_nonneg w i
  have hb := wetCount_nonneg w i
  have hbc := wetCount_le_count w i
  have hp := gridPt_nonneg k i
  have hp' := gridPt_le_one k hk i
  have hr : 0 ≤ wetCount w i / count w i := div_nonneg hb hc
  have hr' : wetCount w i / count w i ≤ 1 := by
    by_cases h : count w i=0
    · simp [h]
    exact (div_le_one (lt_of_le_of_ne hc (Ne.symm h))).2 hbc
  have hs : (wetCount w i / count w i-gridPt k i)^2 ≤ 1 := by nlinarith
  nlinarith
end ACProof

noncomputable section
open scoped BigOperators
open Classical
open AsympCalib.Main CalibratedCE.Forecast
namespace ACProof

def expect {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) : ℝ := ∑ a, (p a).toReal * f a

theorem sum_mass {α : Type*} [Fintype α] (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  simpa only [tsum_fintype, ENNReal.toReal_sum (fun a _ => p.apply_ne_top a), ENNReal.toReal_one] using h

theorem expect_const {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) : expect p (fun _ => c)=c := by
  simp [expect, ← Finset.sum_mul, sum_mass]
theorem expect_add {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    expect p (fun a => f a+g a)=expect p f+expect p g := by simp [expect, mul_add, Finset.sum_add_distrib]
theorem expect_mul_const {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    expect p (fun a => f a*c)=expect p f*c := by simp only [expect, Finset.sum_mul, mul_assoc]
theorem expect_mono {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    expect p f ≤ expect p g := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg

theorem expect_pure {α : Type*} [Fintype α] (a : α) (f : α → ℝ) : expect (PMF.pure a) f=f a := by
  classical
  simp [expect, PMF.pure_apply, apply_ite]

theorem expect_bind {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    expect (p.bind q) f=expect p (fun a => expect (q a) f) := by
  unfold expect
  simp only [PMF.bind_apply, tsum_fintype]
  simp_rw [ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top _)), ENNReal.toReal_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _; ring

theorem expect_map {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (g : α → β) (f : β → ℝ) :
    expect (p.map g) f=expect p (fun a => f (g a)) := by
  rw [PMF.map, expect_bind]
  simp only [Function.comp_apply, expect_pure]

theorem mean_succ {k t : ℕ} (σ : History → PMF (Fin (k+1))) (A : History → PMF (Fin 2))
    (f : Code k (t+1) → ℝ) :
    mean σ A (t+1) f = mean σ A t (fun w => expect (σ (decode w)) (fun i => expect (A (decode w)) (fun x => f (snocCode w i x)))) := by
  change expect (codedLaw σ A (t+1)) f = expect (codedLaw σ A t) _
  rw [codedLaw, expect_bind]
  congr 1
  funext w
  rw [expect_bind]
  congr 1
  funext i
  exact expect_map _ _ _

theorem outcome_prefix (h : History) {s r : ℕ} (hr : r<s) :
    outcomeR (h.take s) r = outcomeR h r := by
  simp [outcomeR, List.getD_eq_getElem?_getD, hr]
theorem mu_prefix {k : ℕ} (σ : History → PMF (Fin (k+1))) (h : History) {s r : ℕ} (hr : r ≤ s) :
    muH σ (h.take s) r = muH σ h r := by
  funext i
  simp [muH, List.take_take, Nat.min_eq_left hr]
theorem outcome_append (h : History) (p : Fin 2 → ℝ) (x : Fin 2) {s : ℕ} (hs : s<h.length) :
    outcomeR (h++[(p,x)]) s = outcomeR h s := by
  simp [outcomeR, List.getD_eq_getElem?_getD, List.getElem?_append_left hs]
theorem outcome_append_last (h : History) (p : Fin 2 → ℝ) (x : Fin 2) :
    outcomeR (h++[(p,x)]) h.length = if x=1 then 1 else 0 := by
  simp [outcomeR, List.getD_eq_getElem?_getD]
theorem mu_append {k : ℕ} (σ : History → PMF (Fin (k+1))) (h : History) (p : Fin 2 → ℝ) (x : Fin 2)
    {s : ℕ} (hs : s ≤ h.length) : muH σ (h++[(p,x)]) s = muH σ h s := by
  funext i
  simp [muH, List.take_append_of_le_length hs]
theorem weightedCount_snoc {k t : ℕ} (σ : History → PMF (Fin (k+1))) (w : Code k t)
    (j i : Fin (k+1)) (x : Fin 2) :
    weightedCount σ (snocCode w j x) i = weightedCount σ w i+(σ (decode w) i).toReal := by
  unfold weightedCount nTilde
  rw [Finset.sum_range_succ, decode_snoc]
  have hsum : (∑ s ∈ Finset.range t, muH σ (decode w++[(gridVec k j,x)]) s i) =
      ∑ s ∈ Finset.range t, muH σ (decode w) s i := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [mu_append σ _ _ _ (by simpa using (Finset.mem_range.mp hs).le)]
  rw [hsum]
  congr 1
  have he : (decode w ++ [(gridVec k j,x)]).take t = decode w := by
    simp
  simp [muH, he]
theorem weightedWet_snoc {k t : ℕ} (σ : History → PMF (Fin (k+1))) (w : Code k t)
    (j i : Fin (k+1)) (x : Fin 2) :
    weightedWet σ (snocCode w j x) i = weightedWet σ w i+(σ (decode w) i).toReal*(if x=1 then 1 else 0) := by
  unfold weightedWet
  rw [Finset.sum_range_succ, decode_snoc]
  have hsum : (∑ s ∈ Finset.range t, muH σ (decode w++[(gridVec k j,x)]) s i * outcomeR (decode w++[(gridVec k j,x)]) s) =
      ∑ s ∈ Finset.range t, muH σ (decode w) s i * outcomeR (decode w) s := by
    apply Finset.sum_congr rfl
    intro s hs
    have h : s < (decode w).length := by simpa using Finset.mem_range.mp hs
    rw [mu_append σ _ _ _ h.le, outcome_append _ _ _ h]
  rw [hsum]
  congr 1
  have hx : outcomeR (decode w ++ [(gridVec k j,x)]) t = if x=1 then 1 else 0 := by
    simpa using outcome_append_last (decode w) (gridVec k j) x
  have he : (decode w ++ [(gridVec k j,x)]).take t = decode w := by
    simp
  simp [muH, he, hx]

theorem expect_const_mul {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    expect p (fun a => c*f a)=c*expect p f := by simp only [expect, Finset.mul_sum, mul_left_comm]
theorem expect_sub {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    expect p (fun a => f a-g a)=expect p f-expect p g := by simp [expect, mul_sub, Finset.sum_sub_distrib]
theorem expect_indicator {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) (i : α) :
    expect p (fun j => if j=i then 1 else 0) = (p i).toReal := by
  classical
  simp [expect, mul_ite]
theorem expect_center {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) (i : α) :
    expect p (fun j => (if j=i then 1 else 0)-(p i).toReal)=0 := by
  classical
  rw [expect_sub, expect_indicator, expect_const, sub_self]
theorem expect_center_step {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] (p : PMF α) (q : PMF β)
    (i : α) (z : β → ℝ) (hz : ∀ x, 0 ≤ z x ∧ z x ≤ 1) (d : ℝ) :
    expect p (fun j => expect q (fun x => (d+((if j=i then 1 else 0)-(p i).toReal)*z x)^2)) ≤ d^2+1 := by
  classical
  let Δ := fun (j : α) (x : β) => ((if j=i then 1 else 0)-(p i).toReal)*z x
  have hp0 : 0 ≤ (p i).toReal := ENNReal.toReal_nonneg
  have hp1 : (p i).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one i)
  have hzero : expect p (fun j => expect q (Δ j))=0 := by
    simp only [Δ, expect_const_mul]
    rw [expect_mul_const, expect_center, zero_mul]
  have hs : ∀ j x, Δ j x ^2 ≤ 1 := by
    intro j x
    obtain ⟨hz0,hz1⟩ := hz x
    have hc : ((if j=i then (1:ℝ) else 0)-(p i).toReal)^2 ≤ 1 := by split_ifs <;> nlinarith
    have hzsq : z x^2 ≤ 1 := by nlinarith
    dsimp [Δ]
    rw [mul_pow]
    calc
      _ ≤ 1*1 := mul_le_mul hc hzsq (sq_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hbound : expect p (fun j => expect q (fun x => Δ j x ^2)) ≤ 1 := by
    calc
      _ ≤ expect p (fun _ => expect q (fun _ => (1:ℝ))) := expect_mono p fun j => expect_mono q (hs j)
      _ = 1 := by rw [expect_const]; exact expect_const _ _
  have heq : (fun j => expect q (fun x => (d+Δ j x)^2)) =
      fun j => d^2 + 2*d*expect q (Δ j)+expect q (fun x => Δ j x^2) := by
    funext j
    conv_lhs => arg 2; ext x; rw [show (d+Δ j x)^2=d^2+2*d*Δ j x+Δ j x^2 by ring]
    rw [expect_add, expect_add, expect_const, expect_const_mul]
  change expect p (fun j => expect q (fun x => (d+Δ j x)^2)) ≤ _
  rw [heq, expect_add, expect_add, expect_const, expect_const_mul, hzero]
  linarith

def countError {k t : ℕ} (σ : History → PMF (Fin (k+1))) (w : Code k t) (i : Fin (k+1)) : ℝ :=
  count w i-weightedCount σ w i
def wetError {k t : ℕ} (σ : History → PMF (Fin (k+1))) (w : Code k t) (i : Fin (k+1)) : ℝ :=
  wetCount w i-weightedWet σ w i

theorem countError_snoc {k t : ℕ} (σ : History → PMF (Fin (k+1))) (w : Code k t)
    (j i : Fin (k+1)) (x : Fin 2) :
    countError σ (snocCode w j x) i = countError σ w i+((if j=i then 1 else 0)-(σ (decode w) i).toReal) := by
  simp only [countError, count_snoc, weightedCount_snoc]; ring
theorem wetError_snoc {k t : ℕ} (σ : History → PMF (Fin (k+1))) (w : Code k t)
    (j i : Fin (k+1)) (x : Fin 2) :
    wetError σ (snocCode w j x) i = wetError σ w i+((if j=i then 1 else 0)-(σ (decode w) i).toReal)*(if x=1 then 1 else 0) := by
  simp only [wetError, wetCount_snoc, weightedWet_snoc]
  split_ifs <;> simp_all <;> ring

theorem countError_sq_mean_le {k : ℕ} (σ : History → PMF (Fin (k+1))) (A : History → PMF (Fin 2))
    (t : ℕ) (i : Fin (k+1)) : mean σ A t (fun w => countError σ w i ^2) ≤ (t:ℝ) := by
  induction t with
  | zero => simp [mean, countError, count, weightedCount, nTilde]
  | succ t ih =>
    rw [mean_succ]
    have h : ∀ w : Code k t,
        expect (σ (decode w)) (fun j => expect (A (decode w)) (fun x => countError σ (snocCode w j x) i ^2)) ≤ countError σ w i ^2+1 := by
      intro w
      simpa only [countError_snoc, mul_one] using expect_center_step (σ (decode w)) (A (decode w)) i (fun _ => 1) (fun _ => ⟨by norm_num,le_rfl⟩) (countError σ w i)
    have hm := expect_mono (codedLaw σ A t) h
    change mean σ A t _ ≤ mean σ A t _ at hm
    have he : mean σ A t (fun w => countError σ w i ^2+1)=mean σ A t (fun w => countError σ w i ^2)+1 := by
      change expect _ _ = expect _ _+1
      rw [expect_add, expect_const]
    rw [he] at hm
    push_cast
    linarith

theorem wetError_sq_mean_le {k : ℕ} (σ : History → PMF (Fin (k+1))) (A : History → PMF (Fin 2))
    (t : ℕ) (i : Fin (k+1)) : mean σ A t (fun w => wetError σ w i ^2) ≤ (t:ℝ) := by
  induction t with
  | zero => simp [mean, wetError, wetCount, weightedWet]
  | succ t ih =>
    rw [mean_succ]
    have h : ∀ w : Code k t,
        expect (σ (decode w)) (fun j => expect (A (decode w)) (fun x => wetError σ (snocCode w j x) i ^2)) ≤ wetError σ w i ^2+1 := by
      intro w
      simpa only [wetError_snoc] using expect_center_step (σ (decode w)) (A (decode w)) i (fun x => if x=1 then 1 else 0) (fun _ => by split_ifs <;> norm_num) (wetError σ w i)
    have hm := expect_mono (codedLaw σ A t) h
    change mean σ A t _ ≤ mean σ A t _ at hm
    have he : mean σ A t (fun w => wetError σ w i ^2+1)=mean σ A t (fun w => wetError σ w i ^2)+1 := by
      change expect _ _ = expect _ _+1
      rw [expect_add, expect_const]
    rw [he] at hm
    push_cast
    linarith

theorem expect_abs_le_sqrt {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) {b : ℝ}
    (hb : 0 ≤ b) (h : expect p (fun a => f a^2) ≤ b) : expect p (fun a => |f a|) ≤ Real.sqrt b := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R:=ℝ) Finset.univ
    (fun a _ => show 0 ≤ (p a).toReal from ENNReal.toReal_nonneg)
    (fun a _ => mul_nonneg (show 0 ≤ (p a).toReal from ENNReal.toReal_nonneg) (sq_nonneg (f a)))
    (r:=fun a => (p a).toReal*|f a|) (fun a _ => by rw [mul_pow, sq_abs]; ring_nf; rfl)
  rw [sum_mass, one_mul] at hc
  change expect p (fun a => |f a|)^2 ≤ expect p (fun a => f a^2) at hc
  have hn : 0 ≤ expect p (fun a => |f a|) := Finset.sum_nonneg fun a _ => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)
  have hs := Real.sq_sqrt hb
  have hp := Real.sqrt_nonneg b
  nlinarith

theorem countError_abs_mean_le {k : ℕ} (σ : History → PMF (Fin (k+1))) (A : History → PMF (Fin 2)) (t : ℕ) (i : Fin (k+1)) :
    mean σ A t (fun w => |countError σ w i|) ≤ Real.sqrt (t:ℝ) :=
  expect_abs_le_sqrt _ _ (Nat.cast_nonneg _) (countError_sq_mean_le σ A t i)
theorem wetError_abs_mean_le {k : ℕ} (σ : History → PMF (Fin (k+1))) (A : History → PMF (Fin 2)) (t : ℕ) (i : Fin (k+1)) :
    mean σ A t (fun w => |wetError σ w i|) ≤ Real.sqrt (t:ℝ) :=
  expect_abs_le_sqrt _ _ (Nat.cast_nonneg _) (wetError_sq_mean_le σ A t i)

end ACProof

noncomputable section
open scoped BigOperators
open AsympCalib.Main CalibratedCE.Forecast
namespace ACProof

theorem outcome_bounds (h : History) (s : ℕ) : 0 ≤ outcomeR h s ∧ outcomeR h s ≤ 1 := by
  unfold outcomeR; split_ifs <;> norm_num

theorem mu_isDist {k : ℕ} (σ : History → PMF (Fin (k+1))) (h : History) (s : ℕ) :
    IsDist (muH σ h s) := by
  exact ⟨fun _ => ENNReal.toReal_nonneg, sum_mass (σ (h.take s))⟩

theorem regret_prefix {k : ℕ} (σ : History → PMF (Fin (k+1))) (h : History) (s : ℕ) (i j : Fin (k+1)) :
    Rg (brierLoss k (outcomeR (h.take s))) (muH σ (h.take s)) s i j =
    Rg (brierLoss k (outcomeR h)) (muH σ h) s i j := by
  unfold Rg S
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hlt := Finset.mem_range.mp hr
  rw [mu_prefix σ h hlt.le]
  simp only [brierLoss, outcome_prefix h hlt]

theorem history_conservation {k : ℕ} (σ : History → PMF (Fin (k+1)))
    (hσ : IsConservationForecaster k σ) (h : History) {s : ℕ} (hs : s ≤ h.length) :
    Conservation k (outcomeR h) (muH σ h) s := by
  intro i
  have h := hσ (h.take s) i
  simpa only [List.length_take, Nat.min_eq_left hs, regret_prefix, muH] using h

theorem weighted_bounds {k t : ℕ} (σ : History → PMF (Fin (k+1))) (w : Code k t) (i : Fin (k+1)) :
    0 ≤ weightedWet σ w i ∧ weightedWet σ w i ≤ weightedCount σ w i := by
  constructor
  · exact Finset.sum_nonneg fun s _ => mul_nonneg ENNReal.toReal_nonneg (outcome_bounds _ _).1
  · unfold weightedWet weightedCount nTilde
    apply Finset.sum_le_sum
    intro s _
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (outcome_bounds _ _).2

theorem CTildeH_eq_sum {k t : ℕ} (σ : History → PMF (Fin (k+1))) (w : Code k t) :
    CTildeH k σ (decode w) = (∑ i, scoreTerm (gridPt k i) (weightedCount σ w i) (weightedWet σ w i))/(t:ℝ) := by
  simp only [CTildeH, decode_length, CTilde, rhoTilde, weightedCount, weightedWet, scoreTerm]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem actual_weighted_le {k t : ℕ} (hk : 0<k) (σ : History → PMF (Fin (k+1))) (w : Code k t) :
    actualScore w ≤ CTildeH k σ (decode w) + (∑ i, (|countError σ w i| + 2 * |wetError σ w i|))/(t:ℝ) := by
  rw [actualScore_eq_sum hk, CTildeH_eq_sum, ← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  have h := scoreTerm_lipschitz (gridPt_nonneg k i) (gridPt_le_one k hk i)
    (wetCount_nonneg w i) (wetCount_le_count w i) (weighted_bounds σ w i).1 (weighted_bounds σ w i).2
  have h' := (le_abs_self (scoreTerm (gridPt k i) (count w i) (wetCount w i)-scoreTerm (gridPt k i) (weightedCount σ w i) (weightedWet σ w i))).trans h
  dsimp [scoreTerm, countError, wetError] at *
  linarith

theorem path_weighted_bound {k t : ℕ} (hk : 0<k) (ht : 0<t) (σ : History → PMF (Fin (k+1)))
    (hσ : IsConservationForecaster k σ) (w : Code k t) :
    CTildeH k σ (decode w) ≤ (k+1:ℕ)*Real.sqrt ((k+1:ℕ)*(t:ℝ))/(t:ℝ)+1/(4*(k:ℝ)^2) := by
  unfold CTildeH
  rw [decode_length]
  apply weighted_score_bound hk
  · intro s _; exact outcome_bounds _ _
  · intro s _; exact mu_isDist _ _ _
  · intro s hs; exact history_conservation σ hσ _ (by simpa using (Nat.le_of_lt hs))
  · exact ht

theorem expect_sum {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (f : α → β → ℝ) :
    expect p (fun a => ∑ b, f a b) = ∑ b, expect p (fun a => f a b) := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]
theorem expect_div {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    expect p (fun a => f a/c)=expect p f/c := by
  simp only [div_eq_mul_inv, expect_mul_const]

theorem expected_score_bound {k : ℕ} (hk : 0<k) (σ : History → PMF (Fin (k+1)))
    (hσ : IsConservationForecaster k σ) (A : History → PMF (Fin 2)) {t : ℕ} (ht : 0<t) :
    mean σ A t actualScore ≤ (k+1:ℕ)*Real.sqrt ((k+1:ℕ)*(t:ℝ))/(t:ℝ) +
      3*(k+1:ℕ)*Real.sqrt (t:ℝ)/(t:ℝ)+1/(4*(k:ℝ)^2) := by
  let B : ℝ := (k+1:ℕ)*Real.sqrt ((k+1:ℕ)*(t:ℝ))/(t:ℝ)+1/(4*(k:ℝ)^2)
  have hp : ∀ w : Code k t, actualScore w ≤ B+(∑ i, (|countError σ w i| + 2 * |wetError σ w i|))/(t:ℝ) := by
    intro w
    exact (actual_weighted_le hk σ w).trans (add_le_add (path_weighted_bound hk ht σ hσ w) le_rfl)
  have hm := expect_mono (codedLaw σ A t) hp
  change mean σ A t actualScore ≤ _ at hm
  rw [expect_add, expect_const, expect_div, expect_sum] at hm
  simp only [expect_add, expect_const_mul] at hm
  have hs : (∑ i, (expect (codedLaw σ A t) (fun w => |countError σ w i|) +
      2*expect (codedLaw σ A t) (fun w => |wetError σ w i|))) ≤ 3*(k+1:ℕ)*Real.sqrt (t:ℝ) := by
    calc
      _ ≤ ∑ _i : Fin (k+1), (Real.sqrt (t:ℝ)+2*Real.sqrt (t:ℝ)) := by
        apply Finset.sum_le_sum
        intro i _
        exact add_le_add (countError_abs_mean_le σ A t i) (mul_le_mul_of_nonneg_left (wetError_abs_mean_le σ A t i) (by norm_num))
      _ = _ := by simp; ring
  have hd := div_le_div_of_nonneg_right hs (show (0:ℝ) ≤ t by positivity)
  dsimp [B] at hm
  linarith

end ACProof

noncomputable section
open scoped BigOperators
open Classical AsympCalib.Main CalibratedCE.Forecast
namespace ACProof

theorem event_eq_ofReal {α : Type*} [Fintype α] (p : PMF α) (S : Set α) :
    p.toOuterMeasure S = ENNReal.ofReal (∑ a, if a∈S then (p a).toReal else 0) := by
  rw [PMF.toOuterMeasure_apply_fintype, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases h : a∈S <;> simp [h, ENNReal.ofReal_toReal (p.apply_ne_top a)]
  · intro a _; split_ifs <;> positivity

theorem finite_markov_strict {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (he : expect p f  <  ε^2) :
    ENNReal.ofReal (1-ε)  <  p.toOuterMeasure {a | f a < ε} := by
  let mass := ∑ a, if f a < ε then (p a).toReal else 0
  have hm : ε-expect p f ≤ ε*mass := by
    calc
      ε-expect p f = ∑ a, (p a).toReal*(ε-f a) := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_mass, one_mul, expect]
      _ ≤ ∑ a, ε*(if f a < ε then (p a).toReal else 0) := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs with h
        · nlinarith [mul_nonneg (show 0 ≤ (p a).toReal from ENNReal.toReal_nonneg) (hf a)]
        · have hn : ε ≤ f a := le_of_not_gt h
          have hp : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
          simp only [mul_zero]
          exact mul_nonpos_of_nonneg_of_nonpos hp (sub_nonpos.mpr hn)
      _ = ε*mass := by rw [Finset.mul_sum]
  have hgood : 1-ε  <  mass := by nlinarith
  rw [event_eq_ofReal]
  apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).2
  exact hgood

theorem explicit_horizon {k : ℕ} (hk0 : 0 < k) {ε : ℝ} (hε : 0 < ε)
    (hk : 1/ε^2 ≤ (k:ℝ)) :
    ∃ T : ℕ, 0 < T ∧ ∀ t ≥ T,
      (k+1:ℕ)*Real.sqrt ((k+1:ℕ)*(t:ℝ))/(t:ℝ) + 3*(k+1:ℕ)*Real.sqrt (t:ℝ)/(t:ℝ) +1/(4*(k:ℝ)^2)  <  ε^2 := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk0
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk0
  have he2 : 0 < ε^2 := sq_pos_of_pos hε
  have hx : 1 ≤ (k:ℝ)*ε^2 := (div_le_iff₀ he2).mp hk
  have hx2 : 1 ≤ (k:ℝ)^2*ε^2 := hx.trans (mul_le_mul_of_nonneg_right (by nlinarith : (k:ℝ) ≤ (k:ℝ)^2) he2.le)
  let b : ℝ := 1/(4*(k:ℝ)^2)
  have hb : b < ε^2 := by
    dsimp [b]
    apply (div_lt_iff₀ (by positivity : (0:ℝ) < 4*(k:ℝ)^2)).2
    nlinarith
  let g := ε^2-b
  have hg : 0 < g := sub_pos.mpr hb
  let m : ℝ := (k+1:ℕ)
  have hm : 0 < m := by dsimp [m]; positivity
  let C := m*Real.sqrt m+3*m
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨T,hT⟩ := exists_nat_gt ((C/g)^2+1)
  have hT0 : 0 < T := by exact_mod_cast (show (0:ℝ) < T by nlinarith [sq_nonneg (C/g)])
  refine ⟨T,hT0,?_⟩
  intro t ht
  have htt : (T:ℝ) ≤ t := by exact_mod_cast ht
  have htR : (0:ℝ) < t := by exact_mod_cast (lt_of_lt_of_le hT0 ht)
  have hs : 0 < Real.sqrt (t:ℝ) := Real.sqrt_pos.2 htR
  have hs2 := Real.sq_sqrt htR.le
  have hcg : C/g  <  Real.sqrt (t:ℝ) := by
    have hn : 0 ≤ C/g := div_nonneg hC.le hg.le
    nlinarith
  have herr : C/Real.sqrt (t:ℝ) < g := by
    apply (div_lt_iff₀ hs).2
    have := (div_lt_iff₀ hg).mp hcg
    nlinarith
  have hid : m*Real.sqrt (m*(t:ℝ))/(t:ℝ)+3*m*Real.sqrt (t:ℝ)/(t:ℝ)=C/Real.sqrt (t:ℝ) := by
    rw [Real.sqrt_mul hm.le]
    dsimp [C]
    field_simp
    nlinarith
  change m*Real.sqrt (m*(t:ℝ))/(t:ℝ)+3*m*Real.sqrt (t:ℝ)/(t:ℝ)+b < ε^2
  rw [hid]
  dsimp [g] at herr
  linarith
end ACProof

namespace AsympCalib.Main

theorem theorem_1 (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (hk0 : 0 < k) (hk : 1 / ε ^ 2 ≤ (k : ℝ))
    (σ : History → PMF (Fin (k + 1)))
    (hσ : IsConservationForecaster k σ)
    (A : History → PMF (Fin 2)) :
    ∃ t₁ : ℕ, ∀ t ≥ t₁,
      ENNReal.ofReal (1 - ε) <
        (CalibratedCE.Forecast.histLaw (forecaster k σ) A t).toOuterMeasure
          {h : History | CalibratedCE.Forecast.calibScore2Hj h 1 < ε} := by
  by_cases he : ε ≤ 1
  · obtain ⟨T,hT,hbound⟩ := ACProof.explicit_horizon hk0 hε hk
    refine ⟨T,fun t ht => ?_⟩
    rw [← ACProof.codedLaw_map σ A t, PMF.toOuterMeasure_map_apply]
    change ENNReal.ofReal (1-ε) < (ACProof.codedLaw σ A t).toOuterMeasure {w | ACProof.actualScore w < ε}
    apply ACProof.finite_markov_strict _ _ (ACProof.actualScore_nonneg hk0) hε he
    exact (ACProof.expected_score_bound hk0 σ hσ A (lt_of_lt_of_le hT ht)).trans_lt (hbound t ht)
  · refine ⟨0,fun t _ => ?_⟩
    rw [← ACProof.codedLaw_map σ A t, PMF.toOuterMeasure_map_apply]
    change ENNReal.ofReal (1-ε) < (ACProof.codedLaw σ A t).toOuterMeasure {w | ACProof.actualScore w < ε}
    have hg : {w : ACProof.Code k t | ACProof.actualScore w < ε} = Set.univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro w
      exact (ACProof.actualScore_le_one hk0 w).trans_lt (lt_of_not_ge he)
    rw [hg]
    have hzero : ENNReal.ofReal (1-ε)=0 := ENNReal.ofReal_eq_zero.mpr (by linarith)
    have hsum : (∑ w : ACProof.Code k t, ACProof.codedLaw σ A t w)=1 :=
      (tsum_fintype (ACProof.codedLaw σ A t)).symm.trans (PMF.tsum_coe _)
    simp only [hzero, PMF.toOuterMeasure_apply_fintype, Set.indicator_univ, hsum]
    exact zero_lt_one
end AsympCalib.Main

theorem solution (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (hk0 : 0 < k) (hk : 1 / ε ^ 2 ≤ (k : ℝ))
    (σ : History → PMF (Fin (k + 1)))
    (hσ : IsConservationForecaster k σ)
    (A : History → PMF (Fin 2)) :
    ∃ t₁ : ℕ, ∀ t ≥ t₁,
      ENNReal.ofReal (1 - ε) <
        (CalibratedCE.Forecast.histLaw (forecaster k σ) A t).toOuterMeasure
          {h : History | CalibratedCE.Forecast.calibScore2Hj h 1 < ε} :=
  AsympCalib.Main.theorem_1 ε hε k hk0 hk σ hσ A

