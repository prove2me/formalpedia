-- Prove2me | Definitions.Def_MegiddoLP_Infeasibility
-- name    : MegiddoLP_Infeasibility
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-23T06:31:13.226911+00:00
-- url     : https://prove2.me/theorems/8731ba2d-5693-4514-8593-ad26fa8d367b
-- title:
--   Infeasibility value and dimensional reduction for fixed-dimension linear programs
-- statement:
--   A common relaxation value detects feasibility. The accompanying lemmas describe how the value behaves on line segments, under removal of slack constraints, and when restricting to a coordinate slice or hyperplane.
-- source:
--   Nimrod Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, JACM 31(1), 1984, §2 and §5. https://theory.stanford.edu/~megiddo/pdf/lplin.pdf

import Definitions.Def_Polyhedron
import Definitions.Def_MegiddoLP_FixedDim_Infeasibility
import Mathlib.Topology.Order.IntermediateValue

/-!
# Convex Minmax Infeasibility Theory for Fixed-Dimension LP

Reduces LP feasibility `∃ x, A x ≥ b` in `ℝ^d` to unconstrained minimization of
`rInfeas hm A b x = max_{i < m} (b i - A i ⬝ᵥ x)` on systems carrying an immortal
zero row `(0, 0)` at index `0`.

Key results:
1. `polyhedron_nonempty_iff_min_rInfeas`: appending row `(0, 0)` turns feasibility of `A x ≥ b`
   into `rInfeas x* ≤ 0` at any global minimizer `x*`.
2. `sliceTransform`: explicit invertible affine coordinate change sending `{x | h ⬝ᵥ x = β}`
   (`h p ≠ 0`) to `{y | y (Fin.last d) = 0}` while preserving residuals `b i - A i ⬝ᵥ x`
   identically and keeping row `0 = (0, 0)` unchanged.
3. `oracle_rInfeas`: unified hyperplane-oracle soundness (generalizing `oracle_caseII` without
   assuming `polyhedron = ∅`), returning a strict side `σ ∈ {.lt, .gt}` valid on the strict
   sublevel set `{w | rInfeas w < rInfeas x'}`.
4. `prune_unwind_sound`: convexity + Intermediate Value Theorem soundness of dropping rows
   dominated on an intersection of oracle halfspaces and unwinding by `argmin {x_cand, y*}` —
   requiring zero LP duality or abstract attainment theorems.
5. `solveAtMostTwoRows_min`: closed-form global minimizer when `m ≤ 2` (`Row 0 = (0, 0)`).
-/

namespace MegiddoLP.Infeasibility

open Matrix LinearOptimization

/-- Maximum residual `max_{i : Fin m} (b i - A i ⬝ᵥ x)` for `0 < m`. -/
noncomputable def rInfeas {m d : ℕ} (hm : 0 < m)
    (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ) (x : Fin d → ℝ) : ℝ :=
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  Finset.univ.sup' Finset.univ_nonempty (fun i => b i - A i ⬝ᵥ x)

theorem le_rInfeas {m d : ℕ} (hm : 0 < m) (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (x : Fin d → ℝ) (i : Fin m) :
    b i - A i ⬝ᵥ x ≤ rInfeas hm A b x := by
  unfold rInfeas
  exact Finset.le_sup' (fun i => b i - A i ⬝ᵥ x) (Finset.mem_univ i)

theorem rInfeas_le_iff {m d : ℕ} (hm : 0 < m) (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (x : Fin d → ℝ) (c : ℝ) :
    rInfeas hm A b x ≤ c ↔ ∀ i, b i - A i ⬝ᵥ x ≤ c := by
  unfold rInfeas
  simp [Finset.sup'_le_iff]

theorem rInfeas_lt_iff {m d : ℕ} (hm : 0 < m) (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (x : Fin d → ℝ) (c : ℝ) :
    rInfeas hm A b x < c ↔ ∀ i, b i - A i ⬝ᵥ x < c := by
  unfold rInfeas
  simp [Finset.sup'_lt_iff]

theorem rInfeas_nonneg_of_zero_row {m d : ℕ} (hm : 0 < m)
    (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (hA0 : A ⟨0, hm⟩ = 0) (hb0 : b ⟨0, hm⟩ = 0) (x : Fin d → ℝ) :
    0 ≤ rInfeas hm A b x := by
  have h := le_rInfeas hm A b x ⟨0, hm⟩
  simpa [hA0, hb0] using h

/-- Prepending row `(0, 0)` to an `n × d` LP `(A, b)` turns feasibility of `polyhedron A b`
into `rInfeas ≤ 0` at any global minimizer `x*`. -/
def augA {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) : Fin (n + 1) → Fin d → ℝ :=
  Fin.cases 0 (fun i => A i)

def augB {n : ℕ} (b : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases 0 b

theorem polyhedron_nonempty_iff_min_aug {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (xs : Fin d → ℝ)
    (hmin : ∀ w : Fin d → ℝ,
      rInfeas (Nat.succ_pos n) (augA A) (augB b) xs ≤
      rInfeas (Nat.succ_pos n) (augA A) (augB b) w) :
    rInfeas (Nat.succ_pos n) (augA A) (augB b) xs ≤ 0 ↔ (polyhedron A b).Nonempty := by
  constructor
  · intro hle
    rw [rInfeas_le_iff] at hle
    refine ⟨xs, fun i => ?_⟩
    have hi := hle i.succ
    simp only [augA, augB, Fin.cases_succ] at hi
    show b i ≤ A.mulVec xs i
    change b i ≤ A i ⬝ᵥ xs
    linarith
  · rintro ⟨w, hw⟩
    refine le_trans (hmin w) ?_
    rw [rInfeas_le_iff]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [augA, augB]
    · simp only [augA, augB, Fin.cases_succ]
      have hj : b j ≤ A j ⬝ᵥ w := hw j
      linarith

/-! ## Continuity and Convexity of `rInfeas` -/

theorem rInfeas_convex_segment {m d : ℕ} (hm : 0 < m)
    (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (x y : Fin d → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rInfeas hm A b ((1 - t) • x + t • y) ≤
      (1 - t) * rInfeas hm A b x + t * rInfeas hm A b y := by
  rw [rInfeas_le_iff]
  intro i
  have hx := le_rInfeas hm A b x i
  have hy := le_rInfeas hm A b y i
  have h1t : 0 ≤ 1 - t := by linarith
  have hdot : b i - A i ⬝ᵥ ((1 - t) • x + t • y) =
      (1 - t) * (b i - A i ⬝ᵥ x) + t * (b i - A i ⬝ᵥ y) := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [hdot]
  nlinarith [mul_le_mul_of_nonneg_left hx h1t, mul_le_mul_of_nonneg_left hy ht0]

theorem rInfeas_continuous_line {m d : ℕ} (hm : 0 < m)
    (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ) (x y : Fin d → ℝ) :
    Continuous (fun t : ℝ => rInfeas hm A b ((1 - t) • x + t • y)) := by
  unfold rInfeas
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  apply Continuous.finset_sup'_apply
  intro i _
  have hdot : (fun t : ℝ => b i - A i ⬝ᵥ ((1 - t) • x + t • y)) =
      fun t : ℝ => b i - ((1 - t) * (A i ⬝ᵥ x) + t * (A i ⬝ᵥ y)) := by
    ext t
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [hdot]
  fun_prop

/-! ## Pruning + Backward Unwind Soundness (Pure Convexity + IVT) -/

/-- If `A', b'` is a subset of rows of `A, b` (`A' j = A (emb j)`, `b' j = b (emb j)`),
`xCand` has `vBar = rInfeas hm A b xCand`, `rInfeas` agrees between `(A, b)` and `(A', b')`
on `{w | rInfeas hm A b w < vBar}`, and `yStar` globally minimizes `rInfeas hm' A' b'`,
then `if vBar ≤ rInfeas hm A b yStar then xCand else yStar` globally minimizes `rInfeas hm A b`. -/
theorem prune_unwind_sound {m m' d : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (emb : Fin m' → Fin m)
    (xCand yStar : Fin d → ℝ)
    (hAgree : ∀ w : Fin d → ℝ,
      rInfeas hm A b w < rInfeas hm A b xCand →
      rInfeas hm' (fun j => A (emb j)) (fun j => b (emb j)) w = rInfeas hm A b w)
    (hyStar : ∀ w : Fin d → ℝ,
      rInfeas hm' (fun j => A (emb j)) (fun j => b (emb j)) yStar ≤
      rInfeas hm' (fun j => A (emb j)) (fun j => b (emb j)) w) :
    let xOut := if rInfeas hm A b xCand ≤ rInfeas hm A b yStar then xCand else yStar
    ∀ w : Fin d → ℝ, rInfeas hm A b xOut ≤ rInfeas hm A b w := by
  set A' : Fin m' → Fin d → ℝ := fun j => A (emb j)
  intro xOut w
  have hOut_le_cand : rInfeas hm A b xOut ≤ rInfeas hm A b xCand := by
    dsimp only [xOut]; split_ifs with h
    · exact le_rfl
    · exact le_of_not_ge h
  have hOut_le_y : rInfeas hm A b xOut ≤ rInfeas hm A b yStar := by
    dsimp only [xOut]; split_ifs with h
    · exact h
    · exact le_rfl
  by_cases hw_cand : rInfeas hm A b xCand ≤ rInfeas hm A b w
  · exact le_trans hOut_le_cand hw_cand
  push Not at hw_cand
  by_cases hw_y : rInfeas hm A b yStar ≤ rInfeas hm A b w
  · exact le_trans hOut_le_y hw_y
  push Not at hw_y
  exfalso
  -- Both `rInfeas A b w < rInfeas A b xCand` and `rInfeas A b w < rInfeas A b yStar`
  have hw_eq : rInfeas hm' A' (fun j => b (emb j)) w = rInfeas hm A b w := hAgree w hw_cand
  have hy_le_w : rInfeas hm' A' (fun j => b (emb j)) yStar ≤ rInfeas hm A b w := by
    rw [← hw_eq]; exact hyStar w
  by_cases hy_cand : rInfeas hm A b yStar < rInfeas hm A b xCand
  · have hy_eq := hAgree yStar hy_cand
    linarith
  push Not at hy_cand
  -- IVT on `g t = rInfeas hm A b ((1 - t) • w + t • yStar)` over `[0, 1]`
  set g : ℝ → ℝ := fun t => rInfeas hm A b ((1 - t) • w + t • yStar)
  have hg_cont : ContinuousOn g (Set.Icc 0 1) :=
    (rInfeas_continuous_line hm A b w yStar).continuousOn
  have hg0 : g 0 = rInfeas hm A b w := by simp [g]
  have hg1 : g 1 = rInfeas hm A b yStar := by simp [g]
  set mid := (rInfeas hm A b w + rInfeas hm A b xCand) / 2
  have hmid_mem : mid ∈ Set.Icc (g 0) (g 1) := by
    rw [hg0, hg1]
    exact ⟨by dsimp [mid]; linarith, by dsimp [mid]; linarith⟩
  obtain ⟨t₀, ht₀, hgt₀⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hg_cont hmid_mem
  have ht₀_lt_cand : g t₀ < rInfeas hm A b xCand := by
    rw [hgt₀]; dsimp [mid]; linarith
  have ht₀_gt_w : rInfeas hm A b w < g t₀ := by
    rw [hgt₀]; dsimp [mid]; linarith
  have hzt₀_eq := hAgree ((1 - t₀) • w + t₀ • yStar) ht₀_lt_cand
  have hconv := rInfeas_convex_segment hm' A' (fun j => b (emb j)) w yStar ht₀.1 ht₀.2
  rw [hzt₀_eq, hw_eq] at hconv
  have h1t : 0 ≤ 1 - t₀ := by linarith [ht₀.2]
  have hmul : t₀ * rInfeas hm' A' (fun j => b (emb j)) yStar ≤ t₀ * rInfeas hm A b w :=
    mul_le_mul_of_nonneg_left hy_le_w ht₀.1
  change g t₀ ≤ _ at hconv
  linarith

/-! ## Affine Coordinate Transformation for Hyperplane Slicing -/

/-- Insert a value `val` at coordinate `p : Fin (d + 1)` and fill the remaining `d`
coordinates from `y' : Fin d → ℝ` via `p.succAbove`. -/
def insertCoord {d : ℕ} (p : Fin (d + 1)) (y' : Fin d → ℝ) (val : ℝ) : Fin (d + 1) → ℝ :=
  p.insertNth val y'

/-- Lift `(y' : Fin d → ℝ, s : ℝ)` to `x : Fin (d + 1) → ℝ` so that `h ⬝ᵥ x = β + s`
when `h p ≠ 0`. Explicitly: `x (p.succAbove j) = y' j` and
`x p = (β + s - ∑ j, h (p.succAbove j) * y' j) / h p`. -/
noncomputable def liftSlice {d : ℕ} (h : Fin (d + 1) → ℝ) (p : Fin (d + 1)) (β : ℝ)
    (y' : Fin d → ℝ) (s : ℝ) : Fin (d + 1) → ℝ :=
  p.insertNth ((β + s - ∑ j : Fin d, h (p.succAbove j) * y' j) / h p) y'

/-- Inverse projection from `x : Fin (d + 1) → ℝ` to `(y', s)` where `s = h ⬝ᵥ x - β`. -/
def projSlice {d : ℕ} (p : Fin (d + 1)) (x : Fin (d + 1) → ℝ) : Fin d → ℝ :=
  fun j => x (p.succAbove j)

theorem dotProduct_insertNth {d : ℕ} (p : Fin (d + 1)) (a : Fin (d + 1) → ℝ)
    (val : ℝ) (y' : Fin d → ℝ) :
    a ⬝ᵥ p.insertNth val y' = a p * val + ∑ j : Fin d, a (p.succAbove j) * y' j := by
  simp only [dotProduct]
  rw [Fin.sum_univ_succAbove _ p]
  simp

theorem liftSlice_dot_h {d : ℕ} (h : Fin (d + 1) → ℝ) (p : Fin (d + 1)) (hp : h p ≠ 0)
    (β : ℝ) (y' : Fin d → ℝ) (s : ℝ) :
    h ⬝ᵥ liftSlice h p β y' s = β + s := by
  unfold liftSlice
  rw [dotProduct_insertNth]
  field_simp [hp]
  ring

theorem liftSlice_projSlice {d : ℕ} (h : Fin (d + 1) → ℝ) (p : Fin (d + 1)) (hp : h p ≠ 0)
    (β : ℝ) (x : Fin (d + 1) → ℝ) :
    liftSlice h p β (projSlice p x) (h ⬝ᵥ x - β) = x := by
  unfold liftSlice projSlice
  have hsum : h ⬝ᵥ x = h p * x p + ∑ j : Fin d, h (p.succAbove j) * x (p.succAbove j) := by
    simp only [dotProduct]
    rw [Fin.sum_univ_succAbove _ p]
  have hpval : (β + (h ⬝ᵥ x - β) - ∑ j : Fin d, h (p.succAbove j) * x (p.succAbove j)) / h p =
      x p := by
    rw [hsum]
    field_simp [hp]
    ring
  rw [hpval]
  ext k
  by_cases hk : k = p
  · subst hk; simp
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    simp

/-- Transformed row normal in `Fin (d + 1) → ℝ` (first `d` coords for `y'`, last coord for `s`). -/
noncomputable def transRowA {d : ℕ} (h : Fin (d + 1) → ℝ) (p : Fin (d + 1))
    (ai : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc (fun j : Fin d => ai (p.succAbove j) - (ai p / h p) * h (p.succAbove j)) (ai p / h p)

/-- Transformed row RHS so residual `transRowB - transRowA ⬝ᵥ snoc y' s = bi - ai ⬝ᵥ liftSlice`. -/
noncomputable def transRowB {d : ℕ} (h : Fin (d + 1) → ℝ) (p : Fin (d + 1)) (β : ℝ)
    (ai : Fin (d + 1) → ℝ) (bi : ℝ) : ℝ :=
  bi - (ai p / h p) * β

theorem transRow_residual {d : ℕ} (h : Fin (d + 1) → ℝ) (p : Fin (d + 1)) (hp : h p ≠ 0)
    (β : ℝ) (ai : Fin (d + 1) → ℝ) (bi : ℝ) (y' : Fin d → ℝ) (s : ℝ) :
    transRowB h p β ai bi - transRowA h p ai ⬝ᵥ Fin.snoc y' s =
      bi - ai ⬝ᵥ liftSlice h p β y' s := by
  unfold transRowB transRowA liftSlice
  rw [dotProduct_insertNth]
  simp only [dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  have hsub : ∑ i : Fin d, (ai (p.succAbove i) - ai p / h p * h (p.succAbove i)) * y' i =
      (∑ i : Fin d, ai (p.succAbove i) * y' i) -
      (ai p / h p) * ∑ i : Fin d, h (p.succAbove i) * y' i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hsub]
  field_simp [hp]
  ring

@[simp] theorem transRowA_zero {d : ℕ} (h : Fin (d + 1) → ℝ) (p : Fin (d + 1)) :
    transRowA h p 0 = 0 := by
  ext k
  unfold transRowA
  refine Fin.lastCases ?_ (fun j => ?_) k <;> simp

@[simp] theorem transRowB_zero {d : ℕ} (h : Fin (d + 1) → ℝ) (p : Fin (d + 1)) (β : ℝ) :
    transRowB h p β 0 0 = 0 := by
  simp [transRowB]

/-! ## Generalized Oracle Soundness for `rInfeas` (No Infeasibility Hypothesis Needed) -/

theorem rInfeas_dir_contradiction {m d : ℕ} (hm : 0 < m)
    (A : Fin m → Fin (d + 1) → ℝ) (b : Fin m → ℝ) (x' : Fin (d + 1) → ℝ)
    (hx' : x' (Fin.last d) = 0)
    (hmin : ∀ w : Fin (d + 1) → ℝ, w (Fin.last d) = 0 → rInfeas hm A b x' ≤ rInfeas hm A b w)
    (y : Fin (d + 1) → ℝ) (hy : ∀ i, rInfeas hm A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ y)
    (w : Fin (d + 1) → ℝ) (hw : rInfeas hm A b w < rInfeas hm A b x')
    (hyw : y (Fin.last d) * w (Fin.last d) < 0) : False := by
  set c := rInfeas hm A b x'
  set yd := y (Fin.last d)
  set wd := w (Fin.last d)
  have hyd0 : yd ≠ 0 := fun h => by rw [h, zero_mul] at hyw; exact lt_irrefl _ hyw
  set α : ℝ := -wd / yd with hα
  have hαpos : 0 ≤ α := by
    have : α = -(yd * wd) / (yd ^ 2) := by rw [hα]; field_simp
    rw [this]; exact div_nonneg (by linarith) (by positivity)
  set v : Fin (d + 1) → ℝ := (w - x') + α • y with hv
  set K : Fin m → ℝ := fun i => A i ⬝ᵥ v with hK
  set r : Fin m → ℝ := fun i => b i - A i ⬝ᵥ x' with hr
  have hKpos : ∀ i, c = r i → 0 < K i := by
    intro i hi
    have h1 := le_rInfeas hm A b w i
    have h2 := hy i hi
    have : K i = (A i ⬝ᵥ w - A i ⬝ᵥ x') + α * (A i ⬝ᵥ y) := by
      simp only [hK, hv, dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [this]
    have h3 : 0 ≤ α * (A i ⬝ᵥ y) := mul_nonneg hαpos h2
    simp only [hr] at hi
    linarith
  have hev : ∀ i, ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), r i - s * K i < c := by
    intro i
    rcases (le_rInfeas hm A b x' i).lt_or_eq with h | h
    · have ht : Filter.Tendsto (fun s : ℝ => r i - s * K i) (nhds 0) (nhds (r i)) := by
        have h0 : Filter.Tendsto (fun s : ℝ => r i - s * K i) (nhds 0) (nhds (r i - 0 * K i)) :=
          tendsto_const_nhds.sub (Filter.tendsto_id.mul tendsto_const_nhds)
        rwa [zero_mul, sub_zero] at h0
      exact nhdsWithin_le_nhds (ht.eventually (gt_mem_nhds h))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have : 0 < s * K i := mul_pos hs (hKpos i h.symm)
      linarith
  have hall := (Filter.eventually_all.2 hev).and self_mem_nhdsWithin
  obtain ⟨s, hs, _⟩ := hall.exists
  set q : Fin (d + 1) → ℝ := x' + s • v with hq
  have hqd : q (Fin.last d) = 0 := by
    simp only [hq, hv, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hx']
    change 0 + s * (wd - 0 + α * yd) = 0
    rw [hα]; field_simp; ring
  have hlt : rInfeas hm A b q < c := by
    rw [rInfeas_lt_iff]
    intro i
    have e : b i - A i ⬝ᵥ q = r i - s * K i := by
      simp only [hq, hr, hK, dotProduct_add, dotProduct_smul, smul_eq_mul]; ring
    rw [e]; exact hs i
  have := hmin q hqd
  linarith

/-- Unified oracle theorem on `{x | x (Fin.last d) = 0}`: given a slice minimizer `yStar : Fin d → ℝ`
and the Booleans `sys1` (`∃ y', ∀ i ∈ I', init A_i ⬝ᵥ y' ≥ -A_{i,last}`) and
`sys2` (`∃ z', ∀ i ∈ I', init A_i ⬝ᵥ z' ≥ A_{i,last}`), the returned side
`σ = if sys1 ∧ ¬sys2 then .gt else if ¬sys1 ∧ sys2 then .lt else .gt`
satisfies `∀ w, rInfeas w < rInfeas (snoc yStar 0) → compare (w (Fin.last d)) 0 = σ`. -/
theorem oracle_zero_coord {m d : ℕ} (hm : 0 < m)
    (A : Fin m → Fin (d + 1) → ℝ) (b : Fin m → ℝ) (yStar : Fin d → ℝ)
    (hSliceMin : ∀ y' : Fin d → ℝ,
      rInfeas hm A b (Fin.snoc yStar 0) ≤ rInfeas hm A b (Fin.snoc y' 0))
    {s1 s2 : Bool}
    (hs1 : s1 = true ↔ ∃ y' : Fin d → ℝ, ∀ i,
      rInfeas hm A b (Fin.snoc yStar 0) = b i - A i ⬝ᵥ Fin.snoc yStar 0 →
      -(A i (Fin.last d)) ≤ Fin.init (A i) ⬝ᵥ y')
    (hs2 : s2 = true ↔ ∃ z' : Fin d → ℝ, ∀ i,
      rInfeas hm A b (Fin.snoc yStar 0) = b i - A i ⬝ᵥ Fin.snoc yStar 0 →
      A i (Fin.last d) ≤ Fin.init (A i) ⬝ᵥ z') :
    let σ : Ordering := if s1 && !s2 then .gt else if !s1 && s2 then .lt else .gt
    ∀ w : Fin (d + 1) → ℝ,
      rInfeas hm A b w < rInfeas hm A b (Fin.snoc yStar 0) →
      compare (w (Fin.last d)) 0 = σ := by
  set x' : Fin (d + 1) → ℝ := Fin.snoc yStar 0
  have hx' : x' (Fin.last d) = 0 := Fin.snoc_last _ _
  have hmin : ∀ w : Fin (d + 1) → ℝ, w (Fin.last d) = 0 → rInfeas hm A b x' ≤ rInfeas hm A b w := by
    intro w hw0
    have heq : w = Fin.snoc (Fin.init w) 0 := by
      rw [← hw0]; exact (Fin.snoc_init_self w).symm
    rw [heq]; exact hSliceMin (Fin.init w)
  have hSys1Imp : (∃ y' : Fin d → ℝ, ∀ i, rInfeas hm A b x' = b i - A i ⬝ᵥ x' →
      -(A i (Fin.last d)) ≤ Fin.init (A i) ⬝ᵥ y') →
      ∀ w, rInfeas hm A b w < rInfeas hm A b x' → 0 < w (Fin.last d) := by
    rintro ⟨y', hy'⟩ w hw
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hneg | hzero
    · refine rInfeas_dir_contradiction hm A b x' hx' hmin (Fin.snoc y' 1) ?_ w hw ?_
      · intro i hi
        have := hy' i hi
        simp only [dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.init] at this ⊢
        linarith
      · simp only [Fin.snoc_last, one_mul]; exact hneg
    · have := hmin w hzero; linarith
  have hSys2Imp : (∃ z' : Fin d → ℝ, ∀ i, rInfeas hm A b x' = b i - A i ⬝ᵥ x' →
      A i (Fin.last d) ≤ Fin.init (A i) ⬝ᵥ z') →
      ∀ w, rInfeas hm A b w < rInfeas hm A b x' → w (Fin.last d) < 0 := by
    rintro ⟨z', hz'⟩ w hw
    by_contra hge
    push Not at hge
    rcases lt_or_eq_of_le hge with hpos | hzero
    · refine rInfeas_dir_contradiction hm A b x' hx' hmin (Fin.snoc z' (-1)) ?_ w hw ?_
      · intro i hi
        have := hz' i hi
        simp only [dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.init] at this ⊢
        linarith
      · simp only [Fin.snoc_last]; linarith
    · have := hmin w hzero.symm; linarith
  intro σ w hw
  cases hs1v : s1 <;> cases hs2v : s2
  · -- both false: no `w` can have `rInfeas w < rInfeas x'`
    exfalso
    rcases lt_trichotomy (w (Fin.last d)) 0 with hneg | hzero | hpos
    · apply (mt hs2.mpr (by simp [hs2v]))
      refine ⟨(1 / (-w (Fin.last d))) • Fin.init (w - x'), fun i hi => ?_⟩
      have h1 := le_rInfeas hm A b w i
      have hact : 0 ≤ A i ⬝ᵥ (w - x') := by rw [dotProduct_sub]; linarith
      have hexp : A i ⬝ᵥ (w - x') = Fin.init (A i) ⬝ᵥ Fin.init (w - x') +
          A i (Fin.last d) * w (Fin.last d) := by
        simp only [dotProduct, Fin.sum_univ_castSucc, Fin.init, Pi.sub_apply, hx', sub_zero]
      rw [dotProduct_smul, smul_eq_mul]
      have hinv : 0 < -w (Fin.last d) := by linarith
      rw [one_div, le_inv_mul_iff₀ hinv]
      linarith
    · have := hmin w hzero; linarith
    · apply (mt hs1.mpr (by simp [hs1v]))
      refine ⟨(1 / (w (Fin.last d))) • Fin.init (w - x'), fun i hi => ?_⟩
      have h1 := le_rInfeas hm A b w i
      have hact : 0 ≤ A i ⬝ᵥ (w - x') := by rw [dotProduct_sub]; linarith
      have hexp : A i ⬝ᵥ (w - x') = Fin.init (A i) ⬝ᵥ Fin.init (w - x') +
          A i (Fin.last d) * w (Fin.last d) := by
        simp only [dotProduct, Fin.sum_univ_castSucc, Fin.init, Pi.sub_apply, hx', sub_zero]
      rw [dotProduct_smul, smul_eq_mul]
      rw [one_div, le_inv_mul_iff₀ hpos]
      linarith
  · -- s1 = false, s2 = true → σ = .lt
    have hlt := hSys2Imp (hs2.mp hs2v) w hw
    simp [σ, hs1v, hs2v, compare_lt_iff_lt.mpr hlt]
  · -- s1 = true, s2 = false → σ = .gt
    have hgt := hSys1Imp (hs1.mp hs1v) w hw
    simp [σ, hs1v, hs2v, compare_gt_iff_gt.mpr hgt]
  · -- both true: impossible when `rInfeas w < rInfeas x'`
    exfalso
    have hgt := hSys1Imp (hs1.mp hs1v) w hw
    have hlt := hSys2Imp (hs2.mp hs2v) w hw
    linarith

/-- Full arbitrary-hyperplane oracle soundness (`h p ≠ 0`). -/
theorem oracle_hyperplane {m d : ℕ} (hm : 0 < m)
    (A : Fin m → Fin (d + 1) → ℝ) (b : Fin m → ℝ)
    (h : Fin (d + 1) → ℝ) (p : Fin (d + 1)) (hp : h p ≠ 0) (β : ℝ)
    (yStar : Fin d → ℝ)
    (hSliceMin : ∀ y' : Fin d → ℝ,
      rInfeas hm (fun i => Fin.init (transRowA h p (A i))) (fun i => transRowB h p β (A i) (b i)) yStar ≤
      rInfeas hm (fun i => Fin.init (transRowA h p (A i))) (fun i => transRowB h p β (A i) (b i)) y')
    {s1 s2 : Bool}
    (hs1 : s1 = true ↔ ∃ y' : Fin d → ℝ, ∀ i,
      rInfeas hm A b (liftSlice h p β yStar 0) = b i - A i ⬝ᵥ liftSlice h p β yStar 0 →
      -(transRowA h p (A i) (Fin.last d)) ≤ Fin.init (transRowA h p (A i)) ⬝ᵥ y')
    (hs2 : s2 = true ↔ ∃ z' : Fin d → ℝ, ∀ i,
      rInfeas hm A b (liftSlice h p β yStar 0) = b i - A i ⬝ᵥ liftSlice h p β yStar 0 →
      transRowA h p (A i) (Fin.last d) ≤ Fin.init (transRowA h p (A i)) ⬝ᵥ z') :
    let σ : Ordering := if s1 && !s2 then .gt else if !s1 && s2 then .lt else .gt
    ∀ w : Fin (d + 1) → ℝ,
      rInfeas hm A b w < rInfeas hm A b (liftSlice h p β yStar 0) →
      compare (h ⬝ᵥ w) β = σ := by
  set tA : Fin m → Fin (d + 1) → ℝ := fun i => transRowA h p (A i)
  set tB : Fin m → ℝ := fun i => transRowB h p β (A i) (b i)
  have hRel : ∀ (y' : Fin d → ℝ) (s : ℝ),
      rInfeas hm tA tB (Fin.snoc y' s) = rInfeas hm A b (liftSlice h p β y' s) := by
    intro y' s
    unfold rInfeas
    congr 1
    ext i
    exact transRow_residual h p hp β (A i) (b i) y' s
  have hRelSlice : ∀ y' : Fin d → ℝ,
      rInfeas hm (fun i => Fin.init (tA i)) tB y' = rInfeas hm tA tB (Fin.snoc y' 0) := by
    intro y'
    unfold rInfeas
    congr 1
    ext i
    simp [dotProduct, Fin.sum_univ_castSucc, Fin.init]
  have hSliceMin' : ∀ y' : Fin d → ℝ,
      rInfeas hm tA tB (Fin.snoc yStar 0) ≤ rInfeas hm tA tB (Fin.snoc y' 0) := by
    intro y'
    rw [← hRelSlice, ← hRelSlice]
    exact hSliceMin y'
  have hs1' : s1 = true ↔ ∃ y' : Fin d → ℝ, ∀ i,
      rInfeas hm tA tB (Fin.snoc yStar 0) = tB i - tA i ⬝ᵥ Fin.snoc yStar 0 →
      -(tA i (Fin.last d)) ≤ Fin.init (tA i) ⬝ᵥ y' := by
    rw [hs1]
    constructor <;> rintro ⟨y', hy'⟩ <;> refine ⟨y', fun i hi => hy' i ?_⟩
    · rwa [hRel, transRow_residual h p hp β (A i) (b i) yStar 0] at hi
    · rwa [← hRel, ← transRow_residual h p hp β (A i) (b i) yStar 0] at hi
  have hs2' : s2 = true ↔ ∃ z' : Fin d → ℝ, ∀ i,
      rInfeas hm tA tB (Fin.snoc yStar 0) = tB i - tA i ⬝ᵥ Fin.snoc yStar 0 →
      tA i (Fin.last d) ≤ Fin.init (tA i) ⬝ᵥ z' := by
    rw [hs2]
    constructor <;> rintro ⟨z', hz'⟩ <;> refine ⟨z', fun i hi => hz' i ?_⟩
    · rwa [hRel, transRow_residual h p hp β (A i) (b i) yStar 0] at hi
    · rwa [← hRel, ← transRow_residual h p hp β (A i) (b i) yStar 0] at hi
  have key := oracle_zero_coord hm tA tB yStar hSliceMin' hs1' hs2'
  intro σ w hw
  have hw_lift : w = liftSlice h p β (projSlice p w) (h ⬝ᵥ w - β) :=
    (liftSlice_projSlice h p hp β w).symm
  have hw' : rInfeas hm tA tB (Fin.snoc (projSlice p w) (h ⬝ᵥ w - β)) <
      rInfeas hm tA tB (Fin.snoc yStar 0) := by
    rw [hRel, hRel, ← hw_lift]; exact hw
  have hcmp := key (Fin.snoc (projSlice p w) (h ⬝ᵥ w - β)) hw'
  simp only [Fin.snoc_last] at hcmp
  have hsub : compare (h ⬝ᵥ w) β = compare (h ⬝ᵥ w - β) 0 := by
    rcases lt_trichotomy (h ⬝ᵥ w) β with hlt | heq | hgt
    · rw [compare_lt_iff_lt.mpr hlt, compare_lt_iff_lt.mpr (by linarith)]
    · subst heq; simp
    · rw [compare_gt_iff_gt.mpr hgt, compare_gt_iff_gt.mpr (by linarith)]
  rw [hsub]
  exact hcmp

/-! ## Closed-Form Base Solver for `m ≤ 2` (`Row 0 = (0, 0)`) -/

/-- Closed-form global minimizer of `max(0, b1 - a1 ⬝ᵥ x)`: if `a1 p ≠ 0` (choosing the first
such coordinate `p`), put `b1 / a1 p` at coordinate `p` and `0` elsewhere; if `a1 = 0`, return `0`. -/
noncomputable def solveOneRow {d : ℕ} (a1 : Fin d → ℝ) (b1 : ℝ) : Fin d → ℝ :=
  if h : ∃ p : Fin d, a1 p ≠ 0 then
    let p := Classical.choose h
    Function.update (0 : Fin d → ℝ) p (b1 / a1 p)
  else 0

theorem solveOneRow_min {d : ℕ} (A : Fin 2 → Fin d → ℝ) (b : Fin 2 → ℝ)
    (hA0 : A 0 = 0) (hb0 : b 0 = 0) (w : Fin d → ℝ) :
    rInfeas (by decide) A b (solveOneRow (A 1) (b 1)) ≤ rInfeas (by decide) A b w := by
  by_cases h : ∃ p : Fin d, A 1 p ≠ 0
  · set p := Classical.choose h
    have hp_ne : A 1 p ≠ 0 := Classical.choose_spec h
    have hspec : solveOneRow (A 1) (b 1) = Function.update (0 : Fin d → ℝ) p (b 1 / A 1 p) := by
      simp [solveOneRow, h, p]
    have hdot : A 1 ⬝ᵥ solveOneRow (A 1) (b 1) = b 1 := by
      rw [hspec]
      simp only [dotProduct]
      rw [Finset.sum_eq_single p]
      · rw [Function.update_self, mul_div_cancel₀ _ hp_ne]
      · intro j _ hjp
        rw [Function.update_of_ne hjp, Pi.zero_apply, mul_zero]
      · intro hp_mem; exact absurd (Finset.mem_univ p) hp_mem
    have hle0 : rInfeas (by decide) A b (solveOneRow (A 1) (b 1)) ≤ 0 := by
      rw [rInfeas_le_iff]
      intro i
      fin_cases i
      · simp [hA0, hb0]
      · simp [hdot]
    exact le_trans hle0 (rInfeas_nonneg_of_zero_row (by decide) A b hA0 hb0 w)
  · push Not at h
    have hA1 : A 1 = 0 := funext h
    have heq : ∀ x, rInfeas (by decide) A b x = max (b 0) (b 1) := by
      intro x
      apply le_antisymm
      · rw [rInfeas_le_iff]; intro i; fin_cases i <;> simp [hA0, hA1]
      · exact max_le (by simpa [hA0] using le_rInfeas (by decide) A b x 0)
                     (by simpa [hA1] using le_rInfeas (by decide) A b x 1)
    rw [heq, heq]

end MegiddoLP.Infeasibility


