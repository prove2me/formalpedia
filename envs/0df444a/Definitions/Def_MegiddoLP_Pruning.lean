-- Prove2me | Definitions.Def_MegiddoLP_Pruning
-- name    : MegiddoLP_Pruning
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T21:12:02.480317+00:00
-- url     : https://prove2.me/theorems/576bbc2b-cdc5-4d1c-9900-63591cbb3362
-- title:
--   Correctness and runtime of LP pruning rounds
-- statement:
--   Rows with strict slack at every optimum can be deleted while preserving the optimal set. A positive minimum common relaxation also certifies infeasibility after slack rows are deleted. A costed real-RAM pruning round that removes a constant fraction yields a linear instruction bound for the enclosing loop.
-- source:
--   Nimrod Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, JACM 31(1), 1984, §2, pp. 116–117, and §5, p. 126. https://theory.stanford.edu/~megiddo/pdf/lplin.pdf

import Definitions.Def_Polyhedron
import Definitions.Def_MegiddoLP_MachineDSL
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Matrix

namespace MegiddoLP.FixedDim

open Matrix LinearOptimization Set Filter MachineDSL

private theorem convex_keptRows {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin n → ℝ) (keep : Set (Fin n)) :
    Convex ℝ {y | ∀ i ∈ keep, b i ≤ (A *ᵥ y) i} := by
  intro u hu v hv a e ha he hae i hi
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    b i = (a + e) * b i := by rw [hae, one_mul]
    _ = a * b i + e * b i := add_mul ..
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hu i hi) ha)
      (mul_le_mul_of_nonneg_left (hv i hi) he)

/-- Rows with strict slack at a known optimum can be deleted together. The remaining
polyhedron still has that optimum for the same linear objective. -/
theorem optimal_after_discarding_slack {n d : ℕ} {A : Matrix (Fin n) (Fin d) ℝ}
    {b : Fin n → ℝ} {c x : Fin d → ℝ} (keep : Set (Fin n))
    (hx : IsLpOptimal c (polyhedron A b) x)
    (hslack : ∀ i ∉ keep, b i < (A *ᵥ x) i) :
    IsLpOptimal c {y | ∀ i ∈ keep, b i ≤ (A *ᵥ y) i} x := by
  let P : Set (Fin d → ℝ) := {y | ∀ i ∈ keep, b i ≤ (A *ᵥ y) i}
  let U : Set (Fin d → ℝ) := ⋂ i ∈ keepᶜ, {y | b i < (A *ᵥ y) i}
  have hxP : x ∈ P := fun i _ => hx.1 i
  have hxU : x ∈ U := by simpa [U] using hslack
  have hopen : IsOpen U := by
    apply (Set.toFinite keepᶜ).isOpen_biInter
    intro i _
    exact isOpen_lt continuous_const (continuous_const.dotProduct continuous_id)
  have hlocal : IsLocalMinOn (fun y => c ⬝ᵥ y) P x := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hxU),
      self_mem_nhdsWithin (a := x) (s := P)] with y hyU hyP
    apply hx.2
    intro i
    by_cases hi : i ∈ keep
    · exact hyP i hi
    · exact (mem_iInter₂.mp hyU i hi).le
  have hconv : ConvexOn ℝ P (fun y => c ⬝ᵥ y) := by
    constructor
    · exact convex_keptRows A b keep
    · intro u _ v _ a e _ _ _
      simp [dotProduct_add, dotProduct_smul, smul_eq_mul]
  exact ⟨hxP, fun _ hy => (IsMinOn.of_isLocalMinOn_of_convexOn hxP hlocal hconv) hy⟩

/-- Strict slack at every original optimum preserves the full set of optima.
This lets the recursive solver return any optimizer of the smaller system. -/
theorem optimal_iff_after_discarding_slack {n d : ℕ} {A : Matrix (Fin n) (Fin d) ℝ}
    {b : Fin n → ℝ} {c x : Fin d → ℝ} (keep : Set (Fin n))
    (hx : IsLpOptimal c (polyhedron A b) x)
    (hslack : ∀ z, IsLpOptimal c (polyhedron A b) z → ∀ i ∉ keep, b i < (A *ᵥ z) i)
    (y : Fin d → ℝ) :
    IsLpOptimal c (polyhedron A b) y ↔ IsLpOptimal c {z | ∀ i ∈ keep, b i ≤ (A *ᵥ z) i} y := by
  let P : Set (Fin d → ℝ) := {z | ∀ i ∈ keep, b i ≤ (A *ᵥ z) i}
  let O : Set (Fin d → ℝ) := P ∩ {z | c ⬝ᵥ z = c ⬝ᵥ x}
  let U : Set (Fin d → ℝ) := ⋂ i ∈ keepᶜ, {z | b i < (A *ᵥ z) i}
  have hx' : IsLpOptimal c P x := optimal_after_discarding_slack keep hx (hslack x hx)
  have hU : IsOpen U := by
    apply (Set.toFinite keepᶜ).isOpen_biInter
    intro i _
    exact isOpen_lt continuous_const (continuous_const.dotProduct continuous_id)
  have hO : Convex ℝ O := by
    intro u hu v hv a e ha he hab
    refine ⟨convex_keptRows A b keep hu.1 hv.1 ha he hab, ?_⟩
    change c ⬝ᵥ (a • u + e • v) = c ⬝ᵥ x
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      show c ⬝ᵥ u = c ⬝ᵥ x from hu.2, show c ⬝ᵥ v = c ⬝ᵥ x from hv.2,
      ← add_mul, hab, one_mul]
  have hopt (z : Fin d → ℝ) (hz : z ∈ O) (hf : z ∈ polyhedron A b) :
      IsLpOptimal c (polyhedron A b) z :=
    ⟨hf, fun w hw => (show c ⬝ᵥ z = c ⬝ᵥ x from hz.2).le.trans (hx.2 w hw)⟩
  have hsub : O ⊆ U := by
    apply hO.isPreconnected.subset_of_closure_inter_subset hU
    · exact ⟨x, ⟨hx'.1, rfl⟩, by simpa [U] using hslack x hx⟩
    · rintro z ⟨hzU, hzO⟩
      have hfeas : z ∈ polyhedron A b := by
        intro i
        by_cases hi : i ∈ keep
        · exact hzO.1 i hi
        · exact closure_minimal (s := U) (t := {w | b i ≤ (A *ᵥ w) i})
            (fun w hw => show b i ≤ (A *ᵥ w) i from (mem_iInter₂.mp hw i hi).le)
            (isClosed_le continuous_const (continuous_const.dotProduct continuous_id)) hzU
      simpa [U] using hslack z (hopt z hzO hfeas)
  refine ⟨fun hy => optimal_after_discarding_slack keep hy (hslack y hy), ?_⟩
  intro hy
  have hyO : y ∈ O := ⟨hy.1, le_antisymm (hy.2 x hx'.1) (hx'.2 y hy.1)⟩
  apply hopt y hyO
  intro i
  by_cases hi : i ∈ keep
  · exact hy.1 i hi
  · exact (mem_iInter₂.mp (hsub hyO) i hi).le

/-- If the minimum common relaxation is positive, rows with strict slack at a
minimizer can be discarded while preserving infeasibility. -/
theorem infeasible_after_discarding_slack {n d : ℕ} {A : Matrix (Fin n) (Fin d) ℝ}
    {b : Fin n → ℝ} {x : Fin d → ℝ} {τ : ℝ} (keep : Set (Fin n)) (hτ : 0 < τ)
    (hx : ∀ i, b i ≤ τ + (A *ᵥ x) i)
    (hmin : ∀ (y : Fin d → ℝ) (t : ℝ), (∀ i, b i ≤ t + (A *ᵥ y) i) → τ ≤ t)
    (hslack : ∀ i ∉ keep, b i < τ + (A *ᵥ x) i) :
    ¬ {y | ∀ i ∈ keep, b i ≤ (A *ᵥ y) i}.Nonempty := by
  let B : Matrix (Fin n) (Fin (d + 1)) ℝ := fun i => Matrix.vecCons 1 (A i)
  let c : Fin (d + 1) → ℝ := Matrix.vecCons 1 0
  have hB (z : Fin (d + 1) → ℝ) (i : Fin n) :
      (B *ᵥ z) i = z 0 + (A *ᵥ Fin.tail z) i := by
    change Matrix.vecCons 1 (A i) ⬝ᵥ z = z 0 + A i ⬝ᵥ Fin.tail z
    rw [Matrix.cons_dotProduct, one_mul]
    rfl
  have hc (z : Fin (d + 1) → ℝ) : c ⬝ᵥ z = z 0 := by simp [c, Matrix.vecHead]
  have hopt : IsLpOptimal c (polyhedron B b) (Matrix.vecCons τ x) := by
    constructor
    · intro i
      simpa [hB, Matrix.vecCons] using hx i
    · intro z hz
      rw [hc, hc]
      exact hmin (Fin.tail z) (z 0) fun i => by simpa [hB] using hz i
  have hpruned := optimal_after_discarding_slack keep hopt
    (fun i hi => by simpa [hB, Matrix.vecCons] using hslack i hi)
  rintro ⟨y, hy⟩
  have hfeas : ∀ i ∈ keep, b i ≤ (B *ᵥ Matrix.vecCons 0 y) i :=
    fun i hi => by simpa [hB, Matrix.vecCons] using hy i hi
  have h := hpruned.2 (Matrix.vecCons 0 y) hfeas
  simp only [hc, Matrix.cons_val_zero] at h
  exact (not_le_of_gt hτ) h

private theorem pay_for_round {n k : ℕ} (hk : 0 < k) (hn : k ≤ n) :
    n + 1 ≤ (2 * k) * (n / k) := by
  have hq : 1 ≤ n / k := (Nat.le_div_iff_mul_le hk).mpr (by simpa using hn)
  have hmod := Nat.mod_lt n hk
  have hdecomp := Nat.mod_add_div n k
  have hmul := Nat.mul_le_mul_left k hq
  rw [Nat.mul_comm 2 k, Nat.mul_assoc, Nat.two_mul, Nat.mul_add]
  omega

/-- A round that discards at least `n / k` rows and costs at most `a * (n + 1)`
has a linear total cost, including the small cases. -/
theorem linear_bound_of_pruning (T : ℕ → ℕ) {k small a : ℕ} (hk : 0 < k)
    (hsmall : ∀ n < k, T n ≤ small * (n + 1))
    (hround : ∀ n, k ≤ n → ∃ m, m + n / k ≤ n ∧ T n ≤ T m + a * (n + 1)) :
    ∀ n, T n ≤ (small + a * (2 * k)) * (n + 1) := by
  let C := small + a * (2 * k)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < k
    · exact (hsmall n hn).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    · have hkn : k ≤ n := le_of_not_gt hn
      obtain ⟨m, hm, hcost⟩ := hround n hkn
      have hq : 1 ≤ n / k := (Nat.le_div_iff_mul_le hk).mpr (by simpa using hkn)
      have hpay := pay_for_round hk hkn
      calc
        T n ≤ T m + a * (n + 1) := hcost
        _ ≤ C * (m + 1) + C * (n / k) := by
          apply Nat.add_le_add (ih m (by omega))
          exact (Nat.mul_le_mul_left a hpay).trans (by
            rw [← Nat.mul_assoc a (2 * k) (n / k)]
            exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
        _ = C * (m + 1 + n / k) := (Nat.mul_add ..).symm
        _ ≤ C * (n + 1) := Nat.mul_le_mul_left C (by omega)

/-- A costed pruning body on the real RAM can be repeated until the cutoff.
The invariant records the current row count and the semantic relation to the
original problem. The budget includes loop tests and back edges. -/
theorem pruning_loop_runs (body : Stmt) (r : ℕ) (Inv : ℕ → MState → Prop)
    {k a : ℕ} (hk : 0 < k)
    (hguard : ∀ n s, Inv n s → (0 < s.regs r ↔ k ≤ n))
    (hbody : ∀ n s, Inv n s → k ≤ n → ∃ m t, m + n / k ≤ n ∧
      Runs body s t (a * (n + 1)) ∧ Inv m t) :
    ∀ n s, Inv n s → ∃ m t, m < k ∧ Inv m t ∧
      Runs (.whilePos r body) s t (((a + 2) * (2 * k) + 1) * (n + 1)) := by
  let C := (a + 2) * (2 * k) + 1
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hs
    by_cases hn : n < k
    · have hz : s.regs r ≤ 0 := le_of_not_gt fun h => hn.not_ge ((hguard n s hs).mp h)
      have hc : 1 ≤ C * (n + 1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
      exact ⟨n, s, hn, hs, (Runs.whilePos_exit hz).mono hc⟩
    · have hkn : k ≤ n := le_of_not_gt hn
      have hq : 1 ≤ n / k := (Nat.le_div_iff_mul_le hk).mpr (by simpa using hkn)
      obtain ⟨m, t, hm, hrun, ht⟩ := hbody n s hs hkn
      obtain ⟨l, u, hl, hu, hrest⟩ := ih m (by omega) t ht
      change Runs (.whilePos r body) t u (C * (m + 1)) at hrest
      have hpos := (hguard n s hs).mpr hkn
      refine ⟨l, u, hl, hu, (Runs.whilePos_step hpos hrun hrest).mono ?_⟩
      change a * (n + 1) + C * (m + 1) + 2 ≤ C * (n + 1)
      have hpay : a * (n + 1) + 2 ≤ C * (n / k) := calc
        _ ≤ (a + 2) * (n + 1) := by rw [Nat.add_mul]; omega
        _ ≤ (a + 2) * ((2 * k) * (n / k)) :=
          Nat.mul_le_mul_left _ (pay_for_round hk hkn)
        _ ≤ C * (n / k) := by
          rw [← Nat.mul_assoc (a + 2) (2 * k)]
          exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      calc
        _ = (a * (n + 1) + 2) + C * (m + 1) := by omega
        _ ≤ C * (n / k) + C * (m + 1) := Nat.add_le_add_right hpay _
        _ = C * (n / k + (m + 1)) := (Nat.mul_add ..).symm
        _ ≤ C * (n + 1) := Nat.mul_le_mul_left _ (by omega)

/-- Dimension recursion preserves the linear bound when a pruning round makes
`q d` calls on instances in the preceding dimension with at most `n` rows.
The term `q d * T d n` can use a monotone envelope for those calls. -/
theorem linear_bound_by_dimension (T : ℕ → ℕ → ℕ) (k small a q : ℕ → ℕ)
    (hk : ∀ d, 0 < k d) (hbase : ∀ n, T 0 n ≤ small 0 * (n + 1))
    (hsmall : ∀ d n, n < k d → T (d + 1) n ≤ small (d + 1) * (n + 1))
    (hround : ∀ d n, k d ≤ n → ∃ m, m + n / k d ≤ n ∧
      T (d + 1) n ≤ T (d + 1) m + q d * T d n + a d * (n + 1)) :
    ∀ d, ∃ C, ∀ n, T d n ≤ C * (n + 1) := by
  intro d
  induction d with
  | zero => exact ⟨small 0, hbase⟩
  | succ d ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨_, linear_bound_of_pruning (T (d + 1)) (a := q d * C + a d)
      (hk d) (hsmall d) ?_⟩
    intro n hn
    obtain ⟨m, hm, hcost⟩ := hround d n hn
    refine ⟨m, hm, hcost.trans ?_⟩
    rw [Nat.add_mul, Nat.mul_assoc, ← Nat.add_assoc]
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hC n)) _) _

end MegiddoLP.FixedDim


