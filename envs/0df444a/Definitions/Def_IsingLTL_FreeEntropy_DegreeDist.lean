-- Prove2me | Definitions.Def_IsingLTL_FreeEntropy_DegreeDist
-- name    : IsingLTL_FreeEntropy_DegreeDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:10:20.571992+00:00
-- url     : https://prove2.me/theorems/29084f06-f2bb-4207-ac0c-b6279c04b7ea
-- title:
--   Degree distribution $P$, size-biased law $\rho$, $\bar P$, $\bar\rho$, and the trees $T(P,\rho,\infty)$, $T(\rho,\infty)$ ((2.1)-(2.2))
-- statement:
--   A **degree distribution** is a probability distribution $P=\{P_k:k\ge0\}$ on the nonnegative integers with finite, positive first moment. Its **size-biased** version is
--   $$\rho_k=\frac{kP_k}{\sum_{l=1}^\infty lP_l},$$
--   and the average root degree and average branching factor are
--   $$\bar P=\sum_{k=0}^\infty kP_k,\qquad \bar\rho=\sum_{k=1}^\infty(k-1)\rho_k.$$
--   "$\rho$ has finite first moment" means $\sum_k k\rho_k<\infty$, which is equivalent to $P$ having finite second moment; $\mathbb E[L^2]=\sum_l l^2P_l$ for $L\sim P$.
--
--   The random tree $T(P,\rho,\infty)$ is the Galton–Watson tree in which the root has $k$ offspring with probability $P_k$, and every other vertex, independently, has $k-1$ offspring with probability $\rho_k$; $T(P,\rho,t)$ is its first $t$ generations. In $T(\rho,\infty)$ every vertex, the root included, has $k-1$ offspring with probability $\rho_k$.
--
--   **Formalization Note** The trees are laws of offspring functions (Ulam–Harris form): an infinite product measure with one independent coordinate per word, the root coordinate distributed as $P$ and every other as $K-1$, $K\sim\rho$. The coordinates of words that are not vertices never affect the tree.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, pp. 3-4, §2.1, (2.1)-(2.2); p. 5

import Mathlib

namespace IsingLTL.FreeEntropy

open MeasureTheory

/-- The probability mass function on `ℕ` with masses `f k`, for a nonnegative real sequence
summing to `1`. -/
noncomputable def pmfOfReal (f : ℕ → ℝ) (h0 : ∀ k, 0 ≤ f k) (h1 : HasSum f 1) : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (f k), by
    have h := ENNReal.ofReal_tsum_of_nonneg h0 h1.summable
    rw [h1.tsum_eq, ENNReal.ofReal_one] at h
    rw [h]
    exact ENNReal.summable.hasSum⟩

/-- A **degree distribution** (Dembo–Montanari, *Ising Models on Locally Tree-Like Graphs*,
arXiv:0804.4726v3, §2.1, p. 3): a probability distribution `P = {P_k : k ≥ 0}` on the
nonnegative integers with finite, positive first moment `∑_k k P_k`. -/
structure DegreeDist where
  /-- The masses `P_k`. -/
  P : ℕ → ℝ
  nonneg : ∀ k, 0 ≤ P k
  hasSum_one : HasSum P 1
  summable_mean : Summable (fun k : ℕ => (k : ℝ) * P k)
  mean_pos : 0 < ∑' k : ℕ, (k : ℝ) * P k

namespace DegreeDist

variable (D : DegreeDist)

/-- The average root degree `P̄ = ∑_{k ≥ 0} k P_k` ((2.2), p. 4). -/
noncomputable def Pbar : ℝ := ∑' k : ℕ, (k : ℝ) * D.P k

/-- The size-biased distribution `ρ_k = k P_k / ∑_{l ≥ 1} l P_l` ((2.1), p. 3). -/
noncomputable def rho (k : ℕ) : ℝ := (k : ℝ) * D.P k / D.Pbar

/-- The average branching factor `ρ̄ = ∑_{k ≥ 1} (k − 1) ρ_k` ((2.2), p. 4). (The `k = 0` term
vanishes since `ρ_0 = 0`.) -/
noncomputable def rhobar : ℝ := ∑' k : ℕ, ((k : ℝ) - 1) * D.rho k

/-- "`ρ` has finite first moment" (Lemma 2.3 and Theorem 2.4, p. 5): `∑_k k ρ_k < ∞`,
equivalently `∑_k k² P_k < ∞` (p. 5). -/
def RhoFiniteMean : Prop := Summable (fun k : ℕ => (k : ℝ) * D.rho k)

/-- The second moment `E[L²] = ∑_l l² P_l` of `L ∼ P` (used in Remark 6.2, (6.4), p. 23). -/
noncomputable def secondMoment : ℝ := ∑' l : ℕ, (l : ℝ) ^ 2 * D.P l

theorem rho_nonneg (k : ℕ) : 0 ≤ D.rho k :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg k) (D.nonneg k)) D.mean_pos.le

theorem hasSum_rho_succ : HasSum (fun j : ℕ => D.rho (j + 1)) 1 := by
  have h : HasSum (fun k : ℕ => D.rho k) 1 := by
    have h1 := D.summable_mean.hasSum.div_const D.Pbar
    have hne : D.Pbar ≠ 0 := ne_of_gt D.mean_pos
    have h3 : (∑' (b : ℕ), (b : ℝ) * D.P b) / D.Pbar = 1 := div_self hne
    rw [h3] at h1
    exact h1
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  simpa [rho] using h2

/-- The law of `P` as a probability mass function on `ℕ`. -/
noncomputable def pmf : PMF ℕ := pmfOfReal D.P D.nonneg D.hasSum_one

/-- The law of `K − 1` for `K ∼ ρ`: mass `ρ_{j+1}` at `j`. A non-root vertex of `T(P, ρ, ·)`, and
every vertex of `T(ρ, ·)`, has `j` offspring with this probability (pp. 3–4). -/
noncomputable def rhoShift : PMF ℕ :=
  pmfOfReal (fun j => D.rho (j + 1)) (fun j => D.rho_nonneg (j + 1)) D.hasSum_rho_succ

/-- The law of the Galton–Watson tree `T(P, ρ, ∞)` (p. 3–4), as the law of its offspring function
`ω : List ℕ → ℕ` in Ulam–Harris form: the root `[]` has `k` offspring with probability `P_k`, and
independently every other word has `k − 1` offspring with probability `ρ_k`. Its first `t`
generations (`ballTree ω t`) are `T(P, ρ, t)`.

Formalization Note: the coordinates of all words are independent, including those of words that
are not vertices of the tree; they never affect the tree. -/
noncomputable def gwTree : Measure (List ℕ → ℕ) :=
  Measure.infinitePi (fun w : List ℕ => (if w = [] then D.pmf else D.rhoShift).toMeasure)

instance : IsProbabilityMeasure D.gwTree := by
  unfold gwTree; infer_instance

/-- The law of the tree `T(ρ, ∞)` (p. 4): every vertex, the root included, has `k − 1` offspring
with probability `ρ_k`, independently. -/
noncomputable def rhoTree : Measure (List ℕ → ℕ) :=
  Measure.infinitePi (fun _ : List ℕ => D.rhoShift.toMeasure)

instance : IsProbabilityMeasure D.rhoTree := by
  unfold rhoTree; infer_instance

end DegreeDist

end IsingLTL.FreeEntropy


