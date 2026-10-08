-- Prove2me | Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
-- name    : BurkholderDFI_SquareFnLp_Martingale
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:38:43.606882+00:00
-- url     : https://prove2.me/theorems/34e95fed-bfa8-4bd5-b29b-549b4784f818
-- title:
--   Difference sequence, square function S(f), maximal function f*, ‖f‖_p, s(f) and the class of Φ of moderate growth
-- statement:
--   This file fixes the notation of Burkholder's 1973 Wald lectures for a real process $f = (f_1, f_2, \dots)$ on a probability space $(\Omega, \mathcal A, P)$, indexed from $1$, with the convention $f_0 = 0$.
--
--   1. **Difference sequence.** $d_1 = f_1$ and $d_k = f_k - f_{k-1}$ for $k \ge 2$, so that $f_n = \sum_{k=1}^n d_k$.
--   2. **Square functions.** $S_n(f) = \bigl(\sum_{k=1}^n d_k^2\bigr)^{1/2}$ for $n \ge 1$, $S_0(f) = 0$, and
--   $$S(f) = S_\infty(f) = \Bigl(\sum_{k=1}^\infty d_k^2\Bigr)^{1/2} = \sup_n S_n(f) \in [0, \infty].$$
--   3. **Maximal functions.** $f_n^* = \max_{1 \le k \le n} |f_k|$ ($f_0^* = 0$) and $f^* = \sup_n |f_n| \in [0, \infty]$. Applied to the difference sequence these give $d_k^*$ and $d^* = \sup_k |d_k|$.
--   4. **Norms.** For a $[0,\infty]$-valued $Y$ and $p > 0$, $\|Y\|_p = (E\,Y^p)^{1/p}$; for the process, $\|f\|_p = \sup_{n \ge 1} \|f_n\|_p \in [0, \infty]$, and $f$ is $L^p$-bounded when $\|f\|_p < \infty$.
--   5. **Exit time.** For $\lambda \in \mathbb R$, $\mu = \inf\{n \ge 1 : |f_n| > \lambda\}$, with $\inf \emptyset = \infty$.
--   6. **Evaluation at a random index.** For $m \in \{0, 1, \dots, \infty\}$, $f_m$ is $0$ at $m = 0$, $f_m$ at finite $m \ge 1$, and $f_\infty$ (a supplied almost-everywhere limit) at $m = \infty$; similarly $S_m(f)$, with $S_\infty(f) = S(f)$.
--   7. **Conditional square function.** Given $\sigma$-fields $\mathcal A_0 \subseteq \mathcal A_1 \subseteq \cdots$, $s(f) = \bigl(\sum_{k=1}^\infty E(d_k^2 \mid \mathcal A_{k-1})\bigr)^{1/2}$, with the conditional expectations of the nonnegative $d_k^2$ taken in $[0, \infty]$.
--   8. **Functions of moderate growth.** $\Phi : [0, \infty] \to [0, \infty]$ is non-decreasing and continuous, $\Phi(0) = 0$, and $\Phi(2\lambda) \le c\,\Phi(\lambda)$ for all $\lambda$; plus the predicates "$\Phi$ convex" and "$\Phi$ concave" on $[0, \infty)$.
--
--   These definitions supply the common notation used by the nine missions based on the paper.
--
--   **Formalization Note** All square functions, maximal functions and norms take values in $[0, \infty]$ (`ℝ≥0∞`), so that an infinite square function or an unbounded process is represented and no junk value $0$ arises. The process is a Lean function `ℕ → Ω → ℝ`; its value at index $0$ is never read by these definitions (the paper's $f_0 = 0$ is built in). The growth condition is stated for every $\lambda \in [0, \infty]$, which is equivalent to the paper's (6.1) for $\lambda > 0$ given continuity and $\Phi(0) = 0$. The shared module is owned by the first mission and referenced by the others.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §1, p. 20; Lemma 2.1, p. 21; §§6–7, pp. 25–26; §20, p. 39

import Mathlib

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*}

/-- §1, p. 20: the difference sequence `d_k = f_k − f_{k−1}` of `f = (f_1, f_2, …)`, with the
paper's convention `f_0 = 0` (so `d_1 = f_1`). The index `0` is padding: `dseq f 0 = 0`. -/
def dseq (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if k = 0 then 0 else if k = 1 then f 1 ω else f k ω - f (k - 1) ω

/-- §1, p. 20: `S_n(f) = [Σ_{k=1}^n d_k²]^{1/2}`; `S_0(f) = 0`. -/
noncomputable def sqFnN (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (∑ k ∈ Finset.Icc 1 n, dseq f k ω ^ 2))

/-- §1, p. 20: the square function `S(f) = S_∞(f) = [Σ_{k=1}^∞ d_k²]^{1/2}`, valued in `[0, ∞]`. -/
noncomputable def sqFn (f : ℕ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ := ⨆ n : ℕ, sqFnN f n ω

/-- §1, p. 20: `f_n^* = sup_{1 ≤ k ≤ n} |f_k|`; `f_0^* = 0`. -/
noncomputable def maxFnN (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ k ∈ Finset.Icc 1 n, ENNReal.ofReal |f k ω|

/-- §1, p. 20: the maximal function `f^* = sup_n |f_n|`, valued in `[0, ∞]`. Applied to `dseq f`
it is `d^* = sup_k |d_k|`, and `maxFnN (dseq f) k` is `d_k^*` (§14, p. 33). -/
noncomputable def maxFn (f : ℕ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ := ⨆ n : ℕ, maxFnN f n ω

/-- `‖Y‖_p = (E Y^p)^{1/p}` for a `[0, ∞]`-valued `Y` and a real exponent `p > 0`. -/
noncomputable def lpNormE [MeasurableSpace Ω] (P : Measure Ω) (p : ℝ) (Y : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ ω, Y ω ^ p ∂P) ^ (1 / p)

/-- §1, p. 20: `‖f‖_p = sup_{n ≥ 1} ‖f_n‖_p`; `f` is `L^p`-bounded iff this is finite. -/
noncomputable def pNorm [MeasurableSpace Ω] (P : Measure Ω) (p : ℝ) (f : ℕ → Ω → ℝ) : ℝ≥0∞ :=
  ⨆ n ∈ Set.Ici (1 : ℕ), lpNormE P p (fun ω => ENNReal.ofReal |f n ω|)

/-- Lemma 2.1 and (18.1): `μ = inf {n ≥ 1 : |f_n| > λ}`, with `inf ∅ = ∞` (`⊤ : ℕ∞`). -/
noncomputable def exitTime (f : ℕ → Ω → ℝ) (l : ℝ) (ω : Ω) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : 1 ≤ n ∧ l < |f n ω|), (n : ℕ∞)

/-- `f_m` for `m ∈ {0, 1, …, ∞}`: `f_0 = 0` (§1) and `f_∞ = fInf`, the almost-everywhere limit,
which every statement using `valAt` supplies together with its convergence hypothesis. -/
noncomputable def valAt (f : ℕ → Ω → ℝ) (fInf : Ω → ℝ) (m : ℕ∞) (ω : Ω) : ℝ :=
  if m = ⊤ then fInf ω else if m.toNat = 0 then 0 else f m.toNat ω

/-- `S_m(f)` for `m ∈ {0, 1, …, ∞}`, with `S_∞(f) = S(f)` (§1). -/
noncomputable def sqFnAt (f : ℕ → Ω → ℝ) (m : ℕ∞) (ω : Ω) : ℝ≥0∞ :=
  if m = ⊤ then sqFn f ω else sqFnN f m.toNat ω

/-- §20, p. 39: `s(f) = [Σ_{k=1}^∞ E(d_k² | 𝒜_{k−1})]^{1/2}`, `ℱ k = 𝒜_k`. The conditional
expectation of the nonnegative, possibly non-integrable `d_k²` is taken in `[0, ∞]` (`condLExp`). -/
noncomputable def condSqFn [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℕ mΩ) (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  (∑' k : ℕ, condLExp (ℱ k) P (fun x => ENNReal.ofReal (dseq f (k + 1) x ^ 2)) ω) ^ (1 / 2 : ℝ)

/-- §§6–7, pp. 25–26: `Φ` is non-decreasing and continuous on `[0, ∞]`, `Φ(0) = 0`, and satisfies
the growth condition (6.1) `Φ(2λ) ≤ cΦ(λ)` with constant `c`. -/
structure IsPhi (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) : Prop where
  mono : Monotone Φ
  cont : Continuous Φ
  zero : Φ 0 = 0
  growth : ∀ x : ℝ≥0∞, Φ (2 * x) ≤ c * Φ x

/-- §15, p. 33: `Φ` is convex on `[0, ∞)` (read through its real values, which are finite on finite
arguments when `IsPhi Φ c` holds). -/
def IsConvexPhi (Φ : ℝ≥0∞ → ℝ≥0∞) : Prop :=
  ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => (Φ (ENNReal.ofReal x)).toReal)

/-- §20, p. 38: `Φ` is concave on `[0, ∞)` (read as for `IsConvexPhi`). -/
def IsConcavePhi (Φ : ℝ≥0∞ → ℝ≥0∞) : Prop :=
  ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => (Φ (ENNReal.ofReal x)).toReal)

end BurkholderDFI.SquareFnLp


