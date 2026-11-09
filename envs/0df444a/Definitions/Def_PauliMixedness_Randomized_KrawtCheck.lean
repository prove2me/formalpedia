-- Prove2me | Definitions.Def_PauliMixedness_Randomized_KrawtCheck
-- name    : PauliMixedness_Randomized_KrawtCheck
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:45:56.183709+00:00
-- url     : https://prove2.me/theorems/59abae64-c820-4014-8d0e-7eef6bcb35fe
-- title:
--   Algorithm 2: sampled Krawtchouk statistic and majority amplification
-- statement:
--   For real parameters $\Delta,\beta$ and integers $N,k$, set $m=\lceil400\sqrt{2\binom Nk}/(\beta\Delta)\rceil$. Each base test uses two independent arrays $X_1,\ldots,X_m$ and $Y_1,\ldots,Y_m$ of iid draws from $p$ and declares YES exactly when
--
--   $$W_k=\frac1{m^2}\sum_{a,b=1}^m K_k^{(N)}(d_H(X_a,Y_b))\ \ge\ \frac{\beta\Delta}{50}.$$
--
--   The integer polynomial is the published $K(N,k,t)=\sum_{j=0}^{\min(t,k)}(-1)^j\binom tj\binom{N-t}{k-j}$, equal to Definition 3.4 on $0\le t,k\le N$. For $0<\delta<1/2$, take $r=2\lceil8\ln(1/\delta)\rceil+1$ independent base tests and return their strict majority. The sample count is $2mr$, including every array. At $\delta\ge1/2$, take $r=0$ and return a fair zero-sample decision. The YES probability is the finite sum of this outcome-only decision against the product of all $2mr$ input masses.
--
--   The statistic uses observed samples, not Fourier coefficients or its expectation. The definitions also have total values outside the promised parameter range, but no guarantees are asserted there. In particular $m=0$ makes $W_k=0$ by empty sums and total inversion; in the theorem's domain $m\ge1$. The explicit repetition count implements the black-box amplification specified in the proof on p.26.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, Definition 3.4 p.12, Algorithm 2 p.16, Appendix A.2 pp.24–26

import Definitions.Def_PauliMixedness_Randomized_CubeFourier
import Definitions.Def_MatousekLP_Codes_DelsarteLP

noncomputable section
open scoped BigOperators

namespace PauliMixedness.Randomized
attribute [local instance] Classical.propDecidable

/-- Algorithm 2 p.16: each of two independent arrays has m samples. -/
def krawtBatchSize (N k : ℕ) (Δ β : ℝ) : ℕ :=
  ⌈400 * Real.sqrt (2 * (N.choose k : ℝ)) / (β * Δ)⌉₊

/-- Algorithm 2's W_k, on two separate arrays, not its expectation. -/
def krawtStatistic {N m : ℕ} (k : ℕ) (X Y : Fin m → Cube N) : ℝ :=
  ((m : ℝ)^2)⁻¹ * ∑ a : Fin m, ∑ b : Fin m,
    (MatousekLP.Codes.K N k (hammingDist (X a) (Y b)) : ℝ)

/-- ≥ βΔ/50 is the source's weak YES threshold. -/
def krawtBaseYes {N m : ℕ} (k : ℕ) (Δ β : ℝ) (X Y : Fin m → Cube N) : Prop :=
  β * Δ / 50 ≤ krawtStatistic k X Y

/-- Explicit black-box amplification (p.26). Odd fresh repetitions;
δ ≥ 1/2 uses a zero-sample fair decision, including δ = 1. -/
def krawtRepetitions (δ : ℝ) : ℕ :=
  if 1 / 2 ≤ δ then 0 else 2 * ⌈8 * Real.log (1 / δ)⌉₊ + 1

/-- All independent arrays for the amplified algorithm. -/
abbrev KrawtData (N k : ℕ) (Δ β δ : ℝ) :=
  Fin (krawtRepetitions δ) →
    (Fin (krawtBatchSize N k Δ β) → Cube N) ×
      (Fin (krawtBatchSize N k Δ β) → Cube N)

/-- The outcome-only decision kernel: majority of base YES decisions;
classical coins implement the fair branch. It has no distribution argument. -/
def krawtDecision (N k : ℕ) (Δ β δ : ℝ) (z : KrawtData N k Δ β δ) : ℝ :=
  if 1 / 2 ≤ δ then 1 / 2 else
    if krawtRepetitions δ < 2 *
      (Finset.univ.filter (fun r => krawtBaseYes k Δ β (z r).1 (z r).2)).card
    then 1 else 0

/-- Full sample count includes both arrays in every repetition. -/
def krawtSamples (N k : ℕ) (Δ β δ : ℝ) : ℕ :=
  2 * krawtBatchSize N k Δ β * krawtRepetitions δ

/-- Exact YES probability with independent samples and fresh repetitions. -/
def krawtYesProbability {N : ℕ} (p : PMF (Cube N)) (k : ℕ) (Δ β δ : ℝ) : ℝ :=
  ∑ z : KrawtData N k Δ β δ,
    (∏ r : Fin (krawtRepetitions δ),
      (∏ a : Fin (krawtBatchSize N k Δ β), mass p ((z r).1 a)) *
      (∏ b : Fin (krawtBatchSize N k Δ β), mass p ((z r).2 b))) *
    krawtDecision N k Δ β δ z

end PauliMixedness.Randomized


