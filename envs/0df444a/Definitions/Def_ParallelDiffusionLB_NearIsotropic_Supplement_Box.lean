-- Prove2me | Definitions.Def_ParallelDiffusionLB_NearIsotropic_Supplement_Box
-- name    : ParallelDiffusionLB_NearIsotropic_Supplement_Box
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:08:41.041199+00:00
-- url     : https://prove2.me/theorems/9108240b-e4b9-477f-9677-cc7b74573650
-- title:
--   Anisotropic box instances, gates (55) and the gated oracle (57)
-- statement:
--   Fix a dimension $d$, a query budget $P$ and a score accuracy $\varepsilon>0$. The public parameters (53) are
--   $$M=100(dP+1),\qquad q=\frac{100Md}{\varepsilon},\qquad a_i=\tfrac14 q^{-(i-1)},\qquad h_i=\frac{a_i}{100M},\qquad t_i=\frac{4a_i}{\varepsilon}\qquad(i\in[d]),$$
--   and for each label $k\in[M]$ the candidate interval (54) is $I_i(k)=[c_i(k)-h_i,\,c_i(k)+h_i]$ with center $c_i(k)=a_i+(k-\tfrac12)a_i/M$. A label vector $\theta\in[M]^d$ selects the axis-aligned box $K^\theta=\prod_{i=1}^d I_i(\theta_i)\subset\mathbb R^d$, and the target is $\pi^\theta=\mathrm{Unif}(K^\theta)$, where for a measurable set $S$ of positive finite volume $\mathrm{Unif}(S)=\mathrm{vol}(S)^{-1}\,\mathrm{vol}|_S$.
--
--   For an interval $I$ and $\sigma>0$, $m_{I,\sigma}(z)$ is the posterior mean of $U\sim\mathrm{Unif}(I)$ given $U+\sigma Z=z$ with $Z\sim N(0,1)$:
--   $$m_{I,\sigma}(z)=\frac{\int_I u\,e^{-(z-u)^2/(2\sigma^2)}\,du}{\int_I e^{-(z-u)^2/(2\sigma^2)}\,du},$$
--   defined at every $z$. For $i<d$ the gate (55) is $g^k_{i,\sigma}\equiv1$ when $\sigma>t_{i+1}$ and otherwise
--   $$g^k_{i,\sigma}(z)=\min\Bigl\{1,\max\Bigl\{0,\,2-\frac{\operatorname{dist}(z,I_i(k))}{10h_i}\Bigr\}\Bigr\}.$$
--   The gated oracle (57) answers a query $(x,\sigma)$, $\sigma>0$, coordinatewise by
--   $$\hat s^\theta_{j,\sigma}(x)=-\frac{x_j}{\sigma^2}+\mathbf 1\{\sigma\le t_j\}\Bigl(\prod_{i<j}g^{\theta_i}_{i,\sigma}(x_i)\Bigr)\frac{m_{I_j(\theta_j),\sigma}(x_j)}{\sigma^2},$$
--   the empty product being $1$, and for $r\in[d]$ the truncated oracle (61) keeps $\hat s^\theta_{j,\sigma}$ for $j\le r$ and answers $-x_j/\sigma^2$ for $j>r$.
--
--   These objects are the hard instance family of §4 and Appendix B and its oracle; all of them are public except the labels $\theta$.
--
--   **Formalization Note** Coordinates and labels are 0-indexed (`Fin d`, `Fin M`), so the paper's $i$ and $k$ are `i.val + 1` and `k.val + 1`. Because $d$ and $P$ are integers, $\lceil 100(dP+1)\rceil=100(dP+1)$. The gate is only defined by the paper for $i<d$; for the last coordinate the Lean function returns the placeholder $1$, which no statement uses (the product in (57) only involves $i<j\le d$). The truncated oracle takes the paper's index $r$ as a natural number.
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, §4 (7), (9), p. 14–15; Appendix B.1 (53)–(55), pp. 30–31; B.2 (57), p. 31; B.3 (61), p. 32; Unif(S) from §2 Notation, p. 5

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Gaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic.Supplement

/-- Uniform law `Unif(S)` of a measurable set of positive finite volume (§Notation, p. 5):
`volume(S)⁻¹ • volume|_S`. Used only for such sets, where it is a probability measure. -/
def unifSet {α : Type*} [MeasureSpace α] (S : Set α) : Measure α :=
  (volume S)⁻¹ • volume.restrict S

/-! ### Public parameters (53)–(54), p. 30.
Paper indices `i ∈ [d]`, `k ∈ [M]` are 1-indexed; here `i : Fin d`, `k : Fin M` are 0-indexed,
so the paper's `i` is `i.val + 1` and the paper's `k` is `k.val + 1`. -/

/-- `M = ⌈100(dP+1)⌉`, an integer already, so the ceiling is the identity. -/
def numIntervals (d P : ℕ) : ℕ := 100 * (d * P + 1)

/-- Ratio of consecutive spatial scales, `q = 100 M d / ε_score`. -/
def ratio (d P : ℕ) (ε : ℝ) : ℝ := 100 * (numIntervals d P : ℝ) * d / ε

/-- Location scale `a_i = q^{-(i-1)}/4` (paper index `i = j.val + 1`). -/
def scale (d P : ℕ) (ε : ℝ) (j : Fin d) : ℝ := (ratio d P ε)⁻¹ ^ j.val / 4

/-- Interval half-length `h_i = a_i/(100 M)`. -/
def halfLen (d P : ℕ) (ε : ℝ) (j : Fin d) : ℝ := scale d P ε j / (100 * numIntervals d P)

/-- Noise cutoff `t_i = 4 a_i / ε_score`. -/
def cutoff (d P : ℕ) (ε : ℝ) (j : Fin d) : ℝ := 4 * scale d P ε j / ε

/-- Center `c_i(k) = a_i + (k - 1/2) a_i / M` (paper label `k = k.val + 1`). -/
def center (d P : ℕ) (ε : ℝ) (j : Fin d) (k : Fin (numIntervals d P)) : ℝ :=
  scale d P ε j + ((k.val : ℝ) + 1 / 2) * scale d P ε j / numIntervals d P

/-- Candidate interval `I_i(k) = [c_i(k) - h_i, c_i(k) + h_i]` (54). -/
def interval (d P : ℕ) (ε : ℝ) (j : Fin d) (k : Fin (numIntervals d P)) : Set ℝ :=
  Set.Icc (center d P ε j k - halfLen d P ε j) (center d P ε j k + halfLen d P ε j)

/-- The box `K^θ = ∏_i I_i(θ_i)` in `E d` (7). -/
def box (d P : ℕ) (ε : ℝ) (θ : Fin d → Fin (numIntervals d P)) : Set (E d) :=
  {x | ∀ j, x j ∈ interval d P ε j (θ j)}

/-- Scalar posterior mean of `U ~ Unif(I)` given `U + σZ = z`, `Z ~ N(0,1)` (p. 31):
the uniform interval measure weighted by its Gaussian likelihood at `z`, defined at every `z`.
The Gaussian normalizing constant cancels. -/
def postMeanUnif (I : Set ℝ) (σ z : ℝ) : ℝ :=
  (∫ u in I, u * Real.exp (-(z - u) ^ 2 / (2 * σ ^ 2))) /
    ∫ u in I, Real.exp (-(z - u) ^ 2 / (2 * σ ^ 2))

/-- Gate `g^k_{i,σ}` (55), p. 31: `≡ 1` when `σ > t_{i+1}`, otherwise
`min{1, max{0, 2 - dist(z, I_i(k))/(10 h_i)}}`. The paper defines it only for `i < d`
(here `i.val + 1 < d`); for the last coordinate the value `1` is a placeholder never used. -/
def gate (d P : ℕ) (ε : ℝ) (i : Fin d) (k : Fin (numIntervals d P)) (σ z : ℝ) : ℝ :=
  if h : i.val + 1 < d then
    if cutoff d P ε ⟨i.val + 1, h⟩ < σ then 1
    else min 1 (max 0 (2 - Metric.infDist z (interval d P ε i k) / (10 * halfLen d P ε i)))
  else 1

/-- Coordinate `j` of the gated oracle (57): `-x_j/σ² + 1{σ ≤ t_j} (∏_{i<j} g^{θ_i}_{i,σ}(x_i))
m^{θ_j}_{j,σ}(x_j)/σ²`, the empty product being `1`. -/
def gatedCoord (d P : ℕ) (ε : ℝ) (θ : Fin d → Fin (numIntervals d P)) (x : E d) (σ : ℝ)
    (j : Fin d) : ℝ :=
  -x j / σ ^ 2 +
    (if σ ≤ cutoff d P ε j then
      (∏ i ∈ Finset.univ.filter (fun i : Fin d => i < j), gate d P ε i (θ i) σ (x i)) *
        postMeanUnif (interval d P ε j (θ j)) σ (x j) / σ ^ 2
    else 0)

/-- The gated oracle `ŝ^θ` (57)/(9) as a map on queries `(x, σ)` with `σ > 0`. -/
def gatedOracle (d P : ℕ) (ε : ℝ) (θ : Fin d → Fin (numIntervals d P)) : Query d → E d :=
  fun q => WithLp.toLp 2 (fun j => gatedCoord d P ε θ q.1 q.2.1 j)

/-- Truncated oracle `ŝ^{θ,[r]}` (61), p. 32, with the paper's `r` (coordinates `j ≤ r`, i.e.
`j.val < r`, keep the gated answer; later ones get the null score `-x_j/σ²`). -/
def truncOracle (d P : ℕ) (ε : ℝ) (r : ℕ) (θ : Fin d → Fin (numIntervals d P)) :
    Query d → E d :=
  fun q => WithLp.toLp 2 (fun j =>
    if j.val < r then gatedCoord d P ε θ q.1 q.2.1 j else -q.1 j / q.2.1 ^ 2)

end ParallelDiffusionLB.NearIsotropic.Supplement


