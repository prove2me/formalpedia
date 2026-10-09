-- Prove2me | Definitions.Def_SphereGRF_Spectral_WeightedSobolev
-- name    : SphereGRF_Spectral_WeightedSobolev
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:06.559619+00:00
-- url     : https://prove2.me/theorems/aea79adf-38ea-437f-b058-d22ce09766e3
-- title:
--   §3, pp. 9–11 — weighted Sobolev spaces $V^n(-1,1)$, the K-functional and the interpolation spaces $V^\eta(-1,1)$
-- statement:
--   All functions are real functions on $(-1,1)$; only their values on $(-1,1)$ enter.
--
--   1. For $j \in \mathbb N_0$ and a smooth $f$, the weighted seminorm is
--   $$
--   |f|^2_{V^j(-1,1)} = \int_{-1}^1 \Big|\frac{\partial^j}{\partial\mu^j} f(\mu)\Big|^2 (1-\mu^2)^j\,d\mu ,
--   $$
--   and for $n \in \mathbb N_0$ the weighted norm is $\|f\|^2_{V^n(-1,1)} = \sum_{j=0}^n |f|^2_{V^j(-1,1)}$.
--
--   2. The space $V^n(-1,1)$ is the closure of the smooth functions with respect to $\|\cdot\|_{V^n(-1,1)}$: a function $u \in L^2(-1,1)$ belongs to $V^n(-1,1)$ if there is a sequence $(\varphi_k)$ of smooth functions with $\varphi_k \to u$ in $L^2(-1,1)$ that is Cauchy for $\|\cdot\|_{V^n(-1,1)}$. Its norm is $\|u\|_{V^n(-1,1)} = \lim_k \|\varphi_k\|_{V^n(-1,1)}$ (the limit does not depend on the sequence); it is set to $+\infty$ for $u \notin V^n(-1,1)$.
--
--   3. For $t > 0$ the **K-functional** of the couple $(V^n(-1,1), V^{n+1}(-1,1))$ is
--   $$
--   K(t,u) = \inf_{u = v + w} \big(\|v\|_{V^n(-1,1)} + t\,\|w\|_{V^{n+1}(-1,1)}\big),
--   $$
--   the infimum over $v \in V^n(-1,1)$, $w \in V^{n+1}(-1,1)$ with $u = v + w$ almost everywhere on $(-1,1)$ ($+\infty$ if there is no such pair).
--
--   4. For $\eta \ge 0$ write $n = \lfloor \eta \rfloor$ and $\theta = \eta - n$. If $\theta = 0$, then $V^\eta(-1,1) = V^n(-1,1)$ with $\|u\|^2_{V^\eta(-1,1)} = \|u\|^2_{V^n(-1,1)}$. If $0 < \theta < 1$, then $V^\eta(-1,1) = (V^n(-1,1), V^{n+1}(-1,1))_{\theta,2}$ is the real interpolation space: $u \in V^n(-1,1)$ with
--   $$
--   \|u\|^2_{V^\eta(-1,1)} = \int_0^\infty t^{-2\theta}\,|K(t,u)|^2\,\frac{dt}{t} < +\infty .
--   $$
--
--   These spaces form the decreasing scale $L^2(-1,1) = V^0 \supset V^1 \supset \cdots$ in which the paper measures the regularity of an isotropic covariance kernel $k_I(\mu)$, $\mu = \langle x, y\rangle$.
--
--   **Formalization Note** The paper defines $V^n(-1,1)$ as the closure of the Sobolev space $H^n(-1,1)$; here the closure is taken of the $C^\infty$ functions on $\mathbb R$ restricted to $(-1,1)$. The two closures coincide, since smooth functions are dense in $H^n(-1,1)$ and the $H^n$ norm dominates the $V^n$ norm. Norms, the K-functional and the interpolation norm take values in $[0,+\infty]$, so that "$< +\infty$" is a genuine condition. $L^2(-1,1)$ convergence and the decomposition $u = v + w$ are with respect to Lebesgue measure on the open interval.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, §3, pp. 9–11 (definitions of |·|_{V^j}, ‖·‖_{V^n}, V^n, V^η, ‖·‖_{V^η}, K(t,u))

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace SphereGRF.Spectral

/-- `u ∈ L²(−1,1)`. -/
def L2m11 (u : ℝ → ℝ) : Prop :=
  MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1))

/-- Squared `L²(−1,1)` distance, as an extended nonnegative real. -/
noncomputable def l2DistSq (u v : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Ioo (-1 : ℝ) 1, ‖u x - v x‖ₑ ^ 2

/-- The weighted seminorm (squared) `|f|²_{V^j(−1,1)} = ∫_{−1}^1 |f^{(j)}(μ)|² (1 − μ²)^j dμ`
(p. 10); applied only to smooth `f`. -/
noncomputable def wSemi (j : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ μ in (-1 : ℝ)..1, (iteratedDeriv j f μ) ^ 2 * (1 - μ ^ 2) ^ j

/-- The weighted norm (squared) `‖f‖²_{V^n(−1,1)} = Σ_{j=0}^n |f|²_{V^j(−1,1)}` (p. 9);
applied only to smooth `f`. -/
noncomputable def vNormSq (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), wSemi j f

/-- `φ` is a sequence of smooth functions converging to `u` in `L²(−1,1)` and Cauchy for
`‖·‖_{V^n(−1,1)}`. -/
def ApproxSeq (n : ℕ) (u : ℝ → ℝ) (φ : ℕ → ℝ → ℝ) : Prop :=
  (∀ k, ContDiff ℝ ∞ (φ k)) ∧
  Tendsto (fun k => l2DistSq (φ k) u) atTop (𝓝 0) ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ k' ≥ N, vNormSq n (φ k - φ k') < ε

/-- `u ∈ V^n(−1,1)`, the closure of the smooth functions under `‖·‖_{V^n(−1,1)}` (p. 9). -/
def MemV (n : ℕ) (u : ℝ → ℝ) : Prop :=
  L2m11 u ∧ ∃ φ : ℕ → ℝ → ℝ, ApproxSeq n u φ

/-- The norm of the closure: `‖u‖_{V^n} = lim_k ‖φ_k‖_{V^n}` along an approximating sequence
(the limit does not depend on the sequence; the infimum only removes the choice).
It is `⊤` when `u` has no approximating sequence. -/
noncomputable def vNorm (n : ℕ) (u : ℝ → ℝ) : ℝ≥0∞ :=
  ⨅ (φ : ℕ → ℝ → ℝ) (_ : ApproxSeq n u φ) (r : ℝ)
    (_ : Tendsto (fun k => Real.sqrt (vNormSq n (φ k))) atTop (𝓝 r)), ENNReal.ofReal r

/-- The K-functional of the couple `(V^n(−1,1), V^{n+1}(−1,1))` (p. 11):
`K(t,u) = inf_{u = v + w} (‖v‖_{V^n} + t ‖w‖_{V^{n+1}})`, the decomposition holding a.e. on
`(−1,1)`. It is `⊤` when no decomposition exists. -/
noncomputable def Kfun (n : ℕ) (t : ℝ) (u : ℝ → ℝ) : ℝ≥0∞ :=
  ⨅ (v : ℝ → ℝ) (w : ℝ → ℝ)
    (_ : MemV n v ∧ MemV (n + 1) w ∧
      ∀ᵐ x ∂(volume.restrict (Set.Ioo (-1 : ℝ) 1)), u x = v x + w x),
    vNorm n v + ENNReal.ofReal t * vNorm (n + 1) w

/-- The squared norm of `V^η(−1,1)`, `η ≥ 0`, with `n = ⌊η⌋`, `θ = η − n`:
for `θ = 0` the squared closure norm `‖u‖²_{V^n}`; for `0 < θ < 1` the norm of the real
interpolation space `(V^n, V^{n+1})_{θ,2}` (p. 11):
`∫_0^∞ t^{−2θ} K(t,u)² dt/t`. -/
noncomputable def vEtaNormSq (η : ℝ) (u : ℝ → ℝ) : ℝ≥0∞ :=
  if η - (⌊η⌋₊ : ℝ) = 0 then vNorm ⌊η⌋₊ u ^ 2
  else ∫⁻ t in Set.Ioi (0 : ℝ),
    ENNReal.ofReal (t ^ (-2 * (η - (⌊η⌋₊ : ℝ))) / t) * Kfun ⌊η⌋₊ t u ^ 2

/-- `u ∈ V^η(−1,1)`, `η ≥ 0`: for integer `η = n` the closure `V^n(−1,1)`; for
`n < η < n + 1` the interpolation space `(V^n, V^{n+1})_{η−n,2}` (pp. 10–11), i.e.
`u ∈ V^n + V^{n+1} = V^n` with finite interpolation norm. -/
def MemVeta (η : ℝ) (u : ℝ → ℝ) : Prop :=
  if η - (⌊η⌋₊ : ℝ) = 0 then MemV ⌊η⌋₊ u
  else MemV ⌊η⌋₊ u ∧ vEtaNormSq η u < ⊤

end SphereGRF.Spectral


