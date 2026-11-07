-- Prove2me | Definitions.Def_Z2PostSamp_GaussModel
-- name    : Z2PostSamp_GaussModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:34.495449+00:00
-- url     : https://prove2.me/theorems/6599e44c-39a2-4a6b-8742-deeef39c951b
-- title:
--   The Gaussian model of §3.1: posterior, replica averages, overlaps and AMP with a side channel
-- statement:
--   Let $\theta$ be uniform on $\{-1,1\}^N$, $W_N$ GOE with off-diagonal variance $1/N$ and diagonal variance $2/N$, and $g\sim\mathcal N(0,I_N)$, independent. For $r,t\ge0$ set
--
--   $$A=\frac rN\theta\theta^\top+\sqrt r\,W_N,\qquad h=t\theta+\sqrt t\,g .$$
--
--   The posterior given $(A,h)$ is proportional to $\exp\{\frac12\sigma^\top A\sigma+h^\top\sigma\}$ on $\{-1,1\}^N$. Write $\langle\cdot\rangle$ for posterior averaging of independent replicas $\sigma^1,\sigma^2,\dots$, $R_{a\theta}=N^{-1}\sum_i\sigma^a_i\theta_i$, $R_{ab}=N^{-1}\sum_i\sigma^a_i\sigma^b_i$, and $m=\langle\sigma\rangle$. The AMP with side channel is $z^0=h$, $u^{-1}=0$, $u^\ell=\tanh z^\ell$, $z^{\ell+1}=Au^\ell+h-r(1-\|u^\ell\|^2/N)u^{\ell-1}$, its state evolution $s_0=t$, $s_{\ell+1}=rF(s_\ell)+t$, and the Hessian form of $\Phi(u)=\sum\phi(u_i)-\frac12u^\top Au-h^\top u+\frac{r(1-q)}2\|u\|^2$ is $\sum\frac{v_i^2}{1-u_i^2}-v^\top Av+r(1-q)\|v\|^2$.
--
--   This is the common normalization in which the cited overlap, cavity and state-evolution inputs are stated; it is later identified with a free block of $J$.
--
--   **Formalization Note** One-replica averages are the published `lawMean`, the covariance is the published `lawCov`; two- and three-replica averages are explicit sums with product weights. $W_N=Z_N/\sqrt N$ with $Z_N$ generated as in the $\mathbb Z_2$ model. $q$ is the positive root.
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), §3.1, p.14; Lemma 3.4, pp.15–16

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_Z2PostSamp_Model
import Definitions.Def_Z2PostSamp_Scalars
import Definitions.Def_Z2PostSamp_Construction

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory ProbabilityTheory OAI.CriticalSK SKAnnealing.Sampling Matrix

namespace Z2PostSamp

noncomputable section

/-!
# The Gaussian model of §3.1: posterior, replica averages, overlaps, AMP with side channel

Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), §3.1, p.14: "Let `θ` be uniform on `{−1,1}^N`, let `W_N` be GOE with
off-diagonal variance `1/N` and diagonal variance `2/N`, and let `g ∼ N(0, I_N)`, independently.
For `r, t ≥ 0`, set `A = (r/N) θθᵀ + √r W_N`, `h = tθ + √t g`. The posterior distribution given
`(A, h)` is proportional to `exp{½ σᵀAσ + hᵀσ}` on `{−1,1}^N`." `⟨·⟩` is posterior averaging,
`E` the expectation under the joint planted law, replicas `σ¹, σ², …` are independent posterior
samples, `R_{aθ} = N^{−1} Σ σ_i^a θ_i`, `R_{ab} = N^{−1} Σ σ_i^a σ_i^b`. Lemma 3.4, pp.15–16: the
AMP `z⁰ = h`, `u^{−1} = 0`, `u^ℓ = tanh z^ℓ`, `z^{ℓ+1} = A u^ℓ + h − r(1 − ‖u^ℓ‖²/N) u^{ℓ−1}`, the
state evolution `s₀ = t`, `s_{ℓ+1} = r F(s_ℓ) + t`, and
`Φ(u) = Σ φ(u_i) − ½ uᵀAu − hᵀu + (r(1 − q)/2)‖u‖²` on `(−1,1)^N`.

**Formalization Note.** The sample space is `(θ, E, g)` with `E` the free entries of `Z_N` as in the
ℤ₂ model (`W_N = Z_N/√N`). Posterior averages are explicit finite sums with product weights: one
replica is the published `SKAnnealing.Sampling.lawMean`, two and three replicas are `avg2`, `avg3`. The Hessian of `Φ` is the explicit form
`Σ v_i²/(1 − u_i²) − vᵀAv + r(1 − q)‖v‖²` (`A` is symmetric). `q = posRoot r t`.
-/

/-- The sample space `(θ, E, g)` of the Gaussian model. -/
abbrev GΩ (N : ℕ) := Spin N × (Free N → ℝ) × (Fin N → ℝ)

/-- The joint planted law of `(θ, W_N, g)`, independent. -/
def gaussLaw (N : ℕ) : Measure (GΩ N) :=
  (signalLaw N).prod ((noiseLaw N).prod (Measure.pi fun _ : Fin N => gaussianReal 0 1))

/-- `W_N = Z_N / √N`: GOE with off-diagonal variance `1/N` and diagonal variance `2/N`. -/
def Wmat {N : ℕ} (ω : GΩ N) : Matrix (Fin N) (Fin N) ℝ := (1 / Real.sqrt N) • Zmat ω.2.1

/-- `A = (r/N) θθᵀ + √r W_N`. -/
def Amat {N : ℕ} (r : ℝ) (ω : GΩ N) : Matrix (Fin N) (Fin N) ℝ :=
  (r / N) • vecMulVec (spinVec ω.1) (spinVec ω.1) + Real.sqrt r • Wmat ω

/-- `h = tθ + √t g`. -/
def hvec {N : ℕ} (t : ℝ) (ω : GΩ N) : Fin N → ℝ :=
  t • spinVec ω.1 + Real.sqrt t • ω.2.2

/-- The posterior `∝ exp{½ σᵀAσ + hᵀσ}` on `{±1}^N`. -/
def gaussPost {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ) (σ : Spin N) : ℝ :=
  Real.exp ((1 / 2 : ℝ) * (spinVec σ ⬝ᵥ (A *ᵥ spinVec σ)) + h ⬝ᵥ spinVec σ) /
    ∑ τ : Spin N, Real.exp ((1 / 2 : ℝ) * (spinVec τ ⬝ᵥ (A *ᵥ spinVec τ)) + h ⬝ᵥ spinVec τ)

/-- The posterior of the Gaussian model at parameters `(r, t)` and sample `ω`. -/
def gpost {N : ℕ} (r t : ℝ) (ω : GΩ N) : Spin N → ℝ := gaussPost (Amat r ω) (hvec t ω)

/-- The posterior average `⟨f(σ¹, σ²)⟩` of two independent replicas. -/
def avg2 {N : ℕ} (μ : Spin N → ℝ) (f : Spin N → Spin N → ℝ) : ℝ :=
  ∑ σ, ∑ τ, μ σ * μ τ * f σ τ

/-- The posterior average `⟨f(σ¹, σ², σ³)⟩` of three independent replicas. -/
def avg3 {N : ℕ} (μ : Spin N → ℝ) (f : Spin N → Spin N → Spin N → ℝ) : ℝ :=
  ∑ σ, ∑ τ, ∑ ρ, μ σ * μ τ * μ ρ * f σ τ ρ

/-- The overlap `N^{−1} Σ_i σ_i τ_i` (`R_{1θ}` with `τ = θ`, `R_{12}` with two replicas). -/
def overlap {N : ℕ} (σ τ : Spin N) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, spinValue (σ i) * spinValue (τ i)

/-- The posterior mean `m = ⟨σ⟩`, coordinatewise `lawMean μ σ_i`; the covariance
`C = ⟨(σ − m)(σ − m)ᵀ⟩` is the published `lawCov μ`. -/
def postMean {N : ℕ} (μ : Spin N → ℝ) : Fin N → ℝ := fun i => lawMean μ fun σ => spinValue (σ i)

/-- One AMP step `(z^ℓ, u^{ℓ−1}) ↦ (z^{ℓ+1}, u^ℓ)` of Lemma 3.4. -/
def gaussAmpStep {N : ℕ} (r t : ℝ) (ω : GΩ N) (p : (Fin N → ℝ) × (Fin N → ℝ)) :
    (Fin N → ℝ) × (Fin N → ℝ) :=
  (Amat r ω *ᵥ tanhV p.1 + hvec t ω - (r * (1 - sqNorm (tanhV p.1) / N)) • p.2, tanhV p.1)

/-- The AMP iterate `u^L = tanh z^L` of Lemma 3.4, from `z⁰ = h`, `u^{−1} = 0`. -/
def gaussAmpU {N : ℕ} (r t : ℝ) (ω : GΩ N) (L : ℕ) : Fin N → ℝ :=
  tanhV ((gaussAmpStep r t ω)^[L] (hvec t ω, 0)).1

/-- The state evolution `s₀ = t`, `s_{ℓ+1} = r F(s_ℓ) + t` of Lemma 3.4. -/
def seIter (r t : ℝ) : ℕ → ℝ
  | 0 => t
  | ℓ + 1 => r * Fch (seIter r t ℓ) + t

/-- The Hessian form `vᵀ∇²Φ(u)v = Σ v_i²/(1 − u_i²) − vᵀAv + r(1 − q)‖v‖²` of Lemma 3.4. -/
def gaussHessQ {N : ℕ} (r t : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) (u v : Fin N → ℝ) : ℝ :=
  ∑ i, v i ^ 2 / (1 - u i ^ 2) - v ⬝ᵥ (A *ᵥ v) + r * (1 - posRoot r t) * sqNorm v

end

end Z2PostSamp


