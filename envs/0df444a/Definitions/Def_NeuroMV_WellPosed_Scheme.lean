-- Prove2me | Definitions.Def_NeuroMV_WellPosed_Scheme
-- name    : NeuroMV_WellPosed_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:12.144363+00:00
-- url     : https://prove2.me/theorems/d9f8f306-03a2-46fb-be95-a3f26ea003b3
-- title:
--   §2, pp. 9–10 — the grid map κ(n, t), sampled segments and the semi-implicit Euler scheme (11)/(13)
-- statement:
--   Fix a step number $n \ge 1$ and the delay $\tau > 0$. The grid map is
--
--   $$\kappa(n,t) := \frac{k\tau}{n}\quad\text{for } t \in \Big]\frac{k\tau}{n}, \frac{(k+1)\tau}{n}\Big],\ k\in\mathbb Z,$$
--
--   written as $\kappa(n,t) = \frac{\tau}{n}\big(\lceil nt/\tau\rceil - 1\big)$. For a path $Y$ the sampled segment at time $s$ is $Y_{\kappa(n,(s-\tau):s)}(u) := Y_{\kappa(n,s+u)}$, $u\in[-\tau,0]$.
--
--   The semi-implicit Euler scheme $X^{n,r}$ of (11), in its global integral form (13), starts from $X^{n,r}_t = \hat z^\zeta_t$ on $[-\tau,0]$ for $r\in\Gamma_\zeta$ and satisfies, for $t \in [0,T]$,
--
--   $$X^{n,r}_t = \hat z^\zeta(0) + \int_0^t f(s,r,X^{n,r}_{s-},\omega')ds + \int_0^t g\,dW_s + \int_0^t\!\!\int_U h\,\tilde N(ds,d\xi) + \sum_{\alpha=1}^P\Big(\int_0^t\tilde{\mathbb E}\int_{\Gamma_\alpha}\theta\big(s,r,r',X^{n,r}_{s-},Y^{n,r'}_{\kappa(n,(s-\tau):s)},\omega'\big)\mathcal R(dr')ds + \int_0^t\tilde{\mathbb E}\int_{\Gamma_\alpha}\beta(\cdots)\mathcal R(dr')dB^\alpha_s + \int_0^t\!\!\int_U\tilde{\mathbb E}\int_{\Gamma_\alpha}\eta(\cdots,\xi)\mathcal R(dr')\tilde N^\alpha(ds,d\xi)\Big),$$
--
--   where $Y^{n,r'}$ is an independent copy of $X^{n,r'}$. The local dynamics are treated implicitly (evaluated at $X^{n,r}_{s-}$); only the mean-field input is sampled on the grid. Summing (11) over the steps $]k\tau/n,(k+1)\tau/n]$ gives (13), and conversely.
--
--   **Formalization Note.** The scheme is the generic solution predicate of the `Setting` module with the sampled segment in place of the true segment; the copy enters through its law (the expectation is taken over $X^n$ itself). In Lean the step number is `ns`, because `n` is the dimension of $B^\alpha$. At $s=0$, $u=-\tau$ the sampled segment reads the path at $-\tau-\tau/n$, a single time point that no integral sees.
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, §2, proof of Theorem 1.5, (11), p. 9, and (13), p. 10

import Mathlib
import Definitions.Def_NeuroMV_WellPosed_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NeuroMV.WellPosed

open EthierKurtz

variable {d m n k P : ℕ} {U Ω Ω' : Type*}

/-- The grid map `κ(n, t) := kτ/n` for `t ∈ ]kτ/n, (k+1)τ/n]`, `k ∈ ℤ` (Mehri–Scheutzow–Stannat–
Zangeneh, arXiv:1805.01654v3, §2, p. 9), written as `κ(n, t) = (τ/n)(⌈nt/τ⌉ − 1)`; meaningful for
`n ≥ 1` and `τ > 0`. -/
noncomputable def kappa (τ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  τ / n * (((⌈(n : ℝ) * t / τ⌉ : ℤ) : ℝ) - 1)

/-- The **sampled segment** `Y^{n,r'}_{κ(n,(s−τ):s)}(u) := Y^{n,r'}_{κ(n, s+u)}`, `u ∈ [−τ, 0]` (p. 9),
of a path `x` at time `s`. -/
noncomputable def sampledSeg (τ : ℝ) (n : ℕ) (x : ℝ → SDEState d) (s : ℝ≥0) : ℝ → SDEState d :=
  fun u => x (kappa τ n ((s : ℝ) + u))

/-- The **semi-implicit Euler scheme (11)/(13)** of §2, pp. 9–10, on `[−τ, T]` at disorder `ω'`
and step `τ/n` (`n` is `ns` here; `n` is the dimension of `B^α`): `X^{n,r}_t = ẑ^ζ_t` on `[−τ, 0]`, and `X^n` satisfies the integral form (13), in
which the local dynamics `f, g, h` are evaluated at `X^{n,r}_{s−}` while the mean-field terms use the
sampled segments `X^{n,r'}_{κ(n,(s−τ):s)}` of the copy (only its law enters, so the expectation is
over `X^n` itself). All other clauses (càdlàg paths, adaptedness, measurability in `(r, ω)`,
integrability of the mean-field integrands) are those of `SolvesOn`. Summing (11) over the steps
gives (13), and conversely. -/
def IsEulerScheme6 [MeasurableSpace U] [MeasurableSpace Ω] (S : Space k P)
    (C : Coeffs d m n k U Ω') (ν : Measure U) (Nz : Noise d m n P U Ω) (τ : ℝ) (ω' : Ω')
    (T : ℝ) (ns : ℕ) (Xn : Pos k → ℝ → Ω → SDEState d) : Prop :=
  SolvesOn S C ν Nz τ (sampledSeg τ ns) ω' T Set.univ Xn

end NeuroMV.WellPosed


