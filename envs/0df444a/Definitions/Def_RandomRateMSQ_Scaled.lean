-- Prove2me | Definitions.Def_RandomRateMSQ_Scaled
-- name    : RandomRateMSQ_Scaled
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:26:38.681534+00:00
-- url     : https://prove2.me/theorems/5acf2dbb-317f-4fff-8a61-5991eb4651e9
-- title:
--   Scaled processes of the $n$-th system: $\hat X^n$, $\hat I^n$, $\bar I^n$, $\hat A^n$, $\hat M^n_1$, $\hat M^n_2$, the noise $\hat N^n$, $\hat\sigma^n$, Assumption 2
-- statement:
--   The diffusion-scaled processes of the $n$-th system:
--
--   $$
--   \hat X^n(t)=\frac{X^n(t)-n}{\sqrt n},\quad \hat I^n(t)=\frac{\sum_kI^n_k(t)}{\sqrt n},\quad \bar I^n(t)=\frac{\sum_kI^n_k(t)}{n},\quad \hat A^n(t)=\frac{A^n(t)-\lambda_nt}{\sqrt n},
--   $$
--
--   $$
--   \hat M^n_1(t)=\frac{\sum_kD^n_k(t)-\sum_k\tilde\mu^n_k\int_0^t(1-I^n_k(s))\,ds}{\sqrt n},\qquad
--   \hat M^n_2(t)=\frac{N^n(\Lambda(t))-\Lambda(t)}{\sqrt n},\quad \Lambda(t)=\gamma\int_0^t(X^n(s)-n)^+ds,
--   $$
--
--   the noise $\hat N^n=\hat A^n-\hat M^n_1-\hat M^n_2$ and the rate fluctuation $\hat\sigma^n=\sum_{k=1}^n(\tilde\mu^n_k-\bar\mu)/\sqrt n$.
--
--   **Assumption 2.** $\hat X^n(0)\Rightarrow\xi_0$ for some real random variable $\xi_0$.
--
--   These are the terms of the decomposition (3.2) of $\hat X^n$.
--
--   **Formalization Note** At $n=0$ every scaled quantity is $0$ (division by $\sqrt0=0$); only the tail of the sequence matters. The paper prints $\hat\sigma^n=(\tilde\mu^n_k-\bar\mu)/\sqrt n$ with a free index $k$; the sum is the reading the sixth term of (3.2) forces.
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, pp.6–7 ((3.2), Assumption 2, Īⁿ, Îⁿ), p.17 (M̂ⁿ₁, M̂ⁿ₂) and p.18 (Âⁿ, σ̂ⁿ)

import Mathlib
import Definitions.Def_RandomRateMSQ_System
import Definitions.Def_RandomRateMSQ_J1Left

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace RandomRateMSQ

variable {Ω : Type*} {n : ℕ}

/-- The scaled system length `X̂ⁿ(t) = (Xⁿ(t) − n)/√n` (Büke–Qin, arXiv:1905.04198v1, p.6).

**Formalization Note.** For `n = 0` every scaled quantity is `0` (division by `√0 = 0`); only the
tail of the sequence enters any limit statement. -/
noncomputable def Xhat (s : System Ω n) (ω : Ω) (t : ℝ≥0) : ℝ :=
  ((s.X ω t : ℝ) - n) / Real.sqrt n

/-- The scaled total idleness `Îⁿ(t) = Σₖ Iⁿₖ(t)/√n` (arXiv:1905.04198v1, p.7). -/
noncomputable def Ihat (s : System Ω n) (ω : Ω) (t : ℝ≥0) : ℝ :=
  (∑ k, (s.I k ω t : ℝ)) / Real.sqrt n

/-- The fluid-scaled total idleness `Īⁿ(t) = Σₖ Iⁿₖ(t)/n` (arXiv:1905.04198v1, p.7). -/
noncomputable def Ibar (s : System Ω n) (ω : Ω) (t : ℝ≥0) : ℝ :=
  (∑ k, (s.I k ω t : ℝ)) / n

/-- The scaled arrival process `Âⁿ(t) = (Aⁿ(t) − λₙ t)/√n` (arXiv:1905.04198v1, p.18). -/
noncomputable def Ahat (lam : ℝ) (s : System Ω n) (ω : Ω) (t : ℝ≥0) : ℝ :=
  ((s.arrivals lam ω t : ℝ) - lam * t) / Real.sqrt n

/-- The scaled service martingale
`M̂ⁿ₁(t) = (Σₖ Dⁿₖ(t) − Σₖ µ̃ⁿₖ ∫₀ᵗ (1 − Iⁿₖ(s)) ds)/√n` (arXiv:1905.04198v1, p.17). -/
noncomputable def M1hat (s : System Ω n) (ω : Ω) (t : ℝ≥0) : ℝ :=
  (∑ k, (s.departures k ω t : ℝ) -
    ∑ k, (s.rate k ω : ℝ) * cumInt (fun r => 1 - (s.I k ω r : ℝ)) t) / Real.sqrt n

/-- The scaled abandonment martingale
`M̂ⁿ₂(t) = (Nⁿ(γ ∫₀ᵗ (Xⁿ − n)⁺) − γ ∫₀ᵗ (Xⁿ − n)⁺)/√n` (arXiv:1905.04198v1, p.17). -/
noncomputable def M2hat (γ : ℝ) (s : System Ω n) (ω : Ω) (t : ℝ≥0) : ℝ :=
  ((s.abandonments γ ω t : ℝ) - γ * s.cumOverflow ω t) / Real.sqrt n

/-- The **noise** of the decomposition (3.2), `N̂ⁿ = Âⁿ − M̂ⁿ₁ − M̂ⁿ₂` (arXiv:1905.04198v1, p.6
and proof of Theorem 5, pp.17–18). -/
noncomputable def Nhat (lam γ : ℝ) (s : System Ω n) (ω : Ω) (t : ℝ≥0) : ℝ :=
  Ahat lam s ω t - M1hat s ω t - M2hat γ s ω t

/-- The scaled rate fluctuation `σ̂ⁿ = Σ_{k=1}^{n} (µ̃ⁿₖ − µ̄)/√n` (arXiv:1905.04198v1, p.18,
read with the sum the sixth term of (3.2) forces).

**Formalization Note.** p.18 prints `σ̂ⁿ = (µ̃ⁿₖ − µ̄)/√n` with a free index `k`; that expression
tends to `0`. The sixth term of (3.2), `Σₖ (µ̃ⁿₖ t − µ̄ t)/√n = σ̂ⁿ t`, fixes the sum. -/
noncomputable def sigmaHat (F : Measure ℝ≥0) (s : System Ω n) (ω : Ω) : ℝ :=
  (∑ k, ((s.rate k ω : ℝ) - muBar F)) / Real.sqrt n

/-- **Assumption 2** (arXiv:1905.04198v1, p.7): "X̂ⁿ(0) = (Xⁿ(0) − n)/√n ⇒ ξ₀": the scaled
initial conditions converge in distribution to some real random variable. -/
def Assumption2 [MeasurableSpace Ω] (P : Measure Ω) (sys : ∀ n, System Ω n) : Prop :=
  ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (ξ₀ : Ω₀ → ℝ),
    ConvInDistCoupling P (fun n ω => Xhat (sys n) ω 0) P₀ ξ₀

end RandomRateMSQ


