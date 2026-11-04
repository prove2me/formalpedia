-- Prove2me | Definitions.Def_ChurnServiceMode_Prop2Conditions
-- name    : ChurnServiceMode_Prop2Conditions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:53:30.358404+00:00
-- url     : https://prove2.me/theorems/8f21c976-ba31-43f6-a888-5cd7862f6a40
-- title:
--   The six conditions of Proposition 2 (verification theorem)
-- statement:
--   Let $V:\mathbb R\to\mathbb R$ and let $\pi$ be a policy. **The conditions of Proposition 2** are:
--   1. $V\ge0$;
--   2. $V$ is continuously differentiable on $\mathbb R$ and twice continuously differentiable on $\mathbb R\setminus E$ for some countable set $E$;
--   3. $V'$ is bounded;
--   4. $B_S(x,V)\le0$ for every $x$ and $B_R(x,V)\le0$ for every $x\notin E$ (display (14));
--   5. $\pi$ is an interval policy with $\pi=S$ on $E$, the process $V(H_t)$ is an adapted continuous semimartingale under every $\pi$-feedback control system, and $B_{\pi(x)}(x,V)=0$ for every $x$ (display (15));
--   6. under every $\pi$-feedback control system started at any $x$,
--   $$\lim_{t\to\infty}\mathbb E\Bigl[(1+|H_t|)\,e^{-\int_0^tQ(H_s)ds}\Bigr]=0\qquad\text{(display (16))}.$$
--
--   These are the hypotheses of the paper's verification theorem; Proposition 3 checks them for the candidate of Theorem 1.
--
--   **Formalization Note** "Twice continuously differentiable on $\mathbb R\setminus E$" means: $V'$ is differentiable at every point outside $E$ and $V''$ is continuous on $\mathbb R\setminus E$ in its relative topology. Because $\sigma_S=0$, the second-order term of $B_S$ is $0$ even on $E$ (footnote 13). The expectation in (16) is a Lebesgue integral of a nonnegative function.
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Proposition 2, displays (14)–(16) and footnote 13, p.17

import Mathlib
import Definitions.Def_ChurnServiceMode_ControlSystem

open MeasureTheory ProbabilityTheory Filter PeskirShiryaev.LocalTime
open scoped NNReal ENNReal Topology

namespace ChurnServiceMode

/-- **The six conditions of Proposition 2** (Kanoria, Lobel & Lu, SSRN 3188226, p.17) on a
function `V̄ : ℝ → ℝ` and a policy `π̄`:

1. `V̄ ≥ 0`;
2. `V̄` is continuously differentiable on `ℝ` and twice continuously differentiable on `ℝ ∖ E`
   for some countable set `E`;
3. `V̄′` is bounded;
4. (14): `B_S(x, V̄) ≤ 0` for every `x`, and `B_R(x, V̄) ≤ 0` for every `x ∉ E`;
5. `π̄` is an interval policy with `π̄ = S` on `E`; the process `V̄(H^{x,π̄}_t)` is an adapted
   continuous semimartingale; and (15): `B_{π̄(x)}(x, V̄) = 0` for every `x`;
6. (16): `lim_{t→∞} E[(1 + |H^{x,π̄}_t|) e^{−∫₀ᵗ Q(H^{x,π̄}_s) ds}] = 0` for every `x`.

Here `B_i(x, V) = −Q(x)V(x) + (μ_i − x)V′(x) + ½σ_i²V″(x) + μ_i` is `Params.generator`.

**Formalization Note.** "Twice continuously differentiable on `ℝ ∖ E`" is: `V̄′` is differentiable
at every point off `E` and `V̄″ = deriv (deriv V̄)` is continuous on `ℝ ∖ E` (relative topology).
The process `H^{x,π̄}` of Conditions 5–6 is any `π̄`-feedback control system started at `x`; the
conditions are required for every such system. The expectation in (16) is a lower Lebesgue
integral of a nonnegative quantity, so it is never a junk value. -/
def Prop2Conditions (p : Params) (V : ℝ → ℝ) (π : ℝ → Mode) : Prop :=
  (∀ y, 0 ≤ V y) ∧
  (∃ E : Set ℝ, E.Countable ∧
    -- Condition 2
    ContDiff ℝ 1 V ∧ (∀ y ∉ E, DifferentiableAt ℝ (deriv V) y) ∧
      ContinuousOn (deriv (deriv V)) Eᶜ ∧
    -- Condition 3
    (∃ K : ℝ, ∀ y, |deriv V y| ≤ K) ∧
    -- Condition 4, display (14)
    (∀ y, p.generator Mode.S V y ≤ 0) ∧ (∀ y ∉ E, p.generator Mode.R V y ≤ 0) ∧
    -- Condition 5, display (15)
    IsIntervalPolicy π ∧ (∀ y ∈ E, π y = Mode.S) ∧
    (∀ x (S : ControlSystem p x), S.IsFeedback π →
      Nonempty (ContinuousSemimartingale S.P S.ℱ (fun t ω => V (S.H t ω)))) ∧
    (∀ y, p.generator (π y) V y = 0)) ∧
  -- Condition 6, display (16)
  (∀ x (S : ControlSystem p x), S.IsFeedback π →
    Tendsto (fun t : ℝ≥0 => ∫⁻ ω, ENNReal.ofReal ((1 + |S.H t ω|) * S.survival t ω) ∂S.P)
      atTop (𝓝 0))

end ChurnServiceMode


