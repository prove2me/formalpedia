-- Prove2me | Definitions.Def_StrongWeakEq_Existence_SecondOrder
-- name    : StrongWeakEq_Existence_SecondOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:28.880701+00:00
-- url     : https://prove2.me/theorems/ac2f8863-102d-4d7b-a838-47a6367ce8ca
-- title:
--   (3.3)–(3.5), p. 6 and the conditions of Lemma 3.2, p. 8 — shift bound h, C¹ regularity with remainder r, G and Λ (3.17)
-- statement:
--   Let $D_i$, $\mathcal Q$, $F$ and $\Gamma^{Q^*}$ be as in the model of §2.
--
--   1. **Shift bound** (3.3)–(3.5), p. 6. There is a nonnegative function $h(t,\varepsilon;i,q)$ such that
--   $$|f(t+\varepsilon,i,q)-f(t,i,q)|\le h(t,\varepsilon;i,q)\qquad\forall t\ge 0,\ \varepsilon>0,\ i\in S,\ q\in D_i, \tag{3.3}$$
--      $\varepsilon\mapsto h(t,\varepsilon;i,q)$ is nondecreasing with $\lim_{\varepsilon\downarrow 0}h(t,\varepsilon;i,q)=0$ (3.4), and $\int_0^\infty h(t,\varepsilon;i,q)\,dt<\infty$ for $\varepsilon>0$ small enough (3.5).
--   2. **The conditions of Lemma 3.2**, p. 8, for a function $f_t$: for every $i$ and $q\in D_i$, $f(\cdot,i,q)$ is $C^1$ on $[0,\infty)$ with derivative $f_t(\cdot,i,q)$; $f_t$ satisfies (2.3); and there is a function $r(t,\varepsilon;i,q)$, continuous in $\varepsilon$, with
--   $$|f(t+\varepsilon,i,q)-(f(t,i,q)+\varepsilon f_t(t,i,q))|\le r(t,\varepsilon;i,q)\qquad t\ge0,\ \varepsilon>0,\ i\in S,\ q\in D_i, \tag{3.14}$$
--      satisfying (3.5), and with $\varepsilon\mapsto r(t,\varepsilon;i,q)/\varepsilon$ nondecreasing (3.15).
--   3. **The derivative payoff** (p. 8): $G(i,Q)=\mathbb E_{i,Q}\big[\int_0^\infty f_t(t,X_t,Q_{X_t})\,dt\big]$, $G(Q)=(G(1,Q),\dots,G(N,Q))$.
--   4. **The second-order coefficient** (3.17):
--   $$\Lambda^{Q^*}(i,Q)=f_t(0,i,Q_i)+Q_i\cdot\big(2G(Q^*)+\Gamma^{Q^*}(Q)\big),\qquad \Gamma^{Q^*}(Q)=\big(\Gamma^{Q^*}(Q_1),\dots,\Gamma^{Q^*}(Q_N)\big).$$
--
--   The shift bound is the hypothesis of the first-order expansion (3.6) and of Theorem 3.1; the Lemma 3.2 conditions give the second-order expansion (3.16) and are the regularity assumption of the strong half of Theorem 3.3.
--
--   **Formalization Note** $f_t$ is a parameter tied to $f$: for $q\in D_i$ and every $t\ge0$, $f_t(t,i,q)$ is the derivative of $s\mapsto f(s,i,q)$ within $[0,\infty)$ at $t$ (one-sided at $0$), and $t\mapsto f_t(t,i,q)$ is continuous on $[0,\infty)$. "Increasing" in (3.4) and (3.15) is read as nondecreasing on $\varepsilon>0$. Condition (3.5) is per $(i,q)$: for each $(i,q)$ there is $\varepsilon_0>0$ with $t\mapsto h(t,\varepsilon;i,q)$ (resp. $r$) integrable on $[0,\infty)$ for $0<\varepsilon<\varepsilon_0$. (2.3) for $f_t$ is the integrable-majorant form used for $f$. The expectation $\mathbb E_{i,Q}$ over the chain is written out through its one-dimensional marginals: under a generator $Q$ the law of $X_t$ given $X_0=i$ is the $i$-th row of the matrix exponential $e^{tQ}$, so $\mathbb E_{i,Q}[\int_0^\infty \varphi(t,X_t)\,dt]=\int_0^\infty\sum_j (e^{tQ})_{ij}\varphi(t,j)\,dt$ by Fubini; no Markov process is constructed. On p. 8 the first entry of the vector $\Gamma^{Q^*}(Q)$ is printed $\Gamma^{Q^*}(Q_i)$; it is $\Gamma^{Q^*}(Q_1)$, as the proof (A.16) on p. 24 confirms.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 6, (3.3)–(3.5); p. 8, Lemma 3.2 hypotheses (3.14)–(3.15), G and (3.17)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model

namespace StrongWeakEq.Existence

open MeasureTheory Filter Topology

/-- (3.3)–(3.5), p. 6: there is a nonnegative `h` with
`|f(t+ε,i,q) − f(t,i,q)| ≤ h(t,ε;i,q)` for `t ≥ 0`, `ε > 0`, `q ∈ Dᵢ` (3.3);
`ε ↦ h(t,ε;i,q)` nondecreasing with `lim_{ε↓0} h(t,ε;i,q) = 0` (3.4);
and, for each `(i,q)`, `∫₀^∞ h(t,ε;i,q) dt < ∞` for `ε > 0` small enough (3.5). -/
def ShiftBound {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) : Prop :=
  ∃ h : ℝ → ℝ → Fin N → (Fin N → ℝ) → ℝ,
    (∀ t, 0 ≤ t → ∀ ε, 0 < ε → ∀ i, ∀ q ∈ D i, 0 ≤ h t ε i q) ∧
    (∀ t, 0 ≤ t → ∀ ε, 0 < ε → ∀ i, ∀ q ∈ D i, |f (t + ε) i q - f t i q| ≤ h t ε i q) ∧
    (∀ t, 0 ≤ t → ∀ i, ∀ q ∈ D i,
      MonotoneOn (fun ε => h t ε i q) (Set.Ioi 0) ∧
      Tendsto (fun ε => h t ε i q) (𝓝[>] (0:ℝ)) (𝓝 0)) ∧
    (∀ i, ∀ q ∈ D i, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε ∈ Set.Ioo (0:ℝ) ε₀, IntegrableOn (fun t => h t ε i q) (Set.Ici 0))

/-- The conditions of Lemma 3.2, p. 8, with `ft` the time derivative of `f`:
`f(·,i,q)` is `C¹` on `[0,∞)` with derivative `ft(·,i,q)` (one-sided at `0`) for `q ∈ Dᵢ`;
`ft` satisfies (2.3); and there is `r`, continuous in `ε`, with
`|f(t+ε,i,q) − (f(t,i,q) + ε ft(t,i,q))| ≤ r(t,ε;i,q)` (3.14), satisfying (3.5), and with
`ε ↦ r(t,ε;i,q)/ε` nondecreasing (3.15). -/
structure SecondOrderReg {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f ft : ℝ → Fin N → (Fin N → ℝ) → ℝ) : Prop where
  hasDeriv : ∀ i, ∀ q ∈ D i, ∀ t, 0 ≤ t →
    HasDerivWithinAt (fun s => f s i q) (ft t i q) (Set.Ici 0) t
  deriv_cont : ∀ i, ∀ q ∈ D i, ContinuousOn (fun t => ft t i q) (Set.Ici 0)
  deriv_integ : ∀ c : ℝ, 0 < c → ∃ g : ℝ → ℝ, IntegrableOn g (Set.Ici 0) ∧
    ∀ t, 0 ≤ t → ∀ i, ∀ q ∈ D i, ‖q‖ ≤ c → |ft t i q| ≤ g t
  remainder : ∃ r : ℝ → ℝ → Fin N → (Fin N → ℝ) → ℝ,
    (∀ t, 0 ≤ t → ∀ ε, 0 < ε → ∀ i, ∀ q ∈ D i,
      |f (t + ε) i q - (f t i q + ε * ft t i q)| ≤ r t ε i q) ∧
    (∀ t, 0 ≤ t → ∀ i, ∀ q ∈ D i, ContinuousOn (fun ε => r t ε i q) (Set.Ioi 0)) ∧
    (∀ i, ∀ q ∈ D i, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε ∈ Set.Ioo (0:ℝ) ε₀, IntegrableOn (fun t => r t ε i q) (Set.Ici 0)) ∧
    (∀ t, 0 ≤ t → ∀ i, ∀ q ∈ D i, MonotoneOn (fun ε => r t ε i q / ε) (Set.Ioi 0))

/-- p. 8: `G(i,Q) = E_i[∫₀^∞ f_t(t, X_t, Q_{X_t}) dt] = ∫₀^∞ ∑ⱼ (e^{tQ})ᵢⱼ f_t(t, j, Qⱼ) dt`. -/
noncomputable def payoffDeriv {N : ℕ} (ft : ℝ → Fin N → (Fin N → ℝ) → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) : ℝ :=
  ∫ t in Set.Ioi (0:ℝ), ∑ j, NormedSpace.exp (t • Q) i j * ft t j (Q j)

/-- (3.17), p. 8: `Λ^{Q*}(i,Q) = f_t(0,i,Qᵢ) + Qᵢ · (2 G(Q*) + Γ^{Q*}(Q))`, where
`Γ^{Q*}(Q) = (Γ^{Q*}(Q₁), …, Γ^{Q*}(Q_N))`. -/
noncomputable def Lambda {N : ℕ} (f ft : ℝ → Fin N → (Fin N → ℝ) → ℝ)
    (Qs : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) (Q : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ft 0 i (Q i) + Q i ⬝ᵥ (fun j => 2 * payoffDeriv ft Qs j + Gamma f Qs j (Q j))

end StrongWeakEq.Existence


