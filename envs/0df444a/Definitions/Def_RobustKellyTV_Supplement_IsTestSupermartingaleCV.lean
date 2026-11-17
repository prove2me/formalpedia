-- Prove2me | Definitions.Def_RobustKellyTV_Supplement_IsTestSupermartingaleCV
-- name    : RobustKellyTV_Supplement_IsTestSupermartingaleCV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:31:59.940975+00:00
-- url     : https://prove2.me/theorems/0bc992bb-936c-4fdf-ab0b-37ae11576ce8
-- title:
--   Test supermartingales under the conditionally varying null of $\mathcal P_0$
-- statement:
--   Let $Q$ be a probability law of an observation sequence $X_1,X_2,\dots$ with values in $\{1,\dots,d\}$, and let $\mathcal F_t=\sigma(X_1,\dots,X_t)$ ($\mathcal F_0$ trivial). The **one-step conditional law** of $X_{t+1}$ given the past is the random probability vector
--
--   $$Q_t(\cdot)=\big(Q(X_{t+1}=i\mid\mathcal F_t)\big)_{i=1}^d .$$
--
--   $Q$ belongs to the **conditionally varying null** of $\mathcal P_0=B_{\mathrm{TV}}(P,\epsilon_0)$ if for every $t\ge0$, $Q$-almost surely, $Q_t\in\mathcal P_0$: the data-generating law may change from round to round, adaptively to the past, as long as each one-step conditional law stays in the total-variation ball. Every i.i.d. law $R^\infty$ with $R\in\mathcal P_0$ belongs to it.
--
--   A process $(M_n)_{n\ge0}$ adapted to $(\mathcal F_n)$ is a **test supermartingale under the conditionally varying null** if
--
--   1. $M_0=1$;
--   2. $M_n\ge0$ for every $n$;
--   3. under every law $Q$ of the conditionally varying null, $M$ is a supermartingale: $\mathbb E_Q[M_n\mid\mathcal F_{n-1}]\le M_{n-1}$ for every $n\ge1$.
--
--   This is the validity notion of Theorem B.1; by Ville's inequality it makes $\tau_\alpha=\inf\{n\ge1:M_n\ge1/\alpha\}$ a level-$\alpha$ sequential test against the whole conditionally varying null, not only against i.i.d. nulls.
--
--   **Formalization Note** The paper uses the phrase "conditionally varying null" without a definition; this is the standard sequential composite null. $X_{t+1}$ is coordinate $t$ of $\omega:\mathbb N\to\mathrm{Fin}\,d$ and $\mathcal F_t$ is the published prefix filtration; $Q(X_{t+1}=i\mid\mathcal F_t)$ is the conditional expectation of the indicator of $\{\omega_t=i\}$. The notion is stronger than the published `RobustKellyTV.IsTestSupermartingale`, which asks for the supermartingale property only under the i.i.d. laws $R^\infty$, $R\in\mathcal P_0$.
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §1.1 eqs. (3)–(4) pp.3–4 (test supermartingale); Theorem B.1, p.35 (conditionally varying null)

import Mathlib
import Definitions.Def_RobustKellyTV_seqLaw

open MeasureTheory

namespace RobustKellyTV.Supplement

variable {d : ℕ}

/-- The one-step conditional law of the next observation under a law `Q` on sequences: the vector
`i ↦ Q(X_{t+1} = i | F_t)`, i.e. the conditional expectation of the indicator of `{ω t = i}` given
the prefix σ-algebra `F_t = σ(X₁, …, X_t)` (arXiv:2611.02130v1, §1.1, pp.3–4).

**Formalization Note.** Observation `X_{t+1}` is coordinate `t` of `ω : ℕ → Fin d` and `F_t` is
the published `prefixFiltration d t`. A conditional expectation is defined up to `Q`-null sets;
it is only used inside `Q`-almost-sure statements. -/
noncomputable def condLaw (Q : Measure (ℕ → Fin d)) (t : ℕ) (ω : ℕ → Fin d) : Fin d → ℝ :=
  fun i => (Q[{ω' : ℕ → Fin d | ω' t = i}.indicator (fun _ => (1 : ℝ)) |
    prefixFiltration d t]) ω

/-- `Q` belongs to the **conditionally varying null** of P0 (arXiv:2611.02130v1, Theorem B.1,
p.35): `Q` is a probability measure on sequences and, for every `t`, `Q`-almost surely the
conditional law of the next observation given the past lies in `P0 = B_TV(P, ϵ0)`.

**Formalization Note.** The paper uses the phrase without defining it; this is the standard
sequential composite null, in which the data-generating law may change from round to round,
adaptively to the past, as long as every one-step conditional law lies in `P0`. Every i.i.d. law
`R^∞` with `R ∈ P0` belongs to it. -/
def IsCondVaryingNull (σ : Setting d) (Q : Measure (ℕ → Fin d)) : Prop :=
  IsProbabilityMeasure Q ∧ ∀ t, ∀ᵐ ω ∂Q, condLaw Q t ω ∈ nullBall σ

/-- `M` is a **test supermartingale under the conditionally varying null** (arXiv:2611.02130v1,
§1.1 p.4 and Theorem B.1 p.35): `M₀ = 1`, `M ≥ 0`, and `M` is a supermartingale for the prefix
filtration under every law `Q` of the conditionally varying null.

**Formalization Note.** This is stronger than the published `RobustKellyTV.IsTestSupermartingale`,
which asks for the supermartingale property only under the i.i.d. laws `R^∞`, `R ∈ P0`. -/
def IsTestSupermartingaleCV (σ : Setting d) (M : ℕ → (ℕ → Fin d) → ℝ) : Prop :=
  (∀ ω, M 0 ω = 1) ∧ (∀ n ω, 0 ≤ M n ω) ∧
    ∀ Q : Measure (ℕ → Fin d), IsCondVaryingNull σ Q → Supermartingale M (prefixFiltration d) Q

end RobustKellyTV.Supplement


