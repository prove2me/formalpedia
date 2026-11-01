-- Prove2me | Definitions.Def_RiskStopTC_IsStoppingFamily
-- name    : RiskStopTC_IsStoppingFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:27.947914+00:00
-- url     : https://prove2.me/theorems/31ddd3b0-eb02-4806-b362-ed089850573e
-- title:
--   Monotone, translation equivariant, local one-step mappings $\varrho_{t|\mathcal F_t}:\mathcal Z_{t+1}\to\mathcal Z_t$
-- statement:
--   Let $(\Omega,\mathcal F,P)$ carry a filtration $(\mathcal F_t)$, fix $p$ and a horizon $T$, and write $\mathcal Z_t=L^p(\Omega,\mathcal F_t,P)$. A family of mappings $\varrho_t=\varrho_{t|\mathcal F_t}$, $t=0,\dots,T-1$, is a **family of one-step stopping mappings** if for every $t<T$:
--
--   1. $\varrho_t$ maps $\mathcal Z_{t+1}$ into $\mathcal Z_t$;
--   2. (**monotone**, Definition 3.4) $X\preceq X'$ in $\mathcal Z_{t+1}$ implies $\varrho_t(X)\preceq\varrho_t(X')$;
--   3. (**translation equivariant**, (v)) $\varrho_t(X+W)=\varrho_t(X)+W$ for $X\in\mathcal Z_{t+1}$ and $W\in\mathcal Z_t$;
--   4. (**local**, (5.17)) $\varrho_t(\mathbb 1_A X)=\mathbb 1_A\,\varrho_t(X)$ for $X\in\mathcal Z_{t+1}$ and $A\in\mathcal F_t$.
--
--   Here $\preceq$ and $=$ hold almost surely. These are exactly the hypotheses of Theorem 5.6 on the mappings; no convexity, coherence, positive homogeneity or normalization is assumed ($\varrho_t(0)=0$ follows from 4 with $A=\emptyset$).
--
--   **Formalization Note** Random variables are functions $\Omega\to\mathbb R$; $X\in\mathcal Z_t$ is the published `IsLp (ℱ t) P p X` ($\mathcal F_t$-measurable and in $L^p$). The mappings are one family `ϱ : ℕ → (Ω → ℝ) → Ω → ℝ`, constrained only on $\mathcal Z_{t+1}$ and only for $t<T$.
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, Theorem 5.6, p.20 (hypotheses); Definition 3.4, p.7; (v), p.7; (5.17), p.20

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions

namespace RiskStopTC

open MeasureTheory RiskFunctionals.NestedAVaR

/-- **The one-step mappings of Theorem 5.6.** Pichler, Liu & Shapiro, *Risk averse stochastic
programming: time consistency and optimal stopping*, arXiv:1808.10807v3, Theorem 5.6, p.20:
"Let ϱt|Ft : Zt+1 → Zt, t = 0, . . . , T − 1, be monotone translation equivariant mappings
possessing property (5.17)". Monotone is Definition 3.4, p.7; translation equivariant is (v), p.7;
(5.17), p.20, is `ϱt|Ft(1A · Z) = 1A · ϱt|Ft(Z)` for all `A ∈ Ft`. Here `Zt := Lp(Ω, Ft, P)` (§2,
p.3).

For every `t < T`:
* `mapsTo`: `ϱ t` maps `Z_{t+1}` into `Z_t`;
* `monotone`: `X ⪯ X'` in `Z_{t+1}` implies `ϱ t X ⪯ ϱ t X'` (a.s.);
* `translation`: `ϱ t (X + W) = ϱ t X + W` a.s. for `X ∈ Z_{t+1}`, `W ∈ Z_t`;
* `local`: (5.17), `ϱ t (1_A X) = 1_A ϱ t X` a.s. for `X ∈ Z_{t+1}` and `A ∈ F_t`.

**Formalization Note.** Random variables are functions `Ω → ℝ`; `X ∈ Z_t = L^p(Ω, F_t, P)` is the
published `IsLp (ℱ t) P p X` (an `F_t`-measurable representative in `L^p`; every class has one).
Relations between random variables hold `P`-almost surely, so by `monotone` each `ϱ t` respects
a.e. equality and acts on classes. The mappings form one family `ϱ : ℕ → (Ω → ℝ) → Ω → ℝ`,
constrained only on `Z_{t+1}` and only for `t < T`. There is no other axiom: no convexity, no
coherence, no positive homogeneity and no normalization (`ϱ t 0 = 0` follows from `local` with
`A = ∅`). -/
structure IsStoppingFamily {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ)
    (P : Measure[mΩ] Ω) (p : ENNReal) (T : ℕ) (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) : Prop where
  /-- `ϱ t` maps `Z_{t+1}` into `Z_t`. -/
  mapsTo : ∀ t < T, ∀ X, IsLp (ℱ (t + 1)) P p X → IsLp (ℱ t) P p (ϱ t X)
  /-- Monotonicity (Definition 3.4, p.7). -/
  monotone : ∀ t < T, ∀ X X', IsLp (ℱ (t + 1)) P p X → IsLp (ℱ (t + 1)) P p X' →
    X ≤ᵐ[P] X' → ϱ t X ≤ᵐ[P] ϱ t X'
  /-- Translation equivariance ((v), p.7). -/
  translation : ∀ t < T, ∀ X W, IsLp (ℱ (t + 1)) P p X → IsLp (ℱ t) P p W →
    ϱ t (X + W) =ᵐ[P] ϱ t X + W
  /-- The local property (5.17), p.20. -/
  «local» : ∀ t < T, ∀ X, IsLp (ℱ (t + 1)) P p X → ∀ A : Set Ω, MeasurableSet[ℱ t] A →
    ϱ t (A.indicator X) =ᵐ[P] A.indicator (ϱ t X)

end RiskStopTC


