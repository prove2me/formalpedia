-- Prove2me | Definitions.Def_CondConvexRisk_Representation_Representable
-- name    : CondConvexRisk_Representation_Representable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:53:33.758733+00:00
-- url     : https://prove2.me/theorems/c888dfed-dffe-4ab4-ab5f-ba7ec74da3db
-- title:
--   Definition 3.1 — representable conditional risk measure, minimal penalty $\alpha^*$, continuity from above
-- statement:
--   Keep the setting of Definition 2.2: $(\Omega,\mathcal F,P)$, $\mathcal G\subseteq\mathcal F$, $\mathcal P_{\mathcal G}$, and a map $\rho:L^\infty\to L^\infty_{\mathcal G}$. For $Q\in\mathcal P_{\mathcal G}$ write $E_Q(X\mid\mathcal G)$ for the conditional expectation of $X$ under $Q$.
--
--   1. A **(random) penalty function** for $\rho$ is a map $\alpha:\mathcal P_{\mathcal G}\to L^0_{\mathcal G}([0,+\infty])$ such that for every $X\in L^\infty$
--   $$\rho(X)=\operatorname*{ess.sup}_{Q\in\mathcal P_{\mathcal G}}\{-E_Q(X\mid\mathcal G)-\alpha(Q)\}\quad P\text{-a.s.},$$
--   where $a-(+\infty)=-\infty$ for real $a$. The map $\rho$ is **representable** if it has a penalty function.
--   2. A map $\alpha^*$ is the **minimal penalty** of $\rho$ if for every $Q\in\mathcal P_{\mathcal G}$
--   $$\alpha^*(Q)=\operatorname*{ess.sup}_{X\in L^\infty}\{-E_Q(X\mid\mathcal G)-\rho(X)\},$$
--   the essential supremum of the family $B_Q=\{-E_Q(X\mid\mathcal G)-\rho(X) : X\in L^\infty\}$.
--   3. $\rho$ is **continuous from above** if $X_n, X\in L^\infty$ and $X_n\searrow X$ $P$-a.s. imply $\rho(X_n)\nearrow\rho(X)$ $P$-a.s.
--
--   These are the three notions compared in Theorem 3.2.
--
--   **Formalization Note** $E_Q(X\mid\mathcal G)$ is Mathlib's `Q[X | m]`; it is $\mathcal G$-measurable and, because $Q=P$ on $\mathcal G$, determined up to a $P$-null set. Penalties take values in `ENNReal` and are coerced to `EReal`, so only real $-(+\infty)$ occurs. $\alpha^*$ is given by the predicate `IsMinimalPenalty` on a candidate (the essential supremum exists by Theorem A.1). "$X_n\searrow X$" means a.s. non-increasing and a.s. convergent to $X$; "$\rho(X_n)\nearrow\rho(X)$" means a.s. non-decreasing and a.s. convergent.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 5, Definition 3.1 (eq. (3)); p. 6, Theorem 3.2 (a) and (c) (continuity from above, α*); p. 7 (the set B_Q)

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

/-- The space `L∞` of payoffs, as the subtype of real functions with `MemLp X ∞ P`. -/
abbrev LInf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) : Type _ :=
  {X : Ω → ℝ // MemLp X ⊤ P}

/-- The family `Q ↦ -E_Q(X | G) - α(Q)`, `Q ∈ P_G`, of extended random variables appearing in
the robust representation (3), p. 5.  `E_Q(X | G)` is Mathlib's conditional expectation
`Q[X | m]` (a `G`-measurable function); the penalty `α(Q)` takes values in `[0, +∞]`, and a
finite number minus `+∞` is `-∞` in `EReal`. -/
noncomputable def reprFamily {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (α : PG m P → Ω → ENNReal) (X : Ω → ℝ) :
    PG m P → Ω → EReal :=
  fun Q ω => ((-(Q.1[X | m]) ω : ℝ) : EReal) - (α Q ω : EReal)

/-- Definition 3.1, p. 5: `α : P_G → L⁰_G([0, +∞])` is a (random) penalty function for `ρ`:
each `α(Q)` is `G`-measurable and `[0, +∞]`-valued, and for every `X ∈ L∞`
`ρ(X) = ess.sup_{Q ∈ P_G} {-E_Q(X | G) - α(Q)}` `P`-a.s. -/
def IsPenaltyFor {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (ρ : (Ω → ℝ) → Ω → ℝ) (α : PG m P → Ω → ENNReal) : Prop :=
  (∀ Q, Measurable[m] (α Q)) ∧
    ∀ X : Ω → ℝ, MemLp X ⊤ P → IsEssSup P (reprFamily m P α X) (fun ω => (ρ X ω : EReal))

/-- Definition 3.1, p. 5: `ρ` is representable, i.e. it admits a (random) penalty function. -/
def IsRepresentable {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ρ : (Ω → ℝ) → Ω → ℝ) : Prop :=
  ∃ α : PG m P → Ω → ENNReal, IsPenaltyFor m P ρ α

/-- The family `B_Q = {-E_Q(X | G) - ρ(X) | X ∈ L∞}` (p. 7), indexed by `X ∈ L∞`. -/
noncomputable def penaltyFamily {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ρ : (Ω → ℝ) → Ω → ℝ) (Q : PG m P) : LInf P → Ω → EReal :=
  fun X ω => ((-(Q.1[X.1 | m]) ω - ρ X.1 ω : ℝ) : EReal)

/-- Theorem 3.2 (c), p. 6: `α*` is the minimal penalty of `ρ`,
`α*(Q) = ess.sup_{X ∈ L∞} {-E_Q(X | G) - ρ(X)}` for every `Q ∈ P_G`.  This is a predicate on a
candidate `α*`; by Theorem A.1 an essential supremum exists and is `P`-a.s. unique. -/
def IsMinimalPenalty {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ρ : (Ω → ℝ) → Ω → ℝ) (α : PG m P → Ω → ENNReal) : Prop :=
  ∀ Q : PG m P, IsEssSup P (penaltyFamily m P ρ Q) (fun ω => (α Q ω : EReal))

/-- Theorem 3.2 (a), p. 6: `ρ` is continuous from above: whenever `X_n, X ∈ L∞` and
`X_n ↘ X` `P`-a.s. (a.s. non-increasing and a.s. convergent to `X`), then `ρ(X_n) ↗ ρ(X)`
`P`-a.s. (a.s. non-decreasing and a.s. convergent to `ρ(X)`). -/
def IsContinuousFromAbove {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ : (Ω → ℝ) → Ω → ℝ) : Prop :=
  ∀ (X : ℕ → Ω → ℝ) (Y : Ω → ℝ), (∀ n, MemLp (X n) ⊤ P) → MemLp Y ⊤ P →
    (∀ᵐ ω ∂P, Antitone (fun n => X n ω) ∧ Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) →
    ∀ᵐ ω ∂P, Monotone (fun n => ρ (X n) ω) ∧ Tendsto (fun n => ρ (X n) ω) atTop (𝓝 (ρ Y ω))

end CondConvexRisk.Representation


