-- Prove2me | Definitions.Def_FreeOrderEPTAS_IsDependentRounding
-- name    : FreeOrderEPTAS_IsDependentRounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:58.279023+00:00
-- url     : https://prove2.me/theorems/9baa6d9f-f485-45b3-8b15-9d8b46112f5a
-- title:
--   Dependent rounding with (P1)–(P3)
-- statement:
--   Let $y$ meet (S1)–(S3). A law of a binary vector $Y=(Y_{(i,t),j})$ has properties (P1)–(P3) if:
--
--   1. (P1) $\mathbb P(Y_{(i,t),j}=1)=y_{(i,t),j}$ for all $i,t$ and $j\in J_t$;
--   2. (P2) $Y$ satisfies (S2) and (S3) with probability 1;
--   3. (P3) for every pair-vertex $(i,t)$, all $[0,1]$-valued coefficients $\{\alpha_j\}_{j\in J_t}$, every $\lambda\le\mathbb E[\sum_{j\in J_t}\alpha_jY_{(i,t),j}]$ and every $\eta\in(0,1)$,
--   $$\mathbb P\Big(\sum_{j\in J_t}\alpha_jY_{(i,t),j}\le(1-\eta)\lambda\Big)\le\exp\Big(-\frac{\lambda\eta^2}{2}\Big).$$
--
--   `IsDependentRounding rnd` says that `rnd P y` has these properties whenever `y` meets (S1)–(S3). `callRnd` is one counted call, and each call is an independent draw.
--
--   This is the rounding of Gandhi et al., as translated on p.12. The milestone `rounding_exists` states that such laws exist.
--
--   **Formalization Note** `pr p S` is the probability of `S` as a real number. Expectations are finite sums over binary vectors.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §2.5, p.12, properties (P1)–(P3)

import Mathlib
import Definitions.Def_FreeOrderEPTAS_LPData
import Definitions.Def_FreeOrderEPTAS_Prog

namespace FreeOrderEPTAS

/-- The probability of an event under a finite law, as a real number. -/
noncomputable def pr {α : Type} (p : PMF α) (S : Set α) : ℝ :=
  (p.toOuterMeasure S).toReal

/-- A dependent-rounding subroutine: a law on binary vectors for each LP and each vector `y`. -/
abbrev Rounding : Type := (P : LPData) → P.Vars → PMF (Assignment P.m P.n)

/-- Properties (P1)–(P3) of a law `p` of `Y = (Y_{(i,t),j})` for the vector `y`
(arXiv:2007.13121v3, p.12). -/
structure RoundingProps (P : LPData) (y : P.Vars) (p : PMF (Assignment P.m P.n)) : Prop where
  /-- (P1) Marginal distribution: `P(Y_{(i,t),j} = 1) = y_{(i,t),j}`. -/
  marginal : ∀ i j, pr p {Y | Y i j = true} = y i j
  /-- (P2) Degree preservation: `Y` satisfies (S2) and (S3) with probability 1. -/
  degree : ∀ Y ∈ p.support, P.S2 (toVars P Y) ∧ P.S3 (toVars P Y)
  /-- (P3) Concentration inequalities: for every pair-vertex `(i, t)`, all `[0, 1]`-valued
  coefficients on `J_t`, every `λ ≤ E[∑_{j ∈ J_t} α_j Y_{(i,t),j}]` and every `η ∈ (0, 1)`,
  `P(∑_{j ∈ J_t} α_j Y_{(i,t),j} ≤ (1 - η) · λ) ≤ exp(-λη²/2)`. -/
  concentration : ∀ (i : Fin P.m) (t : Fin P.T) (α : Fin P.n → ℝ),
    (∀ j, P.ρ j = t → α j ∈ Set.Icc (0 : ℝ) 1) →
    ∀ lam η : ℝ,
      lam ≤ ∑ Y, (p Y).toReal * ∑ j with P.ρ j = t, α j * bit (Y i j) →
      η ∈ Set.Ioo (0 : ℝ) 1 →
      pr p {Y | ∑ j with P.ρ j = t, α j * bit (Y i j) ≤ (1 - η) * lam} ≤
        Real.exp (-(lam * η ^ 2 / 2))

/-- Dependent rounding (§2.5, p.12): on every vector meeting (S1)–(S3), the law has (P1)–(P3). -/
def IsDependentRounding (rnd : Rounding) : Prop :=
  ∀ P y, P.MeetsS123 y → RoundingProps P y (rnd P y)

/-- One counted rounding: a fresh independent draw from `rnd P y`. Writing the instance costs
`P.size` operations; `maxSize` records it. -/
noncomputable def callRnd (rnd : Rounding) (P : LPData) (y : P.Vars) :
    Prog (Assignment P.m P.n) := do
  modify fun c => { c with
    ops := c.ops + P.size, rndCalls := c.rndCalls + 1, maxSize := max c.maxSize P.size }
  StateT.lift (rnd P y)

end FreeOrderEPTAS


