-- Prove2me | Definitions.Def_RecruitSmaller_Supplement_Mechanism
-- name    : RecruitSmaller_Supplement_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:53:50.521201+00:00
-- url     : https://prove2.me/theorems/bc809107-8dc5-40a3-97a1-5758cf71285a
-- title:
--   Randomized two-sided mechanism (expected allocations and payments)
-- statement:
--   A **mechanism** $M$ for $m$ buyers and $k$ sellers specifies, for every reported profile of buyer valuations $b=(b_1,\dots,b_m)\in\mathbb R^m$ and seller costs $s=(s_1,\dots,s_k)\in\mathbb R^k$, a (possibly randomized) allocation rule and payment rule, in expected form:
--
--   1. Borel-measurable expected allocation probabilities $x^B_j(b,s)\in[0,1]$ for each buyer $j$ and $x^S_\ell(b,s)\in[0,1]$ for each seller $\ell$, subject to the feasibility constraint
--   $$
--   \sum_{j=1}^m x^B_j(b,s)=\sum_{\ell=1}^k x^S_\ell(b,s);
--   $$
--   2. expected payments $p^B_j(b,s)\in\mathbb R$ paid by buyer $j$ and $p^S_\ell(b,s)\in\mathbb R$ paid to seller $\ell$.
--
--   This is the class of mechanisms over which the paper's impossibility results quantify: deterministic or randomized, anonymous or not.
--
--   **Formalization Note** Randomization enters only through the expected quantities, as on the page. The allocations are required to be jointly measurable in $(b,s)$; payments carry no measurability requirement (the page asks it of allocations only). A mechanism is a fixed function of the reports, which is prior independence.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), §2.1, p.10 (PDF 12)

import Mathlib

open MeasureTheory

namespace RecruitSmaller.Supplement

/-- A (possibly randomized) **mechanism** for `m` buyers and `k` sellers in a two-sided market
(Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), §2.1, p.10), given in expected form: at every reported profile `(b, s) ∈ ℝᵐ × ℝᵏ` it
specifies Borel-measurable expected allocation probabilities `xB j (b, s) ∈ [0, 1]` for each buyer
`j` and `xS ℓ (b, s) ∈ [0, 1]` for each seller `ℓ`, subject to the feasibility constraint
`∑ⱼ xB j (b, s) = ∑ₗ xS ℓ (b, s)`, and expected payments `pB j (b, s) ∈ ℝ` paid by buyer `j` and
`pS ℓ (b, s) ∈ ℝ` paid to seller `ℓ`.

**Formalization Note** The internal randomness of a randomized mechanism enters only through these
expected quantities, as on the page; deterministic mechanisms are the case of `{0, 1}`-valued
allocations. Measurability is required of the allocation rule (jointly in `(b, s)`) and not of the
payments, as on the page. Reports range over all of `ℝ`. A mechanism is a fixed function of the
reports, so it cannot depend on the distributions (prior independence); the theorems express this
by quantifying over the mechanism before the distributions. -/
structure Mechanism (m k : ℕ) where
  /-- Expected allocation probability of buyer `j` at the reported profile `(b, s)`. -/
  xB : Fin m → (Fin m → ℝ) → (Fin k → ℝ) → ℝ
  /-- Expected allocation probability of seller `ℓ` at the reported profile `(b, s)`. -/
  xS : Fin k → (Fin m → ℝ) → (Fin k → ℝ) → ℝ
  /-- Expected payment made by buyer `j`. -/
  pB : Fin m → (Fin m → ℝ) → (Fin k → ℝ) → ℝ
  /-- Expected payment made to seller `ℓ`. -/
  pS : Fin k → (Fin m → ℝ) → (Fin k → ℝ) → ℝ
  xB_mem : ∀ j b s, xB j b s ∈ Set.Icc (0 : ℝ) 1
  xS_mem : ∀ l b s, xS l b s ∈ Set.Icc (0 : ℝ) 1
  feasible : ∀ b s, ∑ j, xB j b s = ∑ l, xS l b s
  measurable_xB : ∀ j, Measurable fun ω : (Fin m → ℝ) × (Fin k → ℝ) => xB j ω.1 ω.2
  measurable_xS : ∀ l, Measurable fun ω : (Fin m → ℝ) × (Fin k → ℝ) => xS l ω.1 ω.2

end RecruitSmaller.Supplement


