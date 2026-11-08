-- Prove2me | Definitions.Def_ValiantModel_Learnable
-- name    : ValiantModel_Learnable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:54.337552+00:00
-- url     : https://prove2.me/theorems/247338ec-9094-4d56-800d-925c92c749e6
-- title:
--   Definition 1, p.1 — learnability in Valiant's model
-- statement:
--   A sequence of concept classes $H=(H_1,H_2,\dots)$ is **learnable in Valiant's model** if there is a learner $L$ such that, for all $\varepsilon,\delta\in(0,1)$, all $d$, every target $h^\star\in H_d$ and every distribution $D$ with $D(\mathrm{supp}(h^\star))=1$, the learner uses at most $m(d,\varepsilon,\delta)=\mathrm{poly}(d,1/\varepsilon,1/\delta)$ positive examples and membership queries, and with probability at least $1-\delta$ outputs a hypothesis $g$ with
--
--   $$
--   \mathrm{supp}(g)\subseteq\mathrm{supp}(h^\star)\qquad\text{and}\qquad \Pr_{x\sim D}\bigl(x\notin\mathrm{supp}(g)\bigr)\le\varepsilon .
--   $$
--
--   The polynomial bound is what gives the definition content: on a finite domain, $2^d$ queries learn any target. An auxiliary predicate, $L$ *witnesses the guarantee with complexity $m$*, states the same thing with any function $m$ in place of the polynomial, and is what the intermediate results use. The learner $L$ and the budget $m$ come before the target and the distribution.
--
--   **Formalization Note** The learner takes $(d,\varepsilon,\delta)$ as input and returns a distribution over deterministic protocols. Since $d,1/\varepsilon,1/\delta\ge 1$ on the range considered, a bound by a polynomial in these quantities is equivalent to the monomial bound $C\,(d/(\varepsilon\delta))^k$ with natural $C,k$. The budget is counted per oracle, as in Remark 3.1, and $d\ge 1$.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.1 (PDF p.3), Definition 1, footnote 1

import Mathlib
import Definitions.Def_ValiantModel_Guarantee

namespace ValiantModel

/-- A learner: on input `(d, ε, δ)`, a distribution over deterministic protocols. -/
abbrev Learner : Type := (d : ℕ) → ℝ → ℝ → PMF (Protocol d)

/-- `L` witnesses the guarantee of Definition 1 for `H` with sample/query complexity `m`,
arXiv:2605.13840 (version held), p.1 (PDF p.3): for every `d ≥ 1` and `ε, δ ∈ (0,1)`, `L` on
`(d, ε, δ)` stays within `m(d, ε, δ)` on each oracle and meets the Valiant guarantee. The budget
`m` depends only on `(d, ε, δ)`, not on the target or the distribution. No polynomial bound is
required here; `Learnable` adds it. -/
def HasComplexity (H : ConceptSequence) (L : Learner) (m : ℕ → ℝ → ℝ → ℕ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    WithinBudget (L d ε δ) (m d ε δ) ∧ Guarantee (H d) (L d ε δ) ε δ

/-- **Definition 1 (Valiant's Learning Model)**, arXiv:2605.13840 (version held), p.1 (PDF p.3):
`H` is learnable in Valiant's model if some learner witnesses the guarantee with a sample/query
complexity `m(d, ε, δ) = poly(d, 1/ε, 1/δ)`.

**Formalization Note.** Since `d, 1/ε, 1/δ ≥ 1` on the range considered, a bound by a polynomial in
these three quantities is equivalent to the monomial bound `C * (d / (ε * δ)) ^ k` written here. -/
def Learnable (H : ConceptSequence) : Prop :=
  ∃ (L : Learner) (m : ℕ → ℝ → ℝ → ℕ), HasComplexity H L m ∧
    ∃ C k : ℕ, ∀ d : ℕ, 1 ≤ d → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      (m d ε δ : ℝ) ≤ C * ((d : ℝ) / (ε * δ)) ^ k

end ValiantModel


