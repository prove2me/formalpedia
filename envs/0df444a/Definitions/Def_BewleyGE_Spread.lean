-- Prove2me | Definitions.Def_BewleyGE_Spread
-- name    : BewleyGE_Spread
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:13.262002+00:00
-- url     : https://prove2.me/theorems/0799cd83-10c0-4be0-92d5-608e4f420822
-- title:
--   Spread endowments
-- statement:
--   The endowment support $\mathcal Y$ is **spread** if there are $y',y''\in\mathcal Y$ with $y''\ll y'$, i.e. $y''_i<y'_i$ for every good $i$.
--
--   This is the content of the paper's assumption that some $y'\in\mathcal Y$ satisfies $y'-y\gg0$ for all other $y\in\mathcal Y$, which its proof of Lemma 8 uses through the gap $p\cdot y'-\min_{y}p\cdot y>0$. It holds for a joint support with a strict top element and at least two points, and for a product support in which every coordinate takes at least two values.
--
--   **Formalization Note** The paper's literal model (a product support $\mathcal Y_1\times\cdots\times\mathcal Y_n$ with a strict top element) forces $\mathcal Y$ to be a single point when $n\ge2$; in that case several of the paper's lemmas fail, so the lemmas are stated under this hypothesis.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §2, p.5; proof of Lemma 8, pp.26–27

import Mathlib
import Definitions.Def_BewleyGE_Economy

namespace BewleyGE

/-- **Spread endowments**: there are `y′, y″ ∈ 𝒴` with `y″ ≪ y′` (every coordinate strictly
smaller). Light, arXiv:1906.06810v2, §2, p.5, "there exists an element y′ in 𝒴 such that
y′ − y ≫ 0 for all y ∈ 𝒴 \ {y′}"; used in the proof of Lemma 8, pp.26–27.

**Formalization Note.** This is the endowment hypothesis of the milestones (reading R1). The
page's strict top element on a support with at least two points implies it, and so does a
product support `𝒴₁ × ⋯ × 𝒴ₙ` in which every marginal has at least two points. The page's
literal product form plus strict top element forces `𝒴` to be a singleton when `n ≥ 2`; the goal
theorem covers that case separately (`E.Y.card = 1`). -/
def Spread {n : ℕ} (E : Economy n) : Prop :=
  ∃ y' ∈ E.Y, ∃ y'' ∈ E.Y, ∀ i, y'' i < y' i

end BewleyGE


