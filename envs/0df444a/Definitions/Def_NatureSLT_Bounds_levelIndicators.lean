-- Prove2me | Definitions.Def_NatureSLT_Bounds_levelIndicators
-- name    : NatureSLT_Bounds_levelIndicators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:45.383982+00:00
-- url     : https://prove2.me/theorems/ab7b975e-3dba-45aa-ae53-f16716344f60
-- title:
--   Set of indicators $I(z, \alpha, \beta) = \theta\{Q(z, \alpha) - \beta\}$, $\beta \in (A, B)$, of a set of real functions
-- statement:
--   Let $\theta$ be the step function, $\theta(u) = 0$ for $u < 0$ and $\theta(u) = 1$ for $u \ge 0$. Let $Q(z, \alpha)$, $\alpha \in \Lambda$, be a set of real functions on $Z$ and $A < B$ two reals bounding it, and denote by $\mathcal B = (A, B)$ the open interval between them. The **set of indicators** of the set of real functions is
--   $$I(z, \alpha, \beta) = \theta\{Q(z, \alpha) - \beta\}, \qquad \alpha \in \Lambda,\ \beta \in \mathcal B .$$
--   For a given $\alpha^*$ and $\beta^*$, the indicator $I(z, \alpha^*, \beta^*)$ equals $1$ on the region where $Q(z, \alpha^*) \ge \beta^*$ and $0$ where $Q(z, \alpha^*) < \beta^*$.
--
--   The annealed entropy $H^{\Lambda, \mathcal B}_{\mathrm{ann}}$ and the growth function $G^{\Lambda, \mathcal B}$ of this set of indicators replace $H^\Lambda_{\mathrm{ann}}$ and $G^\Lambda$ in the basic inequalities for real functions, (3.6)–(3.17) of the book.
--
--   **Formalization Note** The set of indicators is a family of real functions indexed by the pairs $(\alpha, \beta)$ with $\beta$ in the open interval $(A, B)$ (the subtype `Set.Ioo A B`), so that the counting function $N$, the annealed entropy and the growth function of this mission apply to it unchanged. The step function is `step u = if 0 ≤ u then 1 else 0`, the book's convention $\theta(0) = 1$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 73, Section 3.2; step function θ as in (3.22), p. 80

import Mathlib

namespace NatureSLT.Bounds

/-- The step function `θ(u) = 0` for `u < 0` and `θ(u) = 1` for `u ≥ 0` (Vapnik, *The Nature of
Statistical Learning Theory*, 2nd ed., (3.22), p. 80). -/
noncomputable def step (u : ℝ) : ℝ := if 0 ≤ u then 1 else 0

/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., p. 73, §3.2: the set of
indicators `I(z, α, β) = θ{Q(z, α) − β}`, `α ∈ Λ`, `β ∈ 𝓑`, of a set of real functions
`Q(z, α)`, `α ∈ Λ`, where `𝓑 = (A, B)` is the open interval between the bounds `A` and `B`.
It is indexed by the pairs `(α, β)` with `β ∈ (A, B)`. -/
noncomputable def levelIndicators {Λ Z : Type*} (Q : Λ → Z → ℝ) (A B : ℝ) :
    Λ × Set.Ioo A B → Z → ℝ :=
  fun p z => step (Q p.1 z - p.2)

end NatureSLT.Bounds


