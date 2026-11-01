-- Prove2me | Definitions.Def_ConstrainedTrading_polymatroid
-- name    : ConstrainedTrading_polymatroid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:59.872157+00:00
-- url     : https://prove2.me/theorems/1235c01f-1ccb-4849-b0e2-5f99eaaadcbe
-- title:
--   Polymatroid $P(\rho)$ of an integer set function
-- statement:
--   For $\rho:2^E\to\mathbb Z$ on a finite ground set $E$, the **polymatroid** of $\rho$ is
--   $$
--   P(\rho)=\Bigl\{x\in\mathbb R^E:\ x\ge0,\ \ \sum_{e\in S}x_e\le\rho(S)\ \ \forall S\subseteq E\Bigr\}.
--   $$
--   When $\rho$ is submodular (and integer valued) this is an **integral polymatroid**, the constraint set $P$ on trades in the paper.
--
--   **Formalization Note** This is the published `PolyClinch.TwoSided.polymatroidOn` on the whole ground set, with $\rho$ cast to $\mathbb R$; it bundles no condition on $\rho$. The page's formula omits $x\ge0$; it is included because it is the standard meaning of polymatroid, outcomes are nonnegative (p.3), and without it Theorem 3.1 fails.
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, p.4 (polymatroid P_f, integral polymatroid)

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Polymatroid

namespace ConstrainedTrading

/-- The **polymatroid** of a set function `ρ : 2^E → ℤ` on a finite ground set `E`,
`P(ρ) = {x ∈ ℝ^E : x ≥ 0, Σ_{e∈S} x_e ≤ ρ(S) ∀ S ⊆ E}` (Kizilkale–Vohra, *Constrained Trading
Networks*, arXiv:2008.09757v1, p.4; it is an *integral polymatroid* when `ρ` is integer valued
and submodular, `SteinitzExchange.Duality.IsSubmodular ρ`).

**Formalization Note** This is the published polymatroid `PolyClinch.TwoSided.polymatroidOn`
on the whole ground set (`Finset.univ`), with `ρ` cast to `ℝ`; that definition bundles no
condition on `ρ`. The page's formula
`P_f = {x ∈ ℝ^E : Σ_{e∈S} x_e ≤ f(S) ∀S ⊆ E}` omits `x ≥ 0`; it is included here (reading R1):
it is the standard meaning of "polymatroid", outcomes are nonnegative (`x ∈ ℤ₊^E`, p.3), and
without it Theorem 3.1 is false. -/
def polymatroid {E : Type*} [Fintype E] (ρ : Finset E → ℤ) : Set (E → ℝ) :=
  PolyClinch.TwoSided.polymatroidOn Finset.univ (fun S => (ρ S : ℝ))

end ConstrainedTrading


