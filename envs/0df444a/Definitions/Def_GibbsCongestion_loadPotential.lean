-- Prove2me | Definitions.Def_GibbsCongestion_loadPotential
-- name    : GibbsCongestion_loadPotential
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:25.081895+00:00
-- url     : https://prove2.me/theorems/54e3217d-5f05-46a5-a052-9ffadff56b78
-- title:
--   Rosenthal's potential on load profiles $\Phi(\alpha)$
-- statement:
--   For a strategy load profile $\alpha$, the potential is
--   $$\Phi(\alpha)=\sum_{e\in E}\sum_{k=1}^{\ell_e(\alpha)}c_e(k),\qquad \ell_e(\alpha)=\sum_{p\in\mathcal P:\,e\in p}\alpha_p.$$
--   It equals $\Phi(s)$ for every $s\in\mathcal S(\alpha)$ (footnote 21), so Rosenthal's potential is a function on $\mathcal L$. Proposition 4.1 states that this function is M-convex for extension parallel games.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §4, p.15, footnote 21; display (3), p.7

import Mathlib

namespace GibbsCongestion

/-- **Rosenthal's potential on load profiles**: for `α ∈ L`,
`Φ(α) = ∑_{e ∈ E} ∑_{k=1}^{ℓ_e} c_e(k)` with `ℓ_e = ∑_{p ∋ e} α_p`, which equals `Φ(s)` for every
`s ∈ S(α)` (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §4, p.15, footnote 21, with display (3), p.7). -/
noncomputable def loadPotential {E : Type*} [Fintype E] [DecidableEq E] {P : Finset (Finset E)}
    (c : E → ℕ → ℝ) (α : P → ℕ) : ℝ :=
  ∑ e, ∑ k ∈ Finset.Icc 1 (∑ p ∈ Finset.univ.filter (fun p : P => e ∈ (p : Finset E)), α p), c e k

end GibbsCongestion


