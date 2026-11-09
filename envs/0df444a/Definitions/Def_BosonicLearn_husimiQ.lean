-- Prove2me | Definitions.Def_BosonicLearn_husimiQ
-- name    : BosonicLearn_husimiQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:19:32.338961+00:00
-- url     : https://prove2.me/theorems/a954b419-3fbb-4cc4-8dea-d91b01e70955
-- title:
--   Husimi density $Q_\rho(\beta)=(2\pi)^{-n}\langle\alpha(\beta)|\rho|\alpha(\beta)\rangle$
-- statement:
--   For an $n$-mode density operator $\rho$ and $\beta\in\mathbb R^{2n}$,
--
--   $$Q_\rho(\beta)=(2\pi)^{-n}\,\langle\alpha(\beta)|\rho|\alpha(\beta)\rangle=(2\pi)^{-n}\operatorname{Re}\sum_{u,v}\overline{c(\beta)_u}\,\rho_{uv}\,c(\beta)_v .$$
--
--   It is the density, with respect to Lebesgue measure on $\mathbb R^{2n}$, of the outcome of heterodyne detection on $\rho$.
--
--   **Formalization Note** The familiar normalization $\pi^{-n}\langle\alpha|\rho|\alpha\rangle\,d^2\alpha$ becomes $(2\pi)^{-n}$ in the quadrature coordinates $\beta$, because $d^2\alpha_j=d\beta_{q,j}\,d\beta_{p,j}/2$. For the vacuum it is the density of $\mathcal N(0,I)$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 5

import Mathlib
import Definitions.Def_BosonicLearn_coherentVector

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace BosonicLearn

/-- **Husimi density of a state in heterodyne coordinates.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5 ("heterodyne measurement, whose outcome distribution on an n-mode Gaussian state ρ(µ, Σ)
is a 2n-variate classical Gaussian N(µ, Σ + ½I)").

For a coefficient array `ρ` and `β ∈ ℝ²ⁿ`,
$$Q_ρ(β) = (2π)^{-n}\, \mathrm{Re} \sum_u \sum_v \overline{c(β)_u}\, ρ_{uv}\, c(β)_v = (2π)^{-n} ⟨α(β)|ρ|α(β)⟩ ,$$
the density of the heterodyne outcome with respect to Lebesgue measure `dβ` on `ℝ²ⁿ`.

**Formalization Note.** The usual normalization `π^{-n} ⟨α|ρ|α⟩ d²α` becomes `(2π)^{-n}` in `β`, since
`d²α_j = dβ_{q,j} dβ_{p,j}/2`. For a density the double series converges absolutely (`|ρ_uv| ≤ 1`,
`c(β) ∈ ℓ¹`). -/
noncomputable def husimiQ {n : ℕ} (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (β : Fin n ⊕ Fin n → ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(n : ℝ)) *
    (∑' u, ∑' v, star (coherentVector β u) * ρ u v * coherentVector β v).re

end BosonicLearn


