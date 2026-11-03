-- Prove2me | Definitions.Def_IsotropicSpin_timeReversal
-- name    : IsotropicSpin_timeReversal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:18.598975+00:00
-- url     : https://prove2.me/theorems/fb8c33ad-0260-4cac-8915-d02efebea5f1
-- title:
--   Time-reversal conjugation $\rho\mapsto T\rho T^\dagger$ on spin 1/2
-- statement:
--   Let $T$ be the antiunitary **time-reversal** map on $\mathbb C^2$ of eq. (12),
--
--   $$
--   T|{+}1/2\rangle=|{-}1/2\rangle,\qquad T|{-}1/2\rangle=-|{+}1/2\rangle .
--   $$
--
--   This definition is the map $\rho\mapsto T\rho T^\dagger$ on $2\times2$ matrices. In the basis $(|{+}1/2\rangle,|{-}1/2\rangle)$, $T=JK$ with $K$ entrywise complex conjugation and $J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$, so $T\rho T^\dagger=J\,\bar\rho\,J^\dagger$. It appears in the closed form (11) of $\Lambda_{1/2}$.
--
--   **Formalization Note** $\bar\rho$ is the entrywise complex conjugate `ρ.map (starRingEnd ℂ)`. The map is conjugate-linear, as conjugation by an antiunitary must be.
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, eqs. (11)–(12), p.2

import Mathlib

open scoped Matrix

namespace IsotropicSpin

/-- **Conjugation by the time-reversal map** `ρ ↦ T ρ T†`, Alicki, arXiv:quant-ph/0402080v1,
eqs. (11)–(12), p. 2, where `T` is the antiunitary map on `ℂ²` with `T|+1/2⟩ = |−1/2⟩` and
`T|−1/2⟩ = −|+1/2⟩`.

**Formalization Note** In the basis `(|+1/2⟩, |−1/2⟩)` (index `0` is `|+1/2⟩`) the antiunitary `T`
is `J ∘ K`, with `K` entrywise complex conjugation and `J = !![0, -1; 1, 0]` the unitary with
`J|+1/2⟩ = |−1/2⟩`, `J|−1/2⟩ = −|+1/2⟩`. Hence `T ρ T† = J ρ̄ J†`, where `ρ̄` is the entrywise
complex conjugate (`ρ.map (starRingEnd ℂ)`). -/
def timeReversal (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -1; 1, 0] * ρ.map (starRingEnd ℂ) * (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ

end IsotropicSpin


