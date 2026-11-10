-- Prove2me | Definitions.Def_KnownFidelity_Rank_avgPower
-- name    : KnownFidelity_Rank_avgPower
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:43.629199+00:00
-- url     : https://prove2.me/theorems/0ea4c98c-8e65-4704-93bf-36ec7294d8de
-- title:
--   The $t$-copy average state $\mathbb E_{\tau\sim\Lambda}\,g(\tau)^{\otimes t}$
-- statement:
--   For a measure $\Lambda$ on matrices, a map $g$ to matrices and $t\in\mathbb N$,
--
--   $$\mathbb E_{\tau\sim\Lambda}\ g(\tau)^{\otimes t},$$
--
--   the average over the prior of the $t$-fold tensor power. With $g=\mathrm{id}$ it is the $t$-copy average state $\mathbb E_\Lambda\tau^{\otimes t}$ of the prior; with $g(\tau)=\rho_{p,\tau}$ it is the average state of Lemma 4.2.
--
--   **Formalization Note** The matrix integral is taken entrywise. For a prior on states and a continuous $g$ with values in states, every integrand is measurable and bounded by $1$.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Lemma 2.1, p. 4 (PDF p. 6); Proposition 4.1, p. 8 (PDF p. 10); Lemma 4.2, p. 9 (PDF p. 11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_KnownFidelity_Rank_instMeasurableSpaceMatrix

open MeasureTheory

namespace KnownFidelity.Rank

/-- **The `t`-copy average state of a prior**, `E_{τ∼Λ} g(τ)^{⊗t}`.
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Lemma 2.1, printed p. 4 (PDF p. 6) ("the corresponding n-copy average states"),
Proposition 4.1, printed p. 8 (PDF p. 10) (`E_{Λ_b} τ^{⊗t}`) and Lemma 4.2, printed p. 9
(PDF p. 11) (`E_{Λ_b} ρ_{p,τ}^{⊗n}`).

For a measure `Λ` on `κ × κ` matrices, a map `g` from those matrices to `ι × ι` matrices and
`t : ℕ`, `avgPower Λ g t` is the matrix on `Fin t → ι` with entries
`∫ (g τ)^{⊗t}_{x y} dΛ(τ)`. With `g = id` it is the prior's average `E_Λ τ^{⊗t}`.

**Formalization Note.** The integral is taken entrywise (complex Bochner integrals), which is the
matrix-valued integral without choosing a matrix norm. On a prior carried by states and a
continuous `g` with values in states, each integrand is measurable and bounded by `1`, so no
integral takes its junk value. -/
noncomputable def avgPower {κ ι : Type*} (Λ : Measure (Matrix κ κ ℂ))
    (g : Matrix κ κ ℂ → Matrix ι ι ℂ) (t : ℕ) : Matrix (Fin t → ι) (Fin t → ι) ℂ :=
  Matrix.of fun x y => ∫ τ, QAlgorithms.piKron t (g τ) x y ∂Λ

end KnownFidelity.Rank


