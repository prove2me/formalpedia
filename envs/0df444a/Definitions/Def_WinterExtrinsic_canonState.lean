-- Prove2me | Definitions.Def_WinterExtrinsic_canonState
-- name    : WinterExtrinsic_canonState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:18:24.647542+00:00
-- url     : https://prove2.me/theorems/f19b330c-5b0f-4250-b15a-2babb0bbf0ae
-- title:
--   Canonical ensemble states $\hat\rho_j = \sqrt\rho\, a_j \sqrt\rho / \lambda_j$
-- statement:
--   Let $\rho$ be a state on $\mathbb C^d$ and $a = (a_1, \dots, a_m)$ a POVM, with canonical weights $\lambda_j = \mathrm{Tr}(\rho a_j)$. The **states of the canonical ensemble** are
--
--   $$\hat\rho_j = \frac{1}{\lambda_j}\, \sqrt{\rho}\, a_j \sqrt{\rho}, \qquad j = 1, \dots, m ,$$
--
--   where $\sqrt\rho$ is the positive square root of $\rho$. The ensemble $\{\hat\rho_j, \lambda_j\}$ has average $\sum_j \lambda_j \hat\rho_j = \rho$; it is the ensemble of post-measurement "retrodicted" states whose Holevo quantity gives the intrinsic data rate of $a$ on $\rho$.
--
--   **Formalization Note** $\sqrt\rho$ is `cfc Real.sqrt ρ`. When $\lambda_j = 0$ the paper leaves $\hat\rho_j$ undefined; Lean's convention $0^{-1} = 0$ gives $\hat\rho_j = 0$. Every use of $\hat\rho_j$ in this mission carries the weight $\lambda_j$, so this value never matters.
-- source:
--   Winter, "Extrinsic" and "intrinsic" data in quantum measurements, arXiv:quant-ph/0109050v3, Theorem 6, p.6 (canonical ensemble, "ˆρj = 1/Tr (ρaj) √ρ aj √ρ"), the ensemble of Theorem 2, p.3; cf. p.4 ("aj = ρ−1/2λjρjρ−1/2")

import Mathlib
import Definitions.Def_WinterExtrinsic_canonWeight

namespace WinterExtrinsic

/-- The states `ρ̂_j = (1/Tr(ρ a_j)) √ρ a_j √ρ` of the canonical ensemble of a state `ρ` and a
POVM `a`.

Winter, *"Extrinsic" and "intrinsic" data in quantum measurements*, arXiv:quant-ph/0109050v3,
Theorem 6, p.6 ("define a canonical ensemble {ρ̂_j, λ_j}, with states ρ̂_j = 1/Tr(ρa_j) √ρ a_j √ρ"),
the ensemble used in Theorem 2, p.3, and on p.4 ("a_j = ρ^{−1/2} λ_j ρ̂_j ρ^{−1/2}").

**Formalization Note.** `√ρ` is `cfc Real.sqrt ρ`, the positive square root on positive
semidefinite matrices. When `λ_j = Tr(ρ a_j) = 0` the paper leaves `ρ̂_j` undefined; Lean's
`0⁻¹ = 0` gives `ρ̂_j = 0`. Every use of `ρ̂_j` in this mission is weighted by `λ_j`, so the
value at `λ_j = 0` never matters. -/
noncomputable def canonState {d m : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (a : Fin m → Matrix (Fin d) (Fin d) ℂ) (j : Fin m) : Matrix (Fin d) (Fin d) ℂ :=
  ((canonWeight ρ a j)⁻¹ : ℂ) • (cfc Real.sqrt ρ * a j * cfc Real.sqrt ρ)

end WinterExtrinsic


