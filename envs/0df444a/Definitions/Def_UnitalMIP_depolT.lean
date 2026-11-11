-- Prove2me | Definitions.Def_UnitalMIP_depolT
-- name    : UnitalMIP_depolT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:38:26.805106+00:00
-- url     : https://prove2.me/theorems/5cc282e6-b9e9-4f14-85ec-baf8563053d6
-- title:
--   The depolarizing semigroup $\mathcal T_u=D_u^{\otimes n}$
-- statement:
--   Let $\Pi(X)=\tau_2(X)\mathbb 1$ on $M_2$. For $u\ge 0$ the one-qubit **depolarizing map** and its $n$-qubit tensor power are
--
--   $$
--   D_u=\Pi+e^{-u}(\mathrm{id}_{M_2}-\Pi),\qquad \mathcal T_u=D_u^{\otimes n}.
--   $$
--
--   It acts on Pauli strings by $\mathcal T_u(P_\alpha)=e^{-u|\alpha|}P_\alpha$ and is used to smooth the provers' measurements.
--
--   **Formalization Note** The tensor power of superoperators is the published `QAlgorithms.piSuperop` (matrix-unit expansion, so it is the genuine $D_u^{\otimes n}$ on every operator).
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Definition 2.9, p.13

import Mathlib
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals

open scoped Matrix

namespace UnitalMIP

/-- The one-qubit **depolarizing map** `D_u := Π + e^{−u}(id − Π)`, `Π(X) := τ₂(X)𝟙`
(arXiv:2609.39318, version of 2026-11-03, sha256 56ebc59e…, Definition 2.9, p.13). -/
noncomputable def depol1 (u : ℝ) : QAlgorithms.Superop (Fin 2) (Fin 2) :=
  fun X => ntr X • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    (Real.exp (-u) : ℂ) • (X - ntr X • (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- The `n`-qubit **depolarizing semigroup** `T_u := D_u^{⊗n}` (arXiv:2609.39318, version of
2026-11-03, Definition 2.9, p.13).

**Formalization Note** The tensor product of superoperators is the published
`QAlgorithms.piSuperop`, defined on every operator through the matrix-unit expansion. By
Proposition 2.10 (p.13) it acts on Pauli strings by `T_u(P_α) = e^{−u|α|} P_α`. -/
noncomputable def depolT (u : ℝ) (n : ℕ) : QAlgorithms.Superop (Fin n → Fin 2) (Fin n → Fin 2) :=
  QAlgorithms.piSuperop fun _ : Fin n => depol1 u

end UnitalMIP


