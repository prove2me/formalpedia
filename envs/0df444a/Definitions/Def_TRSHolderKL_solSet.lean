-- Prove2me | Definitions.Def_TRSHolderKL_solSet
-- name    : TRSHolderKL_solSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:53.394994+00:00
-- url     : https://prove2.me/theorems/de209668-2404-4e14-b7f3-7345385f19d0
-- title:
--   Solution set of a (sub)system of inequalities
-- statement:
--   For a system $q_i(x)\le0$, $i\in[m]$, and a set $T\subseteq[m]$ of indices, the solution set of the subsystem indexed by $T$ is
--   $$
--   \{x\in\mathbb R^n:\ q_i(x)\le0\ \text{for all } i\in T\}.
--   $$
--   With $T=[m]$ it is the solution set $S$ of the whole system.
--
--   **Formalization Note** $[m]$ is `Fin m`; subsystems are finite sets of indices.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Definition 3.1, p.4

import Mathlib
import Definitions.Def_RBMSensitivity_E
open RBMSensitivity (E)

namespace TRSHolderKL

/-- The solution set `{x | qᵢ(x) ≤ 0 ∀ i ∈ T}` of the subsystem indexed by `T` of a system
`qᵢ(x) ≤ 0, i ∈ [m]`, Jiang and Li, arXiv:1911.11955v2, Definition 3.1, p.4. -/
def solSet {n m : ℕ} (q : Fin m → E n → ℝ) (T : Finset (Fin m)) : Set (E n) :=
  {x | ∀ i ∈ T, q i x ≤ 0}

end TRSHolderKL


