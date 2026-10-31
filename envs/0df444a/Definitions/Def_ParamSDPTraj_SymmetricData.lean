-- Prove2me | Definitions.Def_ParamSDPTraj_SymmetricData
-- name    : ParamSDPTraj_SymmetricData
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:42.061565+00:00
-- url     : https://prove2.me/theorems/dfd8c1a0-faa1-4f55-816a-fbc0f35ff326
-- title:
--   The data are symmetric matrices
-- statement:
--   The data of $(P_t)$ and $(D_t)$ are symmetric: $A_i(t)\in\mathbb S^n$ for every $i$, and $C(t)\in\mathbb S^n$, for every $t\in T$.
--
--   **Formalization Note** The data are functions on all of $\mathbb R$. Only their values on $T$ are constrained.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, (Pt), (Dt), p.7, and §2.1, p.5

import Mathlib

namespace ParamSDPTraj

/-- **The data are symmetric matrices.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, (Pt), (Dt), p.7, and §2.1, p.5: "Ai ∈ Sn"; C(t) ∈ Sⁿ.

**Formalization Note** Data are functions on all of ℝ; only their values on T are constrained. -/
def SymmetricData {n m : ℕ} (T : Set ℝ) (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (C : ℝ → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ t ∈ T, (∀ i, (A i t).IsSymm) ∧ (C t).IsSymm

end ParamSDPTraj


