-- Prove2me | Definitions.Def_ParamSDPTraj_opA
-- name    : ParamSDPTraj_opA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:32.75593+00:00
-- url     : https://prove2.me/theorems/9c875711-0c16-4319-b7ab-a7962ccc9985
-- title:
--   The linear operator $\mathcal A(t)$
-- statement:
--   Let $A_1(t),\dots,A_m(t)$ be real $n\times n$ matrices depending on a time parameter $t$. The **linear operator** $\mathcal A(t)$ maps a matrix $X$ to the vector
--
--   $$\mathcal A(t)[X]=\big(\langle A_1(t),X\rangle,\dots,\langle A_m(t),X\rangle\big)\in\mathbb R^m.$$
--
--   It carries the equality constraints of the primal problem $(P_t)$.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, §2.1, p.5, and (Pt), p.7

import Mathlib
import Definitions.Def_ParamSDPTraj_pair

namespace ParamSDPTraj

/-- **The linear operator 𝒜(t).**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, §2.1, p.5: "The linear operator A maps X ∈ Sn to (⟨A1, X⟩, . . . , ⟨Am, X⟩) ∈ Rm", with
the parameter t of (Pt), p.7.

**Formalization Note** `A i t` is the matrix A_i(t). -/
noncomputable def opA {n m : ℕ} (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Fin m → ℝ :=
  fun i => pair (A i t) X

end ParamSDPTraj


