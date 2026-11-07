-- Prove2me | Definitions.Def_PsdPermanent_Phi__d25d42
-- name    : PsdPermanent_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:32.423149+00:00
-- url     : https://prove2.me/theorems/d25d4286-b8e3-43c4-a203-76673dcca309
-- title:
--   The value $\Phi(V)$ of the relaxation, Eq. (4)
-- statement:
--   The value of the relaxation is
--   $$\Phi(V)=\max\{\phi_V(X)\mid X\in\mathbb H_d^{++}\},$$
--   the maximum over Hermitian positive definite $d\times d$ matrices.
--
--   **Formalization Note** Lean takes a real supremum. It is the paper's maximum by Lemma 5 for a full column rank $V$ with nonzero rows.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Eq. (4), p.5

import Mathlib
import Definitions.Def_PsdPermanent_phi
open Matrix
open scoped ComplexOrder

namespace PsdPermanent

/-- **The value Φ(V) of the relaxation, Eq. (4).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Eq. (4), p.5: Φ(V) = max{ϕ_V(X) | X ∈ H_d^{++}}.

**Formalization Note.** A real `sSup` over the positive definite matrices (`Matrix.PosDef` over `ℂ`
includes Hermitian). It is the paper's `max` by Lemma 5 (`PsdPermanent.lemma_5`), which proves
`IsGreatest` for a full column rank factor with nonzero rows; every statement about `Phi` that the
paper makes is under those hypotheses or guarded by `Phat`. -/
noncomputable def Phi {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℂ) : ℝ :=
  sSup (phi V '' {X : Matrix (Fin d) (Fin d) ℂ | X.PosDef})

end PsdPermanent


