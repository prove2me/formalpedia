-- Prove2me | Definitions.Def_TolProdTest_highProj
-- name    : TolProdTest_highProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:25:32.657868+00:00
-- url     : https://prove2.me/theorems/08cd60eb-e801-40d4-b9cc-3ada72fcf653
-- title:
--   Spectral projector $\mathbf 1_{(1/R,1]}(A)$
-- statement:
--   For a Hermitian operator $A=\sum_j\lambda_j|v_j\rangle\langle v_j|$, the spectral projector onto the eigenvalues in $(1/R,1]$ is
--
--   $$
--   \mathbf 1_{(1/R,1]}(A)=\sum_{j:\ 1/R<\lambda_j\le1}|v_j\rangle\langle v_j| .
--   $$
--
--   Applied to a block marginal $\rho_c$ it is the projector $\Pi^{\mathrm{hi}}_c$ onto the eigenspaces of $\rho_c$ with eigenvalues larger than $1/R$, which has rank less than $R$.
--
--   **Formalization Note** Mathlib's continuous functional calculus of the indicator of $(1/R,1]$; the interval is open at $1/R$ as printed. For a non-Hermitian argument the value is $0$, but every use applies it to a marginal of a density operator.
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (19), p.8; Lemma 3.6, p.14

import Mathlib

set_option autoImplicit false

open scoped MatrixOrder ComplexOrder

namespace TolProdTest

/-- **The spectral projector `1_{(1/R,1]}(A)`**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (19), p.8 ("For a Hermitian operator
A = Σ_j λ_j |v_j⟩⟨v_j| and an interval J ⊆ R, its spectral projector onto J is 1_J(A) := Σ_{j:λ_j∈J} |v_j⟩⟨v_j|"),
with `J = (1/R, 1]` as in Lemma 3.6, p.14 ("the projector to the eigenspaces of ρ_c with eigenvalues larger
than 1/R").

It is the continuous functional calculus of the indicator of `(1/R, 1]` applied to `A`; for a Hermitian `A`
this is `Σ_{λ_j ∈ (1/R,1]} |v_j⟩⟨v_j|` for any orthonormal eigenbasis.

**Formalization Note** The interval is open at `1/R` and closed at `1`, as printed. `cfc` of a function on the
finite spectrum is always defined; for a non-Hermitian argument it returns `0`, but every use applies it to a
block marginal of a density operator, which is Hermitian with spectrum in `[0,1]`. -/
noncomputable def highProj {X : Type} [Fintype X] [DecidableEq X] (A : Matrix X X ℂ) (R : ℕ) :
    Matrix X X ℂ :=
  cfc (fun x : ℝ => if 1 / (R : ℝ) < x ∧ x ≤ 1 then (1 : ℝ) else 0) A

end TolProdTest


