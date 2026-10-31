-- Prove2me | Definitions.Def_MaskedLinx_linxObjective
-- name    : MaskedLinx_linxObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:05.164279+00:00
-- url     : https://prove2.me/theorems/0072a873-ffee-4af8-9375-beab28f12134
-- title:
--   Scaled linx objective $f(C,s;\gamma;x)=\tfrac12\big(\mathrm{ldet}(\gamma C\,\mathrm{Diag}(x)C+\mathrm{Diag}(e-x))-s\log\gamma\big)$
-- statement:
--   Let $C$ be a real square matrix indexed by a finite set $N$, $s$ a natural number, $\gamma>0$ a scaling parameter and $x\in\mathbb R^N$. The scaled linx objective is
--
--   $$f(C,s;\gamma;x)=\tfrac12\Big(\mathrm{ldet}\big(\gamma\,C\,\mathrm{Diag}(x)\,C+\mathrm{Diag}(e-x)\big)-s\log\gamma\Big),$$
--
--   where $\mathrm{ldet}$ is the natural logarithm of the determinant, taken to be $-\infty$ when the matrix is not positive definite. The value is an extended real number.
--
--   With $\gamma=1$ this is Anstreicher's linx objective $f(C,s;x)=\tfrac12\,\mathrm{ldet}(C\,\mathrm{Diag}(x)\,C+\mathrm{Diag}(e-x))$ of (1). Applied to the Hadamard product $C\circ M$ with a mask $M$ it is the scaled and masked objective $f(C,s;M,\gamma;x)$ of (3).
--
--   **Formalization Note** The objective takes values in `EReal`. It equals $\tfrac12(\log\det A-s\log\gamma)$ when $A$ is positive definite and $\bot=-\infty$ otherwise, so Lean's convention $\log 0=0$ never applies to a singular matrix. For positive semidefinite $C$, $\gamma>0$ and $0\le x\le e$ the matrix is positive semidefinite, so "positive definite" coincides with "$\det A>0$".
-- source:
--   Chen, Fampa, Lee, Masking Anstreicher's linx bound for improved entropy bounds, arXiv:2106.02980v1, §1, definition of f(C,s;γ;x) after display (2), p.2; f(C,s;x) after display (1), p.2; f(C,s;M,γ;x) after display (3), p.3

import Mathlib
import Definitions.Def_MaskedLinx_linxMatrix

namespace MaskedLinx

open scoped Classical in
/-- **The scaled linx objective `f(C,s;γ;x) = ½ (ldet(γ C Diag(x) C + Diag(e − x)) − s log γ)`.**
Chen, Fampa, Lee, *Masking Anstreicher's linx bound for improved entropy bounds*,
arXiv:2106.02980v1, §1, text after display (2), p.2. With `γ = 1` it is the unscaled objective
`f(C,s;x) = ½ ldet(C Diag(x) C + Diag(e − x))` of (1); applied to `C ∘ M` it is the scaled and
masked objective `f(C,s;M,γ;x)` of (3), p.3.

The value is the extended real `½ (log det A − s log γ)` when `A = linxMatrix C γ x` is positive
definite, and `⊥ = −∞` otherwise.

**Formalization Note.** `ldet` is the natural logarithm of the determinant with the convention
`ldet A = −∞` when `A` is not positive definite (Lean's `Real.log 0 = 0` is never used on a
singular matrix). For a positive-semidefinite `C` and `0 ≤ x ≤ e` the matrix `A` is positive
semidefinite, so "positive definite" is the same as "`det A > 0`", i.e. the paper's ldet. The
value lives in `EReal`; `s` is a natural number. The test "is positive definite" is decided
classically. -/
noncomputable def linxObjective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (s : ℕ) (γ : ℝ) (x : ι → ℝ) : EReal :=
  if (linxMatrix C γ x).PosDef then
    (((1 / 2 : ℝ) * (Real.log (linxMatrix C γ x).det - (s : ℝ) * Real.log γ) : ℝ) : EReal)
  else ⊥

end MaskedLinx


