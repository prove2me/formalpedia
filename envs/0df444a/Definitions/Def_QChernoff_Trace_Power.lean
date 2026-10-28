-- Prove2me | Definitions.Def_QChernoff_Trace_Power
-- name    : QChernoff_Trace_Power
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:25:36.861019+00:00
-- url     : https://prove2.me/theorems/10746ca8-eda8-4b4f-bd56-29e63a600b09
-- title:
--   Support projection $\Pi_A$ and the power $A^s$ with $A^0 = \Pi_A$ (pp. 2–4)
-- statement:
--   Let $H$ be a complex Hilbert space and $A$ a bounded operator on $H$.
--
--   1. The **support projection** $\Pi_A$ is the orthogonal projection of $H$ onto the closure $\overline{\operatorname{ran} A}$ of the range of $A$. For $A=(C-B)_+$ it is the "projector on the range of $(C-B)_+$" of Lemma 1 and eq. (10); in finite dimension the range is closed and no closure is needed.
--   2. For a positive operator $A\ge 0$ and a real exponent $s$, the **power** is
--
--   $$A^{s}:=\begin{cases}\Pi_A, & s=0,\\ f_s(A), & s\neq 0,\end{cases}\qquad f_s(x)=x^{s},$$
--
--   where $f_s(A)$ is the continuous functional calculus. Thus $A^0$ is the projection onto the support of $A$, not the identity.
--
--   These are the objects in which Theorem 1 ($\operatorname{Tr}[A^sB^{1-s}]\ge\operatorname{Tr}[A+B-|A-B|]/2$) and Lemma 1 are stated. With $A^0=\Pi_A$ the endpoint cases $s=0$ and $s=1$ of Theorem 1 read $\operatorname{Tr}[\Pi_AB]\ge\cdots$ and $\operatorname{Tr}[A\Pi_B]\ge\cdots$, which is the convention the paper uses on p. 4 (for a pure state $\rho_1=|\psi\rangle\langle\psi|$ the value at $s=0$ is $\langle\psi|\rho_2|\psi\rangle$).
--
--   **Formalization Note** `supportProj A` is `Submodule.starProjection` of the topological closure of the range of `A`; `qPow A s` is `if s = 0 then supportProj A else A ^ s`, where `A ^ s` is Mathlib's `CFC.rpow`, i.e. `cfc (fun x : ℝ => x ^ s) A`. On a non-self-adjoint `A` the functional calculus returns the junk value `0`; every theorem of the mission assumes `0 ≤ A` and only uses $0\le s\le 1$. The file also records the structural fact that `supportProj A` is a self-adjoint idempotent.
-- source:
--   Audenaert et al., The Quantum Chernoff Bound, arXiv:quant-ph/0610027v1, pp. 2–4 (Problem formulation; Theorem 1; Lemma 1; p. 4 remark on pure states)

import Mathlib

namespace QChernoff.Trace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Audenaert et al., arXiv:quant-ph/0610027v1, pp. 2–5: the support projection `Π_A` of a
bounded operator `A`, i.e. the orthogonal projection onto the closure of the range of `A`.
For `A = (C - B)⁺` this is "the projector on the range of `(C − B)₊`" of Lemma 1 and eq. (10);
in finite dimension the range is already closed. -/
noncomputable def supportProj (A : H →L[ℂ] H) : H →L[ℂ] H :=
  (LinearMap.range A.toLinearMap).topologicalClosure.starProjection

/-- The support projection is an orthogonal (self-adjoint, idempotent) projection. -/
theorem isStarProjection_supportProj (A : H →L[ℂ] H) : IsStarProjection (supportProj A) :=
  isStarProjection_starProjection

/-- Audenaert et al., arXiv:quant-ph/0610027v1, pp. 2–4: the power `A^s` of a positive operator
`A` used in Theorem 1 and Lemma 1. For `s ≠ 0` it is the continuous functional calculus power
`A ^ s` (`CFC.rpow`, i.e. `cfc (fun x : ℝ => x ^ s) A`); for `s = 0` it is the support
projection `Π_A` (the paper's convention for the zeroth power of a possibly singular positive
operator, p. 4), not Mathlib's `A ^ (0 : ℝ) = 1`. Only used for `0 ≤ A` and `0 ≤ s ≤ 1`. -/
noncomputable def qPow (A : H →L[ℂ] H) (s : ℝ) : H →L[ℂ] H :=
  if s = 0 then supportProj A else A ^ s

end QChernoff.Trace


