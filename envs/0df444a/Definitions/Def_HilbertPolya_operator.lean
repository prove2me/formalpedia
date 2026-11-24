-- Prove2me | Definitions.Def_HilbertPolya_operator
-- name    : HilbertPolya_operator
-- status  : Definition
-- author  : @LG
-- created : 2026-11-24T02:26:31.885791+00:00
-- url     : https://prove2.me/theorems/812e4866-2fa9-44d2-a9a8-342248441c6b
-- title:
--   Self-adjoint operators and the Hilbert–Pólya spectral correspondence
-- statement:
--   This file provides the operator-theoretic vocabulary for the Hilbert–Pólya conjecture.
--
--   Fix a real inner product space $H$. A (possibly unbounded) operator is given by a linear subspace $D\subseteq H$ (the domain) together with a map $T:H\to H$ whose values are meaningful on $D$. The predicate `IsSelfAdjointOperator T D` asserts four things: $D$ is **dense** in $H$; $T$ is **real-linear on $D$**, $T(ax+by)=a\,Tx+b\,Ty$ for $a,b\in\mathbb R$ and $x,y\in D$; $T$ is **symmetric on $D$**, $\langle Tx,y\rangle=\langle x,Ty\rangle$ for $x,y\in D$; and the **adjoint domain is contained in $D$**: whenever $y\in H$ admits some $z\in H$ with $\langle Tx,y\rangle=\langle x,z\rangle$ for all $x\in D$, then $y\in D$. With density, symmetry gives $D\subseteq\operatorname{dom}(T^*)$ and $T^*=T$ on $D$, so the last condition says $\operatorname{dom}(T^*)\subseteq D$; together they express $T=T^*$, i.e. self-adjointness.
--
--   `IsEigenvalue T D γ` means there is a nonzero $v\in D$ with $Tv=\gamma v$. The structure `Operator` bundles a real Hilbert space $H$ (a complete real inner product space), a domain $D$, a map $T$, and a proof that $T$ is self-adjoint. Finally `Operator.matchesZetaZeros op` asserts that for every complex $s$, $s$ is a nontrivial zero of the Riemann zeta function (i.e. $\zeta(s)=0$ with $0<\Re(s)<1$) **if and only if** $s=\tfrac12+i\gamma$ for some eigenvalue $\gamma$ of $op$.
--
--   **Formalization Note.** The operator is allowed to be unbounded (its domain is a dense submodule, not necessarily all of $H$); this is essential because the imaginary parts of the zeta zeros are unbounded. The space is real; this is equivalent to the complex formulation by restriction/complexification of scalars. Values of $T$ outside $D$ are irrelevant junk values.
-- source:
--   Hilbert–Pólya conjecture: https://en.wikipedia.org/wiki/Hilbert%E2%80%93P%C3%B3lya_conjecture ; https://mathworld.wolfram.com/Hilbert-PolyaConjecture.html . Self-adjoint (unbounded) operator standard definition, e.g. Reed–Simon, Methods of Modern Mathematical Physics I, §VIII.2.

import Mathlib

namespace HilbertPolya

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A densely defined real-linear operator `T` with domain `D` is self-adjoint when it is
symmetric on `D` and every vector admitting an adjoint representative already lies in `D`.
Together with density this expresses `T = T*`. -/
structure IsSelfAdjointOperator (T : H → H) (D : Submodule ℝ H) : Prop where
  dense : Dense (D : Set H)
  linear : ∀ (a b : ℝ) (x y : H), x ∈ D → y ∈ D → T (a • x + b • y) = a • T x + b • T y
  symmetric : ∀ x y : H, x ∈ D → y ∈ D → inner ℝ (T x) y = inner ℝ x (T y)
  adjoint_dom : ∀ y : H, (∃ z : H, ∀ x : H, x ∈ D → inner ℝ (T x) y = inner ℝ x z) → y ∈ D

/-- `γ` is an eigenvalue of `T` (with domain `D`) when some nonzero `v ∈ D` satisfies `T v = γ • v`. -/
def IsEigenvalue (T : H → H) (D : Submodule ℝ H) (γ : ℝ) : Prop :=
  ∃ v : H, v ∈ D ∧ v ≠ 0 ∧ T v = γ • v

/-- A self-adjoint operator on a real Hilbert space, bundled with its space and dense domain. -/
structure Operator where
  H : Type
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℝ H]
  [complete : CompleteSpace H]
  D : Submodule ℝ H
  T : H → H
  selfAdjoint : IsSelfAdjointOperator T D

/-- The eigenvalues of `op` are exactly the imaginary parts of the nontrivial zeros of `ζ`,
via the correspondence `s = 1/2 + i γ`. -/
def Operator.matchesZetaZeros (op : Operator) : Prop :=
  ∀ s : ℂ, (riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1) ↔
    ∃ γ : ℝ, @IsEigenvalue op.H op.normed op.inner op.T op.D γ ∧
      s = (1 / 2 : ℂ) + (γ : ℂ) * Complex.I

end HilbertPolya


