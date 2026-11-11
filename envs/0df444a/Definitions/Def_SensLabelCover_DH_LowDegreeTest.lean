-- Prove2me | Definitions.Def_SensLabelCover_DH_LowDegreeTest
-- name    : SensLabelCover_DH_LowDegreeTest
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:34:39.780004+00:00
-- url     : https://prove2.me/theorems/3a5a918c-1e7a-4ab3-a869-9fe729320c50
-- title:
--   Affine lines of $F^m$, degree-$D$ line polynomials and the line–point test probability
-- statement:
--   Let $F$ be a finite field and $m\ge1$. An **affine line** of $F^m$ is a set $\ell=\{a+tv:t\in F\}$ with $a\in F^m$ and direction $v\neq0$; there are finitely many, and each has $|F|$ points. A function $B_\ell$ on $\ell$ is a **polynomial of degree at most $D$** if $B_\ell(a+tv)=p(t)$ for a univariate polynomial $p$ of degree at most $D$ in some (equivalently every) parametrization of $\ell$. It is the **restriction** $P|_\ell$ of a polynomial $P\in F[x_1,\dots,x_m]$ if $B_\ell(z)=P(z)$ for all $z\in\ell$. For $f:F^m\to F$, an assignment $\ell\mapsto B_\ell$ to the lines and a finite set $L$ of polynomials,
--   $$\Pr_{\ell,\,z\in\ell}\big[B_\ell(z)=f(z)\ \wedge\ B_\ell\notin\{P|_\ell : P\in L\}\big]$$
--   is taken with $\ell$ uniform among all lines and $z$ uniform on $\ell$.
--
--   This is the probability that the Arora–Sudan low-degree test controls.
--
--   **Formalization Note** Points are `Fin m → F`; a line is stored as the `Finset` of its points (`lineThrough a v`), and `lines F m` is the finite set of lines. The line assignment is `B : Finset (Fin m → F) → (Fin m → F) → F`, read only at points of its line. `lineTestFailProb f B L` is the average over lines of $1/|\ell|$ times the number of points satisfying the event.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 42 (PDF 45), §8 and Proposition 8.1

import Mathlib

open scoped BigOperators

namespace SensLabelCover.DH

/-! Fleming, Hopkins, Yoshida, *Sensitivity and Locality Lower Bounds via Low-Soundness Label
Cover*, STOC 2027 submission (manuscript sha256 5bfe95ad…), §8 (p. 42, PDF p. 45): affine lines
of `F^m`, polynomial functions of degree at most `D` on a line, and the line–point test
probability of Proposition 8.1 (Arora–Sudan low-degree test).

A point of `F^m` is `Fin m → F`; a line is stored as the finite set of its points. -/

noncomputable section

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-- The affine line `{a + t v : t ∈ F}` through `a` with direction `v`, as a set of points. -/
def lineThrough (a v : Fin m → F) : Finset (Fin m → F) :=
  Finset.univ.image (fun t : F => a + t • v)

/-- `ℓ` is an affine line of `F^m` (a one-dimensional affine subspace): `ℓ = {a + t v}` for some
point `a` and some direction `v ≠ 0`. -/
def IsLine (ℓ : Finset (Fin m → F)) : Prop :=
  ∃ a v : Fin m → F, v ≠ 0 ∧ ℓ = lineThrough a v

/-- The finite set of all affine lines of `F^m`. -/
def lines (F : Type) [Field F] [Fintype F] [DecidableEq F] (m : ℕ) : Finset (Finset (Fin m → F)) :=
  by classical exact Finset.univ.filter IsLine

/-- `B` restricted to the line `ℓ` is a polynomial function of degree at most `D`: in some affine
parametrization `t ↦ a + t v` of `ℓ`, `B(a + t v) = p(t)` for a univariate `p` with
`deg p ≤ D` (equivalently in every parametrization). -/
def IsLinePoly (D : ℕ) (ℓ : Finset (Fin m → F)) (B : (Fin m → F) → F) : Prop :=
  ∃ a v : Fin m → F, v ≠ 0 ∧ ℓ = lineThrough a v ∧
    ∃ p : Polynomial F, p.natDegree ≤ D ∧ ∀ t : F, B (a + t • v) = p.eval t

/-- `B` agrees on `ℓ` with the restriction `P|_ℓ` of the polynomial `P`. -/
def IsRestrictionOn (ℓ : Finset (Fin m → F)) (B : (Fin m → F) → F)
    (P : MvPolynomial (Fin m) F) : Prop :=
  ∀ z ∈ ℓ, B z = MvPolynomial.eval z P

/-- The probability in (19), for a uniformly random line `ℓ` and a uniformly random point `z ∈ ℓ`:
`Pr_{ℓ, z∈ℓ}[B_ℓ(z) = f(z) ∧ B_ℓ ∉ {P|_ℓ : P ∈ L}]`. The line assignment is
`B : (lines) → F^m → F`, read only at points of its line. -/
def lineTestFailProb (f : (Fin m → F) → F) (B : Finset (Fin m → F) → (Fin m → F) → F)
    (L : Finset (MvPolynomial (Fin m) F)) : ℝ :=
  by classical exact
    (1 / ((lines F m).card : ℝ)) * ∑ ℓ ∈ lines F m,
      (1 / (ℓ.card : ℝ)) *
        ((ℓ.filter (fun z => B ℓ z = f z ∧ ¬ ∃ P ∈ L, IsRestrictionOn ℓ (B ℓ) P)).card : ℝ)

end

end SensLabelCover.DH


