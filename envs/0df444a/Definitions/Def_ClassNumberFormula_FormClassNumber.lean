-- Prove2me | Definitions.Def_ClassNumberFormula_FormClassNumber
-- name    : ClassNumberFormula_FormClassNumber
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T12:52:12.222107+00:00
-- url     : https://prove2.me/theorems/7a59a4d8-a55f-44ce-a989-44cc3823597d
-- title:
--   Form class number $h(d)$, the automorph count $w$ and the Pell unit $\varepsilon$
-- statement:
--   This file defines the quantities $h(d)$, $w$ and $\varepsilon$ in Dirichlet's class number formula.
--
--   1. **Binary quadratic forms.** A form $f = (a,b,c)$ with $a,b,c\in\mathbb Z$ is the polynomial $f(x,y) = ax^2 + bxy + cy^2$; its discriminant is $b^2 - 4ac$. For $\gamma = \begin{pmatrix} p & q \\ r & s\end{pmatrix} \in \mathrm{SL}_2(\mathbb Z)$ the form $f\circ\gamma$ is $(x,y)\mapsto f(px+qy,\,rx+sy)$. Two forms are *(properly) equivalent* if one is obtained from the other by some $\gamma \in \mathrm{SL}_2(\mathbb Z)$.
--
--   2. **Form class number.** For an integer $d$, $h(d)$ is the number of equivalence classes of forms of discriminant $d$; when $d<0$ only positive definite forms ($a > 0$) are counted.
--
--   3. **Automorph count.** For $d<0$,
--   $$w = \begin{cases} 2, & d < -4,\\ 4, & d = -4,\\ 6, & d = -3.\end{cases}$$
--
--   4. **Pell unit.** For $d > 0$, let $t>0$, $u>0$ be the solution of $t^2 - du^2 = 4$ with $u$ as small as possible, and put
--   $$\varepsilon = \tfrac12\left(t + u\sqrt d\right).$$
--
--   These are the quantities on the left- and right-hand sides of Dirichlet's formula $h(d) = \frac{w\sqrt{|d|}}{2\pi}L(1,\chi)$ for $d<0$, and its real-quadratic analogue.
--
--   **Formalization Note** $h(d)$ is `Nat.card` of the quotient of the set of forms of discriminant $d$ (positive definite when $d<0$) by $\mathrm{SL}_2(\mathbb Z)$-equivalence; Lean's `Nat.card` would be $0$ if this set of classes were infinite, which does not happen for $d$ a non-square discriminant. $u$ is an `sInf` over the solution set and $t$ is the matching positive solution, so if no solution existed the values would be junk ($u = 0$); solvability is a separate milestone. For a fundamental discriminant every form of discriminant $d$ is primitive, so no primitivity condition is imposed.
-- source:
--   Wikipedia, "Class number formula" (revision oldid=1366411311), https://en.wikipedia.org/w/index.php?title=Class_number_formula&oldid=1366411311, section "Dirichlet class number formula" (definitions of $h(d)$, $w$, $\varepsilon$); H. Davenport, Multiplicative Number Theory, 3rd ed., GTM 74, Springer 2000, Ch. 6 (pp. 43–53)

import Mathlib

namespace ClassNumberFormula

/-- The integral binary quadratic form `a x² + b x y + c y²`. -/
@[ext] structure BinaryQuadForm where
  a : ℤ
  b : ℤ
  c : ℤ

namespace BinaryQuadForm

/-- The discriminant `b² - 4ac`. -/
def disc (f : BinaryQuadForm) : ℤ := f.b ^ 2 - 4 * f.a * f.c

/-- The value `f(x, y) = a x² + b x y + c y²`. -/
def eval (f : BinaryQuadForm) (x y : ℤ) : ℤ := f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2

/-- The form `(x, y) ↦ f(p x + q y, r x + s y)` obtained from `f` by the substitution
`γ = !![p, q; r, s] ∈ SL₂(ℤ)`. -/
def comp (f : BinaryQuadForm) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : BinaryQuadForm :=
  let p := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  let q := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  let r := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  let s := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  ⟨f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2,
   2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s,
   f.a * q ^ 2 + f.b * q * s + f.c * s ^ 2⟩

/-- Two forms are (properly) equivalent if one is carried to the other by a substitution
of determinant `1`. -/
def ProperlyEquivalent (f g : BinaryQuadForm) : Prop :=
  ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, f.comp γ = g

end BinaryQuadForm

/-- The forms counted by `h(d)`: forms of discriminant `d`, positive definite (`a > 0`)
when `d < 0`. -/
def FormsOfDisc (d : ℤ) : Type :=
  {f : BinaryQuadForm // f.disc = d ∧ (d < 0 → 0 < f.a)}

/-- `h(d)`: the number of proper equivalence classes of forms of discriminant `d`
(positive definite ones when `d < 0`). -/
noncomputable def formClassNumber (d : ℤ) : ℕ :=
  Nat.card (Quot (fun f g : FormsOfDisc d => BinaryQuadForm.ProperlyEquivalent f.1 g.1))

/-- `w = w(d)` for `d < 0`: `2` if `d < -4`, `4` if `d = -4`, `6` if `d = -3`. -/
def formAutomorphCount (d : ℤ) : ℕ :=
  if d = -4 then 4 else if d = -3 then 6 else 2

/-- `u > 0` smallest such that `t² - d u² = 4` for some `t > 0`. -/
noncomputable def pellU (d : ℤ) : ℕ :=
  sInf {u : ℕ | 0 < u ∧ ∃ t : ℕ, 0 < t ∧ (t : ℤ) ^ 2 - d * (u : ℤ) ^ 2 = 4}

/-- The `t > 0` paired with `pellU d`. -/
noncomputable def pellT (d : ℤ) : ℕ :=
  sInf {t : ℕ | 0 < t ∧ (t : ℤ) ^ 2 - d * (pellU d : ℤ) ^ 2 = 4}

/-- `ε = (t + u √d) / 2` for the solution of `t² - d u² = 4` with `t, u > 0` and `u` least. -/
noncomputable def pellEpsilon (d : ℤ) : ℝ :=
  ((pellT d : ℝ) + (pellU d : ℝ) * Real.sqrt d) / 2

end ClassNumberFormula


