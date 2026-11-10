-- Prove2me | Definitions.Def_PRUMicrocrypt_sensitivity
-- name    : PRUMicrocrypt_sensitivity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:50.376702+00:00
-- url     : https://prove2.me/theorems/b580aef4-e20d-4279-ba90-fd8b6720d1a0
-- title:
--   $\delta$-sensitivity $S_\delta(f,x)$, average change $A_f$, low-degree polynomials and one-sided certificates on $\{0,1\}^m$
-- statement:
--   For $x\in\{0,1\}^m$ write $x^{\oplus i}$ for $x$ with bit $i$ flipped. For $f:\{0,1\}^m\to[0,1]$ and $0<\delta\le1$:
--
--   1. the **$\delta$-sensitivity** is $S_\delta(f,x)=\#\{i:|f(x)-f(x^{\oplus i})|\ge\delta\}$;
--   2. the **average change** is $A_f(x)=\frac1m\sum_{i=1}^m|f(x)-f(x^{\oplus i})|$;
--   3. $f$ is a **polynomial of degree at most $d$** if it agrees on $\{0,1\}^m$ with a real multivariate polynomial of total degree at most $d$;
--   4. a **one-sided certificate** at $y$ is a family of nonnegative weights $w(i)$ with $f(y)-f(x)\le\sum_{i:y_i\ne x_i}w(i)$ for every $x$; its mass is $\sum_i w(i)$.
--
--   The module also defines the uniform probability $\Pr_X[E(X)]$ and expectation $\mathbb E_X$ over a finite set.
--
--   These notions carry the sensitivity bounds of Section 6 and Appendix J.
-- source:
--   Gulati–Khurana–Tomer, How to Build Pseudorandom Unitaries in Microcrypt, arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), §6.2, pp.33–34; §J.2, p.94

import Mathlib

set_option autoImplicit false

namespace PRUMicrocrypt

/-- `x^{⊕i}`: the input `x ∈ {0,1}ᵐ` with bit `i` flipped (§6.2, p.33). -/
def flipBit {m : ℕ} (x : Fin m → Bool) (i : Fin m) : Fin m → Bool :=
  Function.update x i (!x i)

/-- `p : {0,1}ᵐ → ℝ` is a real polynomial of degree at most `d`: there is a real multivariate
polynomial `P` of total degree at most `d` with `p(x) = P(x₁, …, x_m)` for every Boolean input
(bits read as `0, 1 ∈ ℝ`) (Lemma J.1, p.94; Lemma 6.2, p.33). -/
def IsPolyDegLE {m : ℕ} (d : ℕ) (p : (Fin m → Bool) → ℝ) : Prop :=
  ∃ P : MvPolynomial (Fin m) ℝ, P.totalDegree ≤ d ∧
    ∀ x, p x = MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) P

/-- **δ-sensitivity** (§6.2, p.33): `S_δ(f, x) = #{i : |f(x) − f(x^{⊕i})| ≥ δ}`.
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), §6.2, p.33. -/
noncomputable def sensitivity {m : ℕ} (δ : ℝ) (f : (Fin m → Bool) → ℝ) (x : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin m => δ ≤ |f x - f (flipBit x i)|).card

/-- **Average change** (§6.2, p.34): `A_f(x) = (1/m) ∑_{i=1}^{m} |f(x) − f(x^{⊕i})|`. -/
noncomputable def avgChange {m : ℕ} (f : (Fin m → Bool) → ℝ) (x : Fin m → Bool) : ℝ :=
  (1 / (m : ℝ)) * ∑ i : Fin m, |f x - f (flipBit x i)|

/-- `Pr_X[E(X)]` for a uniform element `X` of a finite nonempty type: the fraction
`|{x : E(x)}| / |α|`. On the cube `{0,1}ᵐ` this is `|{x : E(x)}| / 2ᵐ`. -/
noncomputable def unifProb {α : Type*} [Fintype α] (E : α → Prop) : ℝ :=
  open scoped Classical in
  ((Finset.univ.filter E).card : ℝ) / (Fintype.card α : ℝ)

/-- `E_X[f(X)]` for a uniform element `X` of a finite nonempty type: `|α|⁻¹ ∑ₓ f(x)`. -/
noncomputable def unifAvg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

/-- A **one-sided certificate** at `y` for `f : {0,1}ᵐ → [0,1]` (§J.2, p.94): nonnegative weights
`w(i)` with `f(y) − f(x) ≤ ∑_{i : yᵢ ≠ xᵢ} w(i)` for every `x`. Its mass is `∑ᵢ w(i)`. -/
def IsOneSidedCert {m : ℕ} (f : (Fin m → Bool) → ℝ) (y : Fin m → Bool) (w : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∀ x, f y - f x ≤ ∑ i ∈ Finset.univ.filter (fun i => y i ≠ x i), w i

end PRUMicrocrypt


