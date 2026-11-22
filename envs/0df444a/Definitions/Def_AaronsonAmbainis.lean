-- Prove2me | Definitions.Def_AaronsonAmbainis
-- name    : AaronsonAmbainis
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-07T07:34:08.134875+00:00
-- url     : https://prove2.me/theorems/86c3f3f2-a48f-484c-8709-fc6a0f12fe5a
-- title:
--   Variance and influence on the Boolean cube
-- statement:
--   Supporting definitions for the Aaronson--Ambainis conjecture: the uniform measure on the Boolean cube $\{0,1\}^N$ and the two functionals it induces on a real polynomial.
--
--   A cube point $x\in\{0,1\}^N$ is identified with the $0/1$ real vector it names, so a real multivariate polynomial $p$ may be evaluated at it. Under the uniform distribution on the cube we set
--
--   $$\mathbb{E}[f]=2^{-N}\sum_{x\in\{0,1\}^N}f(x),\qquad \operatorname{Var}[p]=\mathbb{E}\big[(p-\mathbb{E}[p])^2\big].$$
--
--   Writing $x^{\oplus i}$ for $x$ with its $i$-th bit flipped, the influence of coordinate $i$ on $p$ is
--
--   $$\operatorname{Inf}_i[p]=\mathbb{E}\big[(p(x)-p(x^{\oplus i}))^2\big].$$
--
--   These are the combinatorial (not Fourier-analytic) forms of variance and influence, which is how Aaronson and Ambainis state them. They are the reusable substrate for any statement about bounded low-degree functions on the cube: analysis of Boolean functions, query-complexity lower bounds, and the structure-of-quantum-speedups literature all quantify over exactly these two functionals.
--
--   **Formalization Note** Polynomials are `MvPolynomial (Fin N) ℝ`, so degree is Mathlib's `totalDegree` and no separate Fourier--Walsh layer is required. Expectation is a finite sum scaled by $2^{-N}$ rather than a measure-theoretic integral, which keeps every definition elementary. Bit flipping is `Function.update x i (!x i)`.
-- source:
--   Aaronson & Ambainis, The Need for Structure in Quantum Speedups, arXiv:0911.0996, Conjecture 6 ("Bounded Polynomials Have Influential Variables")

import Mathlib

/-!
# Boolean-cube expectation, variance, and influence

Supporting definitions for Aaronson-Ambainis, *The Need for Structure in
Quantum Speedups*, arXiv:0911.0996, Conjecture 6.
-/

namespace AaronsonAmbainis

variable {N : ℕ}

/-- A cube point `x : Fin N → Bool` as a 0/1 real vector. -/
def toReal (x : Fin N → Bool) : Fin N → ℝ := fun i => if x i then 1 else 0

/-- Value of a real multivariate polynomial at a cube point. -/
noncomputable def cubeEval (p : MvPolynomial (Fin N) ℝ) (x : Fin N → Bool) : ℝ :=
  MvPolynomial.eval (toReal x) p

/-- Expectation of `f` under the uniform distribution on `{0,1}^N`. -/
noncomputable def cubeExp (f : (Fin N → Bool) → ℝ) : ℝ :=
  (2 ^ N : ℝ)⁻¹ * ∑ x : Fin N → Bool, f x

/-- `Var[p]`: variance of `p` over the uniform distribution on the cube. -/
noncomputable def cubeVar (p : MvPolynomial (Fin N) ℝ) : ℝ :=
  cubeExp (fun x => (cubeEval p x - cubeExp (cubeEval p)) ^ 2)

/-- `x` with its `i`-th bit flipped. -/
def flipBit (x : Fin N → Bool) (i : Fin N) : Fin N → Bool := Function.update x i (!x i)

/-- `Inf_i[p]`: the influence of coordinate `i` on `p`. -/
noncomputable def cubeInfl (p : MvPolynomial (Fin N) ℝ) (i : Fin N) : ℝ :=
  cubeExp (fun x => (cubeEval p x - cubeEval p (flipBit x i)) ^ 2)

end AaronsonAmbainis


