-- Prove2me | Definitions.Def_QuadBogolyubov_Lam
-- name    : QuadBogolyubov_Lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:15.021506+00:00
-- url     : https://prove2.me/theorems/9502c7ed-5145-4a57-93d1-797e4a90d180
-- title:
--   The seven-point operator $\Lambda(f_1,\dots,f_7)$
-- statement:
--   For real functions $f_1,\dots,f_7$ on $\mathbb F_2^n$,
--   $$\Lambda(f_1,\dots,f_7)=\mathbb E_{x_1,x_2,x_3}f_1(x_1)f_2(x_2)f_3(x_3)f_4(x_1+x_2)f_5(x_1+x_3)f_6(x_2+x_3)f_7(x_1+x_2+x_3),$$
--   and $\Lambda(f)=\Lambda(f,\dots,f)$. It counts punctured 3-cubes rooted at $0$.
--
--   **Formalization Note** The functions are indexed by `Fin 7`: `f 0, …, f 6` are $f_1,\dots,f_7$.
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), §4, p.11

import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace QuadBogolyubov

/-- The **seven-point operator**
`Λ(f₁, …, f₇) = 𝔼_{x₁,x₂,x₃ ∈ 𝔽₂ⁿ} f₁(x₁) f₂(x₂) f₃(x₃) f₄(x₁+x₂) f₅(x₁+x₃) f₆(x₂+x₃) f₇(x₁+x₂+x₃)`
on real functions, counting punctured 3-cubes rooted at `0`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), §4, p.11:
"we define the multilinear operator Λ acting on functions f1, . . . , f7 : F₂ⁿ → R by
Λ(f1, . . . , f7) = E_{x1,x2,x3∈F₂ⁿ} f1(x1)f2(x2)f3(x3)f4(x1+x2)f5(x1+x3)f6(x2+x3)f7(x1+x2+x3).
If the seven functions are all equal, we write Λ(f) := Λ(f, . . . , f)."

**Formalization Note.** The seven functions are indexed by `Fin 7`: `f 0, …, f 6` are
`f₁, …, f₇`. `Λ(f)` is `Lam (fun _ => f)`. -/
noncomputable def Lam {n : ℕ} (f : Fin 7 → (Fin n → ZMod 2) → ℝ) : ℝ :=
  𝔼 x₁ : Fin n → ZMod 2, 𝔼 x₂ : Fin n → ZMod 2, 𝔼 x₃ : Fin n → ZMod 2,
    f 0 x₁ * f 1 x₂ * f 2 x₃ * f 3 (x₁ + x₂) * f 4 (x₁ + x₃) * f 5 (x₂ + x₃) *
      f 6 (x₁ + x₂ + x₃)

end QuadBogolyubov


