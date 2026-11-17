-- Prove2me | Definitions.Def_SamplingAC0_Supplement_symTarget
-- name    : SamplingAC0_Supplement_symTarget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:39:12.121748+00:00
-- url     : https://prove2.me/theorems/acf12ac5-eba7-4ed3-8ecc-fd1cb2c8a1a4
-- title:
--   The distribution $(U,f(U))$ of a symmetric function
-- statement:
--   A Boolean function $f:\{0,1\}^n\to\{0,1\}$ is **symmetric** if $f(x)$ depends only on the Hamming weight $|x|$. It is then determined by its value table $v:\{0,1,\dots,n\}\to\{0,1\}$ via $f(x)=v(|x|)$.
--
--   For such $f$, $(U,f(U))$ is the distribution on $\{0,1\}^{n+1}$ of
--   $$(x_1,\dots,x_n,f(x))\qquad\text{with }x\text{ uniform on }\{0,1\}^n.$$
--
--   This is the distribution that Theorem 7 samples exactly in AC$^0$.
--
--   **Formalization Note** The function is given by its table $v$, so every symmetric function, constant ones included, is covered. The last coordinate carries $f(x)$.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 7 p.4; §4 p.13

import Mathlib
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_Supplement_slice
set_option autoImplicit false

namespace SamplingAC0.Supplement

/-- The weight of `x ∈ {0,1}^n` as an element of `{0, …, n}`. -/
def weightFin {n : ℕ} (x : Fin n → Bool) : Fin (n + 1) :=
  ⟨weight x, Nat.lt_succ_of_le (by
    simpa [weight] using Finset.card_filter_le (Finset.univ : Finset (Fin n)) fun j => x j = true)⟩

/-- The symmetric Boolean function with value table `v`: `symFn v x = v(|x|)`. Every symmetric
`f : {0,1}^n → {0,1}` is `symFn v` for exactly one table `v : {0,…,n} → {0,1}` (its values on the
possible Hamming weights). -/
def symFn {n : ℕ} (v : Fin (n + 1) → Bool) (x : Fin n → Bool) : Bool :=
  v (weightFin x)

/-- The string `(x, f(x)) ∈ {0,1}^{n+1}`: coordinates `0, …, n-1` are `x`, coordinate `n` is
`symFn v x`. -/
def withValue {n : ℕ} (v : Fin (n + 1) → Bool) (x : Fin n → Bool) : Fin (n + 1) → Bool :=
  fun i => if h : (i : ℕ) < n then x ⟨i, h⟩ else symFn v x

/-- **The distribution `(U, f(U))` of a symmetric function.** Riazanov–Viola, *Sampling Tools and
the Power of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 7, p.4, and §4, p.13
("Fix a symmetric Boolean function f on {0, 1}^n and let D be the distribution (U, f(U))").

For the symmetric function `f = symFn v` given by its value table `v` on the Hamming weights
`0, …, n`, `symTarget n v` is the law of `(x, f(x))` on `{0,1}^{n+1}` for `x` uniform on `{0,1}^n`.

**Formalization Note.** The output coordinates are ordered `(x₁, …, xₙ, f(x))`, the last coordinate
(index `n`) carrying `f(x)`. -/
noncomputable def symTarget (n : ℕ) (v : Fin (n + 1) → Bool) : PMF (Fin (n + 1) → Bool) :=
  SamplingAC0.law (withValue v)

end SamplingAC0.Supplement


