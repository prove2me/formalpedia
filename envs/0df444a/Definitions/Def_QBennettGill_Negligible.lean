-- Prove2me | Definitions.Def_QBennettGill_Negligible
-- name    : QBennettGill_Negligible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:40.801001+00:00
-- url     : https://prove2.me/theorems/bbfd6b45-5bce-4b76-9c67-293ddf52e28b
-- title:
--   Negligible functions $f(n)=n^{-\omega(1)}$
-- statement:
--   A function $f:\mathbb N\to\mathbb R$ is **negligible**, written $f(n)=\mathrm{negl}(n)$, if $f(n)=n^{-\omega(1)}$: for every exponent $c\in\mathbb N$ there is $n_0$ with
--
--   $$|f(n)|\le n^{-c}\qquad\text{for all }n\ge n_0 .$$
--
--   Negligible functions are the error terms in the soundness and zero-knowledge conditions of Definition 4 and in Lemmas 8–10 and 26–28.
--
--   **Formalization Note** Natural exponents suffice. The published negligible-function definitions on the platform additionally require $f\ge0$ (or bundle further notions), a condition the paper does not state, so this one is local.
-- source:
--   Liang, Yamakawa, Yung, Structured Quantum Hardness from Unstructured Assumptions, STOC 2027 submission (held manuscript, sha256 6464b75a…), §3, Notation, p.16 (PDF p.19)

import Mathlib

set_option autoImplicit false

namespace QBennettGill

open Filter

/-- A function `f : ℕ → ℝ` is **negligible**, `f(n) = n^{−ω(1)}`: for every exponent `c`,
`|f(n)| ≤ n^{−c}` for all sufficiently large `n`.

Liang, Yamakawa, Yung, *Structured Quantum Hardness from Unstructured Assumptions*,
STOC 2027 submission (held manuscript, sha256 6464b75a…), §3, Notation, p.16 (PDF p.19): "We say that a function f(n) is negligible in n if
f(n) = n^{−ω(1)}, and we denote this by f(n) = negl(n)."

**Formalization Note.** Natural exponents suffice (real ones are dominated by the next integer).
The absolute value makes the definition sign-free; nothing else is assumed. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∀ᶠ n in atTop, |f n| ≤ ((n : ℝ) ^ c)⁻¹

end QBennettGill


