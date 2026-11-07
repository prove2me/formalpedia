-- Prove2me | Definitions.Def_MatMulDS_omegaExp
-- name    : MatMulDS_omegaExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:22.422137+00:00
-- url     : https://prove2.me/theorems/b133e7c9-a567-4dce-a4e0-db73e730e5bf
-- title:
--   The exponents $\omega(a,b,c)$ and the dual exponent $\alpha$
-- statement:
--   The exponent $\omega(a,b,c)$ over $\mathbb F$ is the infimum of the real $\tau$ such that for every $\varepsilon>0$ there is a $C>0$ with
--   $$\mathrm{MM}(\lceil n^a\rceil,\lceil n^b\rceil,\lceil n^c\rceil)\le C\,n^{\tau+\varepsilon}\quad\text{for all }n\ge 1.$$
--
--   The **dual exponent of matrix multiplication** over $\mathbb F$ is
--   $$\alpha=\sup\{s\ge 0:\omega(1,s,1)=2\}.$$
--
--   These exponents measure when rectangular products can be computed in almost-quadratic time. The set defining $\alpha$ contains $0$ and is bounded above by $1$.
--
--   **Formalization Note** Dimensions are rounded up, as on p.14 of the source, and the exponents are those of the field $\mathbb F$.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), §3, pp.13–14 (PDF pp.15–16)

import Mathlib
import Definitions.Def_MatMulDS_MM

set_option autoImplicit false

namespace MatMulDS

/-- **The exponent ω(a, b, c).** The exponent of multiplying an `n^a × n^b` matrix by an `n^b × n^c`
matrix over `F`, "so that MM(n^a, n^b, n^c) = n^{ω(a,b,c)+o(1)}" (STOC 2027 submission, held file sha256
6c5a1c16…, §3, p.13): the infimum of the `τ` such that for every `ε > 0` there is a `C > 0` with
`MM(⌈n^a⌉, ⌈n^b⌉, ⌈n^c⌉) ≤ C n^{τ+ε}` for all `n ≥ 1`.

**Formalization Note** Dimensions are rounded up, as on p.14 ("an n × ⌈n^s⌉ by ⌈n^s⌉ × n product"). The
exponent is that of the field `F`. For `a, b, c ≥ 0` the set is nonempty (schoolbook) and bounded below,
so the infimum is not a junk value; for `a = c = 1` and `b = s ≥ 0` this is checked in the sanity file. -/
noncomputable def omegaExp (F : Type) [Field F] (a b c : ℝ) : ℝ :=
  sInf {τ : ℝ | ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    (MM F ⌈(n : ℝ) ^ a⌉₊ ⌈(n : ℝ) ^ b⌉₊ ⌈(n : ℝ) ^ c⌉₊ : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)}

/-- **The dual exponent of matrix multiplication.** `α = sup {s ≥ 0 : ω(1, s, 1) = 2}` (STOC 2027
submission, held file sha256 6c5a1c16…, §3, p.14), over the field `F`.

**Formalization Note** The set contains `s = 0` and is bounded above by `1`, because `ω(1, s, 1) ≥ 1 + s`,
so the supremum is not a junk value (checked in the sanity file). -/
noncomputable def dualExponent (F : Type) [Field F] : ℝ :=
  sSup {s : ℝ | 0 ≤ s ∧ omegaExp F 1 s 1 = 2}

end MatMulDS


