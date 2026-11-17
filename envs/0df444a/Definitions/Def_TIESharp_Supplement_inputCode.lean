-- Prove2me | Definitions.Def_TIESharp_Supplement_inputCode
-- name    : TIESharp_Supplement_inputCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:54:32.751609+00:00
-- url     : https://prove2.me/theorems/0d4c7bc0-3848-43aa-81ee-55ef55c7659c
-- title:
--   Binary input of the mechanism on rational reports
-- statement:
--   Let $n$ be the number of machines, $m$ the number of jobs and $b=(b_{ij})\in\mathbb Q^{n\times m}$ a rational report matrix ($b_{ij}$ is machine $i$'s reported processing time for job $j$). The **binary input** of the mechanism is the bit string
--
--   $$\langle m\rangle\;1\,\langle b_{11}\rangle\cdots\langle b_{1m}\rangle\;1\,\langle b_{21}\rangle\cdots\langle b_{2m}\rangle\;\cdots\;1\,\langle b_{n1}\rangle\cdots\langle b_{nm}\rangle\;0,$$
--
--   that is, the number of jobs, then the $n$ rows of the report matrix machine by machine, each row opened by a marker bit $1$, and a final $0$ closing the list of rows. Here $\langle k\rangle$ is the self-delimiting binary code of a natural number (each binary digit preceded by a $1$, a final $0$ ending the number) and $\langle q\rangle$ that of a rational in lowest terms (sign bit, numerator magnitude, denominator), the codes of the published log-cost rational RAM. The length of this string is the **total binary input length** of Theorem 1.3; the number of machines $n$ is part of the input, as the number of rows.
--
--   **Formalization Note** The paper fixes no input format; this is a reading. Every machine contributes at least one bit, also when $m=0$: writing $n$ only in binary would give an input of $O(\log n)$ bits at $m=0$, while every output lists $n$ payments, and no program could then run in time polynomial in the input length. Machines and jobs are 0-based (`Fin n`, `Fin m`). The code is injective (determines $n$, $m$ and $b$), checked in a verification file.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, Theorem 1.3, p.2 (PDF p.3); §6.1, p.29 (PDF p.30)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_BitRAM

set_option autoImplicit false

namespace TIESharp

namespace Supplement

open BlottoFPTAS.Main.BitRAM

/-- The **binary input** of the mechanism on rational reports (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, Theorem 1.3, p.2; §6.1, p.29): the number
of jobs `m`, then the `n` rows of the report matrix `b ∈ ℚ^{n×m}` in machine order (machine `0`'s
row first), each row opened by a marker bit `true` and consisting of its `m` reports `b_i0, …`, and
a final `false` closing the list of rows. Numbers are written in the self-delimiting binary codes of
the published log-cost rational RAM `BlottoFPTAS.Main.BitRAM` (`encNat`, `encRats`). Its length is
"the total binary input length".

**Formalization Note.** The paper fixes no input format; this is a reading. The number of machines
`n` is part of the input ("even when n is part of the input") as the number of rows, so every one
of the `n` machines contributes at least one input bit, also when `m = 0`. (Writing `n` only in
binary would make the input `O(log n)` bits long at `m = 0`, while every output must list `n`
payments, so no program could run in time polynomial in that length.) Machines are `Fin n`, jobs
`Fin m`, 0-based. The code is injective, i.e. it determines `n`, `m` and `b` (checked in
`Solutions/verification/TIESharp_Supplement_sanity.lean`). -/
def inputCode (n m : ℕ) (b : Fin n → Fin m → ℚ) : List Bool :=
  encNat m ++ (List.ofFn fun i => true :: encRats (List.ofFn (b i))).flatten ++ [false]

end Supplement

end TIESharp


