-- Prove2me | Definitions.Def_TIESharp_Supplement_outputCode
-- name    : TIESharp_Supplement_outputCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:55:06.877973+00:00
-- url     : https://prove2.me/theorems/130e1959-8a14-4044-b941-a3ec18af489c
-- title:
--   Binary code of an outcome: an assignment and rational payments
-- statement:
--   An **outcome** of the mechanism on $n$ machines and $m$ jobs is an assignment $A:[m]\to[n]$ (job $j$ is processed by machine $A(j)$) together with a payment $\pi_i\in\mathbb Q$ to each machine $i$. Its **binary code** is
--
--   $$\langle A(1)\rangle\cdots\langle A(m)\rangle\,\langle \pi_1\rangle\cdots\langle \pi_n\rangle,$$
--
--   with the self-delimiting codes of naturals and rationals of the published log-cost rational RAM. A program implementing the mechanism writes this string as its output.
--
--   **Formalization Note** The paper fixes no output format; this is a reading. For fixed $n$ and $m$ the code is injective, checked in a verification file, so an output string determines the sampled outcome.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, Theorem 1.3, p.2 (PDF p.3); proof of Theorem 1.3, p.31 (PDF p.32)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_BitRAM

set_option autoImplicit false

namespace TIESharp

namespace Supplement

open BlottoFPTAS.Main.BitRAM

/-- The **binary code of an outcome** (Li, *Sharp Bounds for Truthful-in-Expectation Scheduling*,
arXiv:2611.05134, Theorem 1.3, p.2; proof of Theorem 1.3, p.31): an assignment
`A : [m] → [n]` (job `j` goes to machine `A j`) followed by the payments `π_1, …, π_n ∈ ℚ` to the
machines. The machine of each job is written with `encNat`, the payments with `encRats`, both
codes of the published log-cost rational RAM `BlottoFPTAS.Main.BitRAM`.

**Formalization Note.** The paper fixes no output format; this is a reading. For fixed `n` and
`m` the code is injective (checked in `Solutions/verification/TIESharp_Supplement_sanity.lean`),
so a run's output string determines the sampled outcome. -/
def outputCode {n m : ℕ} (A : Fin m → Fin n) (π : Fin n → ℚ) : List Bool :=
  (List.ofFn fun j => encNat (A j : ℕ)).flatten ++ encRats (List.ofFn π)

end Supplement

end TIESharp


