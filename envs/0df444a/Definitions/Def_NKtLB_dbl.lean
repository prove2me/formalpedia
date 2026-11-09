-- Prove2me | Definitions.Def_NKtLB_dbl
-- name    : NKtLB_dbl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:54:21.553745+00:00
-- url     : https://prove2.me/theorems/6fac08f1-7df4-42a2-b8cf-662976a56657
-- title:
--   Bit doubling $b_1b_2\cdots\mapsto b_1b_1b_2b_2\cdots$
-- statement:
--   For a bit string $l=b_1b_2\cdots b_k$, $\mathrm{dbl}(l)=b_1b_1b_2b_2\cdots b_kb_k$. Followed by the separator $01$, a doubled string is self-delimiting. The paper uses this device in its program format $s_\alpha\,01\,\langle M\rangle\,\alpha$, where $s_\alpha$ is the binary representation of $|\alpha|$ "with each bit duplicated".
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.2, p.21

import Mathlib

namespace NKtLB

/-- **Bit doubling** `b₁b₂… ↦ b₁b₁b₂b₂…`, the self-delimiting device of the program format
`s_α 01 ⟨M⟩ α` (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §3.2, p.21: "`s_α` is the binary representation of the integer specifying
the length of `α`, with each bit duplicated"). -/
def dbl (l : List Bool) : List Bool := l.flatMap (fun b => [b, b])

end NKtLB


