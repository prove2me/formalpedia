-- Prove2me | Definitions.Def_NKtLB_prog
-- name    : NKtLB_prog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:59:54.028992+00:00
-- url     : https://prove2.me/theorems/d8fbe74f-ca8e-48ac-b17d-5c8d09aabc6d
-- title:
--   The program format $s_\alpha\,01\,\langle M\rangle\,\alpha$
-- statement:
--   A **program** is a pair $\Pi=(M,\alpha)$ of a machine $M$ and an advice string $\alpha$. As a string it is
--   $$
--   \Pi=s_\alpha\,01\,\langle M\rangle\,\alpha ,
--   $$
--   where $s_\alpha$ is the binary representation of $|\alpha|$ with each bit duplicated and $\langle M\rangle$ is the code of $M$. The size $|\Pi|$ is the length of this string.
--
--   **Formalization Note** The machine code $\langle\cdot\rangle$ is a parameter `code : Machine → List Bool`. The binary representation is most significant bit first; $0$ is represented by the empty string.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.2, p.21

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_NKtLB_dbl

namespace NKtLB

/-- **The program `Π = (M, α)` as a string** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §3.2, p.21): "To encode a machine-advice pair
`(M, α)`, we use the following format: `s_α 01 ⟨M⟩ α`, where `s_α` is the binary representation of
the integer specifying the length of `α`, with each bit duplicated. The size of `Π`, denoted `|Π|`,
is the total length of this description."

**Formalization Note.** `⟨M⟩` is `code M` for an encoding `code : Machine → List Bool` that is a
parameter (the paper: "we assume a fixed standard encoding for Turing machines", footnote 15). The
binary representation of `|α|` is most significant bit first, `(Nat.bits |α|).reverse`, so `0` is
represented by the empty string. -/
def prog (code : Machine → List Bool) (M : Machine) (α : List Bool) : List Bool :=
  dbl (Nat.bits α.length).reverse ++ [false, true] ++ code M ++ α

end NKtLB


