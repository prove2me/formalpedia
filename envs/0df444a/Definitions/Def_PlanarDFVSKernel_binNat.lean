-- Prove2me | Definitions.Def_PlanarDFVSKernel_binNat
-- name    : PlanarDFVSKernel_binNat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:33:55.167201+00:00
-- url     : https://prove2.me/theorems/b607de56-88e6-429e-8aeb-6f750ad349e5
-- title:
--   Self-delimiting binary code of a natural number
-- statement:
--   For $n\in\mathbb N$, $\mathrm{bin}(0)=0$ (one bit), and for $n\ge1$ the code of $n$ is a flag bit $1$, the least significant binary digit of $n$, and then the code of $\lfloor n/2\rfloor$. Every binary digit is preceded by a flag $1$ and the code ends with one $0$, so the code of $n\ge1$ has length $2(\lfloor\log_2 n\rfloor+1)+1$ and no code is a proper prefix of another.
--
--   It encodes "a binary parameter" and the explicit arc lists of instances: concatenations of such codes decode uniquely, and their length is logarithmic in the numbers encoded.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §3, p.8 (PDF 9)

import Mathlib

set_option autoImplicit false

namespace PlanarDFVSKernel

/-- **Self-delimiting binary code of a natural number.** Used to encode "a binary parameter"
and the explicit arc lists (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex
Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), §3, p.8 (PDF 9): "We measure the
encoding size using explicit vertex and arc lists and a binary parameter.").

`binNat 0 = [false]`, and for `n ≥ 1` the code is `true`, the least significant bit of `n`,
then the code of `⌊n / 2⌋`. Each binary digit is preceded by a `true` flag and the code ends with
one `false`, so the code of `n` has length `2 (⌊log₂ n⌋ + 1) + 1` for `n ≥ 1` and the code is
prefix-free (no code is a proper prefix of another).

**Formalization Note** The code is self-delimiting so that concatenations of codes (arc lists,
pairs, the parameter) decode uniquely; its length is logarithmic in `n`, so it is a binary, not a
unary, encoding. -/
def binNat : ℕ → List Bool
  | 0 => [false]
  | n + 1 => true :: ((n + 1) % 2 == 1) :: binNat ((n + 1) / 2)
termination_by n => n
decreasing_by omega

end PlanarDFVSKernel


