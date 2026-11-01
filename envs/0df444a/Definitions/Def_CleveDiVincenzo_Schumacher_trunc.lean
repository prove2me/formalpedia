-- Prove2me | Definitions.Def_CleveDiVincenzo_Schumacher_trunc
-- name    : CleveDiVincenzo_Schumacher_trunc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:37.872351+00:00
-- url     : https://prove2.me/theorems/d0aea860-ea3e-46af-89e0-e8882441bf64
-- title:
--   Register bits $X_j$, the bit flip $X_j\leftarrow X_j\oplus1$, and $\mathrm{TRUNC}_j(X)$
-- statement:
--   The paper's high-level pseudocode works on **arithmetic registers**, on which "ordinary integer addition and subtraction are allowed"; a signed register is "ordinary arithmetic in a register with one extra bit". For a register $X$:
--
--   1. $X_j$ denotes bit $j$ of $X$ (bit $0$ is the least significant);
--   2. the statement $X_j\leftarrow X_j\oplus 1$ negates bit $j$;
--   3. $\mathrm{TRUNC}_j(X)$ is the number formed by bits $0,\dots,j-1$ of $X$: "only the $j$ least significant bits of the quantum register $X$ (i.e., bit $0$ to bit $j-1$) should be taken account of" in a comparison,
--   $$
--   \mathrm{TRUNC}_j(X)=X \bmod 2^j\in[0,2^j).
--   $$
--
--   These three operations are the only bit-level primitives of the programs FINAL_SCHUMACHER_INVERSE and FINAL_SCHUMACHER, where $\mathrm{TRUNC}_j$ lets the comparisons ignore the high bits of $X$ that already hold the answer.
--
--   **Formalization Note** Registers are integers. $X_j$ is the two's-complement bit `Int.testBit X j`, which agrees with the bits of a signed $(n+1)$-bit register on its range $[-2^n,2^n)$; negating bit $j$ is subtracting $2^j$ if the bit is $1$ and adding $2^j$ otherwise; $\mathrm{TRUNC}_j$ is `Int.emod`. For $j=0$, $\mathrm{TRUNC}_0(X)=0$: the paper's remark that in the final pass "the comparison should not be performed at all" is read as "no quantum comparison is needed", since its outcome $0\ge\binom 0i$ is fixed.
-- source:
--   Cleve, DiVincenzo, Schumacher's quantum data compression as a quantum computation, arXiv:quant-ph/9603009v1, §III C, pp.16–18 (X_j, X_j ← X_j ⊕ 1; TRUNC_j defined on p.18); §III A, p.11 (arithmetic registers); p.16 (signed registers)

import Mathlib

namespace CleveDiVincenzo.Schumacher

/-- The bit `X_j` of an arithmetic register `X` (Cleve, DiVincenzo, *Schumacher's quantum data
compression as a quantum computation*, arXiv:quant-ph/9603009v1, §III C, pp.16–18):
`bit j X = true` means `X_j = 1`.

**Formalization Note** Registers of the high-level pseudocode are "arithmetic": "ordinary
integer addition and subtraction are allowed" (p.11), and a "signed" register is handled "by
doing ordinary arithmetic in a register with one extra bit" (p.16). They are modelled as
integers `ℤ`, and `X_j` is `Int.testBit X j`, the two's-complement bit, which agrees with the
bits of the signed `(n+1)`-bit register on its range `[−2^n, 2^n)`. -/
def bit (j : ℕ) (X : ℤ) : Bool :=
  X.testBit j

/-- `TRUNC_j(X)` (Cleve, DiVincenzo, arXiv:quant-ph/9603009v1, §III C, p.18): "only the `j`
least significant bits of the quantum register `X` (i.e., bit 0 to bit `j − 1`) should be taken
account of", so `TRUNC_j(X)` is the number `X mod 2^j ∈ [0, 2^j)` formed by those bits.

**Formalization Note** `Int.emod`, so the result is the value of bits `0 … j−1` of the
two's-complement `X`, also for negative `X`. For `j = 0` this is `TRUNC_0(X) = 0`: the p.18
remark that "the occurrence of the zero index in `TRUNC_0(X)` indicates that the comparison
should not be performed at all" is read as "no quantum comparison is needed" (the comparison
`0 ≥ C(0,i)` has a fixed classical outcome), not as "the condition is false". -/
def trunc (j : ℕ) (X : ℤ) : ℤ :=
  X % 2 ^ j

/-- The statement `X_j ← X_j ⊕ 1` (Cleve, DiVincenzo, arXiv:quant-ph/9603009v1, §III C,
pp.16–19): negate bit `j` of the register `X`.

**Formalization Note** On an integer register this subtracts `2^j` if bit `j` is 1 and adds
`2^j` if it is 0; in both cases only bit `j` of the two's-complement `X` changes. -/
def flip (j : ℕ) (X : ℤ) : ℤ :=
  if X.testBit j then X - 2 ^ j else X + 2 ^ j

end CleveDiVincenzo.Schumacher


