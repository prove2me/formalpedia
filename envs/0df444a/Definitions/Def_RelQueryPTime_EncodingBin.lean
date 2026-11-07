-- Prove2me | Definitions.Def_RelQueryPTime_EncodingBin
-- name    : RelQueryPTime_EncodingBin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:35.239568+00:00
-- url     : https://prove2.me/theorems/2381b3c8-5b94-44b8-991e-385c7f13a49c
-- title:
--   Encoding $\langle B, c\rangle$ with the constants in positional binary
-- statement:
--   The variant of the input string in which each constant is written in positional binary:
--   $$
--   1^n\,0\;\; T(R_1)\cdots T(R_k)\;\; \mathrm{bin}(c_1)\cdots \mathrm{bin}(c_r),
--   $$
--   where $T(R_i)$ is the bit table of $R_i$ as in the main encoding and $\mathrm{bin}(c)$ is $c$ written with $\lceil\log_2(n+1)\rceil$ bits (Lean's `Nat.size n`), least significant bit first. $\mathrm{GraphBin}(Q)$ is the language of these encodings of the pairs in the answer of $Q$.
--
--   It is used only to show that the choice between one-hot and positional binary does not affect polynomial-time computability.
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, proof of Theorem 1, p.149 ("followed by some binary representation for c1…cr") (PDF p.3)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_RelQueryPTime_Syntax
import Definitions.Def_RelQueryPTime_Encoding

namespace RelQueryPTime

/-- The input string `⟨B, c⟩` with each `c_i` in positional binary (Immerman, STOC 1982, proof
of Theorem 1, p.149, "some binary representation for `c₁ … c_r`"): the prefix `1ⁿ0`, the bit
tables of `R₁, …, R_k` as in `enc`, then each `c_i` written in `Nat.size n` bits, least
significant bit first. -/
def encBin {σ : Schema} {n r : ℕ} (B : Database σ n) (c : Fin r → Fin n) : List Bool :=
  List.replicate n true ++ false ::
    ((List.finRange σ.k).flatMap B.table ++
      (List.finRange r).flatMap fun i => (List.range (Nat.size n)).map fun b => (c i : ℕ).testBit b)

/-- `Graph(Q)` under the positional-binary encoding `encBin`. -/
def GraphBin {σ : Schema} {r : ℕ} (Q : Query σ r) : CookPvsNP.Lang Bool :=
  {w | ∃ (n : ℕ) (B : Database σ n) (c : Fin r → Fin n), Q n B c ∧ w = encBin B c}

end RelQueryPTime


