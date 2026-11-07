-- Prove2me | Definitions.Def_AvgPHETH_Inst3DNF_enc
-- name    : AvgPHETH_Inst3DNF_enc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:28:37.135611+00:00
-- url     : https://prove2.me/theorems/eb3f6d70-ad0f-4bf6-947c-1fc07a961951
-- title:
--   The binary encoding of $\varphi$, of length $n$
-- statement:
--   An injective binary encoding of the instance, whose length is the input length $n$: the two numbers of variables in unary, then each literal as a marker bit, a sign and a variable index of $\lceil\log_2 N\rceil$ bits, with a terminating bit after each term. In particular $N\le n$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4)

import Mathlib
import Definitions.Def_AvgPHETH_Inst3DNF

namespace AvgPHETH

/-- The binary encoding of a `Σ₂SAT` instance, whose length is the input length `n`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4): "where `n` denotes the input length").

**Formalization Note** The code is `1^numY 0 1^numZ 0`, then the terms: each literal as `1`, its sign
and its variable index with `⌈log₂ N⌉` bits, and a `0` at the end of each term. The numbers of
variables are written in unary, so `N ≤ n`, and the code is injective. -/
def Inst3DNF.enc (φ : Inst3DNF) : List Bool :=
  let w := Nat.clog 2 (φ.numY + φ.numZ)
  let idx := fun i : Fin (φ.numY + φ.numZ) =>
    List.ofFn (fun j : Fin w => (i : ℕ).testBit (j : ℕ))
  List.replicate φ.numY true ++ false :: List.replicate φ.numZ true ++ false ::
    φ.terms.flatMap (fun τ => τ.flatMap (fun lit => true :: lit.1 :: idx lit.2) ++ [false])

end AvgPHETH


