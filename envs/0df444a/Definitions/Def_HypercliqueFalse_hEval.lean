-- Prove2me | Definitions.Def_HypercliqueFalse_hEval
-- name    : HypercliqueFalse_hEval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:47.51504+00:00
-- url     : https://prove2.me/theorems/fbffb6f6-cd77-4647-b93d-7c2b67072048
-- title:
--   Evaluating $H_{k,h}$ (word RAM problem)
-- statement:
--   The problem of **evaluating $H_{k,h}$** on the published word RAM. An instance at scale $s$ consists of a size $m \le s$ and integer arrays $A_S$ over $[m]^h$, one for each $h$-element subset $S \subseteq [k]$. The input is $m$ followed by all entries of the arrays; the machine must write the value $H_{k,h}$ (with variables ranging over $[m]$) into the first cell after the input.
--
--   Time bounds for this problem are stated in the instance's size $m$ (the paper's $n$ in Theorem 2.1 and Section 4); the scale $s \ge m$ fixes the word size and the integer bound (see `SolvedWithin`). The problem $H_h := H_{h+1,h}$ of Section 4 is the case $k = h + 1$.
--
--   **Formalization Note** The subsets are listed in the order of `(List.finRange k).sublistsLen h`, and the $m^h$ entries of each array in the mixed-radix order of `finFunctionFinEquiv` (coordinate $0$ least significant). At $m = s$ this is the plain evaluation problem.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, p.4; Theorem 2.1, p.4

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_HypercliqueFalse_hyperPoly

set_option autoImplicit false

open TrulySubcubicAPSP

namespace HypercliqueFalse

/-- **Evaluating `H_{k,h}`**, as a problem of the published word RAM. Fischer, *The Hyperclique
Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, p.4 ("the
goal is to compute the (k, h)-hyperclique polynomial") and Theorem 2.1, p.4 ("the polynomial
H_{k,h} can be evaluated").

An instance at scale `s` is a pair `⟨m, _, A⟩`: a size `m ≤ s` and integer arrays `A S` over
`[m]^h`, one for each `h`-element subset `S ⊆ [k]`. The input is `m` followed by the entries of the
arrays; the program must write `hyperPoly A` (`H_{k,h}` with variables over `[m]`) into the first
cell after the input.

**Formalization Note.** Subsets are listed in the order of `(List.finRange k).sublistsLen h`; the
`m ^ h` entries of each array follow in the order of `finFunctionFinEquiv.symm` (coordinate `0` least
significant). The scale `s` fixes the word size and the integer bound of `SolvedWithin`; time
bounds are stated in `m` (Theorem 2.1's `n`). At `m = s` this is the plain problem. -/
def hEval (k h : ℕ) : Problem where
  Instance s := Σ' (m : ℕ) (_ : m ≤ s), ({S : Finset (Fin k) // S.card = h} → (Fin h → Fin m) → ℤ)
  input x := (x.1 : ℤ) :: (((List.finRange k).sublistsLen h).map fun l =>
      if hl : l.toFinset.card = h then
        List.ofFn fun t : Fin (x.1 ^ h) => x.2.2 ⟨l.toFinset, hl⟩ (finFunctionFinEquiv.symm t)
      else []).flatten
  output x f := f 0 = hyperPoly x.2.2

end HypercliqueFalse


