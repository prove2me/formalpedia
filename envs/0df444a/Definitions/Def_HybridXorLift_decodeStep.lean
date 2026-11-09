-- Prove2me | Definitions.Def_HybridXorLift_decodeStep
-- name    : HybridXorLift_decodeStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:42.707207+00:00
-- url     : https://prove2.me/theorems/1de7727e-cb74-49ae-82b1-aa1122c1d7f6
-- title:
--   Reading a recorded outcome
-- statement:
--   Given $k$ and $w$, a recorded entry $(L, v)$ of a history is read back as the outcome $(a, v)$ with $a_\ell$ the $\ell$-th element of $L$, provided $L$ has exactly $k$ elements and $v < w$; otherwise the entry is not an outcome of such a subroutine. Reading back a recorded outcome returns that outcome.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §2.2 "Histories", p.10 (PDF p.12)

import Definitions.Def_HybridXorLift_Step

namespace HybridXorLift

/-- Reading a recorded step as an outcome of a subroutine with `k` slots and workspace `Fin w`
(Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §2.2 "Histories", p.10 (PDF p.12)): `some y` when the record has `k` slot labels and a
workspace index `< w` (then it is `encodeStep y`), and `none` otherwise. -/
def decodeStep {ι : Type} (k w : ℕ) (u : Step ι) : Option ((Fin k → ι × Bool) × Fin w) :=
  if h : u.1.length = k ∧ u.2 < w then
    some (fun l => u.1.get (Fin.cast h.1.symm l), ⟨u.2, h.2⟩)
  else none

end HybridXorLift


