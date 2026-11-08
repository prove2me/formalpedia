-- Prove2me | Definitions.Def_AvoidPlast_U
-- name    : AvoidPlast_U
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:47:33.08972+00:00
-- url     : https://prove2.me/theorems/42187484-daae-4bab-aae8-5c5b2d1f6f89
-- title:
--   The universal function $U_\varepsilon$
-- statement:
--   The function computed by the universal machine of Definition 5.13: on input $(x,d)$, with $n=|x|$ and $m_\varepsilon(n)=\lceil n^{\varepsilon^2}\rceil$, parse $d$ as the description of a machine $M$, simulate $M$ on $x$ for at most $2^{m_\varepsilon(n)}$ steps with simulation size at most $m_\varepsilon(n)$, and return its $n$-bit output, or $0^n$ if the simulation exceeds the time or space bounds, returns an output of other length, or $d$ describes no machine.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 5.13, p.29

import Mathlib
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_haltTime
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_decodeMachine
import Definitions.Def_AvoidPlast_simSize

namespace AvoidPlast

open Classical in
/-- The universal function `U_ε` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 5.13, p.29): on `(x, d)` with `n = |x|` it parses
`d` as a description of a machine `M`, simulates `M` on `x` for at most `2^{m_ε(n)}` steps with
simulation size at most `m_ε(n)` (where `m_ε(n) = ⌈n^{ε²}⌉`) and returns its `n`-bit output, or `0^n`
if the simulation exceeds the time or space bounds, or returns an output of other length.

**Formalization Note** Reading R4: the denotation of "a universal deterministic machine `U_ε`". The
budgets use the ceiling `⌈n^{ε²}⌉` (reading R3), which is `|d|`. -/
noncomputable def U (ε : ℝ) (x d : List Bool) : List Bool :=
  match decodeMachine d with
  | some M =>
    if HaltsWithin M ![x] (2 ^ ceilPow (ε ^ 2) x.length) ∧
        (∀ t ≤ haltTime M ![x], simSize M ![x] t ≤ ceilPow (ε ^ 2) x.length) ∧
        (output M ![x]).length = x.length
    then output M ![x] else List.replicate x.length false
  | none => List.replicate x.length false

end AvoidPlast


