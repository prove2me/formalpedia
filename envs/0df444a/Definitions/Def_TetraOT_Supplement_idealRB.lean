-- Prove2me | Definitions.Def_TetraOT_Supplement_idealRB
-- name    : TetraOT_Supplement_idealRB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:39:19.039876+00:00
-- url     : https://prove2.me/theorems/c5cd2106-e7fb-410a-ae74-321e72557f86
-- title:
--   The ideal ½ROT at rate $2/3$
-- statement:
--   The ideal functionality of Theorem 9.1. With probability $1/3$ both parties receive "reject" (none). With probability $2/3$, independently of anything else, they receive a random 1-of-2 oblivious transfer (Definition 2.5): Alice gets $(m_0,m_1)$ and Bob gets $(s, m_s)$, where $m_0, m_1, s$ are independent uniform bits. The point masses are
--   $$\Pr[\text{reject}] = \tfrac13,\qquad \Pr\big[(m_0,m_1),(s,m_s)\big] = \tfrac{1}{12}$$
--   for each of the eight consistent output pairs.
--
--   "Rate $2/3$" is the acceptance probability, the expected number of oblivious transfers per deal.
--
--   **Formalization Note** Built as a uniform three-sided coin (one face meaning reject) followed, on the other two faces, by the published ideal random oblivious transfer.
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Theorem 9.1, p.10, and its proof, p.11 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_idealROT

set_option autoImplicit false

namespace TetraOT.Supplement

open TetraOT

/-- **The ideal ½ROT at rate 2/3** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Theorem 9.1, p.10, and its proof, p.11; p. = PDF
page, the PDF has no printed page numbers): "implements ½ROT … with rate 2/3"; "reject occurs with
probability 1/3 based on the shuffle, independently of any bits established in successful runs".

A fair three-sided coin is tossed. With probability `1/3` both parties receive `none` (reject). With
probability `2/3` they receive `(some o₁, some o₂)` where `(o₁, o₂)` is drawn from the published ideal
random oblivious transfer `TetraOT.idealROT` (Definition 2.5: `o₁ = (m₀, m₁)`, `o₂ = (s, m_s)` with
`m₀, m₁, s` independent uniform bits), independently of the coin. The point masses are `1/3` on
`(none, none)` and `1/12` on each of the 8 consistent pairs `(some (m₀, m₁), some (s, m_s))`.

**Formalization Note.** The coin is `PMF.uniformOfFintype (Fin 3)`, with `0` meaning reject. "Rate 2/3"
is the acceptance probability `2/3`, the expected number of ROTs per deal. -/
noncomputable def idealRB : PMF (Option (Bool × Bool) × Option (Bool × Bool)) :=
  (PMF.uniformOfFintype (Fin 3)).bind (fun i =>
    if i = 0 then PMF.pure (none, none) else idealROT.map (fun o => (some o.1, some o.2)))

end TetraOT.Supplement


