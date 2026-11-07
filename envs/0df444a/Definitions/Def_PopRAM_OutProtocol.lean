-- Prove2me | Definitions.Def_PopRAM_OutProtocol
-- name    : PopRAM_OutProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:17.888422+00:00
-- url     : https://prove2.me/theorems/2799f2de-0703-47c2-9ace-4080d0927c7f
-- title:
--   Out$(\ell,i)$ (Protocol 15) as a mini-protocol
-- statement:
--   In Protocol 15, every agent of the weight $P_\ell$ first adopts an output component, becoming a **marked** weight agent $(p_\ell,\mathrm{out}_i)$, and then passes it to a free agent:
--   $$(p_\ell,\mathrm{out}_i)+\phi\to p_\ell+\mathrm{out}_i.$$
--   The states are $S$ (marked weight agent), $P$ (weight agent), $\phi$ (free), $O$ (output agent $\mathrm{out}_i$) and $X$ (inert); every other pair is unchanged.
--
--   **Formalization Note** The rule is applied with the marked agent as initiator, as printed and as the proof of Lemma 7 counts it.
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Protocol 15, p.26 (PDF p.27)

import Mathlib

set_option autoImplicit false

namespace PopRAM

/-! # Out(ℓ, i) as a mini-protocol (Protocol 15)

Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM Simulation by Population Protocols*,
arXiv:2611.06178 (held version, sha256 f13223b3…), Protocol 15, p.26 (PDF p.27), line 7:
"(p_ℓ, out_i) + φ → p_ℓ + out_i."

**Formalization Note** `S` is a marked weight agent `(p_ℓ, out_i)`, `P` a weight agent `p_ℓ`,
`free` is `φ`, `O` an output agent `out_i`, `X` any other agent (inert). The rule is applied with the
marked agent as initiator, as printed; the proof of Lemma 7 counts "a given interaction … initiated
by this agent with a free agent as responder". Every other pair is unchanged. -/

/-- States of Out. -/
inductive OutState where
  | S
  | P
  | free
  | O
  | X
  deriving DecidableEq

/-- The transition function of Out. -/
def outδ : OutState → OutState → OutState × OutState
  | .S, .free => (.P, .O)
  | a, b => (a, b)

end PopRAM


