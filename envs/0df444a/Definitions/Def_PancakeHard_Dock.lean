-- Prove2me | Definitions.Def_PancakeHard_Dock
-- name    : PancakeHard_Dock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:14.015027+00:00
-- url     : https://prove2.me/theorems/961c6c26-2109-4717-aa2a-8b4ee3043562
-- title:
--   Definition 1 — the dock gadget $Dock(p,q)$
-- statement:
--   For integers $p<q$, the **dock** for $\star\mathcal I_q^{p+1}$ is the sequence
--   $$Dock(p,q)=D=\langle p-1,\;p,\;q+1,\;q+2\rangle .$$
--   Its role is to store the block $\star\mathcal I_q^{p+1}=\langle q,q-1,\dots,p+1\rangle$ out of the head of the sequence without disturbing any other part: by Property 4, when that block is at the head, the only efficient paths merge it into $\mathcal I^{p-1}_{q+2}$ at the position of $D$.
--
--   **Formalization Note** Unlike the other gadgets, no offset is added to a fixed list. The entries are natural numbers and $p-1$ is truncated subtraction; a stack has positive entries, so any stack containing a dock has $p\ge 2$ and the truncation never applies.
-- source:
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.1.1, p.4, Definition 1

import Mathlib
import Definitions.Def_PancakeHard_Basic

set_option autoImplicit false

namespace PancakeHard

/-- **Definition 1** (Bulteau, Fertin, Rusu, arXiv:1111.0434v2, §3.1.1, p.4): "Given two integers
p and q with p < q, the dock for ⋆𝓘^{p+1}_q is the sequence Dock(p, q) = D where
D = ⟨p − 1, p, q + 1, q + 2⟩."

**Formalization Note** No offset is added (unlike Lock, Hook, Fork). The values are natural
numbers; `p − 1` is truncated subtraction, which is `0` at `p = 0`. A sequence containing `0` is not
a stack, so every statement about a dock inside a stack has `p ≥ 2`, and the truncation never
applies there. -/
def Dock (p q : ℕ) : List ℕ := [p - 1, p, q + 1, q + 2]

end PancakeHard


