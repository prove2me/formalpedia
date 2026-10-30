-- Prove2me | Definitions.Def_FlexMargin_IsLongChain
-- name    : FlexMargin_IsLongChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:37:06.822845+00:00
-- url     : https://prove2.me/theorems/6657b274-b536-4684-ba74-c9a630860eb7
-- title:
--   Long chain designs
-- statement:
--   A design $\mathcal A$ on $n$ plants and $n$ products is a **long chain design** if it is the long chain $\mathcal L$ after renaming the plants by a permutation $\pi$ and the products by a permutation $\tau$:
--
--   $$
--   \mathcal A=\{(a_{\pi(j)},b_{\tau(i)}) : (a_j,b_i)\in\mathcal L\}.
--   $$
--
--   The products and their margins belong to the system; different long chain designs differ in which products are adjacent along the chain.
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §2, p. 11, and §4.1, p. 20

import Mathlib
import Definitions.Def_FlexMargin_longChain

namespace FlexMargin

/-- **Long chain designs.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §2, p. 11 (the long chain `ℒ`) and §4.1, p. 20: "Consider the class of long chain designs
with equal number of high profit products and low profit products."

A design `A` on `n` plants and `n` products is a long chain design if it is the long chain
`FlexMargin.longChain n` after relabelling the plants by a permutation `π` and the products by a
permutation `τ`: `A = {(π j, τ i) | (j, i) ∈ ℒ}`.

**Formalization Note.** The products and their margins are fixed by the system; what varies
between long chain designs is the arc set, i.e. which products are adjacent on the chain. This is
how the paper compares two long chains on one system under one uncertainty set (Theorem 3,
Proposition 1). -/
def IsLongChain {n : ℕ} (A : Finset (Fin n × Fin n)) : Prop :=
  ∃ π τ : Equiv.Perm (Fin n), A = (longChain n).image (fun a => (π a.1, τ a.2))

end FlexMargin


