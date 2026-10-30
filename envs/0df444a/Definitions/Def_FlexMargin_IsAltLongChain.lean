-- Prove2me | Definitions.Def_FlexMargin_IsAltLongChain
-- name    : FlexMargin_IsAltLongChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:37:34.911676+00:00
-- url     : https://prove2.me/theorems/eefef00d-bfa4-43c4-8267-29e48014ed92
-- title:
--   The alternate long chain design $\mathcal{AL}$
-- statement:
--   In a system with two product categories, high margin $P_H$ and low margin $P_L$, a design $\mathcal A$ is an **alternate long chain** if it is a long chain $\{(a_{\pi(j)},b_{\tau(i)}) : (a_j,b_i)\in\mathcal L\}$ in which consecutive products along the chain, $b_{\tau(i)}$ and $b_{\tau(i+1)}$ (indices modulo $n$), always have different margins. Equivalently, every plant produces exactly one high profit and one low profit product.
--
--   Figure 2(a) of the paper shows the case $n=4$: H, L, H, L on the standard chain. Theorem 3 says this design is worst-case optimal among long chains.
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §4, p. 20, and Appendix A, p. 44

import Mathlib
import Definitions.Def_FlexMargin_longChain

namespace FlexMargin

/-- **The alternate long chain design `𝒜ℒ`.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §4, p. 20: "Among this class of long chain designs with |SH| = |SL| = n/2, we are
particularly interested in a special design where the high profit products and low profit products
are assigned to the plants in an alternate manner, which we call the alternate long chain design
and is denoted as AL", and p. 44: "the specific structure of the alternate long chain that each
plant is connected to exactly one high profit product and one low profit product".

There are two categories, `cat i = 0` (low margin `P_L`) and `cat i = 1` (high margin `P_H`). A design
`A` is an alternate long chain if it is a long chain relabelled by permutations `π` (plants) and
`τ` (products), `A = {(π j, τ i) | (j, i) ∈ ℒ}`, such that consecutive products along the chain,
`τ i` and `τ (i + 1 mod n)`, always lie in different categories.

**Formalization Note.** Plant `π i` is adjacent exactly to products `τ i` and `τ (i+1)`, so the
alternation condition says each plant produces one high and one low profit product (p. 44). Figure
2(a) (n = 4, products H, L, H, L on the standard chain) is an instance with `π = τ = 1`. -/
def IsAltLongChain {n : ℕ} (cat : Fin n → Fin 2) (A : Finset (Fin n × Fin n)) : Prop :=
  ∃ π τ : Equiv.Perm (Fin n), A = (longChain n).image (fun a => (π a.1, τ a.2)) ∧
    ∀ i, cat (τ i) ≠ cat (τ (finRotate n i))

end FlexMargin


