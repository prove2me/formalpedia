-- Prove2me | Definitions.Def_FlexMargin_windowCount
-- name    : FlexMargin_windowCount
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:39:52.772184+00:00
-- url     : https://prove2.me/theorems/a40bd4e7-73f4-4395-aca7-49bf58b54790
-- title:
--   Products of a category in a sequence of a long chain
-- statement:
--   In a long chain the products, read along the chain, form a cycle $b_{\tau(1)},b_{\tau(2)},\dots,b_{\tau(n)}$. A **sequence of length $k$** is a set of $k$ consecutive products on this cycle, wrapping around (for example $\{b_{\tau(n)},b_{\tau(1)},\dots,b_{\tau(k-1)}\}$). This definition counts how many products of a given category (high or low profit) a sequence contains.
--
--   Lemma 3 and Claims A–B find sequences with prescribed numbers of high and low profit products; they drive the comparison of long chains in Proposition 1.
--
--   **Formalization Note** The sequence starting at position $s$ is $\tau(s),\tau(s+1),\dots$ with indices modulo $n$.
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), Appendix A, proof of Proposition 1, p. 46

import Mathlib

namespace FlexMargin

/-- **Number of products of a category in a "sequence of length k" of a long chain.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), Appendix A, proof of Proposition 1, p. 46: "Consider a long chain with n/2 low profit products
and n/2 high profit products, where n is an even integer. We call a consecutive sequence of k product
nodes a sequence of length k", with the sequences "S1 = {1,2,3,...,2k+1}, S2 = {2,3,4,...,2k+2}, ...,
and Sn = {n,1,2,...,2k}" (p. 46), i.e. windows taken cyclically.

For the long chain relabelled by the product permutation `τ` (`FlexMargin.IsLongChain`), the product
nodes in chain order are `τ 0, τ 1, …, τ (n-1)` (plant `π i` is adjacent to `τ i` and `τ (i+1)`).
`windowCount cat τ s len c` is the number of `j < len` such that the product `τ (s + j mod n)` has
category `c` (`c = 1`: high profit, `c = 0`: low profit).

**Formalization Note.** `(finRotate n)^j s` is `s + j mod n`, so windows wrap around the cycle as
on p. 46. Lengths used by the statements are at most `n`, so the window lists distinct products. -/
def windowCount {n : ℕ} (cat : Fin n → Fin 2) (τ : Equiv.Perm (Fin n)) (s : Fin n) (len : ℕ)
    (c : Fin 2) : ℕ :=
  ((Finset.range len).filter (fun j => cat (τ (((finRotate n) ^ j) s)) = c)).card

end FlexMargin


