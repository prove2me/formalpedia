-- Prove2me | Definitions.Def_SFMQueryLower_EmptyMin_Supplement_HiddenPermutation
-- name    : SFMQueryLower_EmptyMin_Supplement_HiddenPermutation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:26:42.193799+00:00
-- url     : https://prove2.me/theorems/9d9de3de-dad6-4587-8e08-39403d352d87
-- title:
--   The $\mathrm{HiddenPermutation}_k$ prefix-length oracle
-- statement:
--   An instance of $\mathrm{HiddenPermutation}_k$ consists of an unknown string $z\in\{0,1\}^k$ and an unknown permutation $\sigma$ of $[k]$. A query is a string $x\in\{0,1\}^k$, and the oracle replies with
--   $$\operatorname{prefix-len}_{z,\sigma}(x):=\max\{t\in\{0,\dots,k\}: x_{\sigma(j)}=z_{\sigma(j)}\text{ for every }j\in[t]\},$$
--   the length of the longest prefix, in the order $\sigma(1),\dots,\sigma(k)$, on which $x$ agrees with $z$. It equals $k$ exactly when $x=z$.
--
--   Prefix queries are the oracle access in the Afshani et al. lower bound for the hidden-permutation problem, which Appendix C transfers to the CGJS family.
--
--   **Formalization Note** Coordinates are `Fin k` (0-based) and bits are `Bool` (`true` = 1); "$j\in[t]$" becomes `j.val < t`. The maximum is written as the supremum of the qualifying values in $\{0,\dots,k\}$; $t=0$ always qualifies, so this is the maximum.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), §C.1, printed p. 21 / PDF p. 22

import Mathlib

set_option autoImplicit false

namespace SFMQueryLower.EmptyMin.Supplement

/-- §C.1, the `HiddenPermutation_k` oracle. An instance is a hidden string `z ∈ {0,1}^k`
(`Fin k → Bool`, `true` = 1) and a hidden permutation `σ` of `[k]`. For a query `x`,
`prefixLen z σ x = max {t ∈ {0, …, k} : x_{σ(j)} = z_{σ(j)} for every j ∈ [t]}`.
Coordinates are 0-based, so `j ∈ [t]` becomes `j.val < t`. Since `t = 0` always qualifies,
the supremum over the filtered range is that maximum. -/
def prefixLen {k : ℕ} (z : Fin k → Bool) (σ : Equiv.Perm (Fin k)) (x : Fin k → Bool) : ℕ :=
  ((Finset.range (k + 1)).filter
    (fun t => ∀ j : Fin k, j.val < t → x (σ j) = z (σ j))).sup id

end SFMQueryLower.EmptyMin.Supplement


