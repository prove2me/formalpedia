-- Prove2me | Definitions.Def_ProxGapTight_incVec
-- name    : ProxGapTight_incVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:48:59.168541+00:00
-- url     : https://prove2.me/theorems/3419f001-06b1-4ffd-ae0d-4ee6a98a82d6
-- title:
--   Incidence vector $u_W$
-- statement:
--   For a codimension-two subspace $W\subseteq K^m$, its **incidence vector** $u_W$ is indexed by the lines $\ell\in X$ of $K^m$:
--   $$
--   u_W(\ell)=\begin{cases}1,&\ell\subseteq W,\\ 0,&\text{otherwise.}\end{cases}
--   $$
--   Its weight is the number $e_m$ of lines in $W$.
--
--   The paper takes $u_W\in\mathbb F_p^X$; the same $0/1$ vector is also viewed in $\mathbb F_q^X$ for an extension field $\mathbb F_q$ when the code is extended to $\mathrm{span}_{\mathbb F_q}(U_m)$.
--
--   **Formalization Note** The entries lie in an arbitrary semiring $R$, so that both uses share one definition.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), §3.1, p.7

import Mathlib
import Definitions.Def_ProxGapTight_Lines
import Definitions.Def_ProxGapTight_Codim2

namespace ProxGapTight

/-- The **incidence vector** `u_W` of a codimension-two subspace `W ⊆ F_Q^m`, Kominers, Thaler,
Zheng, manuscript (Sept. 2026), §3.1, p.7: indexed by the lines `ℓ ∈ X`, with `u_W(ℓ) = 1` if
`ℓ ⊆ W` and `0` otherwise.

**Formalization Note.** The values lie in any semiring `R`: `R = ZMod p` gives the paper's
`u_W ∈ F_p^X`, and a field `F` of characteristic `p` gives the same vector viewed in `F^X`
(used for `span_{F_q}(U_m)`, pp.9–13). Containment `ℓ ⊆ W` is the submodule order, decided
classically. -/
noncomputable def incVec (R : Type) [Semiring R] {K : Type} [Field K] {m : ℕ}
    (W : Codim2 K m) : Lines K m → R := by
  classical
  exact fun ℓ => if ℓ.1 ≤ W.1 then 1 else 0

end ProxGapTight


