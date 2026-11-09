-- Prove2me | Definitions.Def_ProxGapTight_Codim2
-- name    : ProxGapTight_Codim2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:52.582842+00:00
-- url     : https://prove2.me/theorems/3a539d75-a1f5-4d9f-9f16-527c8cfb9b07
-- title:
--   Codimension-two subspaces $\mathrm{Gr}(m-2,\mathbb F_Q^m)$
-- statement:
--   For a field $K$ (in the paper $K=\mathbb F_Q$) and $m\ge 0$, $\mathrm{Gr}(m-2,K^m)$ is the set of subspaces $W\subseteq K^m$ of codimension two, i.e. of dimension $m-2$.
--
--   Their incidence vectors span the ambient code $U_m$.
--
--   **Formalization Note** The dimension condition is written $\dim W+2=m$, so for $m<2$ the set is empty. For finite $K$ the set is finite.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), §3.1, p.7

import Mathlib

namespace ProxGapTight

/-- The **Grassmannian** `Gr(m − 2, F_Q^m)` of codimension-two subspaces of `F_Q^m`, Kominers,
Thaler, Zheng, manuscript (Sept. 2026), §3.1, p.7.

**Formalization Note.** `F_Q` is any field `K`; codimension two is written
`finrank W + 2 = m` to avoid natural-number subtraction (for `m < 2` the type is empty). -/
def Codim2 (K : Type) [Field K] (m : ℕ) : Type :=
  {W : Submodule K (Fin m → K) // Module.finrank K W + 2 = m}

instance (K : Type) [Field K] [Fintype K] (m : ℕ) : Finite (Codim2 K m) := by
  unfold Codim2
  infer_instance

noncomputable instance (K : Type) [Field K] [Fintype K] (m : ℕ) : Fintype (Codim2 K m) :=
  Fintype.ofFinite _

end ProxGapTight


