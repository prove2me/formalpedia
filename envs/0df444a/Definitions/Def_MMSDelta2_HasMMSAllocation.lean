-- Prove2me | Definitions.Def_MMSDelta2_HasMMSAllocation
-- name    : MMSDelta2_HasMMSAllocation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:09.671055+00:00
-- url     : https://prove2.me/theorems/94dbefd0-2273-4e22-bf90-89b9dce2bce1
-- title:
--   MMS allocations of an additive goods instance
-- statement:
--   Let $N=\{1,\dots,n\}$ be a set of agents and $M=\{1,\dots,m\}$ a set of goods, and let agent $i$ have the additive valuation $v_i(S)=\sum_{g\in S}v_i(g)$ with rational item values $v_i(g)$. The **maximin share** of agent $i$ is
--
--   $$\mathrm{MMS}_i=\max_{(P_1,\dots,P_n)\in\Pi_n(M)}\ \min_{j\in[n]} v_i(P_j),$$
--
--   where $\Pi_n(M)$ is the set of partitions of $M$ into $n$ (labelled, possibly empty) bundles. An **allocation** $(A_1,\dots,A_n)$ is a partition of $M$ into $n$ bundles, bundle $A_i$ going to agent $i$; it is an **MMS allocation** if $v_i(A_i)\ge\mathrm{MMS}_i$ for every agent $i$. The instance admits an MMS allocation if some allocation is an MMS allocation.
--
--   This is the property whose decision problem the mission studies.
--
--   **Formalization Note** $\mathrm{MMS}_i$ is the published `StrategicAlloc.CutChoose.mu` (that is, `LittleCharity.MMS.mms` over all maps from goods to $n$ bundle labels) of the real-valued copy of $v$, and allocations are the published `StrategicAlloc.RRFair.IsAllocation`: pairwise disjoint bundles whose union is all of $M$.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), §1, p.1 (PDF p.3): MMS_i and MMS allocation; additive valuations, §4, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_StrategicAlloc_CutChoose_Setting

namespace MMSDelta2

/-!
# MMS allocations of an additive goods instance

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), §1, p.1 (PDF p.3):
`MMS_i = max_{(P_1,…,P_n) ∈ Π_n(M)} min_{j ∈ [n]} v_i(P_j)`, and "An allocation `(A_1, …, A_n)` is
an MMS allocation if `v_i(A_i) ≥ MMS_i` for every `i ∈ N`"; additive valuations, p.11.

**Formalization Note.** An additive instance is `v : Fin n → Fin m → ℚ` (agent `i` values good `g`
at `v i g`, a bundle at the sum). `MMS_i` is the published `StrategicAlloc.CutChoose.mu` of the
real-valued copy, i.e. `LittleCharity.MMS.mms` over all labelled partitions of the goods into `n`
(possibly empty) bundles. An allocation is the published `StrategicAlloc.RRFair.IsAllocation`:
pairwise disjoint bundles covering all goods.
-/

/-- The item values of `v` as real numbers. -/
def realVal {n m : ℕ} (v : Fin n → Fin m → ℚ) : Fin n → Fin m → ℝ := fun i g => (v i g : ℝ)

/-- The additive instance `v` admits an MMS allocation (p.1). -/
def HasMMSAllocation {n m : ℕ} (v : Fin n → Fin m → ℚ) : Prop :=
  ∃ A : Fin n → Finset (Fin m), StrategicAlloc.RRFair.IsAllocation A ∧
    StrategicAlloc.CutChoose.IsApproxMMS 1 (realVal v) A

end MMSDelta2


