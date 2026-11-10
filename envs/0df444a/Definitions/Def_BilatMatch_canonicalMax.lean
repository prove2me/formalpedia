-- Prove2me | Definitions.Def_BilatMatch_canonicalMax
-- name    : BilatMatch_canonicalMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:08:07.00421+00:00
-- url     : https://prove2.me/theorems/d81b8a98-cb26-4d06-a6f4-d7309ba8743a
-- title:
--   Canonical first-best matching $M^*$ and first-best cap $\kappa_{e,\omega}$
-- statement:
--   Given a weight on matchings, the **canonical maximizer** is the matching in $\mathcal F$ that maximizes the weight, has the fewest edges among maximizers, and among those comes first in a fixed, report-independent order. The **canonical first-best matching** $M^*(\theta)$ uses the gains $\sum_{(i,j)\in M}(v_i-c_j)$.
--
--   For an edge $e=(i,j)$ and residual profile $\omega=\theta_{-ij}$ the **first-best cap** is
--   $$\kappa_{e,\omega}(v)=\{c:\ e\in M^*(v,c,\omega)\},$$
--   the seller reports at which the first-best matching selects $e$ when buyer $i$ reports $v$.
--
--   **Formalization Note** The fixed order is an injective rank on $\mathcal F$; for a finite family every strict order arises this way. The canonical maximizer is defined by its characterizing property.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), §3.1, p.8 (pdf p.10), and p.14 (pdf p.16)

import Mathlib
import Definitions.Def_BilatMatch_Market

open MeasureTheory

namespace BilatMatch

/-!
# Canonical maximizers: the first-best matching `M*` and the first-best cap `κ_{e,ω}`

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), §3.1, p.8 (pdf p.10), and p.14 (pdf p.16).

**Formalization Note** "Among the maximizers, choose one with the fewest edges, breaking remaining
ties by a fixed, report-independent order": the order is an injective rank on `F`
(`IsTieOrder`); every strict order on a finite `F` arises this way. `canonicalMax` is defined by its
characterizing property (`IsCanonicalMax`), which a market with finitely many agents and an
injective rank satisfies for exactly one matching. These objects are used for finite markets.
-/

variable {B S : Type*}

/-- A fixed, report-independent tie-breaking order on `F`: an injective rank (smaller is
preferred). -/
def IsTieOrder (I : Market B S) (rank : Set (B × S) → ℕ) : Prop := Set.InjOn rank I.family

/-- `M` is the canonical maximizer of the weight `w` over `F`: it maximizes `w`, has the fewest
edges among maximizers, and the smallest rank among maximizers with that number of edges. -/
def IsCanonicalMax (I : Market B S) (rank : Set (B × S) → ℕ) (w : Set (B × S) → ℝ)
    (M : Set (B × S)) : Prop :=
  M ∈ I.family ∧ (∀ M' ∈ I.family, w M' ≤ w M) ∧
    (∀ M' ∈ I.family, w M' = w M → M.ncard ≤ M'.ncard) ∧
    (∀ M' ∈ I.family, w M' = w M → M'.ncard = M.ncard → rank M ≤ rank M')

/-- The canonical maximizer of `w` (the unique matching with `IsCanonicalMax`, when it exists). -/
noncomputable def canonicalMax (I : Market B S) (rank : Set (B × S) → ℕ)
    (w : Set (B × S) → ℝ) : Set (B × S) :=
  Classical.epsilon (IsCanonicalMax I rank w)

/-- The canonical first-best matching `M*(θ)` (p.8): among maximum-GFT matchings, the one with the
fewest edges, remaining ties broken by `rank`. -/
noncomputable def firstBestMatching (I : Market B S) (rank : Set (B × S) → ℕ)
    (θ : Profile B S) : Set (B × S) :=
  canonicalMax I rank fun M => matchingGFT M θ

/-- The first-best cap `κ_{e,ω}(v) = {c : e ∈ M*(v, c, ω)}` (p.8): the seller reports at which the
first-best matching selects `e = (i, j)` when buyer `i` reports `v` and the other agents report as
in the residual profile `ω` (its `i`- and `j`-coordinates are ignored). -/
noncomputable def firstBestCap (I : Market B S) (rank : Set (B × S) → ℕ) (e : B × S)
    (ω : Profile B S) (v : ℝ) : Set ℝ :=
  {c | e ∈ firstBestMatching I rank (updateSeller (updateBuyer ω e.1 v) e.2 c)}

end BilatMatch


