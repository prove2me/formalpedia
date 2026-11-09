-- Prove2me | Definitions.Def_MinSumFPT_conflictGraph
-- name    : MinSumFPT_conflictGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:20:05.149442+00:00
-- url     : https://prove2.me/theorems/aef3785a-9703-4584-93bb-eae1b3c91423
-- title:
--   Stage 3: the sets $L_i$ of (27), their revision, and the conflict graph $K$
-- statement:
--   In the setting of Stage 3 (a clustering with estimates as in Hypothesis 1, $\alpha=5$), let
--
--   $$
--   L_i=\{p\in A:\ d(p,\hat\mu_{C_i})<\gamma^{-1}\,\widehat{\widehat{\Delta}}_{C_i}\} \tag{27}
--   $$
--
--   be the set of $\gamma^{-1}$-close points of $C_i$. Then the sets are revised: for all pairs $i,j$ with $\widehat{|C_j|}<\beta\,\widehat{|C_i|}$, in non-increasing order of size, $L_i\cap L_j$ is removed from $L_j$. The **conflict graph** $K$ on the clusters joins $i\ne j$ iff the revised sets satisfy $L_i\cap L_j\ne\emptyset$.
--
--   Stage 3 assigns the points of each connected component of $K$ by a MAX $h$-CUT computation. Lemma 24 shows that clusters in one component have comparable sizes and nearby centers.
--
--   **Formalization Note** A pair is processed only when $\widehat{|C_i|}>\widehat{|C_j|}$, so in that order $L_i$ is final when it is used. The final sets therefore satisfy $L_j=L_j^{(27)}\setminus\bigcup_{i:\widehat{|C_j|}<\beta\widehat{|C_i|}}L_i$, which is computed by $k$ rounds of this recursion.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), §2.5, Eq. (27), p.35, and the revision and the graph K, p.36

import Mathlib
import Definitions.Def_MinSumFPT_labD

open scoped Classical

namespace MinSumFPT

/-!
# Stage 3: the γ⁻¹-close sets L_i of (27), their revision, and the conflict graph K

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), §2.5, pp.35–36: L_i = {p ∈ A : d(p, µ̂_{C_i}) < γ⁻¹ ⋅ Δ̂̂_{C_i}} (27); "For all pairs of
clusters i, j with |Ĉ_j| < β ⋅ |Ĉ_i|, in lexicographic order of non-increasing size, remove L_i ∩ L_j
from L_j"; K connects i and j iff L_i ∩ L_j ≠ ∅.

This module bundles `closeSet`, `revSetAux`, `revSet` and `conflictGraph`.

**Formalization Note.** Δ̂̂_{C_i} is (13) (`dblHat`, α = 5). A pair (i, j) is processed only when
|Ĉ_i| > |Ĉ_j|, and in non-increasing size order all pairs (i′, i) are processed before (i, j); so
when L_i is used it is final, the sets only shrink, and the final sets satisfy
L_j = L_j^{(27)} ∖ ⋃_{i : |Ĉ_j| < β|Ĉ_i|} L_i. `revSetAux t` computes this recursion with `t` rounds;
a chain i₁, i₂, … with |Ĉ_{i_{m+1}}| < β|Ĉ_{i_m}| (β < 1) has strictly decreasing sizes, so has at
most `k` clusters, and `k` rounds reach the final sets (`revSet`). -/

/-- `L_i` of (27): the points `p` with `d(p, µ̂_{C_i}) < γ⁻¹ ⋅ Δ̂̂_{C_i}`. -/
noncomputable def closeSet {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ : ℝ) (E : Estimates n k)
    (i : Fin k) : Finset (Fin n) :=
  Finset.univ.filter (fun p => d p (E.muHat i) < γ⁻¹ * dblHat ε γ E i)

/-- `t` rounds of the revision `L_j ← L_j^{(27)} ∖ ⋃_{i : |Ĉ_j| < β|Ĉ_i|} L_i`. -/
noncomputable def revSetAux {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k) :
    ℕ → Fin k → Finset (Fin n)
  | 0 => closeSet d ε γ E
  | t + 1 => fun j => closeSet d ε γ E j \
      (Finset.univ.filter (fun i => E.chat j < β * E.chat i)).biUnion (revSetAux d ε γ β E t)

/-- The revised sets `L_j` (after the whole revision). -/
noncomputable def revSet {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (j : Fin k) : Finset (Fin n) :=
  revSetAux d ε γ β E k j

/-- The conflict graph `K` on the clusters: `i ≠ j` adjacent iff `L_i ∩ L_j ≠ ∅` (revised sets). -/
noncomputable def conflictGraph {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ)
    (E : Estimates n k) : SimpleGraph (Fin k) :=
  SimpleGraph.fromRel (fun i j => (revSet d ε γ β E i ∩ revSet d ε γ β E j).Nonempty)

end MinSumFPT


