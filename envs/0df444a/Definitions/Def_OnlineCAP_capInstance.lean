-- Prove2me | Definitions.Def_OnlineCAP_capInstance
-- name    : OnlineCAP_capInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:57.246415+00:00
-- url     : https://prove2.me/theorems/209236cc-01b3-43d3-af5d-f8f2f9450e0a
-- title:
--   OWCAP with cut arrivals as online hitting set
-- statement:
--   **Online weighted connectivity augmentation with cut arrivals (OWCAP).** Given a multigraph $G$ on $V=\{v_0,\dots,v_{n-1}\}$, an integer $k$, a set $L$ of links (pairs of vertices) and costs $c$ on the links, the $k$-cuts $C_1,C_2,\dots$ of $G$ arrive online; after the arrival of $C_t$ the purchased link set $F_t\subseteq L$ must cross every $C_i$, $i\le t$, and the goal is to keep $\sum_{\ell\in F_t}c(\ell)$ small.
--
--   As an instance of online hitting set: the ground set is $L$, the costs are $c$, the admissible requests are the $k$-cuts of $G$, and the links hitting a cut $C$ are those in $\delta_L(C)$. The unweighted problem OCAP is the case $c\equiv1$.
--
--   **Formalization Note** Links are unordered pairs (`Sym2 (Fin n)`); the theorems require $L\subseteq\binom V2$ (no pair $\{v,v\}$).
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Problem 1.2, p.2; Problem 2.1, p.9

import Mathlib
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_edgeCut
import Definitions.Def_OnlineCAP_IsKCut
import Definitions.Def_OnlineCAP_OnlineHSInstance

namespace OnlineCAP

/-- **OWCAP with cut arrivals as an online hitting-set instance.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Problem 1.2, p.2, and
Problem 2.1, p.9 (PDF p.9): "A sequence of k-cuts C1, C2, . . . of G arrive online one at a time.
… our cumulative purchased link set Ft ⊆ L must satisfy |δFt(Ci)| ≥ 1 for all i ≤ t. The
objective … is to minimize the total cost ∑_{ℓ∈Ft} c(ℓ)."

Given the base multigraph `ends`, the connectivity `k`, the links `L` and the costs `c`, the
ground set is `L`, the admissible requests are the k-cuts of the base graph, and the links hitting
a cut `C` are those crossing `C`. The unweighted problem OCAP is the case `c ≡ 1`.

**Formalization Note.** Links are unordered pairs of vertices (`Sym2 (Fin n)`); the theorems
require `L ⊆ (V choose 2)` (no diagonal pair). A request is the cut `C` itself (a vertex set). -/
def capInstance {n : ℕ} {E : Type} [Fintype E] (ends : E → Sym2 (Fin n)) (k : ℕ)
    (L : Finset (Sym2 (Fin n))) (c : Sym2 (Fin n) → ℝ) :
    OnlineHSInstance (Sym2 (Fin n)) (Finset (Fin n)) where
  G := L
  c := c
  ok := IsKCut ends k
  cov := fun C => {ℓ | crosses ℓ C}

end OnlineCAP


