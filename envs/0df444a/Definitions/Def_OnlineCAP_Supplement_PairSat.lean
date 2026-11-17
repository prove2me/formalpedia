-- Prove2me | Definitions.Def_OnlineCAP_Supplement_PairSat
-- name    : OnlineCAP_Supplement_PairSat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:20:25.344689+00:00
-- url     : https://prove2.me/theorems/a203ce44-6620-43c0-b1d2-934636170f96
-- title:
--   Terminal pair satisfied by a link set; valid pair sequences and the offline optimum with node arrivals
-- statement:
--   Let $G=(V,E)$ be the base multigraph on $V=\{v_0,\dots,v_{n-1}\}$, $k\ge1$, and $F$ a set of links. A terminal pair $(s,t)$ is **satisfied** by $F$ if $s$ and $t$ are $(k+1)$-edge-connected in $G+F$, that is, every vertex set $C$ with $s\in C$, $t\notin C$ satisfies
--
--   $$|\delta_E(C)|+|\delta_F(C)|\ge k+1.$$
--
--   A sequence of terminal pairs is **valid** for the link set $L$ if every pair consists of two distinct vertices and is satisfied by $L$. The **offline optimum** $\mathrm{OPT}(s)$ of a sequence $s$ is the least cost $\sum_{\ell\in F}c(\ell)$ of a link set $F\subseteq L$ satisfying every pair of $s$.
--
--   These are the requests and the benchmark of connectivity augmentation with node arrivals (Problem 2.3). For a cycle ($k=2$) a pair is satisfied when it is 3-edge-connected in the cycle plus the links.
--
--   **Formalization Note** Edges and links are counted separately in a cut. The optimum is a real infimum; for a valid sequence the set of feasible link sets contains $L$, so it is a minimum.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Problem 2.3, p.9 (PDF p.9); §5.1, p.22

import Mathlib
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_edgeCut

namespace OnlineCAP.Supplement

/-- **A terminal pair satisfied by a link set (node arrivals).** Hathcock–Subramanian–Umboh–Zlatin,
*Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set*, manuscript of
Nov. 3, 2026 (sha256 e3b9cb64…), Problem 2.3, p.9 (PDF p.9): "We must irrevocably purchase links so
that the vertices st and τt are (k + 1)-edge-connected in the augmented graph. That is, at the end
of time step t, the cumulative purchased link set Ft ⊆ L must be such that every cut C separating
st and τt has |δE∪Ft(C)| ≥ k + 1."

`PairSat ends k F (s, t)`: every vertex set `C` with `s ∈ C`, `t ∉ C` is crossed by at least
`k + 1` edges of the base multigraph and links of `F` together.

**Formalization Note.** Edges and links are counted separately (a link parallel to an edge adds one
to the cut). For the cycle (`k = 2`) this is "3-edge-connected in R + F" of §5.1, p.22, in cut
form. Separating `C` and `Cᶜ` give the same condition, so the orientation of the pair is
immaterial. -/
def PairSat {n : ℕ} {E : Type} [Fintype E] (ends : E → Sym2 (Fin n)) (k : ℕ)
    (F : Finset (Sym2 (Fin n))) (p : Fin n × Fin n) : Prop := by
  classical
  exact ∀ C : Finset (Fin n), p.1 ∈ C → p.2 ∉ C →
    k + 1 ≤ (edgeCut ends C).card + (F.filter (fun ℓ => crosses ℓ C)).card

/-- **Valid sequence of terminal pairs.** Problem 2.3, p.9: each request is a pair of distinct
vertices (`(st, τt) ∈ (V choose 2)`), and it can be satisfied with the available links `L`. -/
def NodeValid {n : ℕ} {E : Type} [Fintype E] (ends : E → Sym2 (Fin n)) (k : ℕ)
    (L : Finset (Sym2 (Fin n))) (s : List (Fin n × Fin n)) : Prop :=
  ∀ p ∈ s, p.1 ≠ p.2 ∧ PairSat ends k L p

/-- **The offline optimum with node arrivals.** The minimum cost `∑_{ℓ ∈ F} c(ℓ)` of a link set
`F ⊆ L` satisfying every pair of `s` (a real `sInf`; for a valid sequence the set contains `L` and
the value is the minimum). -/
noncomputable def OPTnode {n : ℕ} {E : Type} [Fintype E] (ends : E → Sym2 (Fin n)) (k : ℕ)
    (L : Finset (Sym2 (Fin n))) (c : Sym2 (Fin n) → ℝ) (s : List (Fin n × Fin n)) : ℝ :=
  sInf ((fun F : Finset (Sym2 (Fin n)) => ∑ ℓ ∈ F, c ℓ) ''
    {F | F ⊆ L ∧ ∀ p ∈ s, PairSat ends k F p})

end OnlineCAP.Supplement


