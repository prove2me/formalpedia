-- Prove2me | Definitions.Def_InducedMinorDeletion1657_Main_Supplement_LocalBranching
-- name    : InducedMinorDeletion1657_Main_Supplement_LocalBranching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:15:07.770531+00:00
-- url     : https://prove2.me/theorems/96d37050-4dcd-489b-ad92-1de858fb55f7
-- title:
--   Local branching outputs, encoding, and all five guarantees
-- statement:
--   For a graph $G$ with $n$ labelled vertices, an entry is a quadruple $(Y,Z,A_1,A_2)$ of vertex sets. This is data only. The input encoding contains $G$ and the membership bits of $W$; a list of entries is encoded by its length followed by the four fixed-length subset encodings for each entry.
--
--   Given $|W|=q$, $\delta>0$, treewidth bound $t$, and constants $c_1,c_3$, the local-result predicate requires, for every entry: $Z\cap Y=\varnothing$; $A_1,A_2$ partition $V(G)\setminus(Y\cup Z)$ with no edges between them; and
--   $$|W\cap A_j|\le 2q/3,\qquad |Z|\le c_1q/(\log_2q)^3,\qquad \operatorname{tw}(G[A_j])\le c_3q/(\log_2q)^4\quad(j=1,2).$$
--   It also requires that every treewidth-$t$ modulator $S$ with $|S|\le q/\delta$ contain $Y$ for at least one entry. The common bound on output count and the exponential part of time is
--   $$B(c_2,\delta,q)=2^{c_2\delta^{-3}(\log_2q)^9}.$$
--
--   These predicates specify the full conclusion of Lemma 7.1, independently of the operational RAM execution predicate. The theorem uses them only for $q\ge q_0\ge2$, so the denominators are positive. Empty child subgraphs are permitted. Lists may repeat an entry; duplicates add no mathematical power and are charged in count and output time.
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 29 (PDF p. 30), Lemma 7.1 (i)–(v), with proof on p. 30 (PDF p. 31)

import Definitions.Def_InducedMinorDeletion1657_Main_Execution

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main.Supplement

/-- Data only; none of Lemma 7.1's guarantees is assumed by the output type. -/
structure LocalEntry (n : ℕ) where
  Y : Finset (Fin n)
  Z : Finset (Fin n)
  A₁ : Finset (Fin n)
  A₂ : Finset (Fin n)

/-- Length-prefixed list of quadruples, in the order Y,Z,A₁,A₂.
Each component is the base fixed-length membership-bit subset encoding. -/
noncomputable def localWords {n : ℕ} (L : List (LocalEntry n)) : List ℕ :=
  L.length :: L.flatMap (fun p =>
    subsetWords p.Y ++ subsetWords p.Z ++ subsetWords p.A₁ ++ subsetWords p.A₂)

/-- The input contains the graph followed by W's membership bits, and no modulator. -/
noncomputable def localInput (G : InputGraph) (W : Finset (Fin G.n)) : List ℕ :=
  graphWords G ++ subsetWords W

/-- The common cardinality/time exponential factor in Lemma 7.1. -/
noncomputable def localCount (c₂ δ : ℝ) (q : ℕ) : ℝ :=
  (2 : ℝ) ^ (c₂ * (δ⁻¹) ^ 3 * (logTwo (q : ℝ)) ^ 9)

/-- All five clauses of Lemma 7.1, printed p.29 / PDF p.30.
A₁,A₂ represent the induced subgraphs, and partition exactly the undeleted vertices. -/
def localResult (G : InputGraph) (W : Finset (Fin G.n)) (q t : ℕ)
    (δ c₁ c₃ : ℝ) (L : List (LocalEntry G.n)) : Prop :=
  (∀ p ∈ L,
    Disjoint p.Z p.Y ∧ Disjoint p.A₁ p.A₂ ∧
    p.A₁ ∪ p.A₂ = Finset.univ \ (p.Y ∪ p.Z) ∧
    (∀ u ∈ p.A₁, ∀ v ∈ p.A₂, ¬ G.graph.Adj u v) ∧
    (∀ A ∈ [p.A₁, p.A₂],
      ((W ∩ A).card : ℝ) ≤ 2 * (q : ℝ) / 3 ∧
      (width (G.graph.induce (↑A : Set (Fin G.n))) : ℝ) ≤
        c₃ * q / (logTwo (q : ℝ)) ^ 4) ∧
    (p.Z.card : ℝ) ≤ c₁ * q / (logTwo (q : ℝ)) ^ 3) ∧
  ∀ S : Finset (Fin G.n), modulator G.graph t S →
    (S.card : ℝ) ≤ (q : ℝ) / δ → ∃ p ∈ L, p.Y ⊆ S

end InducedMinorDeletion1657.Main.Supplement


