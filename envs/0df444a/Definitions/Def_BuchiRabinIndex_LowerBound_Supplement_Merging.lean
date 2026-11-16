-- Prove2me | Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Merging
-- name    : BuchiRabinIndex_LowerBound_Supplement_Merging
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:50:39.010143+00:00
-- url     : https://prove2.me/theorems/c1dc1d16-36f1-4fea-8141-c1f0098f26c5
-- title:
--   Reachable Rabin-pair merging and its attainable indices
-- statement:
--   Let $B$ be a Büchi automaton on the published NBW carrier, and let $I_d:T^{(n)}\to I$ be a map to a finite colour set. For each name $x$, define $A_x$ and $R_x$ to consist of actual history-tree transitions with reachable source at which $x$ is accepting and unstable, respectively. Define the merged pair by
--   $$A_i^{I_d}=\bigcup_{I_d(x)=i} A_x,\qquad R_i^{I_d}=\bigcup_{I_d(x)=i} R_x.$$
--   Both unions range over every name in the class, even names whose individual accepting set is empty. Only colours in the image of $I_d$ are used, and exactly classes with empty merged accepting component are omitted. The condition is a finite set of pairs of sets of transitions. It changes neither history states nor the partial successor. The reduced condition uses $I_d=I_c$ at $n=|Q|$.
--
--   Coexistence-respecting means proper colouring of the published $G_n$. Universal correctness means language equality for every NBW with $n$ states, arbitrary initial and accepting subsets and finite alphabet.
--
--   Two sets of attainable natural indices are defined from this concrete construction. The full-input set records the pair counts of mergings correct for $F_n$. The uniform set records bounds for one merging correct for every $n$-state NBW, with the bound attained on $F_n$. Finite colour sets are enumerated as $\mathrm{Fin}\,k$ when quantifying over all mergings, which changes no partition or pair. Theorem 44 asserts that both sets have an attained least element $\chi(G_n)$. No existence or minimality claim is a field or hypothesis of these definitions.
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf, §2.4 and Remark 8, p. 9; Definition 22 and Remark 23, p. 20; Definition 43 and Theorem 44, pp. 29–30

import Definitions.Def_BuchiRabinIndex_LowerBound_Rabin
import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Flags

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Supplement
noncomputable section
open scoped Classical

/-- Original A and R on the reachable part, including only actual edges. -/
def originalPair {Q Sigma : Type} (B : NBW Q Sigma) (x : Node) :
    RabinPair (Edge Q Sigma) :=
  ({e | IsEdge B e ∧ Reachable B e.1 ∧ x ∈ acc B e},
   {e | IsEdge B e ∧ Reachable B e.1 ∧ x ∈ unst B e})

/-- Both unions include all names of the class, even those with empty A. -/
def mergedPair {Q Sigma I : Type} {n : ℕ} (B : NBW Q Sigma)
    (Id : Vertex n → I) (i : I) : RabinPair (Edge Q Sigma) :=
  ({e | ∃ x : Vertex n, Id x = i ∧ e ∈ (originalPair B x.val).1},
   {e | ∃ x : Vertex n, Id x = i ∧ e ∈ (originalPair B x.val).2})

/-- Remark 23: image colours only, with exactly the empty-A classes omitted. -/
def activeColours {Q Sigma I : Type} {n : ℕ} (B : NBW Q Sigma)
    (Id : Vertex n → I) : Finset I :=
  ((Finset.univ : Finset (Vertex n)).image Id).filter fun i =>
    (mergedPair B Id i).1.Nonempty

/-- Finite set of actual pairs, using the published RabinCondition convention. -/
def mergedCondition {Q Sigma I : Type} {n : ℕ} (B : NBW Q Sigma)
    (Id : Vertex n → I) : RabinCondition (Edge Q Sigma) :=
  (activeColours B Id).image (mergedPair B Id)

def reducedCondition {Q Sigma : Type} [Fintype Q] (B : NBW Q Sigma) :
    RabinCondition (Edge Q Sigma) := mergedCondition B (canonicalColour (Fintype.card Q))

/-- Ordinary proper colouring of the immutable coexistence graph. -/
def CoexistenceRespecting {I : Type} {n : ℕ} (Id : Vertex n → I) : Prop :=
  ∀ x y, (graph n).Adj x y → Id x ≠ Id y

/-- Correctness for every NBW of size n; no restrictions on initial/accepting sets. -/
def UniversallyCorrect {I : Type} {n : ℕ} (Id : Vertex n → I) : Prop :=
  ∀ (Q Sigma : Type) [Fintype Q] [Nonempty Q] [Fintype Sigma],
    Fintype.card Q = n → ∀ B : NBW Q Sigma,
      CorrectTransition B (mergedCondition B Id)

/-- Attainable indices of mergings correct on the specified full automaton.
Finite colour carriers can be relabelled as Fin k without changing any pair. -/
def fullIndices (n : ℕ) (hn : 1 ≤ n) : Set ℕ :=
  {m | ∃ (k : ℕ) (Id : Vertex n → Fin k),
    CorrectTransition (fullBuchi n hn) (mergedCondition (fullBuchi n hn) Id) ∧
    (mergedCondition (fullBuchi n hn) Id).card = m}

/-- A uniform bound for one merging correct on all n-state inputs, attained
already on F_n. The minimum in Theorem 44 is a minimum, not an empty infimum. -/
def uniformIndices (n : ℕ) (hn : 1 ≤ n) : Set ℕ :=
  {m | ∃ (k : ℕ) (Id : Vertex n → Fin k), UniversallyCorrect Id ∧
    (∀ (Q Sigma : Type) [Fintype Q] [Nonempty Q] [Fintype Sigma],
      Fintype.card Q = n → ∀ B : NBW Q Sigma, (mergedCondition B Id).card ≤ m) ∧
    (mergedCondition (fullBuchi n hn) Id).card = m}

end
end BuchiRabinIndex.LowerBound.Supplement


