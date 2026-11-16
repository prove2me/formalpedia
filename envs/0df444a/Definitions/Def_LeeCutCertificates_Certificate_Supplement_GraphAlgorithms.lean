-- Prove2me | Definitions.Def_LeeCutCertificates_Certificate_Supplement_GraphAlgorithms
-- name    : LeeCutCertificates_Certificate_Supplement_GraphAlgorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:01:33.470395+00:00
-- url     : https://prove2.me/theorems/fc9890a3-6649-47bf-b399-c442f25f8006
-- title:
--   Support forests, complete cut output and weak skeletons
-- statement:
--   For a nonnegative weighted graph $G$, its positive support joins distinct vertices of strictly positive aggregate pair capacity. A correct learned forest is acyclic, uses support edges, has exactly the support's reachability relation, and records its edge weights. A component partition consists of the exact nonempty connected-component blocks, including isolated vertices.
--
--   A complete cut answer contains a value, all oriented minimum-cut shores and, when the value is zero, those component blocks. Its correctness requires exact equality with the minimum-cut family and the nonempty proper union characterization. A **weak skeleton** $H$ satisfies
--
--   $$\lambda(H)\ge\lambda(G)>0,\qquad c_H(S^*)\le\tfrac54\lambda(G)\quad\text{for every minimum-cut shore }S^*.$$
--
--   The graph output stores its own finite edge-record count. It need not be a subgraph of $G$. A minimizing two-respecting answer is an eligible shore whose actual cut weight is at most that of every eligible shore.
--
--   **Formalization Note** All correctness conditions are predicates on raw output data. Output types contain no correctness or query-budget assumptions. Graph primitives and nonnegativity are the immutable base interfaces.
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Definition 3, printed p.6 (PDF p.7); Theorem 4, printed p.7 (PDF p.8); Lemma 9, printed pp.17–18 (PDF pp.18–19); §8 and Theorem 19, printed pp.23–25 (PDF pp.24–26)

import Definitions.Def_LeeCutCertificates_Certificate_CutQueries
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_OraclePrograms
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_RootedTrees

set_option autoImplicit false
open SunMinCut.Cactus
open Classical

namespace LeeCutCertificates.Certificate.Supplement

abbrev ExplicitGraph (n : ℕ) := Σ m : ℕ, Graph n m

/-- Positive aggregate capacities, rather than the mere presence of an edge record. -/
noncomputable def positiveSupport {n m : ℕ} (G : Graph n m) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => 0 < pairWeight G u v

structure ForestOutput (n : ℕ) where
  forest : SimpleGraph (Fin n)
  edgeWeight : Fin n → Fin n → ℝ

/-- A maximal support forest together with the weights of its learned edges. -/
def CorrectForest {n m : ℕ} (G : Graph n m) (o : ForestOutput n) : Prop :=
  o.forest.IsAcyclic ∧ o.forest ≤ positiveSupport G ∧
    (∀ u v, o.forest.Reachable u v ↔ (positiveSupport G).Reachable u v) ∧
    ∀ u v, o.forest.Adj u v → o.edgeWeight u v = pairWeight G u v

/-- Explicit component blocks, including singleton isolated vertices. -/
def ComponentPartition {n m : ℕ} (G : Graph n m) (P : Finset (Finset (Fin n))) : Prop :=
  P.biUnion id = Finset.univ ∧ (∀ A ∈ P, A.Nonempty) ∧
    (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
    ∀ u v, (positiveSupport G).Reachable u v ↔ ∃ A ∈ P, u ∈ A ∧ v ∈ A

/-- Includes the explicit list of all oriented shores and zero-case component blocks. -/
structure AllCutsOutput (n : ℕ) where
  value : ℝ
  cuts : Finset (Finset (Fin n))
  zeroComponents : Finset (Finset (Fin n))

/-- Complete equality of the reported set, with the zero-case partition and union formula. -/
def CorrectAllCuts {n m : ℕ} (G : Graph n m) (o : AllCutsOutput n) : Prop :=
  o.value = lam G ∧ (∀ S, S ∈ o.cuts ↔ IsMinCut G S) ∧
    (lam G = 0 → ComponentPartition G o.zeroComponents ∧
      ∀ S, IsMinCut G S ↔ ∃ A : Finset (Finset (Fin n)),
        A ⊆ o.zeroComponents ∧ A.Nonempty ∧ A ≠ o.zeroComponents ∧ S = A.biUnion id)

/-- Definition 3: both inequalities apply to the actual explicit output, for every optimum. -/
def AllMinCutSkeleton {n m : ℕ} (G : Graph n m) (H : ExplicitGraph n) : Prop :=
  Nonnegative H.2 ∧ 0 < lam G ∧ lam G ≤ lam H.2 ∧
    ∀ S, IsMinCut G S → cutw H.2 S ≤ (5 / 4 : ℝ) * lam G

/-- A minimizing two-respecting shore, with attainment rather than just an infimum. -/
def CorrectTwoRespecting {n m : ℕ} (G : Graph n m) (T : RootedTree n)
    (S : Finset (Fin n)) : Prop :=
  T.TwoRespects S ∧ ∀ U, T.TwoRespects U → cutw G S ≤ cutw G U

end LeeCutCertificates.Certificate.Supplement


