-- Prove2me | Definitions.Def_SatisfiableOrderingCSP_Optimal_RichGames
-- name    : SatisfiableOrderingCSP_Optimal_RichGames
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:46:38.3292+00:00
-- url     : https://prove2.me/theorems/b4452d2e-a8bb-430d-af9b-8c641239d8af
-- title:
--   Rich two-to-one games and encoded ordering-gap reductions
-- statement:
--   A two-to-one game has a bipartite multigraph with a positive number of edge occurrences and no isolated vertices, a positive even left alphabet N, a right alphabet N/2, and exactly two preimages of every right label on every edge. Its value is the maximum satisfied edge fraction. Richness requires that at each left vertex the unlabeled partition into pairs induced by a uniformly random incident edge is uniform over all pair partitions. Fiber names need not be uniformly distributed. The rich-games conjecture asserts, for every sigma>0, a fixed positive even alphabet with gap NP-hardness of value one versus at most sigma. Both this conjecture and the target ordering gap use the published generic reduction definition and explicit finite encodings. The target requires unweighted repeated-constraint output, retains distinct arguments, and restricts predicates only as supplied by the theorem. No disjointness condition is added for overlapping thresholds.
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission (not an acceptance claim), sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc; citation_basis: published; Conjecture 1, §7.1 and Theorem 7.1; pp. 39–40 (PDF 42–43)

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Computation
import Definitions.Def_OptInapprox_MaxCut_UGC

open scoped BigOperators

namespace SatisfiableOrderingCSP.Optimal
noncomputable section
attribute [local instance] Classical.propDecidable

def TwoToOne {N : ℕ} (π : Fin N → Fin (N/2)) : Prop :=
  ∀ b, (Finset.univ.filter fun a => π a = b).card = 2

def fiberPartition {N : ℕ} (π : Fin N → Fin (N/2)) :
    Finset (Finset (Fin N)) :=
  Finset.univ.image (fun b => Finset.univ.filter fun a => π a = b)

def pairPartitions (N : ℕ) : Finset (Finset (Finset (Fin N))) :=
  (Finset.univ.filter (fun π : Fin N → Fin (N/2) => TwoToOne π)).image fiberPartition

structure TwoOneGame where
  alphabet : ℕ
  positive : 0 < alphabet
  even : Even alphabet
  leftSize : ℕ
  rightSize : ℕ
  edges : ℕ
  edges_pos : 0 < edges
  left : Fin edges → Fin leftSize
  right : Fin edges → Fin rightSize
  projection : Fin edges → Fin alphabet → Fin (alphabet/2)
  two_to_one : ∀ e, TwoToOne (projection e)
  left_incident : ∀ u, ∃ e, left e = u
  right_incident : ∀ v, ∃ e, right e = v

def TwoOneGame.Rich (G : TwoOneGame) : Prop :=
  ∀ u P, P ∈ pairPartitions G.alphabet →
    ((Finset.univ.filter fun e => G.left e = u ∧ fiberPartition (G.projection e) = P).card : ℝ) /
      (Finset.univ.filter fun e => G.left e = u).card =
      1 / ((pairPartitions G.alphabet).card : ℝ)

def TwoOneGame.score (G : TwoOneGame)
    (L : Fin G.leftSize → Fin G.alphabet) (R : Fin G.rightSize → Fin (G.alphabet/2)) : ℝ :=
  (∑ e, if G.projection e (L (G.left e)) = R (G.right e) then 1 else 0) / (G.edges : ℝ)

def TwoOneGame.value (G : TwoOneGame) : ℝ :=
  sSup {r | ∃ L R, r = G.score L R}

def TwoOneGame.encode (G : TwoOneGame) : List Bool :=
  List.replicate (G.leftSize + G.rightSize) true ++ [false] ++
  [G.alphabet,G.leftSize,G.rightSize,G.edges].flatMap encodeNat ++
  (List.finRange G.edges).flatMap fun e =>
    encodeNat (G.left e).val ++ encodeNat (G.right e).val ++
      (List.finRange G.alphabet).flatMap fun a => encodeNat (G.projection e a).val

def RichGamesConjecture : Prop :=
  ∀ σ : ℝ, 0 < σ → ∃ N : ℕ, 0 < N ∧ Even N ∧
    OptInapprox.MaxCut.GapNPHard TwoOneGame.encode
      (fun G => G.alphabet = N ∧ G.Rich ∧ G.value = 1)
      (fun G => G.alphabet = N ∧ G.Rich ∧ G.value ≤ σ)

def OrderingGapHard (allowed : Predicate → Prop) (s : ℝ) : Prop :=
  OptInapprox.MaxCut.GapNPHard RationalInstance.encode
    (fun I => I.instanceData.Unweighted ∧
      (∀ c, allowed (I.instanceData.constraint c).predicate) ∧ I.instanceData.value = 1)
    (fun I => I.instanceData.Unweighted ∧
      (∀ c, allowed (I.instanceData.constraint c).predicate) ∧ I.instanceData.value ≤ s)

end
end SatisfiableOrderingCSP.Optimal


