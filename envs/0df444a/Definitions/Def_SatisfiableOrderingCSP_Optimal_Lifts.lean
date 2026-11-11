-- Prove2me | Definitions.Def_SatisfiableOrderingCSP_Optimal_Lifts
-- name    : SatisfiableOrderingCSP_Optimal_Lifts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:45:54.533372+00:00
-- url     : https://prove2.me/theorems/ce34ec4a-2a55-44d9-b943-907313d15595
-- title:
--   Sparse lifts, common increasing embeddings, and connected supports
-- statement:
--   A lift maps each new variable to an original variable and each new constraint occurrence to an original occurrence, preserving its predicate and argument order. Copying a local model means copying its singleton and joint probabilities along these maps. An increasing mixture is a finite real probability distribution on strictly increasing maps between finite ordered domains. Its pushforward uses one embedding sampled independently of the old tuple and applied to every coordinate of that tuple, with the same embedding law in all scopes. Connectedness of a coordinate's bipartite support graph is expressed by connectivity of supported values under replacements of one coordinate with all other coordinates fixed; these graphs have the same connected components. Regularized means sparse scopes, connected local supports, and a basic SDP realization with positive definite global centered covariance. Regularization is not part of basic LP or SDP feasibility.
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission (not an acceptance claim), sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc; citation_basis: published; §5.2, Theorem 6.1, Definition 6.5 and §7.2; pp. 26, 30, 32, 40 (PDF 29, 33, 35, 43)

import Definitions.Def_SatisfiableOrderingCSP_Optimal_LocalModel

open scoped BigOperators

namespace SatisfiableOrderingCSP.Optimal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A map of variables to originals and constraint occurrences to originals in argument order. -/
structure Lift (I J : Instance) where
  variableMap : Fin J.n → Fin I.n
  constraint : Fin J.m → Fin I.m
  arity : ∀ c, (J.constraint c).predicate.arity = (I.constraint (constraint c)).predicate.arity
  predicate : ∀ c, (J.constraint c).predicate = (I.constraint (constraint c)).predicate
  scope : ∀ c j, variableMap ((J.constraint c).scope j) =
    (I.constraint (constraint c)).scope (Fin.cast (arity c) j)

def Lift.Copies {I J : Instance} (L : Lift I J) {q : ℕ}
    (M : LocalModel I.scopes q) (M' : LocalModel J.scopes q) : Prop :=
  (∀ v a, M'.singleton v a = M.singleton (L.variableMap v) a) ∧
  ∀ c x, M'.joint c x = M.joint (L.constraint c) (fun j => x (Fin.cast (L.arity c).symm j))

/-- The sampling law is common to all scopes and independent of their tuples. -/
structure IncreasingMixture (q q' : ℕ) where
  size : ℕ
  weight : Fin size → ℝ
  probability : FuchsVdGraaf.IsProbDist weight
  embedding : Fin size → Fin q → Fin q'
  increasing : ∀ a, StrictMono (embedding a)

def IncreasingMixture.Pushes {n q q' : ℕ} {S : Scopes n}
    (F : IncreasingMixture q q') (M : LocalModel S q) (M' : LocalModel S q') : Prop :=
  (∀ v b, M'.singleton v b = ∑ a, F.weight a *
    ∑ x, if F.embedding a x = b then M.singleton v x else 0) ∧
  ∀ c y, M'.joint c y = ∑ a, F.weight a *
    ∑ x, if (∀ i, F.embedding a (x i) = y i) then M.joint c x else 0

/-- The location graph is the projection of the one-coordinate bipartite support graph.
Both have the same connectedness since every retained vertex has an incident edge. -/
def LocalModel.Connected {n q : ℕ} {S : Scopes n} (M : LocalModel S q) : Prop :=
  ∀ c i (a b : Fin q), 0 < M.singleton (S.scope c i) a →
    0 < M.singleton (S.scope c i) b →
    Relation.ReflTransGen (fun a b : Fin q =>
      ∃ x y, 0 < M.joint c x ∧ 0 < M.joint c y ∧ x i = a ∧ y i = b ∧
        ∀ j, j ≠ i → x j = y j) a b

def Regularized {n q : ℕ} {S : Scopes n} (M : LocalModel S q) : Prop :=
  S.Sparse ∧ M.Connected ∧ ∃ (V : SDPVectors M) (G : CovarianceMatrix n q),
    M.ExactCovariance G ∧ M.PositiveDefinite G ∧ V.CovarianceIs G

end
end SatisfiableOrderingCSP.Optimal


