-- Prove2me | Definitions.Def_SatisfiableOrderingCSP_Optimal_Transformations
-- name    : SatisfiableOrderingCSP_Optimal_Transformations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:44:52.640308+00:00
-- url     : https://prove2.me/theorems/b91b797d-4c79-49d1-a782-b15391c6d370
-- title:
--   Two-order transformations, IDU-plus mixtures, and the framework constant
-- statement:
--   A combination has finitely many ordered blocks labeled IL, DL, IR, DR or U and a nonnegative real probability vector. Variables choose blocks independently; blocks use the left order, reversed left order, right order, reversed right order, or a uniform order, and are concatenated. Uniform relative orders in disjoint blocks are realized by restricting one uniform permutation, which gives independent uniform relative orders. A finite mixture samples the whole combination once. Its local payoff is the probability of a satisfying output pattern. Its guarantee is the minimum payoff over eligible local types, and alphaLR is the supremum of these guarantees over all finite mixtures with arbitrary real coefficients. Weak transformations specify normalized laws after making the left input the identity; general inputs are relabeled back. A per-constraint guarantee quantifies over every input size, input pair, and injective occurrence with the specified patterns.
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission (not an acceptance claim), sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc; citation_basis: published; Definitions 3.1, 3.3, 3.4, 4.2; pp. 13–14, 17 (PDF 16–17, 20)

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Ordering

open scoped BigOperators

namespace SatisfiableOrderingCSP.Optimal
noncomputable section
attribute [local instance] Classical.propDecidable

inductive BlockLabel where
  | IL | DL | IR | DR | U
  deriving DecidableEq

structure Combination where
  blocks : ℕ
  label : Fin blocks → BlockLabel
  probability : Fin blocks → ℝ
  isProbability : FuchsVdGraaf.IsProbDist probability

structure Mixture where
  size : ℕ
  combination : Fin size → Combination
  probability : Fin size → ℝ
  isProbability : FuchsVdGraaf.IsProbDist probability

def BlockBefore {n : ℕ} (a : BlockLabel) (L R U : Order n) (i j : Fin n) : Prop :=
  match a with
  | .IL => L i < L j
  | .DL => L j < L i
  | .IR => R i < R j
  | .DR => R j < R i
  | .U => U i < U j

/-- A uniform global seed induces independent uniform relative orders on disjoint U-blocks. -/
def Combination.law (T : Combination) {n : ℕ} (L R σ : Order n) : ℝ :=
  ∑ b : Fin n → Fin T.blocks, (∏ i, T.probability (b i)) *
    (∑ u : Order n, if (∀ i j, σ i < σ j ↔
      (b i < b j ∨ (b i = b j ∧ BlockBefore (T.label (b i)) L R u i j)))
      then 1 else 0) / (Fintype.card (Order n) : ℝ)

def Mixture.law (ν : Mixture) {n : ℕ} (L R σ : Order n) : ℝ :=
  ∑ a, ν.probability a * (ν.combination a).law L R σ

def Mixture.payoff (ν : Mixture) (d : LocalType) : ℝ :=
  ∑ σ ∈ d.predicate.sat, ν.law d.left d.right σ

def Mixture.guarantee (ν : Mixture) (Lg : Language) : ℝ :=
  sInf {x | ∃ d : LocalType, d.Eligible Lg ∧ x = ν.payoff d}

/-- Definition 4.2: arbitrary real coefficients, finite schemes and finite mixtures. -/
def alphaLR (Lg : Language) : ℝ := sSup {x | ∃ ν : Mixture, x = ν.guarantee Lg}

def Mixture.Rational (ν : Mixture) : Prop :=
  (∀ a, ∃ q : ℚ, ν.probability a = q) ∧
  ∀ a b, ∃ q : ℚ, (ν.combination a).probability b = q

structure WeakTransformation where
  law : (n : ℕ) → Order n → Order n → ℝ
  probability : ∀ n γ, FuchsVdGraaf.IsProbDist (law n γ)

/-- General input orders are reduced to identity on the left and relabeled back. -/
def WeakTransformation.applyLaw (T : WeakTransformation) {n : ℕ}
    (L R σ : Order n) : ℝ :=
  T.law n (L.symm.trans R) (L.symm.trans σ)

def WeakTransformation.Guarantees (T : WeakTransformation) (d : LocalType) (β : ℝ) : Prop :=
  ∀ n (L R : Order n) (scope : Fin d.predicate.arity ↪ Fin n),
    HasPattern (fun j => L (scope j)) d.left →
    HasPattern (fun j => R (scope j)) d.right →
    β ≤ ∑ σ : Order n, T.applyLaw L R σ *
      if d.predicate.Accepts (fun j => σ (scope j)) then 1 else 0

def Mixture.Guarantees (ν : Mixture) (d : LocalType) (β : ℝ) : Prop :=
  ∀ n (L R : Order n) (scope : Fin d.predicate.arity ↪ Fin n),
    HasPattern (fun j => L (scope j)) d.left →
    HasPattern (fun j => R (scope j)) d.right →
    β ≤ ∑ σ : Order n, ν.law L R σ *
      if d.predicate.Accepts (fun j => σ (scope j)) then 1 else 0

end
end SatisfiableOrderingCSP.Optimal


