-- Prove2me | Definitions.Def_SatisfiableOrderingCSP_Optimal_LocalModel
-- name    : SatisfiableOrderingCSP_Optimal_LocalModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:44:48.712837+00:00
-- url     : https://prove2.me/theorems/f14796c5-4bb0-41c1-8f42-fa4c025b0d2f
-- title:
--   Local probability models and basic or approximate SDP feasibility
-- statement:
--   A scope family lists ordered injective scopes. A local model on any positive finite domain has real singleton and joint probability distributions, consistent singleton marginals, and joint support on distinct-coordinate tuples. A basic LP solution additionally satisfies each predicate with probability one. No occupancy conditions or global joint law are imposed. Basic SDP vectors share one finite real Euclidean space and a unit vector: vectors for each variable sum to the unit vector, their same-variable Gram matrix is the diagonal singleton distribution, and every scoped pair has the prescribed joint probabilities. Centered functions vanish off singleton support. Covariance matrices denote bilinear forms on these supported centered spaces. Exact covariance has identity diagonal blocks and the local covariance on every scope. Approximate covariance B,W has B and block-diagonal W positive semidefinite, identity diagonal in B, B-W positive semidefinite, and local error between minus and plus eta times the private covariance. The module separately defines sparsity and scope degree.
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission (not an acceptance claim), sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc; citation_basis: published; Definitions 4.6, 5.2, 5.6 and §5.3; pp. 20, 25, 27–28 (PDF 23, 28, 30–31)

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Ordering

open scoped BigOperators

namespace SatisfiableOrderingCSP.Optimal
noncomputable section
attribute [local instance] Classical.propDecidable

structure Scopes (n : ℕ) where
  count : ℕ
  arity : Fin count → ℕ
  scope : (c : Fin count) → Fin (arity c) ↪ Fin n

def Instance.scopes (I : Instance) : Scopes I.n :=
  ⟨I.m, fun c => (I.constraint c).predicate.arity, fun c => (I.constraint c).scope⟩

def Scopes.Sparse {n : ℕ} (S : Scopes n) : Prop :=
  ∀ c d, c ≠ d → ∀ u v : Fin n,
    u ∈ Set.range (S.scope c) → v ∈ Set.range (S.scope c) →
    u ∈ Set.range (S.scope d) → v ∈ Set.range (S.scope d) → u = v

def Scopes.DegreeAtMost {n : ℕ} (S : Scopes n) (D : ℕ) : Prop :=
  ∀ v, (Finset.univ.filter fun c => v ∈ Set.range (S.scope c)).card ≤ D

/-- Consistent singleton marginals and local distinctness, without a global joint law. -/
structure LocalModel {n : ℕ} (S : Scopes n) (q : ℕ) where
  positiveDomain : 0 < q
  singleton : Fin n → Fin q → ℝ
  joint : (c : Fin S.count) → (Fin (S.arity c) → Fin q) → ℝ
  singleton_probability : ∀ v, FuchsVdGraaf.IsProbDist (singleton v)
  joint_probability : ∀ c, FuchsVdGraaf.IsProbDist (joint c)
  distinct : ∀ c x, 0 < joint c x → Function.Injective x
  marginal : ∀ c i a, (∑ x, if x i = a then joint c x else 0) = singleton (S.scope c i) a

def BasicLP (I : Instance) {q : ℕ} (M : LocalModel I.scopes q) : Prop :=
  ∀ c x, 0 < M.joint c x → (I.constraint c).predicate.Accepts x

structure SDPVectors {n q : ℕ} {S : Scopes n} (M : LocalModel S q) where
  dimension : ℕ
  unit : Fin dimension → ℝ
  vector : Fin n → Fin q → Fin dimension → ℝ
  unit_norm : ∑ j, unit j * unit j = 1
  sum_vector : ∀ v j, ∑ a, vector v a j = unit j
  same_variable : ∀ v a b, (∑ j, vector v a j * vector v b j) =
    if a = b then M.singleton v a else 0
  pairwise : ∀ c i k, i ≠ k → ∀ a b,
    (∑ j, vector (S.scope c i) a j * vector (S.scope c k) b j) =
      ∑ x, if x i = a ∧ x k = b then M.joint c x else 0

def HasBasicSDP (I : Instance) (q : ℕ) : Prop :=
  ∃ M : LocalModel I.scopes q, BasicLP I M ∧ Nonempty (SDPVectors M)

abbrev Coefficients (n q : ℕ) := Fin n → Fin q → ℝ
abbrev CovarianceMatrix (n q : ℕ) := Matrix (Fin n × Fin q) (Fin n × Fin q) ℝ

def LocalModel.Centered {n q : ℕ} {S : Scopes n} (M : LocalModel S q)
    (f : Coefficients n q) : Prop :=
  (∀ v, ∑ a, M.singleton v a * f v a = 0) ∧
  ∀ v a, M.singleton v a = 0 → f v a = 0

def form {n q : ℕ} (G : CovarianceMatrix n q) (f g : Coefficients n q) : ℝ :=
  ∑ x, ∑ y, f x.1 x.2 * G x y * g y.1 y.2

def LocalModel.Positive {n q : ℕ} {S : Scopes n} (M : LocalModel S q)
    (G : CovarianceMatrix n q) : Prop :=
  G.IsSymm ∧ ∀ f, M.Centered f → 0 ≤ form G f f

def LocalModel.PositiveDefinite {n q : ℕ} {S : Scopes n} (M : LocalModel S q)
    (G : CovarianceMatrix n q) : Prop :=
  G.IsSymm ∧ ∀ f, M.Centered f → f ≠ 0 → 0 < form G f f

def LocalModel.DiagonalIdentity {n q : ℕ} {S : Scopes n} (M : LocalModel S q)
    (G : CovarianceMatrix n q) : Prop :=
  ∀ v f g, M.Centered f → M.Centered g →
    (∀ u, u ≠ v → f u = 0) → (∀ u, u ≠ v → g u = 0) →
    form G f g = ∑ a, M.singleton v a * f v a * g v a

def LocalModel.localForm {n q : ℕ} {S : Scopes n} (M : LocalModel S q)
    (c : Fin S.count) (f g : Coefficients n q) : ℝ :=
  ∑ x, M.joint c x * (∑ i, f (S.scope c i) (x i)) * (∑ i, g (S.scope c i) (x i))

def SupportedOnScope {n q : ℕ} (S : Scopes n) (c : Fin S.count)
    (f : Coefficients n q) : Prop := ∀ v, v ∉ Set.range (S.scope c) → f v = 0

def LocalModel.ExactCovariance {n q : ℕ} {S : Scopes n} (M : LocalModel S q)
    (G : CovarianceMatrix n q) : Prop :=
  M.Positive G ∧ M.DiagonalIdentity G ∧
  ∀ c f g, M.Centered f → M.Centered g → SupportedOnScope S c f →
    SupportedOnScope S c g → form G f g = M.localForm c f g

def SDPVectors.CovarianceIs {n q : ℕ} {S : Scopes n} {M : LocalModel S q}
    (V : SDPVectors M) (G : CovarianceMatrix n q) : Prop :=
  ∀ f g, M.Centered f → M.Centered g → form G f g =
    ∑ j, (∑ v, ∑ a, f v a * V.vector v a j) *
      (∑ v, ∑ a, g v a * V.vector v a j)

def ApproximateSDP {n q : ℕ} {S : Scopes n} (M : LocalModel S q)
    (η : ℝ) (B W : CovarianceMatrix n q) : Prop :=
  0 ≤ η ∧ M.Positive B ∧ M.DiagonalIdentity B ∧ M.Positive W ∧
  (∀ u v a b, u ≠ v → W (u,a) (v,b) = 0) ∧ M.Positive (B - W) ∧
  ∀ c f, M.Centered f → SupportedOnScope S c f →
    -η * form W f f ≤ M.localForm c f f - form B f f ∧
    M.localForm c f f - form B f f ≤ η * form W f f

def PrivateBlocksPositive {n q : ℕ} {S : Scopes n} (M : LocalModel S q)
    (W : CovarianceMatrix n q) : Prop :=
  ∀ v f, M.Centered f → f ≠ 0 → (∀ u, u ≠ v → f u = 0) → 0 < form W f f

end
end SatisfiableOrderingCSP.Optimal


