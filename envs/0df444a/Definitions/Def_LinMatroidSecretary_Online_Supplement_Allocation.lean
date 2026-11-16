-- Prove2me | Definitions.Def_LinMatroidSecretary_Online_Supplement_Allocation
-- name    : LinMatroidSecretary_Online_Supplement_Allocation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:02:19.513501+00:00
-- url     : https://prove2.me/theorems/9e9418ef-7b48-4e1b-aae8-5c91e7e6fad3
-- title:
--   XOS agent arrivals, feasible allocations and online policies
-- statement:
--   Let $E$ be a finite labelled item set and let the agents be $N=\{0,\ldots,n-1\}$. An instance fixes an eligibility set $E_a\subseteq E$ and a valuation $f_a$ for each agent $a$ before the random arrival order is drawn. The validity predicate requires $f_a$ to be XOS on $E_a$: a maximum of finitely many, at least one, nonnegative additive clauses. It uses the published predicate $\mathrm{DSICHardRev.IsXOS}$ on $D\mapsto f_a(D\cap E_a)$; values outside subsets of $E_a$ are immaterial. An allocation $T$ is feasible on an agent set $X$ when $T_a\subseteq E_a$, its bundles are pairwise disjoint, and $\bigcup_{a\in X}T_a$ is independent in the given matroid. Its welfare is
--   $$F(T)=\sum_{a\in N} f_a(T_a).$$
--   The predicate of linearity requires a representation in $K^d$ over some field $K$, with no finiteness restriction on $K$.
--
--   An observation consists of the current eligibility set, value queries on its subsets, and a vector for each eligible item. A policy receives the arrival-ordered observations so far and its previously assigned bundles, and outputs a distribution on bundles. It receives no agent indices or unrevealed data. In the known-matroid model the vector component is the one-point type, and the policy may be chosen as a function of the known matroid. In the online-representation model the vector component is $F^d$; only vectors restricted to revealed eligibility sets enter observations. The policy is a function with no feasibility or competitive guarantee bundled into its type. Validity says all output probabilities are nonnegative and sum to one.
--
--   For an arrival permutation $\sigma$ and sequence of bundles $b$, the conditional run probability is the product of the policy's step probabilities. The final allocation assigns $b_{\sigma^{-1}(a)}$ to agent $a$. The expected welfare is
--   $$\frac1{n!}\sum_\sigma\sum_b \Pr_\pi[b\mid\sigma]F(T(\sigma,b)).$$
--   Always feasible means that every positive-probability run yields a feasible allocation. The empty allocation is permitted. When $n=0$ the expected welfare is zero and $0!=1$.
--
--   This interface separates the information available to an online policy from its required guarantees and provides the allocation model for Theorem 2 and Lemma 7.
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/608.pdf, §5, PDF pp. 19–21, 25 (printed pp. 17–19, 23)

import Mathlib
import Definitions.Def_DSICHardRev_ValuationClasses
import Definitions.Def_LinMatroidSecretary_Online_Setting

/-!
Agent-arrival model of §5, Bérczi–Dughmi–Livanos–Soto–Verdugo, STOC 2027 #608,
PDF pp. 19–21, 25. Eligibility sets may overlap. Value queries and vectors are restricted
to revealed eligibility sets. Policies contain only functions, with validity stated separately.
-/
namespace LinMatroidSecretary.Online.Supplement

open Finset
noncomputable section

variable {E : Type} [Fintype E] [DecidableEq E] {n : ℕ}

/-- XOS on `S`, by applying the published general XOS predicate to the valuation
extended by ignoring items outside `S`. Values of `f` outside subsets of `S` are unused. -/
def IsXOSOn (S : Finset E) (f : Finset E → ℝ) : Prop :=
  DSICHardRev.IsXOS (fun D => f (D ∩ S))

/-- Data fixed before the random order is drawn; no algorithm or guarantee is a field. -/
structure Instance (E : Type) (n : ℕ) where
  elig : Fin n → Finset E
  val : Fin n → Finset E → ℝ

/-- Each agent has a finite maximum of nonnegative additive clauses on its eligible items. -/
def Instance.Valid (I : Instance E n) : Prop :=
  ∀ a, IsXOSOn (I.elig a) (I.val a)

/-- Feasibility for the agents in `X`: eligibility, disjointness, independent union. -/
def FeasibleOn (M : Matroid E) (elig : Fin n → Finset E) (X : Finset (Fin n))
    (T : Fin n → Finset E) : Prop :=
  (∀ a ∈ X, T a ⊆ elig a) ∧
  (∀ a ∈ X, ∀ b ∈ X, a ≠ b → Disjoint (T a) (T b)) ∧
  M.Indep (↑(X.biUnion T) : Set E)

/-- A feasible allocation to all agents. -/
def Feasible (M : Matroid E) (I : Instance E n) (T : Fin n → Finset E) : Prop :=
  FeasibleOn M I.elig univ T

/-- Total value of an allocation. Only feasible allocations are used for comparisons. -/
def welfare (I : Instance E n) (T : Fin n → Finset E) : ℝ :=
  ∑ a, I.val a (T a)

/-- A finite matroid is linear if it has a finite-dimensional representation over some
field. The field is not required to be finite. -/
def IsLinear (M : Matroid E) : Prop :=
  ∃ (K : Type) (_ : Field K) (d : ℕ) (v : E → Fin d → K),
    M = linMatroid (F := K) v

/-- What one arrival reveals. In the known-matroid model `V = Unit`, so there is no
vector information. Queries are only on subsets of `elig`; vectors only on its elements. -/
structure Observation (E V : Type) where
  elig : Finset E
  value : {D : Finset E // D ⊆ elig} → ℝ
  vec : {e : E // e ∈ elig} → V

/-- A behavioural policy sees arrival-ordered observations and its own earlier bundles.
There are no agent indices, unrevealed data, representation or correctness proofs in the input. -/
structure AllocationPolicy (E V : Type) (n : ℕ) where
  choose : (t : ℕ) → (Fin (t + 1) → Observation E V) →
    (Fin t → Finset E) → Finset E → ℝ

/-- Each output is a probability distribution on bundles, even on unused histories. -/
def AllocationPolicy.Valid {V : Type} (π : AllocationPolicy E V n) : Prop :=
  ∀ t h past, (∀ D, 0 ≤ π.choose t h past D) ∧ ∑ D, π.choose t h past D = 1

/-- Observed information of an agent; full `I` and `v` are not passed to the policy. -/
def observation {V : Type} (I : Instance E n) (v : E → V) (a : Fin n) :
    Observation E V :=
  { elig := I.elig a
    value := fun D => I.val a D.val
    vec := fun e => v e.val }

/-- Run probability conditional on the arrival permutation. Choices at a step use only
the observations up to that step and the bundles strictly before it. -/
def allocationRunProb {V : Type} (π : AllocationPolicy E V n) (I : Instance E n)
    (v : E → V) (σ : Equiv.Perm (Fin n)) (b : Fin n → Finset E) : ℝ :=
  ∏ t : Fin n, π.choose t.val
    (fun j => observation I v (σ ⟨j.val, by omega⟩))
    (fun j => b ⟨j.val, by omega⟩) (b t)

/-- Final allocation indexed by agents, rather than by arrival positions. -/
def allocationAlg (σ : Equiv.Perm (Fin n)) (b : Fin n → Finset E) : Fin n → Finset E :=
  fun a => b (σ.symm a)

/-- Exact expected welfare: uniform random order and the policy's behavioural randomness.
`0! = 1`, so this also defines the zero-agent case without division by zero. -/
def expectedWelfare {V : Type} (π : AllocationPolicy E V n) (I : Instance E n)
    (v : E → V) : ℝ :=
  ((n.factorial : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin n), ∑ b : Fin n → Finset E,
    allocationRunProb π I v σ b * welfare I (allocationAlg σ b)

/-- Always feasible means feasible on every positive-probability complete run. -/
def AlwaysFeasible {V : Type} (M : Matroid E) (π : AllocationPolicy E V n)
    (I : Instance E n) (v : E → V) : Prop :=
  ∀ σ b, 0 < allocationRunProb π I v σ b → Feasible M I (allocationAlg σ b)

end
end LinMatroidSecretary.Online.Supplement


