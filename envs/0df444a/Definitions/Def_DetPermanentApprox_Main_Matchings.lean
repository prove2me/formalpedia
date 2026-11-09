-- Prove2me | Definitions.Def_DetPermanentApprox_Main_Matchings
-- name    : DetPermanentApprox_Main_Matchings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:38.753711+00:00
-- url     : https://prove2.me/theorems/08b2bb04-fa01-4884-9438-155ea183dc1e
-- title:
--   All-matching laws, support graphs, and entropy interpolation
-- statement:
--   A matching is any edge set with no shared endpoint, including the empty set. The graph type and real matching partition function are published definitions. Restricted real and complex partition functions sum over exactly the matchings supported on an induced vertex set. Matching weights are products, with empty product $1$, and the Gibbs mass is the matching weight divided by the partition function.
--
--   For $t$, the feasible finite laws are all nonnegative mass vectors summing to one that cover every vertex with probability $t$. The free energy is entropy plus expected log matching weight, and $F_A(t)$ is its supremum on that set. In the source domain this is an attained maximum on a nonempty compact set. Vertex fields multiply an edge weight by the exponential of the sum of its endpoint fields. The dual is log partition minus $t$ times the sum of all fields. A matrix has distinct row and column vertex copies, edges exactly at positive entries, and total support when each such edge lies in a positive perfect matching.
--
--   This interface uses the published finite entropy and simplex, which allow zero masses, rather than the published perfect-matching-only graph family.
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), §§1.3, 2, pp. 3, 6–8 (PDF pp. 3, 6–8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_partitionFn
import Definitions.Def_MatchingEntropy

open scoped BigOperators

namespace DetPermanentApprox.Main

abbrev Graph (V E : Type) := EdmondsMatching65.Polyhedron.Graph V E

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

abbrev Matching (G : Graph V E) :=
  {M : Finset E // EdmondsMatching65.Polyhedron.IsMatching G M}

noncomputable instance matchingFinite (G : Graph V E) : Fintype (Matching G) :=
  Fintype.ofFinite _

def IsSimple (G : Graph V E) : Prop := Function.Injective G.ends

def Incident (G : Graph V E) (v : V) (e : E) : Prop := v ∈ G.ends e

open Classical in
noncomputable def covered (G : Graph V E) (M : Matching G) (v : V) : ℝ :=
  if ∃ e ∈ M.val, Incident G v e then 1 else 0

noncomputable def matchingWeight (G : Graph V E) (w : E → ℝ) (M : Matching G) : ℝ :=
  ∏ e ∈ M.val, w e

noncomputable abbrev Z (G : Graph V E) (w : E → ℝ) : ℝ := MaxEntOCRS.partitionFn G w

open Classical in
noncomputable def complexZ (G : Graph V E) (S : Finset V) (w : E → ℂ) : ℂ :=
  ∑ M : Matching G,
    if ∀ e ∈ M.val, ∀ v ∈ G.ends e, v ∈ S then ∏ e ∈ M.val, w e else 0

open Classical in
noncomputable def restrictedZ (G : Graph V E) (S : Finset V) (w : E → ℝ) : ℝ :=
  ∑ M : Matching G,
    if ∀ e ∈ M.val, ∀ v ∈ G.ends e, v ∈ S then matchingWeight G w M else 0

noncomputable def gibbs (G : Graph V E) (w : E → ℝ) : Matching G → ℝ :=
  fun M => matchingWeight G w M / Z G w

def matchingLaws (G : Graph V E) (t : ℝ) : Set (Matching G → ℝ) :=
  {ν | ν ∈ OAI.MatchingEntropy.probabilitySimplex (Matching G) ∧
    ∀ v, ∑ M, ν M * covered G M v = t}

noncomputable def freeEnergy (G : Graph V E) (w : E → ℝ) (ν : Matching G → ℝ) : ℝ :=
  OAI.MatchingEntropy.entropy ν + ∑ M, ν M * Real.log (matchingWeight G w M)

/-- The real supremum represents the maximum on the nonempty compact finite-law
feasible set for the source's positive-permanent inputs and 0 < t ≤ 1.
On infeasible inputs Lean's real supremum convention returns 0. -/
noncomputable def interpolation (G : Graph V E) (w : E → ℝ) (t : ℝ) : ℝ :=
  sSup (freeEnergy G w '' matchingLaws G t)

noncomputable def fieldWeights (G : Graph V E) (w : E → ℝ) (θ : V → ℝ) : E → ℝ :=
  fun e => w e * Real.exp (∑ v ∈ (G.ends e).toFinset, θ v)

noncomputable def dualObjective (G : Graph V E) (w : E → ℝ) (t : ℝ) (θ : V → ℝ) : ℝ :=
  Real.log (Z G (fieldWeights G w θ)) - t * ∑ v, θ v

def IsMinimizer (f : (V → ℝ) → ℝ) (θ : V → ℝ) : Prop := ∀ x, f θ ≤ f x

noncomputable def binaryEntropy (t : ℝ) : ℝ :=
  Real.negMulLog t + Real.negMulLog (1 - t)

abbrev Vertex (n : ℕ) := Fin n ⊕ Fin n
abbrev Support {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :=
  {ij : Fin n × Fin n // 0 < A ij.1 ij.2}

def supportGraph {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Graph (Vertex n) (Support A) where
  ends e := s(Sum.inl e.val.1, Sum.inr e.val.2)
  loopless e := by simp

def supportWeights {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Support A → ℝ :=
  fun e => A e.val.1 e.val.2

def TotalSupport {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, 0 < A i j → ∃ σ : Equiv.Perm (Fin n), σ i = j ∧ ∀ k, 0 < A k (σ k)

noncomputable def F {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : ℝ :=
  interpolation (supportGraph A) (supportWeights A) t

noncomputable def Phi {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (θ : Vertex n → ℝ) : ℝ :=
  dualObjective (supportGraph A) (supportWeights A) t θ

end DetPermanentApprox.Main


