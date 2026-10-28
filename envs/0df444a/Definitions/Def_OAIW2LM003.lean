-- Prove2me | Definitions.Def_OAIW2LM003
-- name    : OAIW2LM003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T03:02:01.723994+00:00
-- url     : https://prove2.me/theorems/0b67c96b-f3e6-4256-8c22-e18ecdde3c73
-- title:
--   Definitions bundle OAIW2LM003 of the split of OpenAI, the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LoopMatching.fullEndpoint`, carved from OpenAI's openai/math development (OpenAI, *the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint)*, OpenAI Math Release, October 2026, result family not identified here; see lean/formalization.yaml, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 18 definitions and 3 theorems. The definitions and types are `OAI.MatchingEntropy.LooplessGraph.constraintPolytope`, `OAI.MatchingEntropy.LooplessGraph.cutLinear`, `OAI.MatchingEntropy.LooplessGraph.degreeLinear`, `OAI.MatchingEntropy.LooplessGraph.faceCodimension`, `OAI.MatchingEntropy.LooplessGraph.faceSpace`, `OAI.MatchingEntropy.LooplessGraph.feasibleLaws`, `OAI.MatchingEntropy.LooplessGraph.matchingBits`, `OAI.MatchingEntropy.LooplessGraph.meanLinear`, `OAI.MatchingEntropy.LooplessGraph.polytope`, `OAI.MatchingEntropy.LooplessGraph.sideMarginal`, `OAI.MatchingEntropy.LooplessGraph.sideRestriction`, `OAI.MatchingEntropy.LooplessGraph.supportSimple`, `OAI.MatchingEntropy.binaryEntropy`, `OAI.MatchingEntropy.expLaw`, `OAI.MatchingEntropy.linearScore`, `OAI.MatchingEntropy.matchingNormalized`, `OAI.MatchingEntropy.maxMatchingEntropy`, `OAI.MatchingEntropy.separableLower`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, lean/OAI/Combinatorics, in whole or in part: [`PerfectMatching_Basic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PerfectMatching/Basic.lean), [`PerfectMatching_Contraction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PerfectMatching/Contraction.lean), [`PerfectMatching_Duality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PerfectMatching/Duality.lean), [`PerfectMatching_Entropy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PerfectMatching/Entropy.lean), [`PerfectMatching_EntropyUpper`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PerfectMatching/EntropyUpper.lean), [`PerfectMatching_Face`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PerfectMatching/Face.lean), [`PerfectMatching_MatchingCovariance`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean), [`PerfectMatching_OddCuts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PerfectMatching/OddCuts.lean), [`PerfectMatching_Partition`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PerfectMatching/Partition.lean), [`PerfectMatching_Polytope`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PerfectMatching/Polytope.lean), [`PerfectMatching_Separable`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PerfectMatching/Separable.lean).
--
--   **Imports.** It imports the published bundle `Def_SingletonLoopMatching`; the bundles `OAIW2LM000` and `OAIW2LM001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIW2LM004`.
-- source:
--   OpenAI, the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint), OpenAI Math Release, October 2026, https://github.com/openai/math (result family not identified here; see lean/formalization.yaml; paper: https://github.com/openai/math; Apache License 2.0); definitions carved from lean/OAI/Computability, lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_SingletonLoopMatching
import Definitions.Def_OAIW2LM000
import Definitions.Def_OAIW2LM001

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Basic
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.crossesDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite loopless multigraphs, perfect matching indicators, and their convex hull.
The edge type distinguishes parallel edges. Feasible laws are probability vectors
on perfect matchings with a prescribed mean.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

def polytope (G : LooplessGraph V E) : Set (E → ℝ) :=
  convexHull ℝ (Set.range G.indicator)

def feasibleLaws (G : LooplessGraph V E) (y : E → ℝ) : Set (G.Matching → ℝ) :=
  {p | p ∈ probabilitySimplex G.Matching ∧ G.mean p = y}

def meanLinear (G : LooplessGraph V E) : (G.Matching → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun := G.mean
  map_add' p q := by
    ext e
    simp [mean, add_mul, Finset.sum_add_distrib]
  map_smul' a p := by
    ext e
    simp [mean, mul_assoc, Finset.mul_sum]


end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_OddCuts
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Degree and odd-cut constraints for the perfect matching polytope.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

/-- The degree and odd-cut constraint system. -/
def constraintPolytope (G : LooplessGraph V E) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v, G.degree x v = 1) ∧
    (∀ S : Finset V, Odd S.card → 1 ≤ G.cutMass x S)}


omit [Fintype V] [DecidableEq E] in
theorem degree_linear (G : LooplessGraph V E) (x y : E → ℝ) (a b : ℝ) (v : V) :
    G.degree (a • x+b • y) v = a*G.degree x v+b*G.degree y v := by
  have he : ∀ e, (if G.Incident v e then (a • x+b • y) e else 0) =
      a*(if G.Incident v e then x e else 0)+b*(if G.Incident v e then y e else 0) := by
    intro e
    by_cases h : G.Incident v e <;> simp [h]
  simp only [degree, he, Finset.sum_add_distrib, ← Finset.mul_sum]

omit [Fintype V] [DecidableEq E] in
theorem cutMass_linear (G : LooplessGraph V E) (x y : E → ℝ) (a b : ℝ) (S : Finset V) :
    G.cutMass (a • x+b • y) S = a*G.cutMass x S+b*G.cutMass y S := by
  simp [cutMass, Finset.sum_add_distrib, Finset.mul_sum]

end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Contraction
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Contraction of tight odd cuts and gluing of perfect matchings and their laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype E] [DecidableEq E] in
theorem crosses_of_kept_both (G : LooplessGraph V E) (S : Finset V) (e : E)
    (h₁ : G.left e ∈ S ∨ G.right e ∈ S)
    (h₂ : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ) : G.Crosses S e := by
  simp only [Finset.mem_compl] at h₂
  unfold Crosses
  tauto

end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Entropy
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.crossesDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite Shannon entropy and attainment of its supremum over feasible matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def maxMatchingEntropy (G : LooplessGraph V E) (y : E → ℝ) : ℝ :=
  sSup (entropy '' G.feasibleLaws y)



end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Duality
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.crossesDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite exponential tilts, partition functions, and entropy duality on a face.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]


/-- A score affine in the matching vector; the constant permits centering
without changing the duality calculation. -/
def linearScore (G : LooplessGraph V E) (u : E → ℝ) (c : ℝ) (M : G.Matching) : ℝ :=
  (∑ e, u e * G.indicator M e) - c

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Polytope
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Tutte's criterion and Edmonds' perfect matching polytope theorem for multigraphs.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

/-- The simple support graph forgets only parallel-edge identities. -/
def supportSimple (G : LooplessGraph V E) (x : E → ℝ) : SimpleGraph V where
  Adj v w := ∃ e, 0 < x e ∧ ((G.left e=v ∧ G.right e=w) ∨ (G.left e=w ∧ G.right e=v))
  symm := ⟨by intro v w; rintro ⟨e,hx,h⟩; exact ⟨e,hx,h.symm⟩⟩
  loopless := ⟨by
    intro v
    rintro ⟨e,_,(⟨hl,hr⟩ | ⟨hl,hr⟩)⟩ <;> exact G.loopless e (hl.trans hr.symm)⟩

end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Face
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Active face spaces, their codimension bounds, and local radial extension.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

def degreeLinear (G : LooplessGraph V E) : (E → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := G.degree
  map_add' := by
    intro u v
    ext w
    simpa using G.degree_linear u v 1 1 w
  map_smul' := by
    intro a u
    ext w
    simp only [degree,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    split <;> simp

def cutLinear (G : LooplessGraph V E) (S : Finset V) : (E → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun u => G.cutMass u S
  map_add' := by intro u v; simpa using G.cutMass_linear u v 1 1 S
  map_smul' := by intro a u; simp [cutMass,Finset.mul_sum]

/-- The exact active degree and odd-cut kernel, on the positive edge support. -/
def faceSpace (G : LooplessGraph V E) (x : E → ℝ) : Submodule ℝ ({e // 0<x e} → ℝ) where
  carrier := {u | G.degreeLinear (positiveExtension x u)=0 ∧
    ∀ S : Finset V, Odd S.card → G.cutMass x S=1 → G.cutLinear S (positiveExtension x u)=0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    refine ⟨by simp only [map_add,hu.1,hv.1,add_zero],?_⟩
    intro S hS ht
    simp only [map_add,hu.2 S hS ht,hv.2 S hS ht,add_zero]
  smul_mem' := by
    intro a u hu
    refine ⟨by simp only [map_smul,hu.1,smul_zero],?_⟩
    intro S hS ht
    simp only [map_smul,hu.2 S hS ht,smul_zero]

def faceCodimension (G : LooplessGraph V E) (x : E → ℝ) : ℕ :=
  Module.finrank ℝ (({e // 0<x e} → ℝ) ⧸ G.faceSpace x)


abbrev sideMarginal (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    {e // G.left e ∈ S ∨ G.right e ∈ S} → ℝ := fun e => x e.val

def sideRestriction (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    ({e // 0<x e} → ℝ) →ₗ[ℝ] ({e // 0<G.sideMarginal x S e} → ℝ) where
  toFun := fun u e => u ⟨e.val.val,e.property⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_MatchingCovariance
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Normalized matching covariance: face rank, exact trace, and second variation.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Normalized matching directions on exactly the positive edge support. -/
def matchingNormalized (G : LooplessGraph V E) (x : E → ℝ) :
    G.Matching → {e // 0 < x e} → ℝ :=
  normalizedCentered (fun M e => G.indicator M e.val) (fun e => x e.val)

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section

noncomputable section
open scoped BigOperators Topology
open Filter
namespace MatchingEntropy

variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def binaryEntropy (x : E → ℝ) : ℝ := entropy x + entropy (fun e => 1 - x e)

def separableLower (x : E → ℝ) : ℝ := entropy x - 3 * entropy (fun e => 1 - x e)

end MatchingEntropy
end
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_EntropyUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section

noncomputable section
open scoped BigOperators
namespace MatchingEntropy

variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

def matchingBits (G : LooplessGraph V E) (M : G.Matching) : E → Bool :=
  fun e => decide (e ∈ M.val)

end LooplessGraph

end MatchingEntropy
end
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Partition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section

noncomputable section
open Finset
namespace MatchingEntropy

variable {I : Type*} [Fintype I]

def expLaw (a : I → ℝ) (i : I) : ℝ := Real.exp (a i)/expSum a

end MatchingEntropy
end
end

end OAI
end


