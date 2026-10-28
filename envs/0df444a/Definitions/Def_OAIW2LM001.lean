-- Prove2me | Definitions.Def_OAIW2LM001
-- name    : OAIW2LM001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T02:59:00.527115+00:00
-- url     : https://prove2.me/theorems/3f834c25-bf57-47c5-928e-751bbdb842a2
-- title:
--   Definitions bundle OAIW2LM001 of the split of OpenAI, the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LoopMatching.fullEndpoint`, carved from OpenAI's openai/math development (OpenAI, *the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint)*, OpenAI Math Release, October 2026, result family not identified here; see lean/formalization.yaml, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 108 declarations of OpenAI's Lean: 65 definitions, 2 inductive types or structures, 1 instance and 40 theorems. The definitions and types are `OAI.BinaryMatching.Raw.InputData.powerBits`, `OAI.BinaryMatching.Raw.Optimize.Compiler.instPreorderInt_solutions`, `OAI.BinaryMatching.Raw.Optimize.Compiler.instPreorderInt_solutions_1`, `OAI.BinaryMatching.Raw.Optimize.indexedSlope`, `OAI.BinaryMatching.Raw.Optimize.instPreorderInt_solutions`, `OAI.BinaryMatching.Raw.Optimize.instPreorderInt_solutions_1`, `OAI.BinaryMatching.Raw.oddBudget`, `OAI.BinaryMatching.Raw.oddWordBound`, `OAI.BinaryMatching.Raw.pairs`, `OAI.BinaryMatching.Raw.pathFlow`, `OAI.BinaryMatching.RecursiveEval.Branch`, `OAI.BinaryMatching.RecursiveEval.Command`, `OAI.BinaryMatching.RecursiveEval.State`, `OAI.BinaryMatching.RecursiveEval.branchRepr`, `OAI.BinaryMatching.RecursiveEval.calls`, `OAI.BinaryMatching.RecursiveEval.commandRepr`, `OAI.BinaryMatching.RecursiveEval.cost`, `OAI.BinaryMatching.RecursiveEval.step`, `OAI.BinaryMatching.RecursiveEval.value`, `OAI.BinaryMatching.TrivialCut`, `OAI.LoopMatching.Accumulator.Q`, `OAI.LoopMatching.BitAdd.State`, `OAI.LoopMatching.BitAdd.add`, `OAI.LoopMatching.BitAdd.carry`, `OAI.LoopMatching.BitAdd.digit`, `OAI.LoopMatching.BitAdd.finish`, `OAI.LoopMatching.BitAdd.initial`, `OAI.LoopMatching.BitAdd.potential`, `OAI.LoopMatching.BitAdd.run`, `OAI.LoopMatching.BitAdd.step`, `OAI.LoopMatching.BitAdd.value`, `OAI.LoopMatching.BitAdd.xor`, `OAI.LoopMatching.BitNormalize.normalize`, `OAI.LoopMatching.BitNormalize.step`, `OAI.LoopMatching.InputMachine.LoopBits`, `OAI.LoopMatching.InputMachine.LoopData`, `OAI.LoopMatching.InputMachine.loopBitsRepr`, `OAI.LoopMatching.InputMachine.loopRepr`, `OAI.LoopMatching.SmallBinaryMultiply.State`, `OAI.LoopMatching.SmallBinaryMultiply.initial` and 27 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, lean/OAI/Combinatorics, in whole or in part: `LoopMatching_Accumulator`, `LoopMatching_BinaryMultiply`, `LoopMatching_BitAdd`, `LoopMatching_BitLength`, `LoopMatching_BitNormalize`, `LoopMatching_ExpandBijection`, `LoopMatching_ExpandInput`, `LoopMatching_InputDecode`, `LoopMatching_InputMachine`, `LoopMatching_LoopParser`, `LoopMatching_Model`, `LoopMatching_SparseBoundary`, `MatchingCount_BinarySolve`, `MatchingCount_RawFlow`, `MatchingCount_RawFlowSize`, `MatchingCount_RawOddBounds`, `MatchingCount_RawOptimizerData`, `MatchingCount_RawOptimizerDataCompiler`, `MatchingCount_RawOptimizerRows`, `MatchingCount_RawOptimizerRowsCompiler`, `MatchingCount_RawSearch`, `MatchingCount_RecursiveCoding`, `MatchingCount_RecursiveEval`, `PerfectMatching_Calculus`, `PerfectMatching_Contraction`, `PerfectMatching_Coupling`, `PerfectMatching_Covariance`, `PerfectMatching_Duality`, `PerfectMatching_EntropyUpper`, `PerfectMatching_Face`, `PerfectMatching_FeasibilityRepair`, `PerfectMatching_MatchingCovariance`, `PerfectMatching_Separable`, `PerfectMatching_Simplex`.
--
--   **Imports.** It imports the published bundle `Def_SingletonLoopMatching`.
--
--   **Imported by** (directly, in this split): the bundles `OAIW2LM002` and `OAIW2LM003`.
-- source:
--   OpenAI, the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint), OpenAI Math Release, October 2026, https://github.com/openai/math (result family not identified here; see lean/formalization.yaml; paper: https://github.com/openai/math; Apache License 2.0); definitions carved from lean/OAI/Computability, lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_SingletonLoopMatching

section
-- module Solutions.OAIW2_LoopMatching.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_Accumulator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.Accumulator
open scoped BigOperators

def Q (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => a 0
  | n + 1 => (n + 1) * Q a n + a (n + 1)

@[simp] theorem Q_zero (a : ℕ → ℕ) : Q a 0 = a 0 := rfl

@[simp] theorem Q_succ (a : ℕ → ℕ) (n : ℕ) :
    Q a (n + 1) = (n + 1) * Q a n + a (n + 1) := rfl

end LoopMatching.Accumulator

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Simplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Probability vectors on finite types, with their convexity and compactness properties.
The function-space simplex is the range of the weights of `Convexity.StdSimplex`.
-/

noncomputable section

open scoped BigOperators

namespace MatchingEntropy

/-- Nonnegative real weights with total mass one. -/
def probabilitySimplex (Index : Type*) [Fintype Index] : Set (Index → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Coupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite pushforwards and couplings with a prescribed common marginal.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

/-- Finite pushforward weights. -/
def fiberMass {A C : Type*} [Fintype A] [DecidableEq C]
    (p : A → ℝ) (f : A → C) (c : C) : ℝ := ∑ a, if f a = c then p a else 0

/-- The explicit cut-choice coupling. Only equal choices receive mass. -/
def jointLaw {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    (p : A → ℝ) (q : B → ℝ) (f : A → C) (g : B → C) (z : A × B) : ℝ :=
  if f z.1 = g z.2 then p z.1*q z.2 / fiberMass p f (f z.1) else 0

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Contraction
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

def sideMap (S : Finset V) (v : V) : Option {v // v ∈ S} :=
  if h : v ∈ S then some ⟨v,h⟩ else none

def liftVertices (S : Finset V) (T : Finset (Option {v // v ∈ S})) : Finset V :=
  Finset.univ.filter (fun v => sideMap S v ∈ T)

@[simp] theorem mem_liftVertices (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (v : V) :
    v ∈ liftVertices S T ↔ sideMap S v ∈ T := by simp [liftVertices]

omit [Fintype V] in
@[simp] theorem sideMap_some (S : Finset V) (v : {v // v ∈ S}) :
    sideMap S v.val = some v := by
  simp [sideMap, v.property]

end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Face
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

/-- Restrict the ambient vector space to the genuinely positive edge coordinates. -/
def positiveExtension (x : E → ℝ) : ({e // 0<x e} → ℝ) →ₗ[ℝ] (E → ℝ) := by
  classical
  exact {
    toFun := fun u e => if h : 0<x e then u ⟨e,h⟩ else 0
    map_add' := by intro u v; ext e; by_cases h : 0<x e <;> simp [h]
    map_smul' := by intro a u; ext e; by_cases h : 0<x e <;> simp [h] }

omit [Fintype E] [DecidableEq E] in
@[simp] theorem positiveExtension_pos (x : E → ℝ) (u : {e // 0<x e} → ℝ)
    (e : {e // 0<x e}) : positiveExtension x u e.val=u e := by
  simp [positiveExtension,e.property]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem positiveExtension_zero (x : E → ℝ) (u : {e // 0<x e} → ℝ)
    {e : E} (he : x e=0) : positiveExtension x u e=0 := by
  simp [positiveExtension,he]

end LooplessGraph

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Duality
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

/-- Finite exponential partition function, based on a probability law p. -/
def partition {ι : Type*} [Fintype ι] (p a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, p i * Real.exp (t*a i)

def tiltedLaw {ι : Type*} [Fintype ι] (p a : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  p i * Real.exp (t*a i) / partition p a t

@[simp] theorem partition_zero {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) : partition p a 0 = 1 := by
  simpa only [partition, zero_mul, Real.exp_zero, mul_one] using hp.2

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Calculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Derivatives of entropy and log-partition, and the nonlinear entropy barrier.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

/-- The explicit first derivative along a supported affine marginal path. -/
def entropyLineD {ι : Type*} [Fintype ι] (x v : ι → ℝ) (t : ℝ) : ℝ :=
  -∑ i, v i * Real.log (x i+t*v i) - ∑ i, v i

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Covariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive semidefinite covariance matrices, rank, trace, and a spectral inequality.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

def weightedColumns (p : A → ℝ) (b : A → I → ℝ) : Matrix I A ℝ :=
  fun i a => Real.sqrt (p a) * b a i

def covariance (p : A → ℝ) (b : A → I → ℝ) : Matrix I I ℝ :=
  weightedColumns p b * (weightedColumns p b)ᵀ

def weightedDirectionSpace (p : A → ℝ) (b : A → I → ℝ) : Submodule ℝ (I → ℝ) :=
  Submodule.span ℝ (Set.range fun a : {a // 0 < p a} => b a.val)

def normalizedCentered (v : A → I → ℝ) (x : I → ℝ) (a : A) (i : I) : ℝ :=
  (v a i-x i)/Real.sqrt (x i)

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_MatchingCovariance
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

def normalizeLinear (x : E → ℝ) :
    ({e // 0 < x e} → ℝ) →ₗ[ℝ] ({e // 0 < x e} → ℝ) where
  toFun := fun u e => u e/Real.sqrt (x e.val)
  map_add' := by intro u v; ext e; exact add_div _ _ _
  map_smul' := by intro a u; ext e; exact mul_div_assoc _ _ _

def matchingScoreWeights (x : E → ℝ) (u : {e // 0 < x e} → ℝ) : E → ℝ :=
  LooplessGraph.positiveExtension x (fun e => u e/Real.sqrt (x e.val))

end MatchingEntropy

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_FeasibilityRepair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching
noncomputable section
open Finset MatchingEntropy
variable {n : ℕ}

def TrivialCut (S : Finset (Fin n)) : Prop := S.card=1 ∨ Sᶜ.card=1

end
end BinaryMatching
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

def separableLineD (x v : E → ℝ) (t : ℝ) : ℝ :=
  entropyLineD x v t - 3 * entropyLineD (fun e => 1-x e) (fun e => -v e) t

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

def productBoolean (x : E → ℝ) (b : E → Bool) : ℝ :=
  ∏ e, if b e then x e else 1-x e

end MatchingEntropy
end
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawOptimizerData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.Optimize
open Finset
local instance instPreorderInt_solutions : Preorder ℤ := Int.instLinearOrder.toPreorder

def indexedSlope (k j : ℕ) : ℤ := if j<k then (j:ℤ)-1 else k
end BinaryMatching.Raw.Optimize
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw
open Finset

def pathFlow (p : List ℕ) (i j : ℕ) : ℤ :=
  ((p.zip p.tail).map (fun vu =>
    (if i=vu.2 ∧ j=vu.1 then 1 else 0)-(if i=vu.1 ∧ j=vu.2 then 1 else 0))).sum

end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw
open Finset

def pairs (n : ℕ) : List (ℕ×ℕ) := (List.range n).flatMap (fun i => (List.range n).map (i,·))

lemma argmin_map_eq {α β : Type} (f : α → β) (l : List α) (g : β → ℕ) :
    (l.map f).argmin g=(l.argmin (g ∘ f)).map f := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.map_append,List.map_singleton,List.argmin_concat,List.argmin_concat,ih]
    cases h : l.argmin (g ∘ f) with
    | none => rfl
    | some b => simp only [Option.map_some,Function.comp_apply]; split_ifs <;> rfl

end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawFlowSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw

lemma pathFlow_abs (p : List ℕ) (i j : ℕ) : (pathFlow p i j).natAbs≤p.length := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow]
  | singleton a => simp [pathFlow]
  | cons_cons v u p _ ih =>
    have hip := ih u
    have he : pathFlow (v::u::p) i j=
        ((if i=u ∧ j=v then 1 else 0)-(if i=v ∧ j=u then 1 else 0))+
        pathFlow (u::p) i j := by
      simp [pathFlow]
    rw [he]
    have hsmall : (((if i=u ∧ j=v then 1 else 0)-(if i=v ∧ j=u then 1 else 0)):ℤ).natAbs≤1 := by
      split_ifs <;> decide
    have h := Int.natAbs_add_le
      (((if i=u ∧ j=v then 1 else 0)-(if i=v ∧ j=u then 1 else 0)):ℤ) (pathFlow (u::p) i j)
    simp only [List.length_cons] at *
    omega

end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RecursiveEval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.RecursiveEval

inductive Branch (A B C : Type) where
  | leaf : B → Branch A B C
  | fork : C → A → A → Branch A B C

inductive Command (A C : Type) where
  | call : ℕ → A → Command A C
  | join : C → Command A C

abbrev State (A B C : Type) := List (Command A C) × List B

variable {A B C : Type} (zero : B) (expand : A → Branch A B C)
  (combine : C → B → B → B)

def value : ℕ → A → B
  | 0,_ => zero
  | k+1,a => match expand a with
    | .leaf b => b
    | .fork c x y => combine c (value k x) (value k y)

def cost : ℕ → A → ℕ
  | 0,_ => 1
  | k+1,a => match expand a with
    | .leaf _ => 1
    | .fork _ x y => 2+cost k x+cost k y

def calls : ℕ → A → ℕ
  | 0,_ => 1
  | k+1,a => match expand a with
    | .leaf _ => 1
    | .fork _ x y => 1+calls k x+calls k y

def step (s : State A B C) : State A B C :=
  match s.1 with
  | [] => s
  | .call 0 _ :: w => (w,zero::s.2)
  | .call (k+1) a :: w => match expand a with
    | .leaf b => (w,b::s.2)
    | .fork c x y => (.call k x::.call k y::.join c::w,s.2)
  | .join c :: w => match s.2 with
    | y::x::v => (w,combine c x y::v)
    | _ => ([],s.2)

lemma cost_le_calls (k : ℕ) (a : A) : cost expand k a≤2*calls expand k a := by
  induction k generalizing a with
  | zero => simp [cost,calls]
  | succ k ih =>
    simp only [cost,calls]
    cases h : expand a with
    | leaf b => simp
    | fork c x y => dsimp only; have h₁ := ih x; have h₂ := ih y; omega

lemma runs (k : ℕ) (a : A) (w : List (Command A C)) (v : List B) :
    (step zero expand combine)^[cost expand k a] (.call k a::w,v)=
      (w,value zero expand combine k a::v) := by
  induction k generalizing a w v with
  | zero => simp [cost,step,value]
  | succ k ih =>
    cases h : expand a with
    | leaf b => simp [cost,step,value,h]
    | fork c x y =>
      rw [cost,h]
      dsimp only
      have he : 2+cost expand k x+cost expand k y=(1+cost expand k y)+cost expand k x+1 := by omega
      rw [he,Function.iterate_succ_apply]
      simp only [step,h]
      rw [Function.iterate_add_apply,ih,Function.iterate_add_apply,ih]
      simp only [Function.iterate_one,step,value,h]

lemma runs_extra (k : ℕ) (a : A) (N : ℕ) (hN : cost expand k a≤N) :
    (step zero expand combine)^[N] ([.call k a],[])=
      ([],[value zero expand combine k a]) := by
  have hn : N=(N-cost expand k a)+cost expand k a := by omega
  rw [hn,Function.iterate_add_apply,runs]
  apply Function.iterate_fixed
  rfl

end BinaryMatching.RecursiveEval
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RecursiveCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.RecursiveEval

def branchRepr {A B C : Type} : Branch A B C → Sum B (C×(A×A))
  | .leaf b => .inl b
  | .fork c x y => .inr (c,(x,y))
def commandRepr {A C : Type} : Command A C → Sum (ℕ×A) C
  | .call k a => .inl (k,a)
  | .join c => .inr c
instance instInhabitedCommand {A C : Type} [Inhabited A] : Inhabited (Command A C) := ⟨.call 0 default⟩

end BinaryMatching.RecursiveEval
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawOddBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw
open RecursiveEval

def oddWordBound (n B : ℕ) : ℕ := 1000*(n+1)^2*(B+1)
def oddBudget (n B : ℕ) : ℕ := 100000*(n+1)^3*(B+1)

end BinaryMatching.Raw
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawOptimizerRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.Optimize
open Finset
local instance instPreorderInt_solutions_1 : Preorder ℤ := Int.instLinearOrder.toPreorder

end BinaryMatching.Raw.Optimize
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawOptimizerDataCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.Optimize.Compiler
local instance instPreorderInt_solutions : Preorder ℤ := Int.instLinearOrder.toPreorder

end BinaryMatching.Raw.Optimize.Compiler
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_RawOptimizerRowsCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.Optimize.Compiler
local instance instPreorderInt_solutions_1 : Preorder ℤ := Int.instLinearOrder.toPreorder

end BinaryMatching.Raw.Optimize.Compiler
end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.MatchingCount_BinarySolve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Raw.InputData
open Optimize

def powerBits (k : ℕ) : List Bool := List.replicate k false++[true]
lemma powerBits_eq (k : ℕ) : powerBits k=(2^k).bits := by
  induction k with
  | zero => simp [powerBits]
  | succ k ih =>
    rw [pow_succ,Nat.mul_comm,Nat.bit0_bits (2^k) (by positivity)]
    simpa only [powerBits,List.replicate_succ,List.cons_append] using congrArg (List.cons false) ih
end BinaryMatching.Raw.InputData

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_BitAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.BitAdd

def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

def xor (a b : Bool) : Bool := if a then !b else b
def digit (a b c : Bool) : Bool := xor (xor a b) c
def carry (a b c : Bool) : Bool := (a && b) || (c && (a || b))

lemma fullAdder (a b c : Bool) :
    a.toNat + b.toNat + c.toNat = (digit a b c).toNat + 2 * (carry a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

lemma value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih => simp only [List.cons_append, value, List.length_cons, pow_succ, ih]; ring

lemma value_head_tail (xs : List Bool) :
    value xs = (xs.headD false).toNat + 2 * value xs.tail := by
  cases xs <;> rfl

abbrev State := (List Bool × List Bool) × (Bool × List Bool)

def step (z : State × Bool) : State :=
  ((z.1.1.1.tail, z.1.1.2.tail),
    (carry (z.1.1.1.headD false) (z.1.1.2.headD false) z.1.2.1,
     z.1.2.2 ++ [digit (z.1.1.1.headD false) (z.1.1.2.headD false) z.1.2.1]))

def initial (z : List Bool × List Bool) : State := (z, (false, []))
def finish (s : State) : List Bool := s.2.2 ++ if s.2.1 then [true] else []

def run (l : List Bool) (s : State) : State := l.foldl (fun s b => step (s,b)) s

def add (z : List Bool × List Bool) : List Bool :=
  finish (run (z.1 ++ z.2) (initial z))

def potential (s : State) : ℕ :=
  value s.2.2 + 2 ^ s.2.2.length * (value s.1.1 + value s.1.2 + s.2.1.toNat)

lemma potential_step (s : State) (b : Bool) : potential (step (s,b)) = potential s := by
  rcases s with ⟨⟨xs,ys⟩,c,os⟩
  have h := fullAdder (xs.headD false) (ys.headD false) c
  have hx := value_head_tail xs
  have hy := value_head_tail ys
  simp only [potential, step, value_append, List.length_append, List.length_singleton,
    value, mul_zero, add_zero, pow_succ]
  rw [hx, hy]
  calc
    _ = value os + 2 ^ os.length *
        ((xs.headD false).toNat + (ys.headD false).toNat + c.toNat +
          2 * (value xs.tail + value ys.tail)) := by
      rw [h]
      ring
    _ = _ := by ring

lemma potential_run (l : List Bool) (s : State) : potential (run l s) = potential s := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih =>
    change potential (run l (step (s,b))) = potential s
    rw [ih, potential_step]

lemma run_inputs (l : List Bool) (s : State) :
    (run l s).1 = (s.1.1.drop l.length, s.1.2.drop l.length) := by
  induction l generalizing s with
  | nil => simp [run]
  | cons b l ih =>
    change (run l (step (s,b))).1 = _
    rw [ih]
    simp only [step, List.length_cons]
    congr 1 <;> simp [List.drop_tail]

lemma value_finish (s : State) (h : s.1 = ([], [])) : value (finish s) = potential s := by
  rcases s with ⟨⟨xs,ys⟩,c,os⟩
  cases h
  cases c <;> simp [finish, potential, value_append, value]

theorem value_add (z : List Bool × List Bool) : value (add z) = value z.1 + value z.2 := by
  have hi : (run (z.1 ++ z.2) (initial z)).1 = ([], []) := by
    rw [run_inputs]
    simp only [initial, List.length_append]
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
  rw [add, value_finish _ hi, potential_run]
  simp [potential, initial, value]

lemma value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    cases b <;> simp [value, ih, Nat.bit, Nat.add_comm]

end LoopMatching.BitAdd

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_BitLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.BitAdd

lemma value_lt_two_pow_length (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    cases b <;>
      simp only [value, Bool.toNat_false, Bool.toNat_true, List.length_cons,
        pow_succ] <;> omega

lemma length_bits_value_add (xs ys : List Bool) :
    (value xs + value ys).bits.length ≤ max xs.length ys.length + 1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hx : value xs < 2 ^ max xs.length ys.length :=
    (value_lt_two_pow_length xs).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have hy : value ys < 2 ^ max xs.length ys.length :=
    (value_lt_two_pow_length ys).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  rw [pow_succ]
  omega

end LoopMatching.BitAdd

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_BitNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.BitNormalize
open BitAdd (value)

def step (z : List Bool × Bool) : List Bool :=
  if z.2 then true :: z.1 else if z.1.isEmpty then [] else false :: z.1

def normalize (l : List Bool) : List Bool :=
  l.foldr (fun b acc => step (acc,b)) []

lemma normalize_cons (b : Bool) (l : List Bool) :
    normalize (b::l) = step (normalize l,b) := rfl

lemma step_length (l : List Bool) (b : Bool) :
    (step (l,b)).length ≤ l.length+1 := by
  cases b <;> cases l <;> simp [step]

lemma value_step (l : List Bool) (b : Bool) :
    value (step (l,b)) = b.toNat + 2*value l := by
  cases b <;> cases l <;> simp [step, value]

theorem value_normalize (l : List Bool) : value (normalize l) = value l := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [normalize_cons, value_step, ih]; rfl

theorem normalize_eq_bits (l : List Bool) : normalize l = (value l).bits := by
  induction l with
  | nil => simp [normalize, value]
  | cons b l ih =>
    rw [normalize_cons, ih]
    by_cases hz : value l = 0
    · cases b <;> simp [step, value, hz]
    · have hb : value l = 0 → b = true := fun h => (hz h).elim
      have hn : (value l).bits ≠ [] := by
        intro h
        have hv := BitAdd.value_bits (value l)
        rw [h] at hv
        exact hz hv.symm
      have he : ((value l).bits).isEmpty = false := by
        cases h : (value l).bits with
        | nil => exact (hn h).elim
        | cons a as => rfl
      have hv : value (b::l) = Nat.bit b (value l) := by
        cases b <;> simp [value, Nat.bit]; omega
      rw [hv, Nat.bits_append_bit _ _ hb]
      cases b <;> simp [step, he]

end LoopMatching.BitNormalize

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_BinaryMultiply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.SmallBinaryMultiply
open Polynomial

abbrev State := List Bool × List Bool

def initial (z : ℕ × List Bool) : State := (z.2, [])

end LoopMatching.SmallBinaryMultiply

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

open scoped BigOperators

namespace LoopMatching

noncomputable def countWithLoops (G : Input) (j : ℕ) : ℕ := by
  classical
  exact ∑ M : PartialMatching G.n,
    if (loopVertices M).card = j then weight G M else 0

end LoopMatching

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_ExpandInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching

def crossRecord (n : ℕ) (r : LoopRecord) (d : ℕ) : BinaryMatching.Record :=
  ⟨r.vertex, n + d, r.multiplicity⟩

def crossRecords (n j : ℕ) (rs : List LoopRecord) : List BinaryMatching.Record :=
  rs.flatMap fun r => (List.range j).map (crossRecord n r)

lemma mem_crossRecords {n j : ℕ} {rs : List LoopRecord} {e : BinaryMatching.Record} :
    e ∈ crossRecords n j rs ↔ ∃ r ∈ rs, ∃ d < j, crossRecord n r d = e := by
  simp [crossRecords]

lemma crossRecords_unique (n j : ℕ) (rs : List LoopRecord)
    (h : (rs.map LoopRecord.vertex).Nodup) :
    ((crossRecords n j rs).map (fun e => (e.left,e.right))).Nodup := by
  induction rs with
  | nil => simp [crossRecords]
  | cons r rs ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp h
    simp only [crossRecords, List.flatMap_cons, List.map_append, List.map_map]
    apply List.nodup_append.mpr
    refine ⟨?_, ih ht, ?_⟩
    · apply (List.nodup_range (n := j)).map
      intro a b hab
      have hh := congrArg Prod.snd hab
      dsimp [Function.comp_def, crossRecord] at hh
      omega
    · intro a ha b hb hab
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp ha
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
      obtain ⟨s,hs,c,hc,rfl⟩ := mem_crossRecords.mp he
      have hv := congrArg Prod.fst hab
      dsimp [Function.comp_def, crossRecord] at hv
      exact hn (List.mem_map.mpr ⟨s,hs,hv.symm⟩)

def expand (G : Input) (j : ℕ) : BinaryMatching.Input where
  n := G.n + j
  records := G.ordinary.records ++ crossRecords G.n j G.loops
  valid := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨hlt,hbound⟩ := G.ordinary.valid e he
      change e.right < G.n at hbound
      exact ⟨hlt,by omega⟩
    · obtain ⟨r,hr,d,hd,rfl⟩ := mem_crossRecords.mp he
      have hrn := G.valid r hr
      change r.vertex < G.n at hrn
      dsimp [crossRecord]
      constructor <;> omega
  unique := by
    rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨G.ordinary.unique, crossRecords_unique _ _ _ G.unique, ?_⟩
    intro a ha b hb hab
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hb
    obtain ⟨r,hr,d,hd,rfl⟩ := mem_crossRecords.mp hf
    have hn := (G.ordinary.valid e he).2
    change e.right < G.n at hn
    have hh := congrArg Prod.snd hab
    dsimp [crossRecord] at hh
    omega

@[simp] lemma expand_n (G : Input) (j : ℕ) : (expand G j).n = G.n+j := rfl

def oldPair (G : Input) (j : ℕ) (e : BinaryMatching.Pair G.n) :
    BinaryMatching.Pair (expand G j).n :=
  ⟨(⟨e.val.1.val,by have := e.val.1.isLt; simp only [expand_n]; omega⟩,
    ⟨e.val.2.val,by have := e.val.2.isLt; simp only [expand_n]; omega⟩),e.property⟩

def crossPair (G : Input) (j : ℕ) (v : Fin G.n) (d : Fin j) :
    BinaryMatching.Pair (expand G j).n :=
  ⟨(⟨v.val,by have := v.isLt; simp only [expand_n]; omega⟩,
    ⟨G.n+d.val,by have := d.isLt; simp only [expand_n]; omega⟩),by
      change v.val < G.n+d.val
      have := v.isLt
      omega⟩

def dummyPair (G : Input) (j : ℕ) (e : BinaryMatching.Pair j) :
    BinaryMatching.Pair (expand G j).n :=
  ⟨(⟨G.n+e.val.1.val,by have := e.val.1.isLt; simp only [expand_n]; omega⟩,
    ⟨G.n+e.val.2.val,by have := e.val.2.isLt; simp only [expand_n]; omega⟩),by
      change G.n+e.val.1.val < G.n+e.val.2.val
      have := e.property
      exact Nat.add_lt_add_left this _⟩

end LoopMatching

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_ExpandBijection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

noncomputable section
open scoped BigOperators
namespace LoopMatching

def oldVertex (G : Input) (j : ℕ) (v : Fin G.n) : Fin (expand G j).n :=
  ⟨v.val, by have := v.isLt; simp only [expand_n]; omega⟩

def dummyVertex (G : Input) (j : ℕ) (d : Fin j) : Fin (expand G j).n :=
  ⟨G.n + d.val, by have := d.isLt; simp only [expand_n]; omega⟩

@[simp] lemma incident_oldPair (G : Input) (j : ℕ) (v : Fin G.n)
    (e : BinaryMatching.Pair G.n) :
    (BinaryMatching.completeGraph (expand G j).n).Incident
      (oldVertex G j v) (oldPair G j e) ↔
    (BinaryMatching.completeGraph G.n).Incident v e := by
  simp [MatchingEntropy.LooplessGraph.Incident, BinaryMatching.completeGraph,
    oldVertex, oldPair, Fin.ext_iff]

lemma oldPair_injective (G : Input) (j : ℕ) : Function.Injective (oldPair G j) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg (fun p => p.val.1.val) h
  · exact congrArg (fun p => p.val.2.val) h

lemma crossPair_injective (G : Input) (j : ℕ) {v w : Fin G.n} {d c : Fin j}
    (h : crossPair G j v d = crossPair G j w c) : v = w ∧ d = c := by
  constructor
  · apply Fin.ext
    exact congrArg (fun p => p.val.1.val) h
  · apply Fin.ext
    have hh := congrArg (fun p => p.val.2.val) h
    dsimp [crossPair] at hh
    omega

lemma oldPair_ne_crossPair (G : Input) (j : ℕ) (e : BinaryMatching.Pair G.n)
    (v : Fin G.n) (d : Fin j) : oldPair G j e ≠ crossPair G j v d := by
  intro h
  have hh := congrArg (fun p => p.val.2.val) h
  have he := e.val.2.isLt
  dsimp [oldPair, crossPair] at hh
  omega

end LoopMatching

end

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_InputMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.InputMachine
open BinaryMatching

abbrev LoopData := ℕ × List Bool

def loopRepr (r : LoopRecord) : LoopData := (r.vertex,r.multiplicity.bits)

end LoopMatching.InputMachine

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_InputDecode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.InputMachine
open BinaryMatching

abbrev LoopBits := List Bool × List Bool

def loopBitsRepr (r : LoopRecord) : LoopBits := (r.vertex.bits,r.multiplicity.bits)

end LoopMatching.InputMachine

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_LoopParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.InputMachine
open BinaryMatching Polynomial

lemma encodeLoopRecord_ne_nil (r : LoopRecord) : encodeLoopRecord r≠[] := by
  simp [encodeLoopRecord,encodeNat]

lemma loopRecords_length_le_bits (rs : List LoopRecord) :
    rs.length ≤ (rs.flatMap encodeLoopRecord).length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hr := List.length_pos_iff.mpr (encodeLoopRecord_ne_nil r)
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

end LoopMatching.InputMachine

end OAI
end

section
-- module Solutions.OAIW2_LoopMatching.LoopMatching_SparseBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching

def recordedVertices (G : Input) : Finset ℕ :=
  (G.ordinary.records.map BinaryMatching.Record.left ++
    G.ordinary.records.map BinaryMatching.Record.right ++
    G.loops.map LoopRecord.vertex).toFinset

end LoopMatching

end OAI
end


