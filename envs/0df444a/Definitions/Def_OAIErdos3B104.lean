-- Prove2me | Definitions.Def_OAIErdos3B104
-- name    : OAIErdos3B104
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T18:55:18.934948+00:00
-- url     : https://prove2.me/theorems/f680e28d-2a4e-4036-a32e-67223f200982
-- title:
--   OpenAI Erdős-3 split, definitions bundle 105 of 106
-- statement:
--   Definitions bundle 105 of 106 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B103`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 105 available.
--
--   Modules: `OAI.Erdos3.NativeNilsequenceExpansion`, `OAI.Erdos3.NativeNilsequenceExpansion.conjugate`, `OAI.Erdos3.NativeNilsequenceExpansion.mono`, `OAI.Erdos3.NativeVectorEquivalence.casesOn`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B098

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeNilsequenceExpansion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeNilsequenceExpansion (s N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℂ) where
  count : ℕ
  count_bound : (count : ℝ) ≤ Real.exp p
  L : Fin count → Type
  [lie : ∀ i, LieRing (L i)]
  [algebra : ∀ i, LieAlgebra ℚ (L i)]
  dim : Fin count → ℕ
  [topology : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
  [topologicalAdd : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [continuousSMul : ∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)]
  [hausdorff : ∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  model : ∀ i, RationalFilteredNilmanifold (L i) s (dim i)
  test : ∀ i, (model i).Niltest (fun _ : Unit => 1)
  complexity : ∀ i, (test i).ComplexityLE p
  coefficient : Fin count → ℂ
  cost : (∑ i, ‖coefficient i‖) ≤ Real.exp p
  eval : ∀ x, f x = ∑ i, coefficient i * (test i).evalCyclic N (fun _ => x)

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff

namespace NativeNilsequenceExpansion

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}

noncomputable def mono (E : NativeNilsequenceExpansion s N p f) (hpq : p ≤ q) :
    NativeNilsequenceExpansion s N q f :=
  { E with
    count_bound := E.count_bound.trans (Real.exp_le_exp.mpr hpq)
    complexity := fun i => (E.complexity i).mono hpq
    cost := E.cost.trans (Real.exp_le_exp.mpr hpq) }

noncomputable def conjugate (E : NativeNilsequenceExpansion s N p f) :
    NativeNilsequenceExpansion s N p (fun x => star (f x)) :=
  { E with
    test := fun i => (E.test i).conjugate
    complexity := E.complexity
    coefficient := fun i => star (E.coefficient i)
    cost := by simpa only [norm_star] using E.cost
    eval := by
      intro x
      have h := congrArg star (E.eval x)
      simpa only [star_sum, star_mul, mul_comm, RationalFilteredNilmanifold.Niltest.evalCyclic,
        RationalFilteredNilmanifold.Niltest.eval_conjugate] using h }

end NativeNilsequenceExpansion

structure NativeVectorEquivalence {J K : Type*} [Fintype J] [Fintype K]
    (s N : ℕ) [NeZero N] (p : ℝ) (chi : J → ZMod N → ℂ) (chi' : K → ZMod N → ℂ) : Prop where
  left_dimension : (Fintype.card J : ℝ) ≤ Real.exp p
  right_dimension : (Fintype.card K : ℝ) ≤ Real.exp p
  expansion : ∀ j k, Nonempty (NativeNilsequenceExpansion s N p
    (fun x => chi j x * star (chi' k x)))

end Erdos3

end

end OAI

end


