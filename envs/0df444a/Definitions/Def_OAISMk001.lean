-- Prove2me | Definitions.Def_OAISMk001
-- name    : OAISMk001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T10:37:34.399444+00:00
-- url     : https://prove2.me/theorems/37724c84-cefa-4ec1-ac5c-efa2f193ffde
-- title:
--   Definitions bundle OAISMk001 of the split of OpenAI, Nontrivial Markov Type Forces Superreflexivity
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm`, carved from OpenAI's openai/math development (OpenAI, *Nontrivial Markov Type Forces Superreflexivity*, OpenAI Math Release, September 23, 2026, result family 327, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 39 declarations of OpenAI's Lean: 27 definitions and 12 theorems. The definitions and types are `OAI.MarkovSuperreflexivity.CoordinateCopies`, `OAI.MarkovSuperreflexivity.OrderedComparison`, `OAI.MarkovSuperreflexivity.RowCoefficientGrid`, `OAI.MarkovSuperreflexivity.RowPalette`, `OAI.MarkovSuperreflexivity.boundedNormBin`, `OAI.MarkovSuperreflexivity.cubeBlend`, `OAI.MarkovSuperreflexivity.cubeBlock`, `OAI.MarkovSuperreflexivity.decreaseRamseyTarget`, `OAI.MarkovSuperreflexivity.eventualKernelSubmodule`, `OAI.MarkovSuperreflexivity.normStrongDualSubmodule`, `OAI.MarkovSuperreflexivity.pathReverse`, `OAI.MarkovSuperreflexivity.pathReverseEquiv`, `OAI.MarkovSuperreflexivity.pathTake`, `OAI.MarkovSuperreflexivity.periodicIoo`, `OAI.MarkovSuperreflexivity.sampledEvenIndex`, `OAI.MarkovSuperreflexivity.sampledKey`, `OAI.MarkovSuperreflexivity.sampledOddIndex`, `OAI.MarkovSuperreflexivity.selectedBlockCuts`, `OAI.MarkovSuperreflexivity.smallCut`, `OAI.MarkovSuperreflexivity.smoothnessDeviations`, `OAI.MarkovSuperreflexivity.smoothnessModulus`, `OAI.MarkovSuperreflexivity.spreadingRescale`, `OAI.MarkovSuperreflexivity.walkError`, `OAI.MarkovSuperreflexivity.walkSampleInteger`, `OAI.MarkovSuperreflexivity.walkWindowLeft`, `OAI.MarkovSuperreflexivity.walkWindowPairs`, `OAI.MarkovSuperreflexivity.walkWindowRight`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/MarkovType, in whole or in part: `MarkovType_ChartAveraging`, `MarkovType_CoefficientSelectedBlocks`, `MarkovType_FiniteAnnihilator`, `MarkovType_FiniteMarcinkiewicz`, `MarkovType_FinitePaths`, `MarkovType_FiniteRamsey`, `MarkovType_HomogeneousRows`, `MarkovType_JamesCubeImprovement`, `MarkovType_PeriodicArcs`, `MarkovType_ReversibleMartingales`, `MarkovType_SmoothnessBounds`, `MarkovType_SpreadingLimitEmbedding`, `MarkovType_TriangularNonreflexivity`, `MarkovType_WalkDisplacement`, `MarkovType_WalkParameters`.
--
--   **Imports.** It imports the published bundle `Def_MarkovType`.
--
--   **Imported by** (directly, in this split): the bundle `OAISMk002`; the statement `OAI.MarkovSuperreflexivity.exists_power_smooth_equivalentNorm`.
-- source:
--   OpenAI, Nontrivial Markov Type Forces Superreflexivity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 327; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nontrivial-Markov-Type-Forces-Superreflexivity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/MarkovType at commit adc7f12

import Mathlib
import Init.Data.List.Count
import Lean.Elab.Tactic.Omega
import Definitions.Def_MarkovType

section
-- module Solutions.OAIS_Markov.Compat
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
-- module Solutions.OAIS_Markov.MarkovType_FiniteRamsey
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

def decreaseRamseyTarget.{v} {κ : Type v} [DecidableEq κ]
    (targets : κ → ℕ) (i j : κ) : ℕ :=
  if j = i then targets j - 1 else targets j

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ChartAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity

abbrev OrderedComparison (k : ℕ) :=
  Σ m : Fin (k + 1), ((Fin m.val ↪o Fin k) × (Fin m.val ↪o Fin k))

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientSelectedBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n m : ℕ}

def selectedBlockCuts (e : Fin m ↪o Fin n) (j : Fin (m + 1)) : ℕ :=
  if hj : j.val < m then
    if j.val = 0 then 0 else (e ⟨j.val, hj⟩).val
  else n

@[simp] theorem selectedBlockCuts_castSucc (e : Fin m ↪o Fin n) (j : Fin m) :
    selectedBlockCuts e j.castSucc = if j.val = 0 then 0 else (e j).val := by
  simp [selectedBlockCuts, j.is_lt]

@[simp] theorem selectedBlockCuts_last (e : Fin m ↪o Fin n) :
    selectedBlockCuts e (Fin.last m) = n := by
  simp [selectedBlockCuts]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteAnnihilator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open NormedSpace StrongDual

universe u

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local instance normStrongDualSubmodule (A : Submodule ℝ (StrongDual ℝ Y)) :
    Norm (StrongDual ℝ A) :=
  ContinuousLinearMap.hasOpNorm
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := A) (F := ℝ) (σ₁₂ := RingHom.id ℝ)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteMarcinkiewicz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace MarkovSuperreflexivity

variable {I Ω E F : Type*} [sectionFintypeI : Fintype I] [Fintype Ω]
  [NormedAddCommGroup E] [NormedAddCommGroup F]

noncomputable def smallCut (φ : I → E) (t : ℝ) : I → E :=
  fun i => if t < ‖φ i‖ then 0 else φ i

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FinitePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S : Type*} [sectionFintypeS : Fintype S]

def pathReverse {n : ℕ} (ω : StatePath S n) : StatePath S n :=
  fun i => ω i.rev

omit sectionFintypeS in
@[simp] theorem pathReverse_reverse [Fintype S] {n : ℕ} (ω : StatePath S n) :
    pathReverse (pathReverse ω) = ω := by
  funext i
  simp [pathReverse]

def pathReverseEquiv (n : ℕ) : StatePath S n ≃ StatePath S n where
  toFun := pathReverse
  invFun := pathReverse
  left_inv := pathReverse_reverse
  right_inv := pathReverse_reverse

def pathTake {n : ℕ} (k : ℕ) (hk : k ≤ n) (ω : StatePath S n) : StatePath S k :=
  fun i => ω (Fin.castLE (Nat.add_le_add_right hk 1) i)

omit sectionFintypeS in
@[simp] theorem pathTake_self [Fintype S] {n : ℕ} (ω : StatePath S n) :
    pathTake n le_rfl ω = ω := by
  funext i
  rfl

omit sectionFintypeS in
@[simp] theorem pathTake_snoc [Fintype S] {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (ω : StatePath S n) (t : S) :
    pathTake k (Nat.le_trans hk (Nat.le_succ n)) (Fin.snoc ω t) =
      pathTake k hk ω := by
  funext i
  change Fin.snoc (α := fun _ : Fin (n + 1 + 1) => S) ω t
    ((Fin.castLE (Nat.add_le_add_right hk 1) i).castSucc) = _
  exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1 + 1) => S) t ω
    (Fin.castLE (Nat.add_le_add_right hk 1) i)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_HomogeneousRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

noncomputable section

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

abbrev RowCoefficientGrid (k m : ℕ) := Fin m → Fin (2 * k ^ 2 + 1)

abbrev RowPalette (k m : ℕ) := RowCoefficientGrid k m → Fin (k * m + 1)

def boundedNormBin (k m : ℕ) (z : ℝ) (hz : z ≤ (m : ℝ)) :
    Fin (k * m + 1) :=
  ⟨⌊(k : ℝ) * z⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le (by
    simpa only [Nat.cast_mul] using
      mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg k)))⟩

end

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_JamesCubeImprovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

def CoordinateCopies (c B : ℝ) : Prop :=
  ∀ n : ℕ, ∃ T : (Fin n → ℝ) →ₗ[ℝ] X,
    (∀ i : Fin n, c ≤ ‖T (Pi.single i 1)‖) ∧
    ∀ a, ‖T a‖ ≤ B * ‖a‖

def cubeBlock {n m : ℕ} (e : Fin n × Fin m ≃ Fin (n * m))
    (i : Fin n) : (Fin m → ℝ) →ₗ[ℝ] (Fin (n * m) → ℝ) where
  toFun a k := if (e.symm k).1 = i then a (e.symm k).2 else 0
  map_add' a b := by
    ext k
    by_cases h : (e.symm k).1 = i <;> simp [h]
  map_smul' r a := by
    ext k
    by_cases h : (e.symm k).1 = i <;> simp [h]

def cubeBlend {n m : ℕ} (e : Fin n × Fin m ≃ Fin (n * m))
    (b : Fin n → Fin m → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin (n * m) → ℝ) where
  toFun a k := a (e.symm k).1 * b (e.symm k).1 (e.symm k).2
  map_add' a a' := by
    ext k
    exact add_mul _ _ _
  map_smul' r a := by
    ext k
    change (r * a (e.symm k).1) * b (e.symm k).1 (e.symm k).2 =
      r * (a (e.symm k).1 * b (e.symm k).1 (e.symm k).2)
    exact mul_assoc _ _ _

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_PeriodicArcs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

def periodicIoo (a b : ℝ) : Set ℝ := {x | ∃ j : ℤ, a + j < x ∧ x < b + j}

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ReversibleMartingales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {S X : Type*} [Fintype S]
variable [NormedAddCommGroup X] [sectionNormedSpaceℝX : NormedSpace ℝ X]

def sampledEvenIndex {m : ℕ} (j : Fin (m + 1)) : Fin (2 * m + 1) :=
  ⟨2 * j.val, by omega⟩

def sampledOddIndex {m : ℕ} (j : Fin m) : Fin (2 * m + 1) :=
  ⟨2 * j.val + 1, by omega⟩

def sampledKey (m : ℕ) (k : Fin m) (ω : StatePath S (2 * m)) :
    StatePath S (2 * k.val) :=
  pathTake (2 * k.val) (by omega) ω

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SmoothnessBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

def smoothnessDeviations (p : Seminorm ℝ X) (t : ℝ) : Set ℝ :=
  {d | ∃ x y : X, p x = 1 ∧ p y = 1 ∧
    d = (p (x + t • y) + p (x - t • y)) / 2 - 1}

def smoothnessModulus (p : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sSup (insert 0 (smoothnessDeviations p t))

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_SpreadingLimitEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {E Y : Type*}
variable [AddCommGroup E] [Module ℝ E]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def spreadingRescale (δ : ℝ) (S : E →ₗ[ℝ] Y) : E →ₗ[ℝ] Y :=
  (1 - δ)⁻¹ • S

@[simp] theorem spreadingRescale_apply (δ : ℝ) (S : E →ₗ[ℝ] Y) (x : E) :
    spreadingRescale δ S x = (1 - δ)⁻¹ • S x := rfl

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularNonreflexivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

universe u

variable {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem unit_eval_abs_le (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1)
    (g : StrongDual ℝ Z) (i : ℕ) : |g (e i)| ≤ ‖g‖ := by
  calc
    |g (e i)| = ‖g (e i)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖g‖ * ‖e i‖ := g.le_opNorm (e i)
    _ ≤ ‖g‖ * 1 := mul_le_mul_of_nonneg_left (he i) (norm_nonneg g)
    _ = ‖g‖ := mul_one _

def eventualKernelSubmodule (f : ℕ → StrongDual ℝ Z) : Submodule ℝ Z where
  carrier := {x | ∀ᶠ j in atTop, f j x = 0}
  zero_mem' := Filter.Eventually.of_forall (fun j => (f j).map_zero)
  add_mem' := by
    intro x y hx hy
    exact (hx.and hy).mono (fun j hj => by rw [map_add, hj.1, hj.2, add_zero])
  smul_mem' := by
    intro c x hx
    exact hx.mono (fun j hj => by rw [map_smul, hj, smul_zero])

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

def walkWindowLeft (n : ℕ) : ℕ := 2 * (n + 1)

def walkWindowRight (n : ℕ) : ℕ := 6 * (n + 1)

def walkWindowPairs (n : ℕ) : ℕ := 4 * (n + 1)

noncomputable def walkError (n : ℕ) : ℝ := 1 / (10 * (n : ℝ))

@[simp] theorem walkWindowPairs_pos (n : ℕ) : 0 < walkWindowPairs n := by
  simp [walkWindowPairs]

theorem walk_floor_bounds {n : ℕ} {x : ℝ}
    (hx : |x| < 2 * (n : ℝ)) :
    -(2 * (n : ℤ)) ≤ Int.floor x ∧ Int.floor x ≤ 2 * (n : ℤ) - 1 := by
  rcases abs_lt.mp hx with ⟨hlo, hhi⟩
  constructor
  · apply Int.le_floor.mpr
    push_cast
    exact hlo.le
  · have hf : Int.floor x < 2 * (n : ℤ) := by
      apply Int.floor_lt.mpr
      push_cast
      exact hhi
    omega

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkDisplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

def walkSampleInteger (n : ℕ) (i : Fin (walkWindowPairs n + 1)) : ℤ :=
  (walkWindowLeft n : ℤ) + (i.val : ℤ)

@[simp] theorem walkSampleInteger_succ (n : ℕ) (i : Fin (walkWindowPairs n)) :
    walkSampleInteger n i.succ = walkSampleInteger n i.castSucc + 1 := by
  simp [walkSampleInteger, Nat.cast_add, Nat.cast_one, add_assoc]

end MarkovSuperreflexivity

end

end OAI
end


