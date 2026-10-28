-- Prove2me | Definitions.Def_OAIEG018
-- name    : OAIEG018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-24T23:57:21.4635+00:00
-- url     : https://prove2.me/theorems/9f306804-cff1-4d7f-b44e-6adcc1e8a80a
-- title:
--   Definitions bundle OAIEG018 of the split of OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, carved from OpenAI's openai/math development (OpenAI, *A finitely generated counterexample to the Eilenberg–Ganea conjecture*, OpenAI Math Release, September 23, 2026, result family 249, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 30 definitions, 1 instance and 17 theorems. The definitions and types are `OAI.EilenbergGanea.SeedEncoding.cellEquiv`, `OAI.EilenbergGanea.TraceWords.CubeDescents.artinDescentSystem`, `OAI.EilenbergGanea.TraceWords.CubeDescents.descendingChains`, `OAI.EilenbergGanea.TraceWords.CubeDescents.leastDescent`, `OAI.EilenbergGanea.TraceWords.CubeDescents.positiveChains`, `OAI.EilenbergGanea.arcBlend`, `OAI.EilenbergGanea.cayleySyzygyDifferential`, `OAI.EilenbergGanea.cutoffCoefficientProducts`, `OAI.EilenbergGanea.edgeDifferences`, `OAI.EilenbergGanea.edgeGenerated`, `OAI.EilenbergGanea.generatorExponent`, `OAI.EilenbergGanea.heightDifference`, `OAI.EilenbergGanea.inverseNormalFactor`, `OAI.EilenbergGanea.linkSubgroup`, `OAI.EilenbergGanea.normalFactorCount`, `OAI.EilenbergGanea.normalFactorWord`, `OAI.EilenbergGanea.optionForward`, `OAI.EilenbergGanea.optionGenerator`, `OAI.EilenbergGanea.optionSemidirect`, `OAI.EilenbergGanea.pathSpelling`, `OAI.EilenbergGanea.radialWordMap`, `OAI.EilenbergGanea.seedXUnit`, `OAI.EilenbergGanea.selectedWord`, `OAI.EilenbergGanea.signedDisplacement`, `OAI.EilenbergGanea.smallQuaternionArc`, `OAI.EilenbergGanea.smoothRadialCoefficientWordMap`, `OAI.EilenbergGanea.smoothRadialWordMap`, `OAI.EilenbergGanea.splitWordMap`, `OAI.EilenbergGanea.wordMap`, `OAI.SimplicialChains.Contraction.reindex`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory, in whole or in part: `CliqueCohomology`, `Cubical_ArtinChains`, `IntegralModules`, `Integral_Contraction`, `PresentationAlignment`, `PresentationComparison`, `RightAngledArtin_Basic`, `RightAngledArtin_ResidualFiniteness`, `SeedChains`, `SeedHolonomy`, `Simplicial_Chains`, `SmallHolonomy`, `UnitaryWords`, `WordEquations`.
--
--   **Imports.** It imports the published bundle `Def_EilenbergGanea`; the bundles `OAIEG000`, `OAIEG001`, `OAIEG002`, `OAIEG003`, `OAIEG004`, `OAIEG005` and `OAIEG006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIEG022`; the proof of `OAI.EilenbergGanea.source_finitely_generated`.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_EilenbergGanea
import Definitions.Def_OAIEG000
import Definitions.Def_OAIEG001
import Definitions.Def_OAIEG002
import Definitions.Def_OAIEG003
import Definitions.Def_OAIEG004
import Definitions.Def_OAIEG005
import Definitions.Def_OAIEG006

section
-- module Solutions.OAIEG.RightAngledArtin_Basic
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea


section FiniteGeneration
variable {V : Type*} (L : SimpleGraph V)

def edgeDifferences : Set (ArtinGroup L) :=
  {x | ∃ v w, L.Adj v w ∧ x = artinGenerator L v * (artinGenerator L w)⁻¹}

def edgeGenerated : Subgroup (ArtinGroup L) := Subgroup.closure (edgeDifferences L)

end FiniteGeneration

end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.RightAngledArtin_ResidualFiniteness
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
universe u
/-! Finite permutation separation for free groups. -/

section ArtinOption

variable {V : Type*} (L : SimpleGraph (Option V))

def linkSubgroup : Subgroup (deletedGroup L) :=
  Subgroup.closure {g | ∃ v, L.Adj none (some v) ∧ g = artinGenerator (deletedGraph L) v}

abbrev optionSemidirect :=
  FreeGroup (deletedGroup L ⧸ linkSubgroup L) ⋊[freeAction _ _] deletedGroup L

def optionGenerator : Option V → optionSemidirect L
  | none => SemidirectProduct.inl (FreeGroup.of (QuotientGroup.mk 1))
  | some v => SemidirectProduct.inr (artinGenerator (deletedGraph L) v)

theorem optionGenerator_commute (v w : Option V) (h : L.Adj v w) :
    Commute (optionGenerator L v) (optionGenerator L w) := by
  have hnew (a : V) (ha : L.Adj none (some a)) :
      Commute (optionGenerator L none) (optionGenerator L (some a)) := by
    have hc : (QuotientGroup.mk (artinGenerator (deletedGraph L) a) :
        deletedGroup L ⧸ linkSubgroup L) = QuotientGroup.mk 1 := by
      apply QuotientGroup.eq.mpr
      simpa only [mul_one] using
        (linkSubgroup L).inv_mem (Subgroup.subset_closure ⟨a, ha, rfl⟩)
    apply SemidirectProduct.ext
    · simp [optionGenerator, freeAction_of, MulAction.Quotient.smul_mk, hc]
    · simp [optionGenerator]
  cases v with
  | none =>
    cases w with
    | none => exact False.elim (L.ne_of_adj h rfl)
    | some a => exact hnew a h
  | some a =>
    cases w with
    | none => exact (hnew a h.symm).symm
    | some b =>
      exact (adjacent_generators_commute (deletedGraph L) h).map SemidirectProduct.inr

def optionForward : ArtinGroup L →* optionSemidirect L :=
  artinLift L (optionGenerator L) (optionGenerator_commute L)

end ArtinOption


end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.CliqueCohomology
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
section CliqueSquare
variable {V : Type*} (L : SimpleGraph V)

 def generatorExponent (v : V) : ArtinGroup L →* Multiplicative ℤ := by
  classical
  exact artinLift L (fun w => Multiplicative.ofAdd (if w = v then 1 else 0))
    (fun _ _ _ => Commute.all _ _)

@[simp] theorem generatorExponent_of [DecidableEq V] (v w : V) :
    generatorExponent L v (artinGenerator L w) = Multiplicative.ofAdd (if w = v then 1 else 0) := by
  classical
  simp [generatorExponent]

 def heightDifference (v b : V) : (height L).ker :=
  ⟨artinGenerator L v * (artinGenerator L b)⁻¹, by simp⟩

end CliqueSquare


open CategoryTheory CategoryTheory.Limits

open CategoryTheory CategoryTheory.Limits

end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_ArtinChains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains
variable {V : Type*} (L : SimpleGraph V) [Fintype V] [Nonempty V] [LinearOrder (Letter V)]

def leastDescent (g : ArtinGroup L) : Letter V :=
  if h : (descentFinset L g).Nonempty then (descentFinset L g).min' h
  else Classical.choice (inferInstance : Nonempty (Letter V))

theorem leastDescent_le (g : ArtinGroup L) (x : Letter V) (hx : x ∈ rightDescents L g) :
    leastDescent L g ≤ x := by
  have hm : x ∈ descentFinset L g := (mem_descentFinset L g x).mpr hx
  rw [leastDescent,dite_eq_left ⟨x,hm⟩]
  exact Finset.min'_le _ _ hm

theorem leastDescent_mem (g : ArtinGroup L) (hg : 0 < artinLength L g) :
    leastDescent L g ∈ rightDescents L g := by
  have hne : g ≠ 1 := fun h => by
    have := (artinLength_eq_zero_iff L g).mpr h
    omega
  obtain ⟨x,hx⟩ := rightDescents_nonempty L hne
  have hm : (descentFinset L g).Nonempty := ⟨x,(mem_descentFinset L g x).mpr hx⟩
  rw [leastDescent,dite_eq_left hm]
  exact (mem_descentFinset L _ _).mp (Finset.min'_mem _ _)

/-- The actual RAAG satisfies every hypothesis of the descending-chain
contraction, as a consequence of the independently proved trace normal form. -/
def artinDescentSystem : DescentSystem (fun x => letterValue (artinGenerator L) (invLetter x)) where
  length := artinLength L
  desc := rightDescents L
  step := fun g x hx => (rightDescents_length L g x).mp hx
  preserve := by
    intro g x y hx hy hxy
    have hi := rightDescents_pairwise L g hx hy hxy
    exact (descent_independent_step L g (show Independent L (invLetter x) y from hi)).mpr hy
  commute := by
    intro g x y hx hy hxy
    have hi := rightDescents_pairwise L g hx hy hxy
    exact letterValue_commute (fun _ _ h => adjacent_generators_commute L h)
      (show Independent L (invLetter x) (invLetter y) from hi)
  choose := leastDescent L
  choose_mem := leastDescent_mem L
  choose_le := leastDescent_le L

def descendingChains (k : ℕ) : Submodule ℤ (Chains (ArtinGroup L) (Letter V)) :=
  Finsupp.supported ℤ ℤ {p | (artinDescentSystem L).Valid p.1 p.2 ∧ p.2.length = k}

end EilenbergGanea.TraceWords.CubeDescents

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains CubicalChains.Reorientation
variable {V : Type*} (L : SimpleGraph V) [Fintype V] [Nonempty V] [LinearOrder V]

def positiveChains (k : ℕ) : Submodule ℤ (Chains (ArtinGroup L) V) :=
  Finsupp.supported ℤ ℤ {p | p.2.Pairwise (· < ·) ∧ p.2.Pairwise L.Adj ∧ p.2.length = k}

end EilenbergGanea.TraceWords.CubeDescents


end

end OAI
end

section
-- module Solutions.OAIEG.UnitaryWords
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Topology
open scoped Quaternion ContDiff

open scoped Quaternion
namespace EilenbergGanea

instance su2_compactSpace : CompactSpace SU2 := by
  apply isCompact_iff_compactSpace.mp
  have hs : (unitary ℍ : Set ℍ) = Metric.sphere 0 1 := by
    ext q
    simp [quaternion_mem_unitary_iff]
  rw [hs]
  exact isCompact_sphere 0 1

def wordMap {m : ℕ} (w : Fin m → FreeGroup (Fin m)) (x : Fin m → SU2) : Fin m → SU2 :=
  fun i => FreeGroup.lift x (w i)

open Set Filter Topology
open scoped ContDiff

def radialWordMap {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℍ) : Fin m → ℍ :=
  fun i => ‖x i‖ • ((wordMap w (fun j => normalizeQuaternion (x j)) i : SU2) : ℍ)

@[simp] theorem radialWordMap_norm {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℍ) (i : Fin m) : ‖radialWordMap w x i‖ = ‖x i‖ := by
  have h : ‖((wordMap w (fun j => normalizeQuaternion (x j)) i : SU2) : ℍ)‖ = 1 :=
    (quaternion_mem_unitary_iff _).mp (wordMap w (fun j => normalizeQuaternion (x j)) i).property
  simp [radialWordMap, norm_smul, h]

def smoothRadialWordMap {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℍ) : Fin m → ℍ := radialCutoff x • radialWordMap w x

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
variable {n : Type*} [Fintype n] [DecidableEq n]

@[simp] theorem complexDiagonal_apply (x z : n → ℂ) (i : n) :
    complexDiagonal x z i = x i * z i := by simp [complexDiagonal, Matrix.toLin'_apply, Matrix.mulVec, Matrix.diagonal_apply, dotProduct]

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

def splitWordMap {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (q : (Fin m → ℂ) × (Fin m → ℂ)) : (Fin m → ℂ) × (Fin m → ℂ) :=
  quaternionTupleCoordinates (smoothRadialWordMap w (quaternionTupleCoordinates.symm q)) - (1, 0)

end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.WordEquations
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

def smoothRadialCoefficientWordMap {ι : Type*} {m : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (q : ℝ × (Fin m → ℍ)) : Fin m → ℍ :=
  radialCutoff q.2 • radialCoefficientWordMap w a q

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

def cutoffCoefficientProducts {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (q : ℝ × (Fin m → ℍ)) : Fin d → ℍ :=
  radialCutoff q.2 • fun i =>
    (coefficientWordMap w a (q.1, fun j => normalizeQuaternion (q.2 j)) i : ℍ)

end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.SmallHolonomy
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
open scoped Quaternion ContDiff

def arcBlend (a : SU2) (t : ℝ) : ℍ :=
  (1 - Real.smoothTransition t) • (1 : ℍ) + Real.smoothTransition t • (a : ℍ)

/-- A globally smooth path that remains in the closed chord ball of its
endpoint, avoiding any branch choice of a quaternion logarithm. -/
def smallQuaternionArc (a : SU2) (t : ℝ) : SU2 := normalizeQuaternion (arcBlend a t)

end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion ContDiff
open Set
section SelectedEquations
variable {E : Type*} {m d : ℕ}

def selectedWord (σ : Fin m ↪ E) : FreeGroup E →* FreeGroup (E ⊕ Fin m) :=
  FreeGroup.map (selectedAlphabet σ)

end SelectedEquations
end EilenbergGanea

namespace EilenbergGanea

variable {Γ S H : Type*} [Group Γ] [Group H]

variable {R : Type*}

 def normalFactorWord (r : R → FreeGroup S) (f : NormalFactor S R) : FreeGroup S :=
  f.1 * (if f.2.2 then r f.2.1 else (r f.2.1)⁻¹) * f.1⁻¹

 def normalFactorCount (v : S → Γ) (f : NormalFactor S R) (g : Γ) : (Γ × R) →₀ ℤ :=
  Finsupp.single (g * wordValue v f.1, f.2.1) (if f.2.2 then 1 else -1)

end EilenbergGanea

open scoped Quaternion

namespace EilenbergGanea
open scoped Quaternion

def signedDisplacement (b : SU2) (ε : Bool) : ℍ := if ε then (b : ℍ) - 1 else -((b : ℍ) - 1)

end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.PresentationComparison
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
section NaturalPath
variable {Γ S H K : Type*} [Group Γ] [Group H] [Group K]

/-- The literal edge word traversed by a generator word. Free reduction of
this word is harmless for all nonabelian edge labelings. -/
def pathSpelling (v : S → Γ) (w : FreeGroup S) (g : Γ) : FreeGroup (Γ × S) :=
  pathProduct v (fun p s => FreeGroup.of (p,s)) w g

end NaturalPath
end EilenbergGanea

namespace EilenbergGanea
section NormalExpressions
variable {S R : Type*}

def inverseNormalFactor (f : NormalFactor S R) : NormalFactor S R :=
  (f.1, f.2.1, !f.2.2)

end NormalExpressions
end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.PresentationAlignment
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

/-! Actual word and cycle-basis alignment. -/

namespace EilenbergGanea
section CycleSpaces
variable {Γ S T U R : Type*} [Group Γ]

theorem wordValue_substitution (v : T → Γ) (f : S → FreeGroup T) (w : FreeGroup S) :
    wordValue v (FreeGroup.lift f w) = wordValue (fun s => wordValue v (f s)) w := by
  have h : (wordValue v).comp (FreeGroup.lift f) =
      wordValue (fun s => wordValue v (f s)) := by
    apply FreeGroup.ext_hom
    intro s
    simp [wordValue]
  exact DFunLike.congr_fun h w

end CycleSpaces
end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.IntegralModules
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

/-! Group-ring augmentation and literal two-syzygy dimension criterion. -/
namespace EilenbergGanea
open CategoryTheory

section CayleyModules
variable {Γ S : Type} [Group Γ]

theorem cayleyDifferential_aug (v : S → Γ) :
    (cayleyAugmentation (Γ := Γ)).comp (cayleyDifferential v) = 0 := by
  change (cayleyAugmentation (Γ := Γ)).comp
    (Finsupp.linearCombination _ (fun s => MonoidAlgebra.single (v s) 1 - 1)) = 0
  rw [← Finsupp.linearCombination_linear_comp]
  have he : (cayleyAugmentation (Γ := Γ)) ∘
      (fun s => MonoidAlgebra.single (v s) 1 - 1) = (0 : S → IntegralTrivialModule Γ) := by
    funext s
    exact cayleyAugmentation_difference (v s)
  rw [he, Finsupp.linearCombination_zero]

def cayleySyzygyDifferential (v : S → Γ) :
    (S →₀ IntegralGroupRing Γ) →ₗ[IntegralGroupRing Γ]
      LinearMap.ker (cayleyAugmentation (Γ := Γ)) :=
  (cayleyDifferential v).codRestrict _ (by
    intro r
    exact LinearMap.congr_fun (cayleyDifferential_aug v) r)

end CayleyModules
end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.Integral_Contraction
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

open Classical

namespace FiniteIntegralContraction
noncomputable section
open Classical
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

/-- A stable rank equality turns a checked split boundary and a checked bottom
contraction into the full middle identity. This avoids a large redundant finite
matrix certificate; no rational exactness is substituted for integer exactness. -/
theorem middle_of_rank
    (card : Fintype.card J + 1 = Fintype.card K + Fintype.card I)
    (root : I) (d₁ : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (d₂ : (K → ℤ) →ₗ[ℤ] (J → ℤ))
    (h₀ : (I → ℤ) →ₗ[ℤ] (J → ℤ)) (h₁ : (J → ℤ) →ₗ[ℤ] (K → ℤ))
    (hd : ∀ t, d₁ (d₂ (Pi.single t 1)) = 0)
    (hb : ∀ i, d₁ (h₀ (Pi.single i 1)) = Pi.single i 1 - Pi.single root 1)
    (hl : ∀ t, h₁ (d₂ (Pi.single t 1)) = Pi.single t 1) :
    (∀ t, corrected d₁ h₀ h₁ (d₂ (Pi.single t 1)) = Pi.single t 1) ∧
    (∀ j, d₂ (corrected d₁ h₀ h₁ (Pi.single j 1)) + h₀ (d₁ (Pi.single j 1)) = Pi.single j 1) := by
  have hd' : d₁.comp d₂ = 0 := map_eq_of_single hd
  have hb' : d₁.comp h₀ = LinearMap.id - (rootCoordinates root).comp sumCoordinates := by
    apply map_eq_of_single
    intro i
    simpa only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
      sumCoordinates_single,rootCoordinates_one] using hb i
  have hl' : h₁.comp d₂ = LinearMap.id := map_eq_of_single hl
  have dz (t : K → ℤ) : d₁ (d₂ t) = 0 := LinearMap.congr_fun hd' t
  have bz (i : I → ℤ) : d₁ (h₀ i) = i - rootCoordinates root (sumCoordinates i) :=
    LinearMap.congr_fun hb' i
  have lz (t : K → ℤ) : h₁ (d₂ t) = t := LinearMap.congr_fun hl' t
  let F : ((K → ℤ) × (I → ℤ)) →ₗ[ℤ] ((J → ℤ) × ℤ) :=
    (((d₂.comp (LinearMap.fst ℤ _ _)) + (h₀.comp (LinearMap.snd ℤ _ _))).prod
      (sumCoordinates.comp (LinearMap.snd ℤ _ _)))
  let D : ((J → ℤ) × ℤ) →ₗ[ℤ] (I → ℤ) :=
    d₁.comp (LinearMap.fst ℤ _ _) + (rootCoordinates root).comp (LinearMap.snd ℤ _ _)
  let H : ((J → ℤ) × ℤ) →ₗ[ℤ] ((K → ℤ) × (I → ℤ)) :=
    (h₁.comp (LinearMap.fst ℤ _ _ - h₀.comp D)).prod D
  have hDF (p : (K → ℤ) × (I → ℤ)) : D (F p) = p.2 := by
    change d₁ (d₂ p.1 + h₀ p.2) + rootCoordinates root (sumCoordinates p.2) = p.2
    rw [map_add,dz,bz,zero_add,sub_add_cancel]
  have hHF (p : (K → ℤ) × (I → ℤ)) : H (F p) = p := by
    apply Prod.ext
    · change h₁ ((d₂ p.1 + h₀ p.2) - h₀ (D (F p))) = p.1
      rw [hDF,add_sub_cancel_right,lz]
    · exact hDF p
  let ei : J ⊕ Unit ≃ K ⊕ I := Fintype.equivOfCardEq (by simpa using card)
  let e : ((J → ℤ) × ℤ) ≃ₗ[ℤ] ((K → ℤ) × (I → ℤ)) :=
    (LinearEquiv.prodCongr (LinearEquiv.refl ℤ (J → ℤ)) (LinearEquiv.funUnique Unit ℤ ℤ).symm).trans
      ((LinearEquiv.sumArrowLequivProdArrow J Unit ℤ ℤ).symm.trans
        ((LinearEquiv.piCongrLeft ℤ (fun _ : K ⊕ I => ℤ) ei).trans
          (LinearEquiv.sumArrowLequivProdArrow K I ℤ ℤ)))
  have hi : Function.Injective H := IsNoetherian.injective_of_surjective_of_injective
    e.toLinearMap H e.injective (fun p => ⟨F p,hHF p⟩)
  have hFH (p : (J → ℤ) × ℤ) : F (H p) = p := hi (hHF (H p))
  constructor
  · intro t
    simp only [corrected,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,hd,map_zero,sub_zero,hl]
  · intro j
    have he := congrArg Prod.fst (hFH (Pi.single j 1,0))
    change d₂ (h₁ (Pi.single j 1 - h₀ (d₁ (Pi.single j 1) + rootCoordinates root 0))) +
      h₀ (d₁ (Pi.single j 1) + rootCoordinates root 0) = Pi.single j 1 at he
    simpa only [map_zero,add_zero,corrected,LinearMap.comp_apply,LinearMap.sub_apply,
      LinearMap.id_apply] using he

end
end FiniteIntegralContraction



end

end OAI
end

section
-- module Solutions.OAIEG.Simplicial_Chains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace SimplicialChains
variable {V : Type*}

variable [LinearOrder V] (L : SimpleGraph V)

variable {L}

theorem includeVec_supported {I : Type*} [Fintype I] (f : I → List V) {k : ℕ}
    (hf : ∀ i, Valid L (f i) ∧ (f i).length = k) (c : I → ℤ) :
    includeVec f c ∈ chains L k := by
  have he : ∃ d : I →₀ ℤ, (Pi.basisFun ℤ I).repr.symm d = c :=
    (Pi.basisFun ℤ I).repr.symm.surjective c
  obtain ⟨d,rfl⟩ := he
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa using Submodule.add_mem _ hc hd
  | single i n =>
    have hh : Finsupp.single (f i) (1 : ℤ) ∈ chains L k :=
      Finsupp.single_mem_supported ℤ 1 (hf i)
    have hv : (Pi.basisFun ℤ I).repr.symm (Finsupp.single i n) = n • Pi.single i 1 := by
      simp
    rw [hv,map_smul,includeVec_single]
    exact Submodule.smul_mem _ n hh

namespace TwoDimensionalIndices
variable {E T : Type*} [Fintype V] [Fintype E] [Fintype T]
variable (D : TwoDimensionalIndices (L := L) E T)

variable (root : V) (h₀ : (V → ℤ) →ₗ[ℤ] (E → ℤ))
    (h₁ : (E → ℤ) →ₗ[ℤ] (T → ℤ))

variable (d₁ : (E → ℤ) →ₗ[ℤ] (V → ℤ)) (d₂ : (T → ℤ) →ₗ[ℤ] (E → ℤ))
    (hd₁ : ∀ e, d₁ (Pi.single e 1) = Pi.single (D.edge e).2 1 - Pi.single (D.edge e).1 1)
    (hd₂ : ∀ t, d₂ (Pi.single t 1) = Pi.single (D.face t).1 1 -
      Pi.single (D.face t).2.1 1 + Pi.single (D.face t).2.2 1)

omit [Fintype V] in
theorem fill_degree (k : ℕ) (c : Chains V) (hc : c ∈ chains L k) :
    D.fill root h₀ h₁ c ∈ chains L (k+1) := by
  rw [chains,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => D.fill root h₀ h₁ c ∈ chains L (k+1)) _ _ _ _ hc
  · rintro _ ⟨w,⟨hw,hl⟩,rfl⟩
    simp only [fill_single,one_smul]
    subst k
    rcases w with _ | ⟨a,w⟩
    · exact Finsupp.single_mem_supported ℤ 1 (by simp [Valid])
    rcases w with _ | ⟨b,w⟩
    · exact includeVec_supported D.eList (fun e => ⟨D.edge_valid e,rfl⟩) _
    rcases w with _ | ⟨d,w⟩
    · exact includeVec_supported D.tList (fun t => ⟨D.triangle_valid t,rfl⟩) _
    · exact Submodule.zero_mem _
  · simp
  · intro c d _ _ hc hd
    simpa using Submodule.add_mem _ hc hd
  · intro n c _ hc
    simpa using Submodule.smul_mem _ n hc

end TwoDimensionalIndices
end SimplicialChains



namespace SimplicialChains
variable {V W : Type*}

theorem reindex_boundaryTerm (f : V → W) (w : List V) :
    reindex f (boundaryTerm w) = boundaryTerm (w.map f) := by
  induction w with
  | nil => simp
  | cons v w ih => simp only [boundaryTerm_cons,map_sub,reindex_single,reindex_front,ih,List.map_cons]

theorem reindex_boundary (f : V → W) (c : Chains V) :
    reindex f (boundary c) = boundary (reindex f c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single w n => simp [reindex_boundaryTerm]

variable [LinearOrder V] [LinearOrder W] {L : SimpleGraph V} {M : SimpleGraph W}
theorem reindex_degree (f : V → W) (hf : ∀ w, Valid L w → Valid M (w.map f))
    {k : ℕ} {c : Chains V} (hc : c ∈ chains L k) : reindex f c ∈ chains M k := by
  rw [chains,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => reindex f c ∈ chains M k) _ _ _ _ hc
  · rintro _ ⟨w,⟨hw,hl⟩,rfl⟩
    rw [reindex_single]
    exact Finsupp.single_mem_supported ℤ 1 ⟨hf w hw,by simpa using hl⟩
  · simp
  · intro c d _ _ hc hd; simpa only [map_add] using (chains M k).add_mem hc hd
  · intro n c _ hc; simpa only [map_smul] using (chains M k).smul_mem n hc

/-- Transport a genuine augmented contraction along a graph/order reindexing. -/
def Contraction.reindex (K : Contraction L) (e : V ≃ W)
    (hf : ∀ w, Valid L w → Valid M (w.map e))
    (hb : ∀ w, Valid M w → Valid L (w.map e.symm)) : Contraction M where
  homotopy := (SimplicialChains.reindex e).comp (K.homotopy.comp (SimplicialChains.reindex e.symm))
  degree := by
    intro k c hc
    exact reindex_degree e hf (K.degree k _ (reindex_degree e.symm hb hc))
  identity := by
    intro w hw
    have hh := congrArg (SimplicialChains.reindex e) (K.identity (w.map e.symm) (hb w hw))
    simp only [map_add,reindex_boundary,← reindex_boundaryTerm] at hh
    simpa only [LinearMap.comp_apply,reindex_single,List.map_map,Equiv.apply_symm_apply,
      Function.comp_def,List.map_id_fun',id_eq] using hh
end SimplicialChains



end

end OAI
end

section
-- module Solutions.OAIEG.SeedChains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
namespace SeedEncoding

theorem cellAt_code (c : SeedCell) : cellAt (cellCode c) = c := by
  rcases c with (v|e)
  · rcases v with (v|r)
    · rcases v with _ | ⟨q,j⟩
      · decide +kernel
      · cases q <;> fin_cases j <;> decide +kernel
    · cases r <;> decide +kernel
  · rcases e with (e|s)
    · rcases e with (⟨q,j⟩|⟨r,i⟩)
      · cases q <;> fin_cases j <;> decide +kernel
      · cases r <;> fin_cases i <;> decide +kernel
    · rcases s with ⟨r,i⟩
      cases r <;> fin_cases i <;> decide +kernel
theorem code_cellAt : ∀ i : Fin 103, cellCode (cellAt i) = i := by decide +kernel

def cellEquiv : SeedCell ≃ Fin 103 where
  toFun := cellCode
  invFun := cellAt
  left_inv := cellAt_code
  right_inv := code_cellAt

end SeedEncoding
end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.SeedHolonomy
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

/-! Exact quaternion monodromy of the fixed presentation seed. -/
open scoped Quaternion
namespace EilenbergGanea

theorem seedX_normSq : Quaternion.normSq seedXQuaternion = 1 := by
  rw [Quaternion.normSq_def']
  norm_num [seedXQuaternion]

def seedXUnit : SeedSU2 := ⟨seedXQuaternion,by
  rw [Unitary.mem_iff,Quaternion.star_mul_self,Quaternion.self_mul_star,seedX_normSq]
  simp⟩

end EilenbergGanea



end

end OAI
end


