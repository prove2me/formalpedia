-- Prove2me | Definitions.Def_OAIQ16Cd002
-- name    : OAIQ16Cd002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T14:41:41.611994+00:00
-- url     : https://prove2.me/theorems/60158ba6-aa3e-432a-bfd4-ef581e03d5ee
-- title:
--   Definitions bundle OAIQ16Cd002 of the split of OpenAI, The optimal order of convex-body covering density
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 73 declarations of OpenAI's Lean: 52 definitions, 4 instances and 17 theorems. The definitions and types are `OAI.SingleLatticeCovering.Shear.Pattern.branches`, `OAI.SingleLatticeCovering.Shear.Pattern.failure`, `OAI.SingleLatticeCovering.Shear.Pattern.labelProduct`, `OAI.SingleLatticeCovering.Shear.Pattern.points`, `OAI.SingleLatticeCovering.Shear.Pattern.second`, `OAI.SingleLatticeCovering.Shear.Pattern.size`, `OAI.SingleLatticeCovering.Shear.Pattern.weight`, `OAI.SingleLatticeCovering.Shear.SliceClosed`, `OAI.SingleLatticeCovering.Shear.SourceSliceClosed`, `OAI.SingleLatticeCovering.Shear.encodeFamily`, `OAI.SingleLatticeCovering.SimplexYoung.normalizePositiveDensity`, `OAI.SingleLatticeCovering.SimplexYoung.rationalCircuitVolumeSum`, `OAI.SingleLatticeCovering.SimplexYoung.simplexConfiguration`, `OAI.SingleLatticeCovering.SimplexYoung.simplexDerivative`, `OAI.SingleLatticeCovering.SimplexYoung.simplexDiagonal`, `OAI.SingleLatticeCovering.SimplexYoung.simplexDual`, `OAI.SingleLatticeCovering.SimplexYoung.simplexForm`, `OAI.SingleLatticeCovering.SimplexYoung.simplexJacobian`, `OAI.SingleLatticeCovering.SimplexYoung.simplexMean`, `OAI.SingleLatticeCovering.SimplexYoung.simplexSpatial`, `OAI.SingleLatticeCovering.SimplexYoung.simplexTransport`, `OAI.SingleLatticeCovering.Vertical.Block.Selected`, `OAI.SingleLatticeCovering.Vertical.Block.g`, `OAI.SingleLatticeCovering.Vertical.Block.grid`, `OAI.SingleLatticeCovering.Vertical.Block.lattice`, `OAI.SingleLatticeCovering.Vertical.Block.weight`, `OAI.SingleLatticeCovering.Vertical.Chain.AtomBound`, `OAI.SingleLatticeCovering.Vertical.Chain.FullResidual`, `OAI.SingleLatticeCovering.Vertical.Chain.FullSelected`, `OAI.SingleLatticeCovering.Vertical.Chain.Good`, `OAI.SingleLatticeCovering.Vertical.Chain.RawMem`, `OAI.SingleLatticeCovering.Vertical.Chain.Residual`, `OAI.SingleLatticeCovering.Vertical.Chain.Selected`, `OAI.SingleLatticeCovering.Vertical.Chain.det`, `OAI.SingleLatticeCovering.Vertical.Chain.fullLattice`, `OAI.SingleLatticeCovering.Vertical.Chain.fullLinear`, `OAI.SingleLatticeCovering.Vertical.Chain.fullRaw`, `OAI.SingleLatticeCovering.Vertical.Chain.injectLast`, `OAI.SingleLatticeCovering.Vertical.Chain.linear`, `OAI.SingleLatticeCovering.Vertical.Chain.physicalLattice` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `LatticeCovering_Chains`, `LatticeCovering_CircuitVolumes`, `LatticeCovering_GridCounts`, `LatticeCovering_Patterns`, `LatticeCovering_Products`, `LatticeCovering_Residuals`, `LatticeCovering_Shears`, `LatticeCovering_Transport`, `TranslativeCovering_DistinctCosets`, `TranslativeCovering_PeriodicDensity`, `TranslativeCovering_Periodization`, `TranslativeCovering_SphericalLaw`, `TranslativeCovering_TargetGeometry`.
--
--   **Imports.** It imports the published bundle `Def_CoveringDensity`; the bundles `OAIQ16Cd000` and `OAIQ16Cd001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.PatternCross.fine`, `OAI.SingleLatticeCovering.Vertical.vertical_patterns_alphabets`, `OAI.TargetGeometry.select` and `OAI.TranslativeCovering.periodization_exact`; the proofs of `OAI.BodySelection.volume_lower`, `OAI.CapCost.clipped_cost`, `OAI.CapCost.raw_upper`, `OAI.CapGeometry.halfcap_ratio`, `OAI.CoveringOrder.optimal_order`, `OAI.LensDeployment.tangent_bad_vector`, `OAI.NormalizedCaps.clipped_affinity`, `OAI.PatternCross.fine`, `OAI.PatternTail.bound`, `OAI.RadiusLens.lens_at_radius`, `OAI.SingleLatticeCovering.Assembly.eventual_single_lattice_covering`, `OAI.SingleLatticeCovering.GaussianNumerics.eventually_local_position`, `OAI.SingleLatticeCovering.PrimeKernel.eventually_meanPrimeHole_all`, `OAI.SingleLatticeCovering.Vertical.vertical_patterns_alphabets`, `OAI.SlotGeometry.ratio`, `OAI.TargetGeometry.select`, `OAI.TranslativeCovering.main` and `OAI.TranslativeCovering.periodization_exact`.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_CoveringDensity
import Definitions.Def_OAIQ16Cd000
import Definitions.Def_OAIQ16Cd001

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Chains
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks
open scoped BigOperators


namespace Block

def lattice (B : Block) : Submodule ℤ B.Vec :=
  codeLattice B.p (Submodule.span (ZMod B.p) {B.direction})

def g (B : Block) : B.Group → ℝ :=
  lineMax (K := ZMod B.p) (sparseWeight (K := ZMod B.p) B.usable
    (fun z => folded B.h (anchor B.p z))) B.direction

def grid (B : Block) (y : B.Vec) : B.Group :=
  residue B.p (floorVector B.p (fun j => y j/B.h))

def weight (B : Block) (y l : B.Vec) : ℝ :=
  B.h^B.b/(B.p : ℝ)*gamma (fun j => y j-B.h*l j)



end Block
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks
open scoped BigOperators



namespace Chain
variable {A B : Block}


def RawMem : {B : Block} → (c : Chain B) → c.Vec → Prop
  | _, .base B, l => l ∈ B.lattice
  | _, .append c B _, l =>
      c.RawMem (fun j => l (Fin.castAdd B.b j)) ∧
      (fun j => l (Fin.natAdd c.dim j)) ∈ B.lattice



def weight : {B : Block} → (c : Chain B) → c.Vec → c.Vec → ℝ
  | _, .base B, y, l => B.weight y l
  | _, .append (A := A) c B w, y, l =>
      c.weight (c.subLast (fun j => y (Fin.castAdd B.b j))
        (A.shift B w (fun j => l (Fin.natAdd c.dim j))))
        (fun j => l (Fin.castAdd B.b j)) *
      B.weight (fun j => y (Fin.natAdd c.dim j)) (fun j => l (Fin.natAdd c.dim j))

def Residual : {B : Block} → (c : Chain B) → c.Vec → c.Vec → Prop
  | _, .base B, y, l => ∀ j, |y j-B.h*l j| ≤ B.h
  | _, .append (A := A) c B w, y, l =>
      c.Residual (c.subLast (fun j => y (Fin.castAdd B.b j))
        (A.shift B w (fun j => l (Fin.natAdd c.dim j))))
        (fun j => l (Fin.castAdd B.b j)) ∧
      ∀ j, |y (Fin.natAdd c.dim j)-B.h*l (Fin.natAdd c.dim j)| ≤ B.h



def Good (loss : Block → ℝ) : {B : Block} → Chain B → Prop
  | _, .base _ => True
  | _, .append (A := A) c B w =>
      c.Good loss ∧ 0 ≤ 1-loss B ∧ 0 ≤ 1-loss A ∧
      1-loss A ≤ (𝔼 x, A.g x) ∧
      ∀ z ∈ B.usable, ∀ x : A.Group,
        (1-loss B)*(𝔼 y, A.g y) ≤
          ∑ e : Fin B.b → Bool, wordMass B.h (anchor B.p z) e * A.g (x-Bits.groupShift w e)


end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded _root_.OAI.SingleLatticeCovering.Blocks ConstructionA Filter Topology
open scoped BigOperators


def Regular (A : ℝ) (B : Block) : Prop :=
  B.h = height B.b ∧
  (B.b : ℝ)*logMean (height B.b)-4*(B.b : ℝ)^(56/100 : ℝ) ≤ Real.log B.p ∧
  Real.log B.p ≤ (B.b : ℝ)*logMean (height B.b)-3*(B.b : ℝ)^(56/100 : ℝ) ∧
  B.usable ⊆ eligible B.b B.p ∧
  |(𝔼 x, B.g x)-1| ≤ blockLoss A B ∧
  (∀ x, B.g x ≤ Real.exp (5*(B.b : ℝ)^(56/100 : ℝ)))


end SingleLatticeCovering.Vertical

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Products
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks LatticeGeometry
open scoped BigOperators

namespace Block
instance lattice_discrete (B : Block) : DiscreteTopology B.lattice :=
  Classical.choose (line_lattice B.p B.direction B.direction_ne)
instance lattice_full (B : Block) : IsZLattice ℝ B.lattice :=
  (Classical.choose_spec (line_lattice B.p B.direction B.direction_ne)).1
end Block

namespace Chain
variable {A B : Block}

def injectLast : {B : Block} → (c : Chain B) → B.Vec →ₗ[ℝ] c.Vec
  | _, .base _ => LinearMap.id
  | _, .append c B _ => (appendEquiv c.dim B.b).toLinearMap.comp (LinearMap.inr ℝ c.Vec B.Vec)

abbrev rawLattice : {B : Block} → (c : Chain B) → Submodule ℤ c.Vec
  | _, .base B => B.lattice
  | _, .append c B _ => finProduct c.rawLattice B.lattice
instance raw_discrete (c : Chain B) : DiscreteTopology c.rawLattice := by
  induction c with
  | base B => exact B.lattice_discrete
  | append c B w ih => let := ih; exact finProduct_discrete _ _
instance raw_full (c : Chain B) : IsZLattice ℝ c.rawLattice := by
  induction c with
  | base B => exact B.lattice_full
  | append c B w ih => let := ih; exact finProduct_full _ _

def linear : {B : Block} → (c : Chain B) → c.Vec ≃ₗ[ℝ] c.Vec
  | _, .base B => B.linear
  | _, .append (A := A) c B w =>
    triangular c.linear B.linear (c.injectLast.comp (A.shiftMap B w))
def det : {B : Block} → Chain B → ℝ
  | _, .base B => B.det
  | _, .append c B _ => c.det*B.det
abbrev physicalLattice (c : Chain B) : Submodule ℤ c.Vec := image c.rawLattice c.linear



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators

namespace Chain
variable {B : Block}
abbrev fullRaw (c : Chain B) : Submodule ℤ c.FullVec := finProduct c.rawLattice (integerLattice B.terminalDim)
def fullLinear (c : Chain B) : c.FullVec ≃ₗ[ℝ] c.FullVec :=
  triangular c.linear (LinearEquiv.refl ℝ _) (c.injectLast.comp B.terminalShift)
abbrev fullLattice (c : Chain B) : Submodule ℤ c.FullVec := image c.fullRaw c.fullLinear



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks
open scoped BigOperators

namespace Block

def Selected (B : Block) (y l : B.Vec) : Prop :=
  ∃ z ∈ B.usable, ∃ lam : B.Vec,
    ((fun j => y j/B.h)-lam) ∈ gridCell B.p z ∧
    ∃ e : Fin B.b → Bool, l=bits B.b lam e

end Block

namespace Chain
variable {A B : Block}

def Selected : {B : Block} → (c : Chain B) → c.Vec → c.Vec → Prop
  | _, .base B, y, l => B.Selected y l
  | _, .append (A := A) c B w, y, l =>
      c.Selected (c.subLast (fun j => y (Fin.castAdd B.b j))
        (A.shift B w (fun j => l (Fin.natAdd c.dim j))))
        (fun j => l (Fin.castAdd B.b j)) ∧
      B.Selected (fun j => y (Fin.natAdd c.dim j)) (fun j => l (Fin.natAdd c.dim j))


end Chain
end SingleLatticeCovering.Vertical


end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Residuals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators

namespace Chain
variable {B : Block}

def FullResidual (c : Chain B) (y l : c.FullVec) : Prop :=
  c.Residual (c.subLast (fun j => y (Fin.castAdd B.terminalDim j))
    (B.terminalShift (fun j => l (Fin.natAdd c.dim j))))
    (fun j => l (Fin.castAdd B.terminalDim j)) ∧
  ∀ j, |y (Fin.natAdd c.dim j)-l (Fin.natAdd c.dim j)| ≤ 1

def FullSelected (c : Chain B) (y l : c.FullVec) : Prop :=
  c.Selected (c.subLast (fun j => y (Fin.castAdd B.terminalDim j))
    (B.terminalShift (fun j => l (Fin.natAdd c.dim j))))
    (fun j => l (Fin.castAdd B.terminalDim j))




end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators

namespace Chain
variable {A B : Block}

def AtomBound (q : Block → ℝ) (B : Block) : Prop :=
  ∀ z ∈ B.usable, ∀ t : B.Vec, t ∈ gridCell B.p z →
    ∀ e : Fin B.b → Bool, atom B.h t e/(B.p : ℝ) ≤ q B



end Chain
end SingleLatticeCovering.Vertical


end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Patterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section





noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace SingleLatticeCovering.Shear

universe u



namespace Pattern
variable {α : Type*}

def size : {q : ℕ} → Pattern α q → ℕ
  | _, .leaf _ => 1
  | _, .mono _ p => p.size
  | _, .split _ p r => p.size+r.size

lemma size_pos {q : ℕ} (p : Pattern α q) : 0 < p.size := by
  induction p with
  | leaf => exact Nat.zero_lt_one
  | mono v p ih => exact ih
  | split v p r ih ihr => exact Nat.add_pos_left ih _

def weight (L : ℝ≥0∞) (η : α → ℝ≥0∞) : {q : ℕ} → Pattern α q → ℝ≥0∞
  | _, .leaf a => η a
  | _, .mono _ p => p.weight L η
  | _, .split _ p r => L * p.weight L η * r.weight L η

def labelProduct (η : α → ℝ≥0∞) : {q : ℕ} → Pattern α q → ℝ≥0∞
  | _, .leaf a => η a
  | _, .mono _ p => p.labelProduct η
  | _, .split _ p r => p.labelProduct η * r.labelProduct η

def second {q : ℕ} : Pattern α (q+1) → Pattern α q
  | .mono _ p => p
  | .split _ _ r => r

def branches {q : ℕ} : Pattern α (q+1) → Prop
  | .mono _ _ => False
  | .split _ _ _ => True

section Evaluation
variable {E T : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup T]

def failure (π : E →+ T) (U : α → Set T) : {q : ℕ} → Pattern α q → (Fin q → E) → Set T
  | _, .leaf a, _ => U a
  | _, .mono v p, Z => translate (p.failure π U (Fin.init Z)) (π (v • Z (Fin.last _)))
  | _, .split v p r, Z =>
    translate (p.failure π U (Fin.init Z)) (π (v • Z (Fin.last _))) ∩
    translate (r.failure π U (Fin.init Z)) (π ((v+1) • Z (Fin.last _)))

end Evaluation
end Pattern



def SliceClosed {α : Type*} (P : (q : ℕ) → Finset (Pattern α q)) (D : ℕ) : Prop :=
  ∀ q < D, ∀ p ∈ P (q+1), p.first ∈ P q ∧ p.second ∈ P q

end SingleLatticeCovering.Shear

namespace SingleLatticeCovering.Shear.Pattern
variable {α : Type*}

lemma appendPoint_injective {q : ℕ} (v : ℝ) :
    Function.Injective (appendPoint (α := α) (q := q) v) := by
  intro x y h
  have h1 := congrArg (fun l : (Fin (q+1) → ℝ) × α => Fin.init l.1) h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (by simpa only [appendPoint, Fin.init_snoc] using h1) h2


attribute [local instance] OAI.SingleLatticeCovering.Shear.Pattern.instDecidableEqProdForallFinReal
def points : {q : ℕ} → Pattern α q → Finset ((Fin q → ℝ) × α)
  | _, .leaf a => {(0,a)}
  | _, .mono v p => by classical exact p.points.image (appendPoint v)
  | _, .split v p r => by
    classical
    exact p.points.image (appendPoint v) ∪ r.points.image (appendPoint (v+1))

lemma points_card {q : ℕ} (p : Pattern α q) : p.points.card = p.size := by
  classical
  induction p with
  | leaf a => simp [points, size]
  | mono v p ih =>
    simp only [points, Finset.card_image_of_injective _ (appendPoint_injective _), size, ih]
  | split v p r ih ihr =>
    rw [points, Finset.card_union_of_disjoint (appendPoint_disjoint _ _ _)]
    simp only [Finset.card_image_of_injective _ (appendPoint_injective _), size, ih, ihr]

lemma points_nonempty {q : ℕ} (p : Pattern α q) : p.points.Nonempty := by
  rw [← Finset.card_pos, points_card]
  exact p.size_pos

end SingleLatticeCovering.Shear.Pattern


end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Shears
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace SingleLatticeCovering.Shear.Pattern
variable {α : Type*}

attribute [local instance] OAI.SingleLatticeCovering.Shear.Pattern.instDecidableEqProdForallFinReal_1
lemma mem_slice {q : ℕ} (s : Finset ((Fin (q+1) → ℝ) × α)) (v : ℝ)
    (l : (Fin q → ℝ) × α) : l ∈ slice s v ↔ appendPoint v l ∈ s := by
  classical
  simp only [slice, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha,hav⟩,hal⟩
    have heq : appendPoint v l = a := by
      rw [← hal]
      simp only [appendPoint, ← hav, Fin.snoc_init_self]
    simpa only [heq] using ha
  · intro hl
    refine ⟨appendPoint v l, ⟨hl, by simp [appendPoint]⟩, ?_⟩
    simp only [appendPoint, Fin.init_snoc]

lemma slice_image {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) (a v : ℝ) :
    slice (s.image (appendPoint a)) v = if a=v then s else ∅ := by
  classical
  ext l
  rw [mem_slice]
  simp only [Finset.mem_image]
  by_cases hav : a=v
  · subst v
    simp only [↓reduceIte, (appendPoint_injective a).eq_iff, exists_eq_right]
  · simp only [hav, ↓reduceIte, Finset.notMem_empty, iff_false, not_exists, not_and]
    intro b hb heq
    have h := congrArg (fun x : (Fin (q+1) → ℝ) × α => x.1 (Fin.last q)) heq
    simp only [appendPoint, Fin.snoc_last] at h
    exact hav h

lemma slice_union {q : ℕ} (s t : Finset ((Fin (q+1) → ℝ) × α)) (v : ℝ) :
    slice (s ∪ t) v = slice s v ∪ slice t v := by
  classical
  ext l
  simp only [mem_slice, Finset.mem_union]

@[simp] lemma slice_mono {q : ℕ} (v : ℝ) (p : Pattern α q) :
    slice (Pattern.mono v p).points v = p.points := by
  simp [points, slice_image]

@[simp] lemma slice_split_left {q : ℕ} (v : ℝ) (p r : Pattern α q) :
    slice (Pattern.split v p r).points v = p.points := by
  simp [points, slice_union, slice_image]

@[simp] lemma slice_split_right {q : ℕ} (v : ℝ) (p r : Pattern α q) :
    slice (Pattern.split v p r).points (v+1) = r.points := by
  simp [points, slice_union, slice_image]

lemma height_mono {q : ℕ} {v : ℝ} {p : Pattern α q}
    {l : (Fin (q+1) → ℝ) × α} (hl : l ∈ (Pattern.mono v p).points) :
    l.1 (Fin.last q) = v := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  simp only [appendPoint, Fin.snoc_last]

lemma height_split {q : ℕ} {v : ℝ} {p r : Pattern α q}
    {l : (Fin (q+1) → ℝ) × α} (hl : l ∈ (Pattern.split v p r).points) :
    l.1 (Fin.last q) = v ∨ l.1 (Fin.last q) = v+1 := by
  rcases Finset.mem_union.mp hl with hl | hl
  · exact Or.inl (height_mono (p := p) hl)
  · exact Or.inr (height_mono (p := r) hl)

lemma mono_base_unique {q : ℕ} {v w : ℝ} {p r : Pattern α q}
    (h : (Pattern.mono v p).points = (Pattern.mono w r).points) : v=w := by
  obtain ⟨a,ha⟩ := p.points_nonempty
  have hm : appendPoint v a ∈ (Pattern.mono w r).points := by rw [← h]; exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  simpa only [appendPoint, Fin.snoc_last] using height_mono hm

lemma mono_ne_split {q : ℕ} (v w : ℝ) (p r s : Pattern α q) :
    (Pattern.mono v p).points ≠ (Pattern.split w r s).points := by
  intro h
  obtain ⟨a,ha⟩ := r.points_nonempty
  obtain ⟨b,hb⟩ := s.points_nonempty
  have h1 : appendPoint w a ∈ (Pattern.mono v p).points := by
    rw [h, points]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  have h2 : appendPoint (w+1) b ∈ (Pattern.mono v p).points := by
    rw [h, points]; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
  have h1' := height_mono h1
  have h2' := height_mono h2
  simp only [appendPoint, Fin.snoc_last] at h1' h2'
  linarith

lemma split_base_unique {q : ℕ} {v w : ℝ} {p r s t : Pattern α q}
    (h : (Pattern.split v p r).points = (Pattern.split w s t).points) : v=w := by
  obtain ⟨a,ha⟩ := p.points_nonempty
  obtain ⟨b,hb⟩ := s.points_nonempty
  have h1 : appendPoint v a ∈ (Pattern.split w s t).points := by
    rw [← h, points]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  have h2 : appendPoint w b ∈ (Pattern.split v p r).points := by
    rw [h, points]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
  have h1' := height_split h1
  have h2' := height_split h2
  simp only [appendPoint, Fin.snoc_last] at h1' h2'
  rcases h1' with h1' | h1'
  · exact h1'
  · rcases h2' with h2' | h2' <;> linarith



lemma points_injective (q : ℕ) : Function.Injective (points (α := α) (q := q)) := by
  induction q with
  | zero =>
    intro p r h
    cases p with
    | leaf a =>
      cases r with
      | leaf b =>
        have : a=b := by simpa [points] using h
        subst b
        rfl
  | succ q ih =>
    intro p z h
    cases p with
    | mono v p =>
      cases z with
      | mono w r =>
        have hv := mono_base_unique h
        subst w
        have hp := congrArg (fun s => slice s v) h
        simp only [slice_mono] at hp
        rw [ih hp]
      | split w r s => exact (mono_ne_split _ _ _ _ _ h).elim
    | split v p r =>
      cases z with
      | mono w s => exact (mono_ne_split _ _ _ _ _ h.symm).elim
      | split w s t =>
        have hv := split_base_unique h
        subst w
        have hp := congrArg (fun s => slice s v) h
        have hr := congrArg (fun s => slice s (v+1)) h
        simp only [slice_split_left] at hp
        simp only [slice_split_right] at hr
        rw [ih hp, ih hr]

end SingleLatticeCovering.Shear.Pattern

namespace SingleLatticeCovering.Shear
open Pattern
variable {α : Type*}


noncomputable def encodeFamily (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α)))
    (q : ℕ) : Finset (Pattern α q) :=
  (S q).preimage Pattern.points (Pattern.points_injective q).injOn

@[simp] lemma mem_encodeFamily (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α)))
    (q : ℕ) (p : Pattern α q) : p ∈ encodeFamily S q ↔ p.points ∈ S q :=
  Finset.mem_preimage


def SourceSliceClosed (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α))) (D : ℕ) : Prop :=
  ∀ q < D, ∀ s ∈ S (q+1), ∀ v : ℝ, (slice s v).Nonempty → slice s v ∈ S q

end SingleLatticeCovering.Shear



end
end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_GridCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section


noncomputable section







noncomputable section
namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Measure Set Matrix Filter Topology
open scoped ENNReal BigOperators

def simplexMean {r : ℕ} (u : V (r+1)) : ℝ := (∑ i, u i) / (r+1:ℕ)

def simplexForm {r : ℕ} (i : Fin (r+1)) : V r →ₗ[ℝ] ℝ :=
  Fin.cases (-(∑ j : Fin r, (LinearMap.proj j : V r →ₗ[ℝ] ℝ)))
    (fun j => LinearMap.proj j) i

def simplexDual {r : ℕ} : V (r+1) →ₗ[ℝ] V r where
  toFun u j := u j.succ - simplexMean u
  map_add' u v := by
    ext j
    simp [simplexMean, Finset.sum_add_distrib, add_div]; ring
  map_smul' c u := by
    ext j
    simp only [simplexMean, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [←Finset.mul_sum]
    ring

def simplexJacobian {r : ℕ} (s : V (r+1)) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.diagonal (fun j : Fin r => s j.succ) +
    Matrix.replicateCol Unit (fun _ : Fin r => (1:ℝ)) *
      Matrix.replicateRow Unit (fun j : Fin r => (s 0-s j.succ)/(r+1:ℕ))


def simplexTransport {r : ℕ} (T : Fin (r+1) → ℝ → ℝ) (x : V r) : V r :=
  simplexDual (fun i => T i (simplexForm i x))

def simplexDerivative {r : ℕ} (s : V (r+1)) : V r →L[ℝ] V r :=
  simplexDual.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => s i • (simplexForm i).toContinuousLinearMap))



end SingleLatticeCovering.SimplexYoung





open MeasureTheory Filter Set
open scoped Topology
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section

namespace SingleLatticeCovering.SimplexYoung
open SingleLatticeCovering.SharpYoung
open MeasureTheory Filter Set
open scoped Topology ENNReal


def normalizePositiveDensity (f : ℝ → ℝ) (hc : Continuous f) (hp : ∀ x, 0 < f x)
    (hi : Integrable f volume) : PositiveDensity where
  toFun := fun x => f x / ∫ t, f t
  continuous := hc.div_const _
  positive := fun x => div_pos (hp x) (integral_pos_of_continuous_density hp hi)
  integrable := hi.div_const _
  integral_one := by
    rw [integral_div, div_self (ne_of_gt (integral_pos_of_continuous_density hp hi))]



end SingleLatticeCovering.SimplexYoung


open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section

namespace SingleLatticeCovering.SimplexYoung
open SingleLatticeCovering.SharpYoung
open MeasureTheory Filter Set
open scoped Topology ENNReal
def simplexSpatial {r d : ℕ} (i : Fin (r+1)) (x : Fin d → V r) : Fin d → ℝ :=
  fun j => simplexForm i (x j)



end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Filter Set
open scoped Topology ENNReal


def simplexConfiguration {r d : ℕ} (J : Fin (r+1) → Set (Fin d → ℝ)) :
    Set (Fin d → V r) := {x | ∀ i, simplexSpatial i x ∈ J i}


end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Measure Set Matrix
open scoped ENNReal Pointwise


def simplexDiagonal {r d : ℕ} (c : Fin r → ℝ) :
    (Fin d → V r) →ₗ[ℝ] (Fin d → V r) :=
  LinearMap.pi (fun a : Fin d => (Matrix.diagonal c).mulVecLin.comp (LinearMap.proj a))


end SingleLatticeCovering.SimplexYoung



end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_CircuitVolumes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory
open scoped ENNReal BigOperators



def rationalCircuitVolumeSum {r d : ℕ} (J : Set (Fin d → ℝ)) : ℝ≥0∞ :=
  ∑' a : Fin (r+1) → ℤ, rationalCircuitVolume J a




end SingleLatticeCovering.SimplexYoung

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SphericalLaw
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace SphericalLaw
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

noncomputable def act {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) (u : Sphere n) : Sphere n :=
  ⟨e u.val, by simpa only [mem_sphere_zero_iff_norm, e.norm_map] using u.property⟩

end SphericalLaw

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_TargetGeometry
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4

namespace TargetGeometry
open Set MeasureTheory Metric CylinderProbability ConeStretch
open scoped ENNReal
noncomputable def bad {n : ℕ} {I : Type u_1} (p : I → Space n) (L ξ : ℝ) : Set (Space n × Space n) :=
  ⋃ i,⋃ j,pairEvent (p i) (p j) L ξ

end TargetGeometry

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_Periodization
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace TranslativeCovering

open scoped Classical Topology

noncomputable def cubicCenterInfimum {n : ℕ} (K : Set (Space n)) : ℝ≥0∞ :=
  ⨅ P : CubicCover K,
    (P.centers.card : ℝ≥0∞) / ENNReal.ofReal ((2 * P.L) ^ n)

end TranslativeCovering

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PeriodicDensity
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace TranslativeCovering
open Set MeasureTheory Module
open scoped ENNReal Classical

noncomputable def PeriodicCover.intensity {n : ℕ} {K : Set (Space n)} (P : PeriodicCover K) : ℝ≥0∞ :=
  (P.m:ℝ≥0∞)/ENNReal.ofReal (ZLattice.covolume P.lattice volume)

noncomputable def thetaPerListed {n : ℕ} (K : Set (Space n)) : ℝ≥0∞ :=
  ⨅ P : PeriodicCover K,volume K*P.intensity

noncomputable def CubicCover.toPeriodic {n : ℕ} {K : Set (Space n)} (P : CubicCover K) : PeriodicCover K where
  lattice := Submodule.span ℤ (Set.range (CubicLattice.basis n P.L P.positive))
  discrete := inferInstance
  fullrank := inferInstance
  m := P.centers.card
  offsets := fun i => ((Finset.equivFin P.centers).symm i).val
  covers := by
    intro y
    obtain ⟨i,l,hy⟩ := CubicLattice.covering P y
    refine ⟨Finset.equivFin P.centers i,l,?_⟩
    simpa only [Equiv.symm_apply_apply] using hy

end TranslativeCovering

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_DistinctCosets
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace TranslativeCovering
open Set MeasureTheory
open scoped ENNReal Classical
noncomputable def PeriodicCover.coset {n : ℕ} {K : Set (Space n)} (P : PeriodicCover K)
    (i : Fin P.m) : Space n ⧸ P.lattice := Submodule.Quotient.mk (P.offsets i)

def PeriodicCover.Distinct {n : ℕ} {K : Set (Space n)} (P : PeriodicCover K) : Prop :=
  Function.Injective P.coset

noncomputable def thetaPer {n : ℕ} (K : Set (Space n)) : ℝ≥0∞ :=
  ⨅ P : {P : PeriodicCover K // P.Distinct},volume K*P.val.intensity

end TranslativeCovering

end OAI
end


