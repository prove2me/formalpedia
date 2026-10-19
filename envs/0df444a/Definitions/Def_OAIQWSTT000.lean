-- Prove2me | Definitions.Def_OAIQWSTT000
-- name    : OAIQWSTT000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T17:06:59.754522+00:00
-- url     : https://prove2.me/theorems/c6f94a84-7bbf-4e3d-8f42-13368f50d961
-- title:
--   OpenAI strong thin tree split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of the strong thin tree conjecture (`OAI.StrongThinTree.strongThinTree`): OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/ThinTrees` (OpenAI, *The strong thin tree conjecture*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It also contains the lemmas those definitions use in their bodies (several definitions choose witnesses of existence lemmas, for example `neighbor` from `neighbor_exists` and `partOf` from `exists_maxPackable`, or build structures that carry proofs, so the bundle has to contain those proofs), and OpenAI's `@[simp]` lemmas about these definitions.
--
--   The definitions of the published statement (`MultiGraph`, `cut`, `Connected`, `SpanningTree`, `EdgeConnected`, `MainStatement`) are not repeated: the bundle imports them from the published bundle `Def_StrongThinTree`. It imports no other bundle.
--
--   Modules: `AssignedFamilies.lean`, `Assignment.lean`, `BagBounds.lean`, `BagConstruction.lean`, `Barrier.lean`, `BasePacking.lean`, `Blocks.lean`, `Capture.lean`, `ChainEdges.lean`, `Characteristic.lean`, `Coarea.lean`, `CompactPacking.lean`, `DeterminantCalculus.lean`, `Duality.lean`, `DyadicSelection.lean`, `Expectation.lean`, `ExtractionBounds.lean`, `ExtractionLimit.lean`, `FixedPoint.lean`, `GraphMatrix.lean`, `Hierarchy.lean`, `HierarchyBounds.lean`, `HierarchyBuilder.lean`, `IterationBounds.lean`, `MatrixDomain.lean`, `MatrixMixture.lean`, `MixedPolynomial.lean`, `OptionalDirections.lean`, `PartialFractions.lean`, `PartitionHierarchy.lean`, `PartitionRank.lean`, `Partitions.lean`, `RealRoots.lean`, `Records.lean`, `Representation.lean`, `ResponseBounds.lean`, `Restriction.lean`, `RootBound.lean`, `Selection.lean`, `Shells.lean`, `ShortcutDuality.lean`, `SpectralPacking.lean`, `Stability.lean`, `StepBounds.lean`, `ThresholdChain.lean`, `Translation.lean`, `Truncation.lean`.
--
--   The theorems of the development that the definitions do not need are proved in the three solutions of this split: two of them prove the published intermediate statements `OAI.StrongThinTree.MultiGraph.Hierarchy.binary_numerator_bound` and `OAI.StrongThinTree.MultiGraph.sparsify_from_extraction`, and the third proves `OAI.StrongThinTree.strongThinTree` from them. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The strong thin tree conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-strong-thin-tree-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/ThinTrees at commit adc7f12

import Mathlib
import Definitions.Def_StrongThinTree

section
-- module Solutions.OAIQW_StrongThinTree.Coarea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uE uV2 uE2 uV3 uE3 uI uI2 uI3

section
open scoped Classical
open Matrix

namespace StrongThinTree.Geometry
noncomputable section
open Finset MeasureTheory Set

def clamp (a b x : ℝ) : ℝ := min b (max a x)

end
end StrongThinTree.Geometry

namespace StrongThinTree.Geometry
noncomputable section
open Finset

def cube {h : ℕ} (x : Fin h → ℝ) : Prop := ∀j, 0 ≤ x j ∧ x j ≤ 1

def binary {h : ℕ} (x : Fin h → ℝ) : Prop := ∀j, x j = 0 ∨ x j = 1

def l1dist {h : ℕ} (x y : Fin h → ℝ) : ℝ := ∑j, |x j-y j|

lemma l1dist_comm {h : ℕ} (x y : Fin h → ℝ) : l1dist x y = l1dist y x := by
  simp only [l1dist, abs_sub_comm]

end
end StrongThinTree.Geometry

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Shells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uV2 uV3 uV4 uV5 uV6

section
open scoped Classical
open Matrix

namespace StrongThinTree.Geometry
noncomputable section
open Finset

structure RadialShell (V : Type uV) where
  center : V
  inner : ℝ
  outer : ℝ
  ordinary : Bool
  deriving DecidableEq

namespace RadialShell
variable {V : Type uV2} {h : ℕ}

def ball (v : V) (r : ℝ) : RadialShell V := ⟨v,0,r,true⟩
def hollow (v : V) (a b : ℝ) : RadialShell V := ⟨v,a,b,false⟩
def width (H : RadialShell V) : ℝ := H.outer-H.inner

def support (X : V → Fin h → ℝ) (H : RadialShell V) : Set (Fin h → ℝ) :=
  {w | cube w ∧ l1dist w (X H.center)<H.outer ∧
    (H.ordinary = true ∨ H.inner<l1dist w (X H.center))}

def Valid (X : V → Fin h → ℝ) (H : RadialShell V) : Prop :=
  0 ≤ H.inner ∧ H.inner < H.outer ∧ (H.ordinary = true → H.inner = 0) ∧
  (∃u, l1dist (X u) (X H.center) ≤ H.inner) ∧
  (∃v, H.outer ≤ l1dist (X v) (X H.center))

end RadialShell
end
end StrongThinTree.Geometry

namespace StrongThinTree.Geometry.RadialShell
noncomputable section
open Finset
variable {V : Type uV3} [DecidableEq V] {h : ℕ} {X : V → Fin h → ℝ}

def Arrangement (X : V → Fin h → ℝ) (O : Finset (RadialShell V)) : Prop :=
  (∀H ∈ O, H.Valid X) ∧ (O : Set (RadialShell V)).Pairwise (fun H K => Disjoint (H.support X) (K.support X))

def capacity (Δ : ℝ) (H : RadialShell V) : ℝ := max (H.width-6*Δ) 0

def potential (Δ : ℝ) (O : Finset (RadialShell V)) : ℝ := ∑H ∈ O, capacity Δ H

end
end StrongThinTree.Geometry.RadialShell

namespace StrongThinTree.Geometry.RadialShell
noncomputable section
open Finset
variable {V : Type uV6} [DecidableEq V] {h : ℕ} {X : V → Fin h → ℝ}

structure CompactFamily (X : V → Fin h → ℝ) (δ Δ : ℝ) where
  bags : Finset (Finset V)
  nonempty : bags.Nonempty
  radius_pos : 0 < δ
  bags_disjoint : (bags : Set (Finset V)).Pairwise Disjoint
  balls_disjoint : (bags.biUnion id : Set V).Pairwise
    (fun u v => Disjoint ((ball u δ).support X) ((ball v δ).support X))
  cardinal : ∀D ∈ bags, 2 ≤ D.card
  diameter : ∀D ∈ bags, ∀u ∈ D, ∀v ∈ D, l1dist (X u) (X v) ≤ Δ
  compact : ∀D ∈ bags, 36*Δ ≤ (D.card : ℝ)*δ

end
end StrongThinTree.Geometry.RadialShell

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.SpectralPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι uι2 uV uι3 uV2 uV3 uV4 uV5 uV6 uι4 uη

section
open scoped Classical
open Matrix

namespace StrongThinTree.Spectral
noncomputable section
open Finset LinearMap
open scoped InnerProductSpace
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def frobSq (T : E →ₗ[ℝ] E) : ℝ := LinearMap.trace ℝ E (T.adjoint ∘ₗ T)

def tail {d : ℕ} (s : Fin d → ℝ) (p : ℕ) := ∑i with p ≤ i.val + 1, s i
def block {d : ℕ} (s : Fin d → ℝ) (p : ℕ) := ∑i with p ≤ i.val + 1 ∧ i.val + 1 < 2*p, s i

end
end StrongThinTree.Spectral

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Hierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

def inducedEdges (A : Finset (Fin n)) : Finset (Fin m) :=
  univ.filter (fun e => G.left e ∈ A ∧ G.right e ∈ A)

def EdgeConnectedReal (A : Finset (Fin n)) (q : ℝ) : Prop :=
  ∀S : Finset (Fin n), S.Nonempty → S ⊂ A → q ≤ (G.cut (G.inducedEdges A) S).card

lemma mem_inducedEdges (A : Finset (Fin n)) (e : Fin m) :
    e ∈ G.inducedEdges A ↔ G.left e ∈ A ∧ G.right e ∈ A := by simp [inducedEdges]

def VertexPartition (A : Finset (Fin n)) (P : Finset (Finset (Fin n))) : Prop :=
  (∀B ∈ P, B.Nonempty ∧ B ⊆ A) ∧
  (P : Set (Finset (Fin n))).Pairwise Disjoint ∧ P.biUnion id = A

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

def endpointMass (A : Finset (Fin n)) (e : Fin m) : ℝ :=
  (if G.left e ∈ A then 1 else 0)+(if G.right e ∈ A then 1 else 0)

def volume (R A : Finset (Fin n)) : ℝ := ∑e ∈ G.inducedEdges R, G.endpointMass A e

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset

structure Hierarchy (n : ℕ) where
  nodes : Finset (Finset (Fin n))
  nonempty : ∀A ∈ nodes, A.Nonempty
  root_mem : univ ∈ nodes
  singletons : ∀v, {v} ∈ nodes
  laminar : ∀A ∈ nodes, ∀B ∈ nodes, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B
  parent : Finset (Fin n) → Finset (Fin n)
  parent_mem : ∀A ∈ nodes, A ≠ univ → parent A ∈ nodes
  parent_strict : ∀A ∈ nodes, A ≠ univ → A ⊂ parent A
  parent_minimal : ∀A ∈ nodes, A ≠ univ → ∀B ∈ nodes, A ⊂ B → parent A ⊆ B

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Records
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n h : ℕ} (H : Hierarchy n)

def domain (A : Finset (Fin n)) (P : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  H.nodes.filter (fun B => B ⊆ A ∧ ∀S ∈ P, ¬B ⊆ S)

def leaves (_H : Hierarchy n) (A : Finset (Fin n)) (P : Finset (Finset (Fin n))) : Finset (Fin n) :=
  A\P.biUnion id

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry

structure Record (n : ℕ) where
  shell : RadialShell (Fin n)
  owner : Finset (Fin n)
  predecessors : Finset (Finset (Fin n))
  avoided : Option (Finset (Fin n))
  deriving DecidableEq

namespace Record
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

def excluded (B : Record n) : Finset (Finset (Fin n)) :=
  B.predecessors ∪ B.avoided.toFinset

def conflict (B : Record n) := H.domain B.owner B.excluded
def leafSet (B : Record n) := H.leaves B.owner B.excluded
def routing (B : Record n) : Finset (Fin n) := B.owner\B.avoided.getD ∅

def Shape (B : Record n) : Prop :=
  B.owner ∈ H.nodes ∧ (∀S ∈ B.excluded, S ∈ H.nodes ∧ S ⊂ B.owner)

def Protected (B : Record n) : Prop :=
  ∀S ∈ B.predecessors, ∀e ∈ G.cut univ S,
    B.shell.outer ≤ l1dist (X (G.left e)) (X B.shell.center) ∧
    B.shell.outer ≤ l1dist (X (G.right e)) (X B.shell.center)

def RoutingCertificate (q : ℝ) (B : Record n) : Prop :=
  ∃R : Finset (Fin n), R ⊆ B.routing ∧ G.EdgeConnectedReal R q ∧
    (∃u ∈ R, u ∈ B.leafSet H ∧ l1dist (X u) (X B.shell.center) ≤ B.shell.inner) ∧
    (∃v ∈ R, B.shell.outer ≤ l1dist (X v) (X B.shell.center))

def Valid (q : ℝ) (B : Record n) : Prop :=
  B.Shape H ∧ B.Protected G X ∧ B.shell.Valid X ∧ B.RoutingCertificate H G X q

end Record
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

def LabeledArrangement (q : ℝ) (Z : Finset (Record n)) : Prop :=
  (∀B ∈ Z, B.Valid H G X q) ∧
  (Z : Set (Record n)).Pairwise (fun B D =>
    ¬Disjoint (B.shell.support X) (D.shell.support X) →
      Disjoint (B.conflict H) (D.conflict H))

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

def parentBoundary (A : Finset (Fin n)) : Finset (Fin m) :=
  G.cut (G.inducedEdges (H.parent A)) A

def LocallyConnectedReal (q : ℝ) : Prop := ∀A ∈ H.nodes, G.EdgeConnectedReal A q

structure AssignedBag (δ η : ℝ) where
  owner : Finset (Fin n)
  owner_mem : owner ∈ H.nodes
  nonroot : owner ≠ univ
  centers : Finset (Fin n)
  nonempty : centers.Nonempty
  radius_pos : 0 < δ
  disjoint : (centers : Set (Fin n)).Pairwise (fun u v =>
    Disjoint ((RadialShell.ball u δ).support X) ((RadialShell.ball v δ).support X))
  assignment : η*(H.parentBoundary G owner).card ≤ (centers.card : ℝ)
  endpoint : ∀u ∈ centers, u ∈ owner ∧ ∃e ∈ H.parentBoundary G owner,
    (G.left e = u ∨ G.right e = u) ∧ l1dist (X (G.left e)) (X (G.right e)) < δ

namespace AssignedBag
variable {H G X} {δ η : ℝ} (A : H.AssignedBag G X δ η)

def input (P : Finset (Finset (Fin n))) (u : Fin n) : Record n :=
  ⟨RadialShell.ball u δ,A.owner,P,none⟩

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Partitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n)

namespace Record
variable (G : MultiGraph n m) (X : Fin n → Fin h → ℝ)

def innerRecord (B : Record n) (t : Finset (Fin n)) (a b : ℝ) : Record n :=
  ⟨RadialShell.hollow B.shell.center a b,t,B.predecessors.filter (fun S => S ⊂ t),none⟩
def outsideRecord (B : Record n) (t : Finset (Fin n)) (a b : ℝ) : Record n :=
  ⟨RadialShell.hollow B.shell.center a b,B.owner,B.predecessors,some t⟩

end Record
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

namespace Record

def Compatible (B D : Record n) : Prop :=
  Disjoint (B.shell.support X) (D.shell.support X) ∨ Disjoint (B.conflict H) (D.conflict H)

def Interior (C δ : ℝ) (A B : Record n) : Prop :=
  (A.conflict H ∩ B.conflict H).Nonempty ∧
    B.shell.inner+C*δ < l1dist (X A.shell.center) (X B.shell.center) ∧
    l1dist (X A.shell.center) (X B.shell.center) < B.shell.outer-C*δ

end Record

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

namespace Record

def restriction (B : Record n) (a b : ℝ) : Record n :=
  {B with shell := RadialShell.hollow B.shell.center a b}

def Refines (D B : Record n) : Prop :=
  D.shell.support X ⊆ B.shell.support X ∧ D.conflict H ⊆ B.conflict H

end Record

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Selection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uU uI

section
open scoped Classical
open Matrix

namespace StrongThinTree.Geometry
noncomputable section
open Finset
variable {h : ℕ}

def antipode (x : Fin h → ℝ) : Fin h → ℝ := fun j => 1-x j

end
end StrongThinTree.Geometry

namespace StrongThinTree.AssignedAccounting
noncomputable section

def base (avoiding : Bool) (R δ : ℝ) : ℝ :=
  max (R-3*δ) 0 / (if avoiding then 10 else 1)

def fresh (δ ε : ℝ) : ℝ := δ-3*ε

def theta : ℝ := 1/512

end
end StrongThinTree.AssignedAccounting

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Assignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

namespace Record

def phaseToken (F : Finset (Record n)) (δ ε : ℝ) (B : Record n) : ℝ :=
  if B ∈ F then AssignedAccounting.fresh δ ε else
    AssignedAccounting.base B.avoided.isSome B.shell.width δ

end Record

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

namespace Record

def restrictionSet (B : Record n) (a b : ℝ) : Finset (Record n) :=
  if a < b then {B.restriction a b} else ∅

end Record

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.BagBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}

namespace AssignedBag

lemma neighbor_exists (A : H.AssignedBag G X δ η) {u : Fin n} (hu : u ∈ A.centers) :
    ∃v ∈ H.parent A.owner\A.owner, l1dist (X u) (X v) < δ ∧
      ∃e : Fin m, (G.left e = u ∧ G.right e = v) ∨
        (G.left e = v ∧ G.right e = u) := by
  obtain ⟨huT,e,he,heu,hlen⟩ := A.endpoint u hu
  obtain ⟨heP,heT⟩ := mem_filter.mp he
  obtain ⟨hlP,hrP⟩ := (G.mem_inducedEdges _ _).mp heP
  rcases heu with heu | heu
  · have hrT : G.right e ∉ A.owner := by
      rcases heT with hh | hh
      · exact hh.2
      · exact (hh.2 (heu.symm ▸ huT)).elim
    refine ⟨G.right e,mem_sdiff.mpr ⟨hrP,hrT⟩,?_,e,Or.inl ⟨heu,rfl⟩⟩
    simpa only [heu] using hlen
  · have hlT : G.left e ∉ A.owner := by
      rcases heT with hh | hh
      · exact (hh.2 (heu.symm ▸ huT)).elim
      · exact hh.2
    refine ⟨G.left e,mem_sdiff.mpr ⟨hlP,hlT⟩,?_,e,Or.inr ⟨rfl,heu⟩⟩
    simpa only [heu,l1dist_comm] using hlen

def neighbor (A : H.AssignedBag G X δ η) (u : Fin n) : Fin n :=
  if hu : u ∈ A.centers then (A.neighbor_exists hu).choose else u

end AssignedBag

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

namespace Record

def RadialRefines (D B : Record n) : Prop :=
  D.shell.center = B.shell.center ∧ B.shell.inner ≤ D.shell.inner ∧
    D.shell.outer ≤ B.shell.outer ∧ D.conflict H ⊆ B.conflict H

def InteriorTo (δ : ℝ) (Z : Finset (Record n)) (A : Record n) : Prop :=
  ∃B ∈ Z, A.Interior H X 256 δ B

end Record

def Evolution (F Z Z' : Finset (Record n)) : Prop :=
  ∀D ∈ Z', D ∈ F ∨ ∃B ∈ Z, D.RadialRefines (H := H) B

def OwnerEvolution (t : Finset (Fin n)) (Z Z' : Finset (Record n)) : Prop :=
  ∀D ∈ Z', D.owner = t ∨ ∃B ∈ Z, D.owner = B.owner

namespace AssignedBag
variable {δ η : ℝ} (A : H.AssignedBag G X δ η)

def SameOwnerSeparated (P : Finset (Finset (Fin n))) (U : Finset (Fin n))
    (Z : Finset (Record n)) : Prop :=
  ∀u ∈ U, (A.input P u).InteriorTo (H := H) (X := X) δ Z →
    ∀B ∈ Z, B.owner = A.owner →
      Disjoint ((RadialShell.ball u δ).support X) (B.shell.support X)

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}
namespace AssignedBag

structure InteriorMove (A : H.AssignedBag G X δ η)
    (q ε : ℝ) (P : Finset (Finset (Fin n)))
    (F Z : Finset (Record n)) (U : Finset (Fin n)) where
  treated : Finset (Fin n)
  next : Finset (Record n)
  nonempty : treated.Nonempty
  treated_interior : ∀u ∈ treated, u ∈ U ∧
    (A.input P u).InteriorTo (H := H) (X := X) δ Z
  valid : H.LabeledArrangement G X (q/4) next
  credit : (∑D ∈ Z, Record.phaseToken F δ ε D)+
      AssignedAccounting.theta*(treated.card : ℝ)*δ ≤
      ∑D ∈ next, Record.phaseToken F δ ε D
  evolution : Evolution (H := H) F Z next
  owners : OwnerEvolution A.owner Z next
  fresh : ∀D ∈ next, D ∈ F → D ∈ Z ∨ ∃u ∈ treated, D = A.input P u
  separation : A.SameOwnerSeparated P (U\treated) next

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.BagConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}
namespace Record

def baseToken (r : ℝ) (B : Record n) : ℝ :=
  AssignedAccounting.base B.avoided.isSome B.shell.width r

def shrinkRecord (F : Finset (Record n)) (δ : ℝ) (B : Record n) : Record n :=
  if B ∈ F then B else B.restriction (B.shell.inner+257*δ) (B.shell.outer-257*δ)

def shrinkValue (F : Finset (Record n)) (δ ε : ℝ) (B : Record n) : ℝ :=
  if B ∈ F then AssignedAccounting.fresh δ ε else
    AssignedAccounting.base B.avoided.isSome (B.shell.width-514*δ) ε

end Record

def shrinkFamily (F Z : Finset (Record n)) (δ : ℝ) : Finset (Record n) :=
  (Z.filter (fun B => 0 < (B.shrinkRecord F δ).shell.width)).image (Record.shrinkRecord F δ)

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.AssignedFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {η : ℝ}

structure AssignedFamily (H : Hierarchy n) (G : MultiGraph n m)
    (X : Fin n → Fin h → ℝ) (η : ℝ) where
  radius : ℝ
  positive : 0 < radius
  count : ℕ
  bag : Fin count → H.AssignedBag G X radius η
  owner_injective : Function.Injective (fun i => (bag i).owner)
  separated : ∀i, ∀u ∈ (bag i).centers, ∀j, ∀v ∈ (bag j).centers,
    (i ≠ j ∨ u ≠ v) → Disjoint ((RadialShell.ball u radius).support X)
      ((RadialShell.ball v radius).support X)

namespace AssignedFamily
variable (F : AssignedFamily H G X η)

def owners : Finset (Finset (Fin n)) := univ.image (fun i => (F.bag i).owner)
def mass : ℝ := (∑i, ((F.bag i).centers.card : ℝ))*F.radius
def predecessors (E : Finset (Finset (Fin n))) (i : Fin F.count) : Finset (Finset (Fin n)) :=
  E.filter (fun S => S ⊂ (F.bag i).owner)

def ProtectedFrom (E : Finset (Finset (Fin n))) : Prop :=
  ∀i, ∀u ∈ (F.bag i).centers, ((F.bag i).input (F.predecessors E i) u).Protected G X

end AssignedFamily

namespace AssignedSequence
abbrev Family := AssignedFamily H G X η

def initialRadius : List (Family (H := H) (G := G) (X := X) (η := η)) → ℝ
  | [] => 0
  | F::_ => F.radius

def mass : List (Family (H := H) (G := G) (X := X) (η := η)) → ℝ
  | [] => 0
  | F::L => F.mass+mass L

def Geometric : List (Family (H := H) (G := G) (X := X) (η := η)) → Prop
  | [] => True
  | F::L => initialRadius L ≤ F.radius/1536 ∧ Geometric L

def Ready (E : Finset (Finset (Fin n))) : List (Family (H := H) (G := G) (X := X) (η := η)) → Prop
  | [] => True
  | F::L => Disjoint E F.owners ∧ F.ProtectedFrom E ∧ Ready (E∪F.owners) L

end AssignedSequence
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {η : ℝ}

namespace AssignedFamily
variable (F : AssignedFamily H G X η)

def goodCenters (E : Finset (Finset (Fin n))) (i : Fin F.count) : Finset (Fin n) :=
  (F.bag i).centers.filter (fun u => ((F.bag i).input (F.predecessors E i) u).Protected G X)

def badCenters (E : Finset (Finset (Fin n))) (i : Fin F.count) : Finset (Fin n) :=
  (F.bag i).centers\F.goodCenters E i

def badCount (E : Finset (Finset (Fin n))) : ℕ := ∑i, (F.badCenters E i).card

def boundaryCount (G : MultiGraph n m) (E : Finset (Finset (Fin n))) : ℕ :=
  ∑S ∈ E, (G.cut univ S).card

end AssignedFamily
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Capture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

namespace AssignedFamily
variable {q : ℝ} (F : AssignedFamily H G X (6144/q))

def BoundaryRatio (ρ : ℝ) : Prop := ∀i,
  (q*ρ)*((G.cut univ (F.bag i).owner).card : ℝ) ≤ (H.parentBoundary G (F.bag i).owner).card

end AssignedFamily

namespace AssignedSequence
open AssignedFamily
variable {q : ℝ}

def Fresh (E : Finset (Finset (Fin n))) : List (AssignedFamily H G X (6144/q)) → Prop
  | [] => True
  | F::L => Disjoint E F.owners ∧ Fresh (E∪F.owners) L

def Ratios (ρ : ℝ) : List (AssignedFamily H G X (6144/q)) → Prop
  | [] => True
  | F::L => F.BoundaryRatio ρ ∧ Ratios ρ L

def GeometricAt {η : ℝ} (ρ : ℝ) : List (AssignedFamily H G X η) → Prop
  | [] => True
  | F::L => initialRadius L ≤ ρ*F.radius ∧ GeometricAt ρ L

end AssignedSequence
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.CompactPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uJ uJ2 uJ3

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset _root_.OAI.StrongThinTree.Geometry Geometry.RadialShell
open scoped Classical

structure CompactPackage {n h : ℕ} (X : Fin n → Fin h → ℝ) where
  radius : ℝ
  diameter : ℝ
  family : CompactFamily X radius diameter

namespace CompactPackage
variable {n m h : ℕ} {G : MultiGraph n m} {X : Fin n → Fin h → ℝ}
def mass (F : CompactPackage X) : ℝ := F.radius*(∑D ∈ F.family.bags, (D.card : ℝ))

end CompactPackage

namespace Hierarchy
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m} {X : Fin n → Fin h → ℝ}

namespace AssignedBag
variable {δ η η' : ℝ}
def weaken (A : H.AssignedBag G X δ η) (hη : η' ≤ η) : H.AssignedBag G X δ η' :=
  { A with assignment := (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)).trans A.assignment }
end AssignedBag

namespace AssignedFamily
variable {η η' : ℝ}
def weaken (F : AssignedFamily H G X η) (hη : η' ≤ η) : AssignedFamily H G X η' where
  radius := F.radius
  positive := F.positive
  count := F.count
  bag := fun i => (F.bag i).weaken hη
  owner_injective := F.owner_injective
  separated := F.separated
end AssignedFamily

end Hierarchy
end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset _root_.OAI.StrongThinTree.Geometry Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m} {X : Fin n → Fin h → ℝ}

abbrev CapturedFamily (H : Hierarchy n) (G : MultiGraph n m) (X : Fin n → Fin h → ℝ) (η : ℝ) :=
  Sum (CompactPackage X) (AssignedFamily H G X η)

namespace CapturedFamily
variable {η : ℝ}
def radius : CapturedFamily H G X η → ℝ
  | .inl F => F.radius
  | .inr F => F.radius
def upper : CapturedFamily H G X η → ℝ
  | .inl F => F.diameter
  | .inr F => F.radius
def mass : CapturedFamily H G X η → ℝ
  | .inl F => F.mass
  | .inr F => F.mass
def owners : CapturedFamily H G X η → Finset (Finset (Fin n))
  | .inl _ => ∅
  | .inr F => F.owners

def Ratio {q : ℝ} (F : CapturedFamily H G X (6144/q)) (ρ : ℝ) : Prop :=
  match F with
  | .inl _ => True
  | .inr F => F.BoundaryRatio ρ

end CapturedFamily
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Truncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3 uE4

section
open scoped Classical
open Matrix

namespace StrongThinTree.Truncation
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE2} [DecidableEq E]

def dyadicIndex (L x : ℝ) : ℕ := ⌊Real.logb 2 (x/L)⌋₊

end
end StrongThinTree.Truncation

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

def truncationBins (α : ℝ) : ℕ := 1+⌈Real.logb 2 (256/α^2)⌉₊
def truncationGain (α : ℝ) : ℝ := 1/(4*(truncationBins α:ℝ)^4)

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Duality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uJ uV uI2 uI3 uV2 uW uJ2 uV3 uE2 uT uJ3 uH uI4

section

namespace StrongThinTree.Duality
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE} {I : Type uI} [AddCommGroup E] [Module ℝ E] [Fintype I]

def strictUpperImage (S : Set E) (F : I → E → ℝ) : Set (I → ℝ) :=
  {v | ∃x ∈ S, ∀i, F i x < v i}

end
end StrongThinTree.Duality

namespace StrongThinTree.ShortcutDual
noncomputable section
open Matrix Finset Filter Topology
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {V : Type uV3} {E : Type uE2} {T : Type uT} {J : Type uJ3} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype T] [Fintype J]

def boundaryMatrix (b : E → V → ℝ) (O : T → Finset E) (t : T) : Matrix V V ℝ :=
  ((O t).card : ℝ)⁻¹ • ∑e ∈ O t, vecMulVec (b e) (b e)

def boundaryAverage (b : E → V → ℝ) (O : T → Finset E) (t : T)
    (D : Matrix V V ℝ) : ℝ :=
  ((O t).card : ℝ)⁻¹ * ∑e ∈ O t, b e ⬝ᵥ (D⁻¹ *ᵥ b e)

def objectiveMatrix (b : E → V → ℝ) (O : T → Finset E) (lam : T → ℝ) : Matrix V V ℝ :=
  ∑t, lam t • boundaryMatrix b O t

def cutMatrix (c : J → V → ℝ) (y : J → ℝ) : Matrix V V ℝ :=
  ∑j, y j • vecMulVec (c j) (c j)

def edgeWeight (O : T → Finset E) (lam : T → ℝ) (e : E) : ℝ :=
  Real.sqrt (∑t, if e ∈ O t then lam t / ((O t).card : ℝ) else 0)

def replicaMatrix (c : J → V → ℝ) (a : J → ℕ) :
    Matrix (Fin (Fintype.card (Σj, Fin (a j)))) V ℝ :=
  fun i v => c ((Fintype.equivFin (Σj, Fin (a j))).symm i).1 v

end
end StrongThinTree.ShortcutDual

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ShortcutDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset StrongThinTree.Geometry
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {n m h : ℕ} (G : MultiGraph n m)

abbrev point (v : Fin n) : Fin n → ℝ := Pi.single v 1

def incidence (e : Fin m) : Fin n → ℝ := point (G.left e) - point (G.right e)

abbrev ProperCut (n : ℕ) := {S : Finset (Fin n) // S.Nonempty ∧ S ≠ univ}

def cutIndicator (S : Finset (Fin n)) (v : Fin n) : ℝ := if v ∈ S then 1 else 0

namespace Hierarchy
variable {G : MultiGraph n m} {H : Hierarchy n}

def shortcutCoefficient (q L R : ℕ) (α ε : ℝ) : ℝ :=
  2*α+2*(R:ℝ)*(L:ℝ)/(((q:ℝ)/8192)*((α*truncationGain α/32)^ε/(6912*(1024/ε^2)))*truncationGain α)

end Hierarchy
end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.GraphMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]
def qform (X : Matrix V V ℝ) (v : V → ℝ) : ℝ := v ⬝ᵥ (X *ᵥ v)

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
def laplacian (F : Finset (Fin m)) : Matrix (Fin n) (Fin n) ℝ := ∑e ∈ F, vecMulVec (G.incidence e) (G.incidence e)
def resistance (X : Matrix (Fin n) (Fin n) ℝ) (e : Fin m) : ℝ := qform X⁻¹ (G.incidence e)

def baseMatrix : Matrix (Fin n) (Fin n) ℝ := G.laplacian univ+(n:ℝ)⁻¹ • 1

end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.MatrixDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder Matrix.Norms.Elementwise
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

def matrixDomain : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | G.baseMatrix ≤ X ∧ ∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
    qform X (cutIndicator S) ≤ 3*(G.cut univ S).card}

end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.HierarchyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset Filter
open scoped Topology
namespace StrongThinTree.ShortcutNumeric
open MultiGraph.Hierarchy

def alpha (x : ℝ) : ℝ := x^(-4/5:ℝ)
def gamma (x : ℝ) : ℝ := truncationGain (alpha x)
def scale (x : ℝ) : ℝ := alpha x*gamma x/32
def rho (x : ℝ) : ℝ := 1/(2*x^2)
def count (x : ℝ) : ℕ := ⌈x^(1/100:ℝ)⌉₊

def coefficient (x : ℝ) : ℝ :=
  2*alpha x+2*(count x:ℝ)*(count x:ℝ)/
    ((x/8192)*((scale x)^(1/10:ℝ)/(6912*(1024/(1/10:ℝ)^2)))*gamma x)

def largeConstant : ℝ := 8*8192*6912*102400

structure GoodParameters (x : ℝ) : Prop where
  large : 2 ≤ x
  small : (scale x)^(1/10:ℝ) ≤ 1/(1728*(1024/(1/10:ℝ)^2))
  assignment : 6144/x ≤ (scale x)^(1+2*(1/10:ℝ))
  rho_small : rho x ≤ 1/1536
  log_left : Real.logb 2 (16/(alpha x*gamma x))+1 < (count x:ℝ)
  log_right : Real.logb 2 (24/(rho x*(scale x)^2)) < (count x:ℝ)
  coefficient_small : coefficient x ≤ x^(-31/40:ℝ)/2

end StrongThinTree.ShortcutNumeric

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.BasePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uI2

section

noncomputable section
open Finset Submodule
namespace StrongThinTree.Packing

variable {E : Type uE} {I : Type uI} {V : Type uV} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

abbrev span (v : E → V) (s : Finset E) : Submodule ℝ V :=
  Submodule.span ℝ (v '' (s : Set E))

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma span_mono (v : E → V) {s t : Finset E} (h : s ⊆ t) : span v s ≤ span v t :=
  Submodule.span_mono (Set.image_mono h)

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma mem_span_self (v : E → V) {s : Finset E} {e : E} (he : e ∈ s) :
    v e ∈ span v s := Submodule.subset_span ⟨e, he, rfl⟩

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma span_le_iff (v : E → V) {s : Finset E} {W : Submodule ℝ V} :
    span v s ≤ W ↔ ∀ e ∈ s, v e ∈ W := by
  rw [Submodule.span_le]
  constructor
  · intro h e he; exact h ⟨e, he, rfl⟩
  · rintro h x ⟨e, he, rfl⟩; exact h e he

def Valid (v : E → V) (F : I → Finset E) : Prop :=
  (∀ i, LinearIndepOn ℝ v (F i : Set E)) ∧ Pairwise (fun i j => Disjoint (F i) (F j))

abbrev State (v : E → V) (I : Type uI2) [Fintype I] := {F : I → Finset E // Valid v F}

def cost {v : E → V} (F : State v I) : ℕ := ∑ i, (F.1 i).card

def unused {v : E → V} (F : State v I) (e : E) : Prop := ∀ i, e ∉ F.1 i

def Move {v : E → V} (F F' : State v I) : Prop :=
  ∃ i e f, unused F e ∧ f ∈ F.1 i ∧
    F'.1 = Function.update F.1 i (insert e ((F.1 i).erase f))

def recycled {v : E → V} (F : State v I) : Finset E := by
  classical
  exact Finset.univ.filter fun e => ∃ F', Relation.ReflTransGen Move F F' ∧ unused F' e

end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

abbrev edgeSpan (T : Finset (Fin m)) := Packing.span G.incidence T

def Same (T : Finset (Fin m)) (u v : Fin n) : Prop :=
  point u - point v ∈ G.edgeSpan T

lemma same_refl (T : Finset (Fin m)) (u : Fin n) : G.Same T u u := by
  simp [Same]

lemma same_symm {T : Finset (Fin m)} {u v : Fin n} (h : G.Same T u v) : G.Same T v u := by
  change point v - point u ∈ G.edgeSpan T
  simpa only [neg_sub] using (G.edgeSpan T).neg_mem h

lemma same_trans {T : Finset (Fin m)} {u v w : Fin n}
    (huv : G.Same T u v) (hvw : G.Same T v w) : G.Same T u w := by
  change point u - point w ∈ G.edgeSpan T
  simpa only [sub_add_sub_cancel] using (G.edgeSpan T).add_mem huv hvw

def components (T : Finset (Fin m)) : Setoid (Fin n) where
  r := G.Same T
  iseqv := ⟨G.same_refl T, G.same_symm, G.same_trans⟩

def rep (T : Finset (Fin m)) (u : Fin n) : Fin n := (Quotient.mk (G.components T) u).out

abbrev repDifference (T : Finset (Fin m)) (u : Fin n) : Fin n → ℝ :=
  point u - point (G.rep T u)

def componentCount (T : Finset (Fin m)) : ℕ := (Finset.univ.image (G.rep T)).card

def crossing (T : Finset (Fin m)) (p : Fin n → Fin n) : Finset (Fin m) :=
  T.filter fun e => p (G.left e) ≠ p (G.right e)

def partitionSize (p : Fin n → Fin n) : ℕ := (Finset.univ.image p).card

def TreePackable (T : Finset (Fin m)) (r : ℕ) : Prop :=
  ∃ F : Fin r → Finset (Fin m),
    (∀ i, F i ⊆ T ∧ G.SpanningTree (F i)) ∧ Pairwise (fun i j => Disjoint (F i) (F j))

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.PartitionRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uE2 uV2

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

def internal (F : Finset (Fin m)) (A : Finset (Fin n)) : Finset (Fin m) :=
  F.filter (fun e => G.left e ∈ A ∧ G.right e ∈ A)

def ConnectedOn (A : Finset (Fin n)) (F : Finset (Fin m)) : Prop :=
  ∀ u ∈ A, ∀ v ∈ A, G.Same F u v

def TreeOn (A : Finset (Fin n)) (F : Finset (Fin m)) : Prop :=
  F ⊆ G.internal univ A ∧ G.ConnectedOn A F ∧ LinearIndepOn ℝ G.incidence (F : Set (Fin m))

def PackableOn (F : Finset (Fin m)) (q : ℕ) (A : Finset (Fin n)) : Prop :=
  ∃ T : Fin q → Finset (Fin m),
    (∀ i, T i ⊆ G.internal F A ∧ G.ConnectedOn A (T i)) ∧
    ∀ ⦃i j⦄, i ≠ j → Disjoint (T i) (T j)

lemma connectedOn_mono_span {A : Finset (Fin n)} {F T : Finset (Fin m)}
    (h : G.edgeSpan F ≤ G.edgeSpan T) (hc : G.ConnectedOn A F) : G.ConnectedOn A T := by
  intro u hu v hv
  exact h (hc u hu v hv)

lemma connectedOn_mono {A : Finset (Fin n)} {F T : Finset (Fin m)}
    (h : F ⊆ T) (hc : G.ConnectedOn A F) : G.ConnectedOn A T :=
  G.connectedOn_mono_span (Packing.span_mono G.incidence h) hc

lemma packableOn_singleton (F : Finset (Fin m)) (q : ℕ) (u : Fin n) :
    G.PackableOn F q {u} := by
  refine ⟨fun _ => ∅, fun i => ⟨empty_subset _, ?_⟩, fun _ _ _ => disjoint_empty_left _⟩
  intro v hv w hw
  simp only [mem_singleton] at hv hw
  subst v; subst w
  exact G.same_refl _ _

lemma packableOn_mono_edges {F F' : Finset (Fin m)} {q : ℕ} {A : Finset (Fin n)}
    (h : F ⊆ F') (hp : G.PackableOn F q A) : G.PackableOn F' q A := by
  obtain ⟨T, hT, hd⟩ := hp
  exact ⟨T, fun i => ⟨(hT i).1.trans (filter_subset_filter _ h), (hT i).2⟩, hd⟩

lemma splice_span {A : Finset (Fin n)} {T U : Finset (Fin m)}
    (hT : G.ConnectedOn A T) : G.edgeSpan U ≤ G.edgeSpan (T ∪ (U \ G.internal univ A)) := by
  apply (Packing.span_le_iff G.incidence).mpr
  intro e he
  by_cases ha : e ∈ G.internal univ A
  · have heA := (mem_filter.mp ha).2
    exact Packing.span_mono G.incidence subset_union_left (hT _ heA.1 _ heA.2)
  · exact Packing.mem_span_self G.incidence (mem_union_right _ (mem_sdiff.mpr ⟨he, ha⟩))

theorem packableOn_union {F : Finset (Fin m)} {q : ℕ} {A B : Finset (Fin n)}
    (hA : G.PackableOn F q A) (hB : G.PackableOn F q B) (hAB : (A ∩ B).Nonempty) :
    G.PackableOn F q (A ∪ B) := by
  classical
  obtain ⟨T, hT, hdT⟩ := hA
  obtain ⟨U, hU, hdU⟩ := hB
  obtain ⟨w, hw⟩ := hAB
  obtain ⟨hwA, hwB⟩ := mem_inter.mp hw
  let W := fun i => T i ∪ (U i \ G.internal univ A)
  have hconn (i : Fin q) : G.ConnectedOn (A ∪ B) (W i) := by
    have h1 : G.ConnectedOn A (W i) := G.connectedOn_mono subset_union_left (hT i).2
    have h2 : G.ConnectedOn B (W i) := G.connectedOn_mono_span (G.splice_span (hT i).2) (hU i).2
    have hs : ∀ v ∈ A ∪ B, G.Same (W i) v w := by
      intro v hv
      rcases mem_union.mp hv with hv | hv
      · exact h1 v hv w hwA
      · exact h2 v hv w hwB
    intro u hu v hv
    exact G.same_trans (hs u hu) (G.same_symm (hs v hv))
  refine ⟨W, fun i => ⟨?_, hconn i⟩, ?_⟩
  · intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨heF, hl, hr⟩ := mem_filter.mp ((hT i).1 he)
      exact mem_filter.mpr ⟨heF, mem_union_left _ hl, mem_union_left _ hr⟩
    · obtain ⟨heF, hl, hr⟩ := mem_filter.mp ((hU i).1 (mem_sdiff.mp he).1)
      exact mem_filter.mpr ⟨heF, mem_union_right _ hl, mem_union_right _ hr⟩
  · intro i j hij
    apply disjoint_left.mpr
    intro e he hi
    rcases mem_union.mp he with he | he <;> rcases mem_union.mp hi with hi | hi
    · exact disjoint_left.mp (hdT hij) he hi
    · exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ((hT i).1 he)).2⟩)
    · exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ((hT j).1 hi)).2⟩)
    · exact disjoint_left.mp (hdU hij) (mem_sdiff.mp he).1 (mem_sdiff.mp hi).1

def MaxPackable (F : Finset (Fin m)) (q : ℕ) (A : Finset (Fin n)) : Prop :=
  A.Nonempty ∧ G.PackableOn F q A ∧
    ∀ B, A ⊆ B → G.PackableOn F q B → B = A

def packingParts (F : Finset (Fin m)) (q : ℕ) : Finset (Finset (Fin n)) :=
  by classical exact univ.filter (G.MaxPackable F q)

lemma exists_maxPackable {F : Finset (Fin m)} {q : ℕ} {A : Finset (Fin n)}
    (hA : A.Nonempty) (hp : G.PackableOn F q A) :
    ∃ B, A ⊆ B ∧ G.MaxPackable F q B := by
  classical
  let C : Finset (Finset (Fin n)) := univ.filter (fun B => A ⊆ B ∧ G.PackableOn F q B)
  have hC : A ∈ C := by simp [C, hp]
  obtain ⟨B, hB, hmax⟩ := exists_max_image C card ⟨A, hC⟩
  obtain ⟨hAB, hpB⟩ := (mem_filter.mp hB).2
  refine ⟨B, hAB, hA.mono hAB, hpB, ?_⟩
  intro D hBD hpD
  have hD : D ∈ C := mem_filter.mpr ⟨mem_univ _, hAB.trans hBD, hpD⟩
  exact (eq_of_subset_of_card_le hBD (hmax D hD)).symm

lemma maxPackable_disjoint {F : Finset (Fin m)} {q : ℕ} {A B : Finset (Fin n)}
    (hA : G.MaxPackable F q A) (hB : G.MaxPackable F q B) : A = B ∨ Disjoint A B := by
  classical
  by_cases h : Disjoint A B
  · exact Or.inr h
  · have hne : (A ∩ B).Nonempty := not_disjoint_iff_nonempty_inter.mp h
    have hp := G.packableOn_union hA.2.1 hB.2.1 hne
    exact Or.inl ((hA.2.2 _ subset_union_left hp).symm.trans (hB.2.2 _ subset_union_right hp))

theorem packingParts_partition (F : Finset (Fin m)) (q : ℕ) :
    (∀ A ∈ G.packingParts F q, A.Nonempty ∧ G.PackableOn F q A) ∧
    ((G.packingParts F q : Finset (Finset (Fin n))) : Set (Finset (Fin n))).Pairwise Disjoint ∧
    (G.packingParts F q).biUnion id = univ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    exact ⟨(mem_filter.mp hA).2.1, (mem_filter.mp hA).2.2.1⟩
  · intro A hA B hB hne
    exact (G.maxPackable_disjoint (mem_filter.mp hA).2 (mem_filter.mp hB).2).resolve_left hne
  · apply eq_univ_of_forall
    intro v
    obtain ⟨B, hvB, hB⟩ := G.exists_maxPackable (singleton_nonempty v) (G.packableOn_singleton F q v)
    exact mem_biUnion.mpr ⟨B, mem_filter.mpr ⟨mem_univ _, hB⟩, hvB (mem_singleton_self v)⟩

theorem packingParts_coarsens {F F' : Finset (Fin m)} {q : ℕ} (h : F ⊆ F') :
    ∀ A ∈ G.packingParts F q, ∃ B ∈ G.packingParts F' q, A ⊆ B := by
  classical
  intro A hA
  obtain ⟨hne, hp, hmax⟩ := (mem_filter.mp hA).2
  obtain ⟨B, hAB, hB⟩ := G.exists_maxPackable hne (G.packableOn_mono_edges h hp)
  exact ⟨B, mem_filter.mpr ⟨mem_univ _, hB⟩, hAB⟩

def vertexProjection (A : Finset (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x v := if v ∈ A then x v else 0
  map_add' x y := by ext v; by_cases hv : v ∈ A <;> simp [hv]
  map_smul' c x := by ext v; by_cases hv : v ∈ A <;> simp [hv]

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

def partOf (F : Finset (Fin m)) (q : ℕ) (v : Fin n) : Finset (Fin n) :=
  Classical.choose (G.exists_maxPackable (singleton_nonempty v) (G.packableOn_singleton F q v))

lemma partOf_spec (F : Finset (Fin m)) (q : ℕ) (v : Fin n) :
    v ∈ G.partOf F q v ∧ G.MaxPackable F q (G.partOf F q v) := by
  have h := Classical.choose_spec (G.exists_maxPackable (singleton_nonempty v) (G.packableOn_singleton F q v))
  exact ⟨h.1 (mem_singleton_self _), h.2⟩

def partLabel (F : Finset (Fin m)) (q : ℕ) (v : Fin n) : Fin n :=
  (G.partOf F q v).min' (G.partOf_spec F q v).2.1

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

def withinParts (F : Finset (Fin m)) (q : ℕ) : Finset (Fin m) :=
  F.filter (fun e => G.partLabel F q (G.left e) = G.partLabel F q (G.right e))

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.HierarchyBuilder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n : ℕ}

structure PartitionChain (n : ℕ) where
  parts : ℕ → Finset (Finset (Fin n))
  partition : ∀i, VertexPartition univ (parts i)
  coarsens : ∀i j, i ≤ j → ∀A ∈ parts i, ∃B ∈ parts j, A ⊆ B

namespace PartitionChain
variable (P : PartitionChain n)

lemma part_exists (i : ℕ) (v : Fin n) : ∃A ∈ P.parts i, v ∈ A := by
  have hv : v ∈ (P.parts i).biUnion id := (P.partition i).2.2.symm ▸ mem_univ v
  exact mem_biUnion.mp hv

def nodes (I : Finset ℕ) : Finset (Finset (Fin n)) :=
  I.biUnion P.parts ∪ univ.image (fun v : Fin n => {v})

end PartitionChain
end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ChainEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph.PartitionChain
noncomputable section
open Finset
variable {n m : ℕ} (P : PartitionChain n) (G : MultiGraph n m)

def block (i : ℕ) (v : Fin n) : Finset (Fin n) := (P.part_exists i v).choose

def crossing (i : ℕ) : Finset (Fin m) := univ.filter (fun e => P.block i (G.left e) ≠ P.block i (G.right e))

end
end StrongThinTree.MultiGraph.PartitionChain

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.PartitionHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

lemma packingParts_vertexPartition (F : Finset (Fin m)) (q : ℕ) :
    VertexPartition univ (G.packingParts F q) := by
  obtain ⟨hn,hd,hc⟩ := G.packingParts_partition F q
  exact ⟨fun A hA => ⟨(hn A hA).1,subset_univ _⟩,hd,hc⟩

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ThresholdChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

def thresholdEdges (_G : MultiGraph n m) (R : Fin m → ℝ) (s : ℝ) : Finset (Fin m) := univ.filter (fun e => R e ≤ s)
def rankedEdges (R : Fin m → ℝ) (i : ℕ) : Finset (Fin m) := univ.filter (fun e => (G.thresholdEdges R (R e)).card ≤ i)
lemma rankedEdges_mono (R : Fin m → ℝ) : Monotone (G.rankedEdges R) := by
  intro i j hij e he
  exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2.trans hij⟩

def packingChain (R : Fin m → ℝ) (q : ℕ) : PartitionChain n where
  parts i := G.packingParts (G.rankedEdges R i) q
  partition _i := G.packingParts_vertexPartition _ q
  coarsens _i _j hij := G.packingParts_coarsens (G.rankedEdges_mono R hij)

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.DyadicSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.Dyadic
noncomputable section
open Finset

def selected (M : ℕ → ℕ) (z : ℕ) : Finset ℕ :=
  ((range (z+1)).filter (fun i => 0 < M i)).filter
    (fun i => ∀j ≤ z, 0 < M j → Nat.log 2 (M j)=Nat.log 2 (M i) → i ≤ j)

end
end StrongThinTree.Dyadic

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ResponseBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph.PartitionChain
noncomputable section
open Finset
variable {n m : ℕ} (P : PartitionChain n) (G : MultiGraph n m)

def nextIndex (I : Finset ℕ) (i z : ℕ) : ℕ :=
  if h : (I.filter (fun j => i < j)).Nonempty then (I.filter (fun j => i < j)).min' h else z

end
end StrongThinTree.MultiGraph.PartitionChain

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.FixedPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uV2 uW uI uV3 uV4 uV5 uE

section

namespace StrongThinTree.FixedPoint
noncomputable section
open Finset

abbrev Chain (V : Type uV) := Finset V →₀ ZMod 2

variable {V : Type uV2} {W : Type uW} [DecidableEq V] [DecidableEq W]

def face (s : Finset V) : Chain V := Finsupp.single s 1

def boundary : Chain V →ₗ[ZMod 2] Chain V :=
  Finsupp.linearCombination (ZMod 2) (fun s : Finset V => ∑ v ∈ s, face (s.erase v))

def cone (v : V) : Chain V →ₗ[ZMod 2] Chain V :=
  Finsupp.linearCombination (ZMod 2) (fun s : Finset V =>
    if v ∈ s then 0 else face (insert v s))

def subdivFace (s : Finset V) : Chain (Finset V) :=
  if _hs : s = ∅ then face ∅ else
    cone s (∑ v : s, subdivFace (s.erase v.1))
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem v.2

def subdivision : Chain V →ₗ[ZMod 2] Chain (Finset V) :=
  Finsupp.linearCombination (ZMod 2) subdivFace

def rename (f : V → W) : Chain V →ₗ[ZMod 2] Chain W := by
  classical
  exact Finsupp.linearCombination (ZMod 2) (fun s : Finset V =>
    if Set.InjOn f (s : Set V) then face (s.image f) else 0)

def Supported (P : Finset V → Prop) (c : Chain V) : Prop :=
  ∀ s, ¬ P s → c s = 0

def Flag (s : Finset V) (t : Finset (Finset V)) : Prop :=
  t.card = s.card ∧ (∀ a ∈ t, a.Nonempty ∧ a ⊆ s) ∧
    ∀ a ∈ t, ∀ b ∈ t, a ⊆ b ∨ b ⊆ a

def IterV (V : Type uV3) : ℕ → Type _
  | 0 => V
  | k+1 => Finset (IterV V k)

instance iterVDecidableEq (V : Type uV4) [DecidableEq V] :
    (k : ℕ) → DecidableEq (IterV V k)
  | 0 => inferInstanceAs (DecidableEq V)
  | k+1 => letI := iterVDecidableEq V k
      inferInstanceAs (DecidableEq (Finset (IterV V k)))

def iterSubdivision : (k : ℕ) → Chain V →ₗ[ZMod 2] Chain (IterV V k)
  | 0 => LinearMap.id
  | k+1 => subdivision.comp (iterSubdivision k)

def mean (z : V → ℝ) (s : Finset V) : ℝ := (∑ v ∈ s, z v) / s.card

section Coordinates
variable [Fintype V]

def CoordFace (s : Finset V) (x : V → ℝ) : Prop :=
  (∀i, 0 ≤ x i) ∧ (∑i, x i) = 1 ∧ ∀i, i ∉ s → x i = 0

def baryPoint (p : W → V → ℝ) (s : Finset W) : V → ℝ :=
  fun i => mean (fun w => p w i) s

def iterPoint : (k : ℕ) → IterV V k → V → ℝ
  | 0 => fun (v : V) i => if v = i then 1 else 0
  | k+1 => baryPoint (iterPoint k)

def meshFactor (N : ℕ) : ℝ := 1 - 1 / (N : ℝ)^2

def GeometricFacet (k : ℕ) (s : Finset V) (t : Finset (IterV V k)) : Prop :=
  t.card = s.card ∧ (∀v ∈ t, CoordFace s (iterPoint k v)) ∧
    ∀u ∈ t, ∀v ∈ t, ∀i,
      |iterPoint k u i - iterPoint k v i| ≤ (meshFactor (Fintype.card V))^k

def simplex (V : Type uV5) [Fintype V] : Set (V → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

abbrev Delta (V : Type uV5) [Fintype V] := {x : V → ℝ // x ∈ simplex V}

end Coordinates

end
end StrongThinTree.FixedPoint

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.MatrixMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uV uE

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {I : Type uI} {V : Type uV} [Fintype V] [DecidableEq V]
def mixtureBadWeight (C : Finset I) (w : I → ℝ) (Y : I → Matrix V V ℝ) (t : ℝ) (b : V → ℝ) : ℝ :=
  ∑i ∈ C, if t < qform (Y i)⁻¹ b then w i else 0

end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ExtractionLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Matrix Finset Filter
open scoped MatrixOrder Matrix.Norms.Elementwise Topology
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
def thresholdCrossing (q : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) : Finset (Fin m) :=
  G.crossing univ (G.partLabel (G.thresholdEdges (G.resistance X) s) q)

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ExtractionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Filter
open scoped Topology
namespace StrongThinTree

def extractQ (r : ℕ) : ℕ := ⌊(1-(r:ℝ)^(-1/16:ℝ))*r⌋₊
def errorU (r : ℕ) : ℝ := (r:ℝ)^(-1/16:ℝ)
def resistanceT (r : ℕ) : ℝ := (r:ℝ)^(-1/2:ℝ)

end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Expectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uR uS

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {D : Type uD} {R : Type uR} {S : Type uS} [Fintype D] [DecidableEq D] [CommRing R] [CommRing S]

def detLinear (M : Matrix D D R) : Matrix D D R →ₗ[R] R :=
  Matrix.detRowAlternating.toMultilinearMap.linearDeriv M

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Stability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uI2 uA uD uI3 uD2

section

namespace StrongThinTree.MSS
noncomputable section
open Finset Polynomial
open scoped Classical ComplexOrder

def Stable {I : Type uI} (p : MvPolynomial I ℂ) : Prop :=
  ∀z : I → ℂ, (∀i, 0 < (z i).im) → MvPolynomial.eval z p ≠ 0

variable {I : Type uI2} [DecidableEq I]

def slice (p : MvPolynomial I ℂ) (z : I → ℂ) (i : I) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C (fun j => if j=i then Polynomial.X else Polynomial.C (z j)) p

section Determinant
open Matrix
variable {D : Type uD} [Fintype D] [DecidableEq D] [Fintype I]

def determinantPencil (A : I → Matrix D D ℂ) : MvPolynomial I ℂ :=
  Matrix.det (fun a b => ∑i, MvPolynomial.X i*MvPolynomial.C (A i a b))

end Determinant

end
end StrongThinTree.MSS

namespace StrongThinTree.MSS
noncomputable section
open Finset Polynomial
open scoped Classical ComplexOrder
variable {I : Type uI3} [DecidableEq I]

def differentialProduct (dirs : List I) (p : MvPolynomial I ℂ) : MvPolynomial I ℂ :=
  dirs.foldl (fun q i => q-MvPolynomial.pderiv i q) p

open Matrix

end
end StrongThinTree.MSS

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.PartialFractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Polynomial Filter Finset
open scoped Topology
namespace StrongThinTree.MSS.Rational

def cval (p : ℝ[X]) (z : ℂ) : ℂ := (p.map (algebraMap ℝ ℂ)).eval z

@[simp] lemma cval_real (p : ℝ[X]) (x : ℝ) : cval p x=((p.eval x:ℝ):ℂ) := by
  exact Polynomial.eval_map_apply (algebraMap ℝ ℂ) x

@[simp] lemma cval_mul (p q : ℝ[X]) (z : ℂ) : cval (p*q) z=cval p z*cval q z := by
  simp [cval]
@[simp] lemma cval_pow (p : ℝ[X]) (n : ℕ) (z : ℂ) : cval (p^n) z=(cval p z)^n := by
  simp [cval]
@[simp] lemma cval_X_sub_C (x : ℝ) (z : ℂ) : cval (X-C x) z=z-x := by
  simp [cval]

end StrongThinTree.MSS.Rational

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Barrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uR uR2 uR3 uR4 uS uR5 uS2 uR6

section

noncomputable section
open Polynomial Finset Filter
open scoped Topology
namespace StrongThinTree.MSS

variable {I : Type uI} [DecidableEq I]

def ray {R : Type uR} [CommRing R] (p : MvPolynomial I R) (z : I → R) (i : I) : R[X] :=
  MvPolynomial.eval₂ Polynomial.C (fun j => Polynomial.C (z j)+if j=i then Polynomial.X else 0) p

def RealStable (p : MvPolynomial I ℝ) : Prop := Stable (p.map (algebraMap ℝ ℂ))
def Above (p : MvPolynomial I ℝ) (z : I → ℝ) : Prop :=
  ∀s : I → ℝ, (∀i, 0 ≤ s i) → 0 < MvPolynomial.eval (z+s) p

def barrier (p : MvPolynomial I ℝ) (z : I → ℝ) (i : I) : ℝ :=
  MvPolynomial.eval z (MvPolynomial.pderiv i p)/MvPolynomial.eval z p

omit [DecidableEq I] in
lemma Above.add {p : MvPolynomial I ℝ} {z s : I → ℝ} (hz : Above p z) (hs : ∀i, 0 ≤ s i) :
    Above p (z+s) := by
  intro t ht
  simpa [add_assoc] using hz (s+t) (fun i => add_nonneg (hs i) (ht i))

lemma Above.update {p : MvPolynomial I ℝ} {z : I → ℝ} (hz : Above p z) (i : I) {t : ℝ} (ht : 0 ≤ t) :
    Above p (Function.update z i (z i+t)) := by
  have he : Function.update z i (z i+t)=z+Pi.single i t := by
    ext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Function.update_of_ne hj,Pi.single_eq_of_ne hj]
  rw [he]
  exact hz.add (fun j => by by_cases hj : j=i; subst j; simp [ht]; simp [Pi.single_eq_of_ne hj])

def crossBarrier (p : MvPolynomial I ℝ) (z : I → ℝ) (i j : I) : ℝ :=
  (MvPolynomial.eval z (MvPolynomial.pderiv j (MvPolynomial.pderiv i p))*MvPolynomial.eval z p-
    MvPolynomial.eval z (MvPolynomial.pderiv i p)*MvPolynomial.eval z (MvPolynomial.pderiv j p))/(MvPolynomial.eval z p)^2

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.DeterminantCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

def basePencil (M : Matrix D D R) (A : I → Matrix D D R) : MvPolynomial I R :=
  (M.map MvPolynomial.C + ∑i, (MvPolynomial.X i : MvPolynomial I R) • (A i).map MvPolynomial.C).det

def zeroSub (j : I) : MvPolynomial I R →+* MvPolynomial I R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Function.update MvPolynomial.X j 0)

def zeroDiff (j : I) (p : MvPolynomial I R) : MvPolynomial I R :=
  zeroSub j (p-MvPolynomial.pderiv j p)

def view (j : I) : MvPolynomial I R →+* (MvPolynomial I R)[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (Function.update (fun i => Polynomial.C (MvPolynomial.X i)) j Polynomial.X)

omit [Fintype I] [Fintype D] [DecidableEq D] in
@[simp] lemma view_C (j : I) (r : R) : view j (MvPolynomial.C r)=C (MvPolynomial.C r) := by
  simp [view]

omit [Fintype I] [Fintype D] [DecidableEq D] in
@[simp] lemma view_X (j i : I) : view (R := R) j (MvPolynomial.X i)=
    if i=j then X else C (MvPolynomial.X i) := by
  simp [view,Function.update_apply]

omit [Fintype I] [Fintype D] [DecidableEq D] in
@[simp] lemma zeroSub_C (j : I) (r : R) : zeroSub j (MvPolynomial.C r)=MvPolynomial.C r := by
  simp [zeroSub]

omit [Fintype I] [Fintype D] [DecidableEq D] in
@[simp] lemma zeroSub_X (j i : I) : zeroSub (R := R) j (MvPolynomial.X i)=
    if i=j then 0 else MvPolynomial.X i := by
  simp [zeroSub,Function.update_apply]

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.MixedPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

def diffProduct (dirs : List I) : MvPolynomial I R →ₗ[R] MvPolynomial I R :=
  dirs.foldr (fun j f => f.comp (LinearMap.id-(MvPolynomial.pderiv j).toLinearMap)) LinearMap.id

omit [Fintype I] [Fintype D] [DecidableEq D] in
omit [DecidableEq I] in
@[simp] lemma diffProduct_nil (p : MvPolynomial I R) : diffProduct [] p=p := rfl

omit [Fintype I] [Fintype D] [DecidableEq D] in
omit [DecidableEq I] in
@[simp] lemma diffProduct_cons (j : I) (dirs : List I) (p : MvPolynomial I R) :
    diffProduct (j::dirs) p=diffProduct dirs (p-MvPolynomial.pderiv j p) := rfl

def mixedEval (dirs : List I) (M : Matrix D D R) (A : I → Matrix D D R) : R :=
  MvPolynomial.eval (fun _ => 0) (diffProduct dirs (basePencil M A))

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.RootBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR uS

section

noncomputable section
open Polynomial Finset Matrix
open scoped MatrixOrder ComplexOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D]

def pencil [CommRing R] (A : I → Matrix D D R) : MvPolynomial I R :=
  Matrix.det (fun a b => ∑i, MvPolynomial.X i*MvPolynomial.C (A i a b))

def realDifferentialProduct (dirs : List I) (p : MvPolynomial I ℝ) : MvPolynomial I ℝ :=
  dirs.foldl (fun q j => q-MvPolynomial.pderiv j q) p

def shiftVector (dirs : List I) (δ : ℝ) : I → ℝ :=
  (dirs.map (fun j => Pi.single j δ)).sum

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.OptionalDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR uS

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} {S : Type uS} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D]
  [CommRing R] [CommRing S]

def coefficientX : MvPolynomial (Option I) R →+* MvPolynomial I R[X] :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp Polynomial.C)
    (fun o => o.elim (MvPolynomial.C Polynomial.X) MvPolynomial.X)

def uniSlice : MvPolynomial (Option I) R →+* R[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun o => o.elim Polynomial.X (fun _ => 0))

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
@[simp] lemma coefficientX_C (r : R) : coefficientX (I := I) (MvPolynomial.C r)=
    MvPolynomial.C (Polynomial.C r) := by simp [coefficientX]

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
@[simp] lemma coefficientX_X (i : Option I) : coefficientX (R := R) (MvPolynomial.X i)=
    i.elim (MvPolynomial.C Polynomial.X) MvPolynomial.X := by simp [coefficientX]

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
@[simp] lemma uniSlice_C (r : R) : uniSlice (I := I) (MvPolynomial.C r)=Polynomial.C r := by
  simp [uniSlice]

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
@[simp] lemma uniSlice_X (i : Option I) : uniSlice (R := R) (MvPolynomial.X i)=
    i.elim Polynomial.X (fun _ => 0) := by simp [uniSlice]

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR uO uO2

section

noncomputable section
open Matrix Polynomial Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

def mixedChar (A : I → Matrix D D R) : R[X] :=
  mixedEval Finset.univ.toList ((Polynomial.X : R[X]) • (1 : Matrix D D R[X]))
    (fun i => (A i).map Polynomial.C)

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.RealRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR uS

section

noncomputable section
open Matrix Polynomial Finset
open scoped MatrixOrder ComplexOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

def fullPencil (A : I → Matrix D D R) : MvPolynomial (Option I) R :=
  pencil (fun o => o.elim 1 A)

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Translation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR uS

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} {S : Type uS} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D]
  [CommRing R] [CommRing S]

def translate (x : R) : MvPolynomial I R →+* MvPolynomial I R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i+MvPolynomial.C x)

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
@[simp] lemma translate_C (x r : R) : translate (I := I) x (MvPolynomial.C r)=MvPolynomial.C r := by
  simp [translate]

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
@[simp] lemma translate_X (x : R) (i : I) : translate x (MvPolynomial.X i)=
    MvPolynomial.X i+MvPolynomial.C x := by
  simp [translate]

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Blocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uO uI uI2

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {D : Type uD} {O : Type uO} [Fintype D] [DecidableEq D] [Fintype O] [DecidableEq O]

omit [Fintype D] [DecidableEq D] in
def blockEmbed (v : D → ℝ) (b : Bool) : D × Bool → ℝ :=
  fun p => if p.2=b then v p.1 else 0

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Representation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uE uT uI uE2 uE3 uV uE4 uV2 uW

section

open Matrix Finset
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise
namespace StrongThinTree
noncomputable section

section Covariance
variable {T : Type uT} {I : Type uI} [Fintype T] [DecidableEq T] [Nonempty T]
  [Fintype I] [DecidableEq I]

def basisCov (b : Matrix I I ℝ) (a : I → ℝ) : Matrix I I ℝ :=
  b * diagonal (fun j => Real.exp (a j)) * bᵀ

def packingCov (b : T → Matrix I I ℝ) (a : EuclideanSpace ℝ (T × I)) :
    Matrix I I ℝ := ∑ t, basisCov (b t) (fun j => a (t, j))

def packingObjective (b : T → Matrix I I ℝ) (a : EuclideanSpace ℝ (T × I)) : ℝ :=
  Real.log (packingCov b a).det - (∑ e, a e) / Fintype.card T

end Covariance

end
end StrongThinTree

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset
open scoped BigOperators
variable {n m : ℕ} (G : MultiGraph n m)

def zeroSumSpace (n : ℕ) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (∑ u : Fin n, LinearMap.proj u)

lemma mem_zeroSumSpace (x : Fin n → ℝ) : x ∈ zeroSumSpace n ↔ ∑ u, x u = 0 := by
  simp [zeroSumSpace, LinearMap.mem_ker, LinearMap.sum_apply]

lemma incidence_zeroSum (e : Fin m) : G.incidence e ∈ zeroSumSpace n := by
  rw [mem_zeroSumSpace]
  simp [incidence, point, Pi.sub_apply, Finset.sum_sub_distrib, Pi.single_apply,
    Finset.sum_ite_eq']

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.StepBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace StrongThinTree

def splitEpsilon (r : ℕ) : ℝ := 6*resistanceT r
def splitTau (r : ℕ) : ℝ := 2*Real.sqrt (splitEpsilon r)+splitEpsilon r
def stepCount (r : ℕ) : ℕ := ⌊(1-4*errorU r)*r/2⌋₊

structure StepNumeric (r : ℕ) : Prop where
  rlarge : 4 ≤ r
  usmall : errorU r ≤ 1/16
  qpos : 0 < extractQ r
  size : (1+errorU r)/(extractQ r:ℝ) ≤ 2*resistanceT r
  tausmall : splitTau r ≤ errorU r/2
  packing : stepCount r ≤ ⌊(1/2-splitTau r)*(extractQ r:ℝ)/(1+errorU r)⌋₊
  lower : (5/16:ℝ)*r ≤ stepCount r
  upper : (stepCount r:ℝ) ≤ (r:ℝ)/2
  ratio : (1/2+3*splitTau r)*(r:ℝ) ≤ (1+15*errorU r)*stepCount r

end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Restriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

def edgeEmbedding (F : Finset (Fin m)) : Fin F.card ↪ Fin m :=
  F.equivFin.symm.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
def restrict (F : Finset (Fin m)) : MultiGraph n F.card where
  left e := G.left (edgeEmbedding F e)
  right e := G.right (edgeEmbedding F e)
  loopless e := G.loopless (edgeEmbedding F e)
def liftEdges (F : Finset (Fin m)) (T : Finset (Fin F.card)) : Finset (Fin m) :=
  T.map (edgeEmbedding F)
def lowerEdges (F T : Finset (Fin m)) : Finset (Fin F.card) :=
  T.preimage (edgeEmbedding F) (edgeEmbedding F).injective.injOn

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.IterationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace StrongThinTree

def iterationB : ℝ := 15 / ((2:ℝ)^(1/16:ℝ)-1)
def iterationPotential (r : ℕ) : ℝ := Real.exp (iterationB*(1-errorU r))

end StrongThinTree

end
end

end OAI
end


