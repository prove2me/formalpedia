-- Prove2me | Definitions.Def_EilenbergGanea
-- name    : EilenbergGanea
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:09.426649+00:00
-- url     : https://prove2.me/theorems/acac05cd-1dc6-4794-bf5c-de6943526a2c
-- statement:
--   The construction starts with two signed relator words, x²y⁻⁵ and x²(yx⁻¹)³, of lengths seven and eight. Each of two circles meeting at a common vertex is divided into three edges, and each relator boundary traverses these edges in the direction prescribed by its letters. For each relator, a new central vertex and radial edges divide its boundary into respectively 21 or 24 triangular sectors. The resulting incidence data comprise seven vertices, 51 edges, and 45 sectors; edge endpoints and sector boundaries determine the proper-face relation. The seed graph has these cells as vertices, with two cells adjacent exactly when one is a proper face of the other. For any simple graph, its Artin group is the group presented by one generator per vertex and the commutator relation for every adjacent pair. The height homomorphism sends every generator to 1 in the additive group of integers, and SourceGroup is its kernel for the seed graph. The cohomological dimension of a group is defined as the projective dimension of the trivial integral module over its integral group ring, valued in the extended natural numbers with an additional bottom element. HasClassifyingSpace(G,d) is the proposition that there exists a Hausdorff, path-connected CW space with no cells in degrees greater than d, whose fundamental group at some basepoint is isomorphic to G, and which admits a surjective covering map from a contractible space. Both spaces lie in the specified universe; the definition imposes no bound on the number of cells.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EilenbergGanea.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EilenbergGanea.lean; bytes 16..4624
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open Classical Set Topology

namespace EilenbergGanea

/-- The signed words encode the relators `x²y⁻⁵` and `x²(yx⁻¹)³`. -/
def seedWord : Bool → List (Bool × Bool)
  | false => [(false, true), (false, true), (true, false), (true, false),
      (true, false), (true, false), (true, false)]
  | true => [(false, true), (false, true), (true, true), (false, false),
      (true, true), (false, false), (true, true), (false, false)]

def boundaryLength (relation : Bool) : ℕ := 3 * (seedWord relation).length

abbrev RoseVertex := Option (Bool × Fin 2)
abbrev SeedVertex := RoseVertex ⊕ Bool
abbrev CircleEdge := Bool × Fin 3
abbrev Sector := (relation : Bool) × Fin (boundaryLength relation)
abbrev SeedEdge := CircleEdge ⊕ Sector
abbrev SeedCell := SeedVertex ⊕ (SeedEdge ⊕ Sector)

def circleStart (edge : CircleEdge) : RoseVertex :=
  ![none, some (edge.1, 0), some (edge.1, 1)] edge.2

def circleEnd (edge : CircleEdge) : RoseVertex :=
  ![some (edge.1, 0), some (edge.1, 1), none] edge.2

def sectorLetter (sector : Sector) : Bool × Bool :=
  (seedWord sector.1).get ⟨sector.2.val / 3, by
    have bound := sector.2.isLt
    dsimp [boundaryLength] at bound
    omega⟩

def sectorCircleEdge (sector : Sector) : CircleEdge :=
  ((sectorLetter sector).1, if (sectorLetter sector).2 then
    ⟨sector.2.val % 3, Nat.mod_lt _ (by decide)⟩ else
    ⟨2 - sector.2.val % 3, by omega⟩)

def sectorStart (sector : Sector) : RoseVertex :=
  if (sectorLetter sector).2 then circleStart (sectorCircleEdge sector)
  else circleEnd (sectorCircleEdge sector)

def nextSector (sector : Sector) : Sector :=
  ⟨sector.1, ⟨(sector.2.val + 1) % boundaryLength sector.1,
    Nat.mod_lt _ (by have := sector.2.isLt; omega)⟩⟩

def edgeVertices : SeedEdge → Finset SeedVertex
  | .inl edge => {.inl (circleStart edge), .inl (circleEnd edge)}
  | .inr sector => {.inr sector.1, .inl (sectorStart sector)}

def sectorEdges (sector : Sector) : Finset SeedEdge :=
  {.inl (sectorCircleEdge sector), .inr sector, .inr (nextSector sector)}

def sectorVertices (sector : Sector) : Finset SeedVertex :=
  (sectorEdges sector).biUnion edgeVertices

def properFace : SeedCell → SeedCell → Prop
  | .inl vertex, .inr (.inl edge) => vertex ∈ edgeVertices edge
  | .inl vertex, .inr (.inr sector) => vertex ∈ sectorVertices sector
  | .inr (.inl edge), .inr (.inr sector) => edge ∈ sectorEdges sector
  | _, _ => False

/-- Comparability graph of the seven vertices, 51 edges and 45 sectors. -/
def seedGraph : SimpleGraph SeedCell where
  Adj first second := properFace first second ∨ properFace second first
  symm := ⟨fun _ _ adjacent => adjacent.elim Or.inr Or.inl⟩
  loopless := ⟨by
    intro cell
    rcases cell with vertex | cell
    · simp [properFace]
    · rcases cell with edge | sector <;> simp [properFace]⟩

def artinRelations {Vertex : Type*} (graph : SimpleGraph Vertex) : Set (FreeGroup Vertex) :=
  {word | ∃ first second, graph.Adj first second ∧
    word = FreeGroup.of first * FreeGroup.of second *
      (FreeGroup.of first)⁻¹ * (FreeGroup.of second)⁻¹}

abbrev ArtinGroup {Vertex : Type*} (graph : SimpleGraph Vertex) :=
  PresentedGroup (artinRelations graph)

def height {Vertex : Type*} (graph : SimpleGraph Vertex) :
    ArtinGroup graph →* Multiplicative ℤ :=
  PresentedGroup.toGroup (f := fun _ : Vertex => Multiplicative.ofAdd (1 : ℤ)) (by
    rintro word ⟨first, second, _, rfl⟩
    simp)

abbrev SourceGroup := (height seedGraph).ker

/-- Projective dimension of the trivial integral left group-ring module. -/
def cohomologicalDimension (GroupType : Type*) [Group GroupType] : WithBot ℕ∞ :=
  CategoryTheory.projectiveDimension
    (ModuleCat.of (MonoidAlgebra ℤ GroupType)
      (Representation.trivial ℤ GroupType ℤ).asModule)

universe u

/-- Ordinary classifying CW spaces, with no bound on the cardinality of their cells. -/
def HasClassifyingSpace (GroupType : Type*) [Group GroupType] (dimension : ℕ) : Prop :=
  ∃ (Space : Type u) (_ : TopologicalSpace Space) (_ : T2Space Space)
    (_ : Topology.CWComplex (Set.univ : Set Space)),
    (∀ degree : ℕ, dimension < degree →
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set Space) degree)) ∧
    PathConnectedSpace Space ∧
    ∃ basepoint : Space, Nonempty (FundamentalGroup Space basepoint ≃* GroupType) ∧
    ∃ (Cover : Type u) (_ : TopologicalSpace Cover), ContractibleSpace Cover ∧
    ∃ projection : Cover → Space, IsCoveringMap projection ∧ Function.Surjective projection



end EilenbergGanea
end
end OAI


