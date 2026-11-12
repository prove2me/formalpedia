-- Prove2me | Definitions.Def_QuantumGroupCodes836_Addressability_Families
-- name    : QuantumGroupCodes836_Addressability_Families
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T17:11:35.548312+00:00
-- url     : https://prove2.me/theorems/07d3f06a-3868-4ad7-89cb-d48130055936
-- title:
--   Growing addressable quantum group-code families with uniform asymptotics
-- statement:
--   A family consists of actual encoded CSS codes with specified physical and logical permutation actions of the same finite group, related by the encoding. The lengths tend to infinity. All asymptotic constants and eventual indices are chosen before the varying family index, error or logical circuit.
--
--   $$[[n,\Theta(n/\log n),\Theta(n)]]_q\quad\hbox{or}\quad[[n,\Theta(n),\Theta(n)]]_q.$$
--
--   Full addressability quantifies over every weighted logical tuple on distinct blocks. Orbit addressability also includes all simultaneous products with common group shifts. Global gates act on every logical register in aligned blocks. Decoding uses uniform executable programs for both error types, with positive linear radius and expected charged cost $O(n^2\log^4 n)$; the reusable description has the same polynomial size bound.
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Theorems 1.1 and 4.8, pp.3,18–19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Mathlib
import Definitions.Def_QuantumGroupCodes836_Addressability_Decoder

set_option autoImplicit false
noncomputable section

namespace QuantumGroupCodes836.Addressability

structure QuantumAlphabet (q : ℕ) where
  carrier : Type
  field : Field carrier
  fintype : Fintype carrier
  primeAlgebra : Algebra (ZMod 2) carrier
  cardinality : Fintype.card carrier = q

attribute [instance] QuantumAlphabet.field QuantumAlphabet.fintype QuantumAlphabet.primeAlgebra

/-- An actual encoded CSS code with its specified group action and module-linear section. -/
structure GroupCode (F : Type) [Field F] where
  code : EncodedCSS F
  group : Type
  groupStructure : Group group
  groupFinite : Fintype group
  physical : QuantumAction code.toCSS group
  logicalCoordinates : group →* Equiv.Perm (Fin code.toCSS.logicalDimension)
  encodingEquivariant : ∀ g x,
    code.toCSS.quotientMap
      ⟨permute (physical.action.coordinates g) (physical.sectionMap (code.encoding x)),
        physical.action.preserves g _ (physical.sectionMap (code.encoding x)).2⟩ =
      code.encoding (permute (logicalCoordinates g) x)

attribute [instance] GroupCode.groupStructure GroupCode.groupFinite

def logicalOrbit {F : Type} [Field F] (Q : GroupCode F) (j : Fin Q.code.toCSS.logicalDimension) :
    Set (Fin Q.code.toCSS.logicalDimension) := Set.range fun g => Q.logicalCoordinates g j

def orbitCount {F : Type} [Field F] (Q : GroupCode F) : ℕ := by
  classical
  exact (Finset.univ.image (logicalOrbit Q)).card

def orbitSize {F : Type} [Field F] (Q : GroupCode F) (j : Fin Q.code.toCSS.logicalDimension) : ℕ :=
  Nat.card (logicalOrbit Q j)

def alignedGate {F : Type} {n a : ℕ} (j : Fin n) (γ : F) : InterblockGate F a n a :=
  ⟨id, Function.injective_id, fun _ => j, γ⟩

/-- Global action on all logical registers, implemented at aligned physical registers. -/
def GlobalTransversal {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (Q : EncodedCSS F) (a : ℕ) : Prop :=
  ∀ γ : F, ∃ u : Fin Q.n → F, ∃ layer : PhysicalLayer F a Q.n a,
    layer.gates = List.ofFn (fun j => alignedGate j (γ * u j)) ∧
    Implements Q (List.ofFn fun j => alignedGate j γ) [layer]

/-- Includes simultaneous shared shifts across different orbits, not just single gates. -/
def OrbitAddressable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (Q : GroupCode F) (a : ℕ) : Prop :=
  (∀ j, ∀ g : InterblockGate F a Q.code.toCSS.logicalDimension a,
    (∀ h, g.sites h ∈ logicalOrbit Q j) → DepthAtMost Q.code [g] 1) ∧
  (∀ (S : Finset (Fin Q.code.toCSS.logicalDimension)) (σ : Fin a → Q.group)
      (weights : Fin Q.code.toCSS.logicalDimension → F),
    DepthAtMost Q.code
      (S.toList.map fun j =>
        (⟨id, Function.injective_id, fun h => Q.logicalCoordinates (σ h) j, weights j⟩ :
          InterblockGate F a Q.code.toCSS.logicalDimension a)) 1)

def Growing {F : Type} [Field F] (Q : ℕ → GroupCode F) : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ i ≥ N, M ≤ (Q i).code.n

def Theta (f g : ℕ → ℝ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ, ∀ i ≥ N, a * g i ≤ f i ∧ f i ≤ b * g i

def LinearDistance {F : Type} [Field F] (Q : ℕ → GroupCode F) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ i ≥ N, ∃ d : ℕ,
    (Q i).code.toCSS.quantumDistance = d ∧
    c * ((Q i).code.n : ℝ) ≤ d ∧ d ≤ (Q i).code.n

def QuasiQuadraticDecoding {F : Type} [Field F] [Fintype F]
    (Q : ℕ → GroupCode F) : Prop :=
  ∃ PX PZ : DecoderProgram F, ∃ aux : ℕ → List F, ∃ C ρ : ℝ,
    0 < C ∧ 0 < ρ ∧ ∃ N : ℕ, ∀ i ≥ N,
    let n := (Q i).code.n
    let bound := C * (n : ℝ)^2 * (Real.log n)^4
    (aux i).length ≤ bound ∧
    Decodes (Q i).code.toCSS .X PX (aux i) ⌊ρ * n⌋ bound ∧
    Decodes (Q i).code.toCSS .Z PZ (aux i) ⌊ρ * n⌋ bound

def RegularFamily {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (m : ℕ) (Q : ℕ → GroupCode F) : Prop :=
  Growing Q ∧ LinearDistance Q ∧
  Theta (fun i => (Q i).code.toCSS.logicalDimension)
    (fun i => ((Q i).code.n : ℝ) / Real.log (Q i).code.n) ∧
  (∀ i, FreeQuantum (Q i).physical 1) ∧
  (∀ a, 1 < a → a ≤ m → ∀ i, FullyAddressable (Q i).code a) ∧
  (∃ C : ℕ, 0 < C ∧ ∃ N : ℕ, ∀ i ≥ N, ∀ a, 1 < a → a ≤ m →
    ∀ logical : List (InterblockGate F m (Q i).code.toCSS.logicalDimension a),
      DepthAtMost (Q i).code logical (C * (Q i).code.toCSS.logicalDimension ^ (a - 1))) ∧
  QuasiQuadraticDecoding Q

def FreeFamily {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (m : ℕ) (Q : ℕ → GroupCode F) : Prop :=
  Growing Q ∧ LinearDistance Q ∧
  Theta (fun i => (Q i).code.toCSS.logicalDimension) (fun i => (Q i).code.n) ∧
  (∀ i, ∃ r, FreeQuantum (Q i).physical r) ∧
  Theta (fun i => orbitCount (Q i)) (fun i => Real.log (Q i).code.n) ∧
  (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ, ∀ i ≥ N,
    ∀ j : Fin (Q i).code.toCSS.logicalDimension,
    a * ((Q i).code.n : ℝ) / Real.log (Q i).code.n ≤ orbitSize (Q i) j ∧
    (orbitSize (Q i) j : ℝ) ≤ b * ((Q i).code.n : ℝ) / Real.log (Q i).code.n) ∧
  (∀ a, 1 < a → a ≤ m → ∀ i,
    GlobalTransversal (Q i).code (a + 1) ∧ OrbitAddressable (Q i) a) ∧
  QuasiQuadraticDecoding Q

end QuantumGroupCodes836.Addressability


