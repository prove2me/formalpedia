-- Prove2me | Definitions.Def_QuantumGroupCodes836_Addressability_Quantum
-- name    : QuantumGroupCodes836_Addressability_Quantum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T17:07:27.683704+00:00
-- url     : https://prove2.me/theorems/f79f524e-5f1d-4555-8723-2df1e9fb8d85
-- title:
--   CSS coset encoding, group sections and physical circuit semantics
-- statement:
--   Let $S\subseteq C\subseteq F^n$ be linear subspaces, representing $C_0^\perp$ and $C_1$. The CSS space is spanned by normalized coset states, and its logical space is $C/S$.
--
--   $$|c+S\rangle=|S|^{-1/2}\sum_{s\in S}|c+s\rangle.$$
--
--   Logical dimension and quantum distance are computed from this quotient and the two nontrivial quotient-weight minima. A quantum group action includes an equivariant linear section. Regular and free modules are represented by one or several copies of functions on the group. Field-trace gates act on complex amplitudes; a physical layer contains only gates with disjoint supports. Implementation means equality of operators on all encoded states, and physical depth counts such layers.
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Definitions 3.1–3.2 and multi-control gates, pp.9–10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Mathlib
import Definitions.Def_QuantumGroupCodes836_Addressability_Linear

set_option autoImplicit false
noncomputable section

namespace QuantumGroupCodes836.Addressability

/-- Store the two actual subspaces C₀ᵖᵉʳᵖ and C₁, not numerical code parameters. -/
structure CSS (F : Type) [Field F] where
  n : ℕ
  stabilizerX : Code F (Fin n)
  classical : Code F (Fin n)
  included : stabilizerX ≤ classical

namespace CSS
variable {F : Type} [Field F]

def kernel (Q : CSS F) : Submodule F Q.classical := Q.stabilizerX.comap Q.classical.subtype
abbrev Logical (Q : CSS F) := Q.classical ⧸ Q.kernel

def logicalDimension (Q : CSS F) : ℕ := Module.finrank F Q.Logical

def quotientMap (Q : CSS F) : Q.classical →ₗ[F] Q.Logical := Q.kernel.mkQ

def quantumDistance (Q : CSS F) : ℕ∞ :=
  min (⨅ (c : Q.classical) (_ : (c : Fin Q.n → F) ∉ Q.stabilizerX),
    (weight (c : Fin Q.n → F) : ℕ∞))
    (⨅ (c : dual Q.stabilizerX) (_ : (c : Fin Q.n → F) ∉ dual Q.classical),
      (weight (c : Fin Q.n → F) : ℕ∞))

/-- Normalized coset basis, including its complex normalization. -/
def cosetState [Fintype F] (Q : CSS F) (y : Q.Logical) : (Fin Q.n → F) → ℂ := by
  classical
  let c : Q.classical := Quotient.out y
  exact fun v => if v - (c : Fin Q.n → F) ∈ Q.stabilizerX
    then ((Real.sqrt (Nat.card Q.stabilizerX : ℝ))⁻¹ : ℂ) else 0

def codespace [Fintype F] (Q : CSS F) : Submodule ℂ ((Fin Q.n → F) → ℂ) :=
  Submodule.span ℂ (Set.range Q.cosetState)

end CSS

structure EncodedCSS (F : Type) [Field F] extends CSS F where
  encoding : (Fin toCSS.logicalDimension → F) ≃ₗ[F] toCSS.Logical

/-- The group acts freely on the physical coordinates and preserves both CSS subspaces. -/
structure QuantumAction {F : Type} [Field F] (Q : CSS F) (G : Type) [Group G] where
  action : CodeAction F (Fin Q.n) G Q.classical
  stabilizes : ∀ g c, c ∈ Q.stabilizerX → permute (action.coordinates g) c ∈ Q.stabilizerX
  sectionMap : Q.Logical →ₗ[F] Q.classical
  sectionLaw : ∀ y, Q.quotientMap (sectionMap y) = y
  equivariant : ∀ (g : G) (c : Q.classical),
    sectionMap (Q.quotientMap ⟨permute (action.coordinates g) c, action.preserves g c c.2⟩) =
      ⟨permute (action.coordinates g) (sectionMap (Q.quotientMap c)),
        action.preserves g _ (sectionMap (Q.quotientMap c)).2⟩

/-- Functions on G are the regular module; r copies give the free module of rank r. -/
def FreeQuantum {F : Type} [Field F] {G : Type} [Group G]
    {Q : CSS F} (A : QuantumAction Q G) (r : ℕ) : Prop :=
  ∃ E : (Fin r × G → F) ≃ₗ[F] Q.Logical, ∀ g f,
    Q.quotientMap ⟨permute (A.action.coordinates g) (A.sectionMap (E f)),
      A.action.preserves g _ (A.sectionMap (E f)).2⟩ = E (fun j => f (j.1, g⁻¹ * j.2))

/-- A gate has one qudit in each of its distinct participating blocks. -/
structure InterblockGate (F : Type) (b n a : ℕ) where
  blocks : Fin a → Fin b
  distinctBlocks : Function.Injective blocks
  sites : Fin a → Fin n
  coefficient : F

def gateSupport {F : Type} {b n a : ℕ} (g : InterblockGate F b n a) : Set (Fin b × Fin n) :=
  Set.range fun j => (g.blocks j, g.sites j)

structure PhysicalLayer (F : Type) (b n a : ℕ) where
  gates : List (InterblockGate F b n a)
  disjoint : gates.Pairwise fun g h => Disjoint (gateSupport g) (gateSupport h)

/-- The trace to the prime field F₂, and the literal field-trace phase in the paper. -/
def phase {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] (x : F) : ℂ :=
  Complex.exp (Complex.I * Real.pi * ((Algebra.trace (ZMod 2) F x).val : ℂ))

def gatePhase {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    {b n a : ℕ} (g : InterblockGate F b n a) (v : Fin b → Fin n → F) : ℂ :=
  phase (g.coefficient * ∏ j, v (g.blocks j) (g.sites j))

def circuitPhase {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    {b n a : ℕ} (gates : List (InterblockGate F b n a)) (v : Fin b → Fin n → F) : ℂ :=
  (gates.map fun g => gatePhase g v).prod

def tensorEncoding {F : Type} [Field F] [Fintype F] (Q : EncodedCSS F) (b : ℕ)
    (ψ : (Fin b → Fin Q.toCSS.logicalDimension → F) → ℂ)
    (v : Fin b → Fin Q.n → F) : ℂ :=
  ∑ x, ψ x * ∏ j, Q.toCSS.cosetState (Q.encoding (x j)) (v j)

/-- Equality of operators on the actual tensor-product codespace. -/
def Implements {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (Q : EncodedCSS F) {b a : ℕ}
    (logical : List (InterblockGate F b Q.toCSS.logicalDimension a))
    (physical : List (PhysicalLayer F b Q.n a)) : Prop :=
  ∀ ψ v, circuitPhase (physical.flatMap PhysicalLayer.gates) v * tensorEncoding Q b ψ v =
    tensorEncoding Q b (fun x => circuitPhase logical x * ψ x) v

def DepthAtMost {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (Q : EncodedCSS F) {b a : ℕ}
    (logical : List (InterblockGate F b Q.toCSS.logicalDimension a)) (d : ℕ) : Prop :=
  ∃ physical, physical.length ≤ d ∧ Implements Q logical physical

def FullyAddressable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (Q : EncodedCSS F) (a : ℕ) : Prop :=
  ∀ g : InterblockGate F a Q.toCSS.logicalDimension a, DepthAtMost Q [g] 1

end QuantumGroupCodes836.Addressability


