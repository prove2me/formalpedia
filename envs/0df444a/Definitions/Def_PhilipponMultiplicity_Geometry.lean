-- Prove2me | Definitions.Def_PhilipponMultiplicity_Geometry
-- name    : PhilipponMultiplicity_Geometry
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-23T20:15:55.165406+00:00
-- url     : https://prove2.me/theorems/6a3e0960-6182-400f-9a4c-ddea6638806b
-- title:
--   Embedded groups and multihomogeneous geometry
-- statement:
--   Actual complex or completed algebraic-closure ℓ-adic base fields, products of projective spaces, polynomial coordinates, locally closed commutative group varieties with locally polynomial regular group operations, closed algebraic subgroups, identity-component sets, sumsets, translates, and finite coset counts. No dimension or degree function is supplied as unconstrained data.
--
--   Compiled, admission-free definition bundle. Theorems asserting its substantive properties remain open targets in the full-paper goal.
-- source:
--   Philippon 1986, §§2–5; 1987 corrections/addenda. https://numdam.org/articles/10.24033/bsmf.2060/

import Mathlib

/-! Concrete multiprojective coordinates and embedded commutative group data.
No multiplicity estimate or degree value is an input to these definitions. -/

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity

universe u

def IsPhilipponBaseField (K : Type u) [NontriviallyNormedField K] : Prop :=
  (∃ e : K ≃+* ℂ, Isometry e) ∨
  (∃ p : ℕ, ∃ hp : p.Prime,
    letI : Fact p.Prime := ⟨hp⟩
    ∃ e : K ≃+* PadicComplex p, Isometry e)

structure MultiProjectiveSpace (K : Type u) where
  factorCount : ℕ
  positive : 0 < factorCount
  ambientDimension : Fin factorCount → ℕ

namespace MultiProjectiveSpace

variable {K : Type u} [Field K]

abbrev FactorIndex (M : MultiProjectiveSpace K) := Fin M.factorCount
abbrev Variable (M : MultiProjectiveSpace K) :=
  (i : M.FactorIndex) × Fin (M.ambientDimension i + 1)
abbrev CoordinateRing (M : MultiProjectiveSpace K) := MvPolynomial M.Variable K
abbrev Point (M : MultiProjectiveSpace K) :=
  ∀ i : M.FactorIndex, Projectivization K (Fin (M.ambientDimension i + 1) → K)

def coordinate (M : MultiProjectiveSpace K) (x : M.Point) (v : M.Variable) : K :=
  (x v.1).rep v.2

def eval (M : MultiProjectiveSpace K) (P : M.CoordinateRing) (x : M.Point) : K :=
  MvPolynomial.eval (M.coordinate x) P

def IsHomogeneous (M : MultiProjectiveSpace K)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) : Prop :=
  ∀ m ∈ P.support, ∀ i, ∑ j : Fin (M.ambientDimension i + 1), m ⟨i, j⟩ = D i

def IsHomogeneousAtMost (M : MultiProjectiveSpace K)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) : Prop :=
  ∃ d : M.FactorIndex → ℕ, (∀ i, d i ≤ D i) ∧ M.IsHomogeneous P d

def IsHomogeneousIdeal (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing) : Prop :=
  I = Ideal.span {P | P ∈ I ∧ ∃ D, M.IsHomogeneous P D}

def zariskiTopology (M : MultiProjectiveSpace K) : TopologicalSpace M.Point :=
  TopologicalSpace.generateFrom
    {U | ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
      U = {x | M.eval P x ≠ 0}}

def vanishingIdeal (M : MultiProjectiveSpace K) (S : Set M.Point) : Ideal M.CoordinateRing :=
  Ideal.span {P | (∃ D, M.IsHomogeneous P D) ∧ ∀ x ∈ S, M.eval P x = 0}

def zeroLocus (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing) : Set M.Point :=
  {x | ∀ P ∈ I, M.eval P x = 0}

def IsRegularAlong (M Q : MultiProjectiveSpace K) {X : Type u}
    (e : X → M.Point) (f : X → Q.Point) : Prop :=
  ∀ x : X, ∀ b : Q.FactorIndex,
    ∃ U : Set M.Point, @IsOpen _ M.zariskiTopology U ∧ e x ∈ U ∧
      ∃ D : M.FactorIndex → ℕ,
      ∃ P : Fin (Q.ambientDimension b + 1) → M.CoordinateRing,
        (∀ j, M.IsHomogeneous (P j) D) ∧
        ∀ y : X, e y ∈ U →
          ∃ h : (fun j => M.eval (P j) (e y)) ≠ 0,
            Projectivization.mk K (fun j => M.eval (P j) (e y)) h = f y b

end MultiProjectiveSpace

def projectiveSpace (K : Type u) (n : ℕ) : MultiProjectiveSpace K :=
  ⟨1, by omega, fun _ => n⟩

def projectiveSquare (K : Type u) (n : ℕ) : MultiProjectiveSpace K :=
  ⟨2, by omega, fun _ => n⟩

structure EmbeddedCommutativeGroup (K : Type u) [Field K] where
  ambientDimension : ℕ
  carrier : Set (Projectivization K (Fin (ambientDimension + 1) → K))
  group : AddCommGroup carrier
  locallyClosed : @IsLocallyClosed _
    (TopologicalSpace.induced (fun x _ => x) (projectiveSpace K ambientDimension).zariskiTopology)
    carrier
  addition_regular :
    letI := group
    MultiProjectiveSpace.IsRegularAlong
      (projectiveSquare K ambientDimension) (projectiveSpace K ambientDimension)
      (fun xy : carrier × carrier => fun i => if i.val = 0 then xy.1.val else xy.2.val)
      (fun xy : carrier × carrier => fun _ => (xy.1 + xy.2).val)
  negation_regular :
    letI := group
    MultiProjectiveSpace.IsRegularAlong
      (projectiveSpace K ambientDimension) (projectiveSpace K ambientDimension)
      (fun x : carrier => fun _ => x.val)
      (fun x : carrier => fun _ => (-x).val)

namespace EmbeddedCommutativeGroup

variable {K : Type u} [Field K]
abbrev Point (E : EmbeddedCommutativeGroup K) := E.carrier
instance (E : EmbeddedCommutativeGroup K) : AddCommGroup E.Point := E.group

end EmbeddedCommutativeGroup

structure EmbeddedGroupProduct (K : Type u) [Field K] where
  factorCount : ℕ
  positive : 0 < factorCount
  factor : Fin factorCount → EmbeddedCommutativeGroup K

namespace EmbeddedGroupProduct

variable {K : Type u} [Field K]
abbrev FactorIndex (G : EmbeddedGroupProduct K) := Fin G.factorCount
abbrev Point (G : EmbeddedGroupProduct K) := ∀ i, (G.factor i).Point

def ambient (G : EmbeddedGroupProduct K) : MultiProjectiveSpace K :=
  ⟨G.factorCount, G.positive, fun i => (G.factor i).ambientDimension⟩

abbrev CoordinateRing (G : EmbeddedGroupProduct K) := G.ambient.CoordinateRing

def embedding (G : EmbeddedGroupProduct K) (x : G.Point) : G.ambient.Point :=
  fun i => (x i).val

def zariskiTopology (G : EmbeddedGroupProduct K) : TopologicalSpace G.Point :=
  TopologicalSpace.induced G.embedding G.ambient.zariskiTopology

def vanishingIdeal (G : EmbeddedGroupProduct K) (S : Set G.Point) : Ideal G.CoordinateRing :=
  G.ambient.vanishingIdeal (G.embedding '' S)

end EmbeddedGroupProduct

structure AlgebraicSubgroup {K : Type u} [Field K] (G : EmbeddedGroupProduct K) where
  toAddSubgroup : AddSubgroup G.Point
  isClosed : @IsClosed _ G.zariskiTopology (toAddSubgroup : Set G.Point)

namespace AlgebraicSubgroup

variable {K : Type u} [Field K] {G : EmbeddedGroupProduct K}
def carrier (H : AlgebraicSubgroup G) : Set G.Point := H.toAddSubgroup
def IsConnected (H : AlgebraicSubgroup G) : Prop :=
  @_root_.IsConnected _ G.zariskiTopology H.carrier

def identityComponent (H : AlgebraicSubgroup G) : Set G.Point :=
  @connectedComponentIn _ G.zariskiTopology H.carrier 0

end AlgebraicSubgroup

def translate {X : Type u} [Add X] (g : X) (S : Set X) : Set X :=
  (fun x => g + x) '' S

def sumset {X : Type u} [AddCommGroup X] (sample : Finset X) (n : ℕ) : Finset X := by
  classical
  exact Finset.univ.image (fun x : Fin n → {y // y ∈ sample} => ∑ i, (x i).val)

def cosetCount {X : Type u} [AddCommGroup X] (sample : Finset X) (H : Set X) : ℕ := by
  classical
  exact (sample.image (fun x => translate x H)).card

def zeroLocusOnGroup {K : Type u} [Field K] (G : EmbeddedGroupProduct K)
    (P : G.CoordinateRing) : Set G.Point :=
  {x | G.ambient.eval P (G.embedding x) = 0}

def IsMultihomogeneousOfDegree {K : Type u} [Field K] (G : EmbeddedGroupProduct K)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) : Prop :=
  G.ambient.IsHomogeneous P D

end PhilipponMultiplicity


