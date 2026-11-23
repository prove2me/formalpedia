-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_CompactFixesLattice
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_CompactFixesLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:23.35329+00:00
-- url     : https://prove2.me/theorems/382e1a74-2972-400b-b4e3-501089491de6
-- title:
--   Compact Fixes Lattice
-- statement:
--   Definitions and structural lemmas for Compact Fixes Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL1/CompactFixesLattice/CompactFixesLattice.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
section Group
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
def stabGL {R : Type} [CommRing R] [Algebra R A] (Λ : Submodule R (n → A)) : Subgroup (GL n A) where
  carrier := {g | ∀ x : n → A, x ∈ Λ ↔ (g : Matrix n n A) *ᵥ x ∈ Λ}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro a b ha hb x
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb x).trans (ha _)
  inv_mem' := by
    intro g hg x
    have := hg (((g⁻¹ : GL n A) : Matrix n n A) *ᵥ x)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    exact this.symm
end Group
section Points
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]
def inclE (R : Type) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom
def tensInt (R : Type) [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R) :
    Subring (E ⊗[F] R) :=
  Subring.closure (Set.range (fun x : S₁ => (x : E) ⊗ₜ[F] (1 : R)) ∪
    Set.range (fun y : S₂ => (1 : E) ⊗ₜ[F] (y : R)))
def intAd (F : Type) [Field F] [NumberField F] : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  mul_mem' := fun {a b} ha hb v => by
    show a v * b v ∈ _
    exact mul_mem (ha v) (hb v)
  one_mem' := fun v => by show (1 : v.adicCompletion F) ∈ _; exact one_mem _
  add_mem' := fun {a b} ha hb v => by
    show a v + b v ∈ _
    exact add_mem (ha v) (hb v)
  zero_mem' := fun v => by show (0 : v.adicCompletion F) ∈ _; exact zero_mem _
  neg_mem' := fun {a} ha v => by
    show -(a v) ∈ _
    exact neg_mem (ha v)
def intOE (E : Type) [Field E] [NumberField E] : Subring E := (algebraMap (𝓞 E) E).range
def latS (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R)) {O : Type} [CommRing O]
    [Algebra O E] (Λ : Submodule O (n → E)) : Submodule S (n → E ⊗[F] R) :=
  Submodule.span S ((fun x : n → E => fun i => inclE (F := F) R (x i)) '' (Λ : Set (n → E)))
@[reducible] def tensTop (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (E ⊗[F] R) :=
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  moduleTopology R (E ⊗[F] R)
end Points
def CompactFixesLattice : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ),
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ U : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    IsCompact (U : Set (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) →
    ∃ Λ : Submodule (𝓞 E) (Fin k → E), Module.Finite (𝓞 E) Λ ∧
      Submodule.span E (Λ : Set (Fin k → E)) = ⊤ ∧
      U ≤ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ)
abbrev AF (F : Type) [Field F] [NumberField F] : Type := FiniteAdeleRing (𝓞 F) F
abbrev AE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : Type :=
  E ⊗[F] FiniteAdeleRing (𝓞 F) F
abbrev SS (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (AE F E) :=
  tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
end


