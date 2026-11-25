-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
-- name    : Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:19:07.756901+00:00
-- url     : https://prove2.me/theorems/7efc4ce1-bc7f-5e27-aa01-c112a8048b91
-- title:
--   Hermitian Lattices
-- statement:
--   Definitions and structural lemmas for Hermitian Lattices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/HermitianLattices.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
def form (L : LocE F E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ i, ∑ j, x i * G i j * L.cj (y j)
def IsHermND (L : LocE F E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ i j, G j i = L.cj (G i j)) ∧ IsUnit G.det
def IsLattice (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) : Prop :=
  Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤
def IsSelfDual (L : LocE F E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule L.O (Fin n → E)) : Prop :=
  IsLattice L Λ ∧ ∀ y : Fin n → E, y ∈ Λ ↔ ∀ x ∈ Λ, form L G x y ∈ L.O
def IsIsometry (L : LocE F E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop :=
  ∀ x y, form L G (g x) (g y) = form L G x y
def HasOrthonormalBasis (L : LocE F E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule L.O (Fin n → E)) : Prop :=
  ∃ b : Module.Basis (Fin n) L.O Λ,
    ∀ i j, form L G (b i : Fin n → E) (b j : Fin n → E) = if i = j then 1 else 0
def SelfDualOneOrbit : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermND L G →
    (∀ Λ : Submodule L.O (Fin n → E), IsSelfDual L G Λ → HasOrthonormalBasis L G Λ) ∧
    (∀ Λ Λ' : Submodule L.O (Fin n → E), IsSelfDual L G Λ → IsSelfDual L G Λ' →
      ∃ g : (Fin n → E) ≃ₗ[E] (Fin n → E), IsIsometry L G g ∧
        g '' (Λ : Set (Fin n → E)) = (Λ' : Set (Fin n → E)))
end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks
end


