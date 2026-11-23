-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:30.657803+00:00
-- url     : https://prove2.me/theorems/ba4947ee-60b6-4a5d-ad79-12c603de656c
-- title:
--   Is Proper Spreads Out
-- statement:
--   Definitions and structural lemmas for Is Proper Spreads Out, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter
namespace GlobalTheory.CompanionTheory.Ultra
section Core
variable {R₀ R : Type} [CommRing R₀] [CommRing R] {X Y : Scheme.{0}}
  (f₀ : X ⟶ Spec (CommRingCat.of R₀))
def baseHom (W : X.affineOpens) : R₀ →+* Γ(X, W.1) :=
  (Spec.preimage (W.2.fromSpec ≫ f₀)).hom
variable {f₀}
variable (f₀)
variable {ι : Type} (U : Ultrafilter ι) {T V K : ι → Type} [∀ i, CommRing (T i)]
  [∀ i, CommRing (V i)] [∀ i, IsDomain (V i)] [∀ i, ValuationRing (V i)] [∀ i, Field (K i)]
  [∀ i, Algebra (V i) (K i)] [∀ i, IsFractionRing (V i) (K i)]
  (ψ : ∀ i, R₀ →+* T i)
  (a : ∀ i, Spec (CommRingCat.of (K i)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i))))
  (β : ∀ i, T i →+* V i)
end Core
def lvl {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) (S₀ : Set R₀) (F : Finset R) :
    Subalgebra ℤ R :=
  Algebra.adjoin ℤ (φ '' S₀ ∪ (F : Set R))
lemma map_mem_lvl {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {S₀ : Set R₀}
    (hS₀ : Algebra.adjoin ℤ S₀ = ⊤) (F : Finset R) (r : R₀) : φ r ∈ lvl φ S₀ F := by
  have hr : r ∈ Algebra.adjoin ℤ S₀ := hS₀ ▸ Algebra.mem_top
  induction hr using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (Or.inl ⟨x, hx, rfl⟩)
  | algebraMap z => simpa using (lvl φ S₀ F).algebraMap_mem z
  | add x y _ _ hx hy => simpa using (lvl φ S₀ F).add_mem hx hy
  | mul x y _ _ hx hy => simpa using (lvl φ S₀ F).mul_mem hx hy
def lvlHom {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {S₀ : Set R₀}
    (hS₀ : Algebra.adjoin ℤ S₀ = ⊤) (F : Finset R) : R₀ →+* lvl φ S₀ F :=
  φ.codRestrict (lvl φ S₀ F) (map_mem_lvl φ hS₀ F)
end GlobalTheory.CompanionTheory.Ultra
namespace GlobalTheory.CompanionTheory.SpreadingModels
open GlobalTheory.CompanionTheory.Ultra
end GlobalTheory.CompanionTheory.SpreadingModels


