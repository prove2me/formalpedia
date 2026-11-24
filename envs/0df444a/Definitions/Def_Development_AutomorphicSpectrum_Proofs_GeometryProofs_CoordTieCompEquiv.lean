-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
-- name    : Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:41.900391+00:00
-- url     : https://prove2.me/theorems/4e48f4fb-9250-4318-b0dc-ea378ab49ad0
-- title:
--   Coord Tie Comp Equiv
-- statement:
--   Definitions and structural lemmas for Coord Tie Comp Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/CoordTieCompEquiv.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.FlagBun
open AlgebraicGeometry CategoryTheory
def GenIx {S : Type} (r : S → ℕ) : Type := Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1}
abbrev GenField (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) : Type :=
  FractionRing (MvPolynomial (GenIx r) Ω)
def genU (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) :
    Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := fun l k =>
  if h : k < l then algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩)
  else if l = k then 1 else 0
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {S : Type} {r : S → ℕ}
def genB (c : ∀ s, Fin (r s) → E) (s : S) (k : Fin (r s)) : TensorProduct Ω (GenField Ω r) E :=
  ∑ l, genU Ω r s l k • TensorProduct.mk Ω (GenField Ω r) E 1 (c s l)
def flagMat {n : S → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S) :
    Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) :=
  Matrix.of (fun j l => algebraMap Ω (GenField Ω r) (φ s j (c s l))) * genU Ω r s
def FlagIx (κ : Type) {S : Type} (n : S → ℕ) (r : S → ℕ) : Type :=
  κ × ((q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
def flagCoord [Fintype S] (κ : Type) (x : κ → Ω) {n : S → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E)
    (c : ∀ s, Fin (r s) → E) : FlagIx κ n r → GenField Ω r := fun cJ =>
  algebraMap Ω (GenField Ω r) (x cJ.1) *
    ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (cJ.2 q) (Fin.castLE q.2.2)).det
def IsTwistGen {X : Scheme.{0}} (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type} (x : κ → Ω) (L : Lat ξ E) (m : ℕ)
    {n : ℕ} (φ : Fin n → Module.Dual Ω E) : Prop :=
  (∀ j (p : Cpt ξ) c, InChart ξ x c p → ∀ e ∈ L p, φ j e / x c ^ m ∈ regAt ξ p) ∧
  ∀ (p : Cpt ξ) c, InChart ξ x c p → ∀ w : Module.Dual Ω E, (∀ e ∈ L p, w e ∈ regAt ξ p) →
    ∃ g : Fin n → Ω, (∀ j, g j ∈ regAt ξ p) ∧ ∀ e ∈ L p, w e = ∑ j, g j * (φ j e / x c ^ m)
end GlobalTheory.CompanionTheory.Ar.FlagBun


