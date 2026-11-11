-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T04:27:26.939071+00:00
-- url     : https://prove2.me/theorems/bace8a71-2080-457c-90fe-7e2d6e2a7581
-- title:
--   Keyed Geometric Events
-- statement:
--   Definitions and structural lemmas for Keyed Geometric Events, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
set_option autoImplicit false
namespace QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
def KeyEligible (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (s : Finset (Triangle P)) : Prop :=
  s.card = 4 ∧
    (∀ a ∈ s, ∀ b ∈ s, BDL26NativeTriangleColors.policyColor P key a = BDL26NativeTriangleColors.policyColor P key b) ∧
    ∀ a ∈ s, ∀ b ∈ s, dist (oldAnchor P J a) (oldAnchor P J b) ≤ radius
abbrev KeyEvent (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ) :=
  {s : Finset (Triangle P) // KeyEligible P key hk J radius s}
noncomputable instance keyEventFintype (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius : ℝ) : Fintype (KeyEvent P key hk J radius) := Fintype.ofFinite _
theorem keyEvent_nonempty (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) : e.val.Nonempty := by
  apply Finset.card_pos.mp
  rw [e.property.1]
  norm_num
noncomputable def keyAnchor (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius : ℝ) (e : KeyEvent P key hk J radius) : Triangle P := by
  letI : LinearOrder (Triangle P) := LinearOrder.lift' key hk
  exact e.val.min' (keyEvent_nonempty P key hk J radius e)
noncomputable def keySupport (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius : ℝ) (e : KeyEvent P key hk J radius) : Finset (Vertex P) := by
  classical
  exact e.val.biUnion (triangleSupport P)
def keyVertex (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) (a : e.val) (i : Fin 3) : keySupport P key hk J radius e :=
  ⟨triangleVertex P a.val i, by
    classical
    exact Finset.mem_biUnion.mpr ⟨a.val,a.property,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩⟩
noncomputable def keyCenter (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : KeyEvent P key hk J radius) (g : Grid K) : Space :=
  lambda • oldAnchor P J (keyAnchor P key hk J radius e)+gridPoint K g
def keyBad (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : KeyEvent P key hk J radius) :
    Set (keySupport P key hk J radius e → Space) :=
  ⋃ g : Grid K, ⋂ a : e.val,
    (fun p i => p (keyVertex P key hk J radius e a i)) ⁻¹'
      triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i)))
        (keyCenter P key hk J radius lambda K e g) 2
end QEC.Coding.BDL26KeyedGeometric


