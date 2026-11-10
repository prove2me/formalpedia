-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:57:23.479962+00:00
-- url     : https://prove2.me/theorems/5a6df969-dda3-47e3-bcea-b59f48506522
-- title:
--   Events
-- statement:
--   Definitions and structural lemmas for Events, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Events.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingGeometry
import Mathlib.Data.Nat.Choose.Bounds
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleKey_injective

set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
noncomputable def oldAnchor (P : TannerSquarePresentation) (J : Vertex P → Space)
    (a : Triangle P) : Space := (1/2 : ℝ) • J (.x (P.faceX a.1))
def Eligible (P : TannerSquarePresentation) (J : Vertex P → Space) (radius : ℝ)
    (s : Finset (Triangle P)) : Prop :=
  s.card = 4 ∧
    (∀ a ∈ s, ∀ b ∈ s, triangleColor P a = triangleColor P b) ∧
    ∀ a ∈ s, ∀ b ∈ s, dist (oldAnchor P J a) (oldAnchor P J b) ≤ radius
abbrev Event (P : TannerSquarePresentation) (J : Vertex P → Space) (radius : ℝ) :=
  {s : Finset (Triangle P) // Eligible P J radius s}
noncomputable instance eventFintype (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) : Fintype (Event P J radius) := Fintype.ofFinite _
theorem event_nonempty (P : TannerSquarePresentation) (J : Vertex P → Space) (radius : ℝ)
    (e : Event P J radius) : e.val.Nonempty := by
  apply Finset.card_pos.mp
  rw [e.property.1]
  norm_num
noncomputable def eventAnchor (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) : Triangle P := by
  letI : LinearOrder (Triangle P) := LinearOrder.lift' (triangleKey P) (triangleKey_injective P)
  exact e.val.min' (event_nonempty P J radius e)
noncomputable def eventSupport (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) : Finset (Vertex P) := by
  classical
  exact e.val.biUnion (triangleSupport P)
def eventVertex (P : TannerSquarePresentation) (J : Vertex P → Space) (radius : ℝ)
    (e : Event P J radius) (a : e.val) (i : Fin 3) : eventSupport P J radius e :=
  ⟨triangleVertex P a.val i, by
    classical
    exact Finset.mem_biUnion.mpr ⟨a.val,a.property,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩⟩
noncomputable def eventCenter (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius) (g : Grid K) : Space :=
  lambda • oldAnchor P J (eventAnchor P J radius e)+gridPoint K g
def eventBad (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius) :
    Set (eventSupport P J radius e → Space) :=
  ⋃ g : Grid K, ⋂ a : e.val,
    (fun p i => p (eventVertex P J radius e a i)) ⁻¹'
      triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i)))
        (eventCenter P J radius lambda K e g) 2
end QEC.Coding.BDL26RandomPerturbation


