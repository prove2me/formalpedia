-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RigFrame
-- name    : Development_AbelianVarietyTheory_Proofs_GenericRegularity_RigFrame
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:07.333089+00:00
-- url     : https://prove2.me/theorems/d1039b5e-46c9-46d3-8ddb-b841a18a4644
-- title:
--   Rig Frame
-- statement:
--   Definitions and structural lemmas for Rig Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RigFrame.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_BaseNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameNorm
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}
def AHMean {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (P : (F.Di k).La →+ (Fin g → ℂ)) (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (m : ℝ) : Prop :=
  ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
    (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
    Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
    (∀ a b, (hermForm Hm (P a) (P b)).im = (F.Di k).EF a b) ∧
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ j z, ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
    (∀ j j' z, ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex k P z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
    (∀ j, ⊤ ≤ (F.ex k P 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    (∀ a j z, ‖χl (P a)‖ = 1 ∧ (⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (P a) * Complex.exp (Real.pi * hermForm Hm z (P a) +
        Real.pi / 2 * hermForm Hm (P a) (P a)) * fr j (z + P a))) ∧
    (∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ gxFst x = (F.ex k P z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) ∧
    MeasureTheory.IsAddFundamentalDomain P.range Fd MeasureTheory.volume ∧
    (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
      (MeasureTheory.volume Fd).toReal = m
def RigFrame {g m : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ)))
    (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ) : Prop :=
  (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ (F.ex k (P bz.1) bz.2).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ j b z, b ∈ B → ⊤ ≤ (F.ex k (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, z) ≠ 0) ∧
    (∀ j j' b z, b ∈ B → ⊤ ≤ (F.ex k (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j (b, z) = valAt' (F.ex k (P b) z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' (b, z)) ∧
    ∀ j b, b ∈ B → ⊤ ≤ (F.ex k (P b) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j (b, 0) = valAt' (F.u k (P b)) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val
def SecVal {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (P : (F.Di k).La →+ (Fin g → ℂ)) (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (θ : (Fin g → ℂ) → ℂ)
    (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) : Prop :=
  ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ gxFst x = (F.ex k P z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
    ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z
end GlobalTheory.FrameNorm


