-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T13:17:32.298626+00:00
-- url     : https://prove2.me/theorems/02715296-cb25-47ac-9a70-f52ce3f1f870
-- title:
--   Exists Is Bump
-- statement:
--   Definitions and structural lemmas for Exists Is Bump, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff InnerProductSpace
noncomputable section
namespace CompanionTheory.D.gk.Poul
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {hG : IsMatGroup G}
structure IsBump (G : Set (Mat n)) (φ : Mat n → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  nonneg : 0 ≤ φ
  one : φ 1 ≠ 0
  symm : ∀ x ∈ G, φ x⁻¹ = φ x
  supp : ∃ S : Set (Mat n), IsCompact S ∧ (∀ B ∈ S, B.det ≠ 0) ∧ ∀ y, φ y ≠ 0 → y ∈ S
section One
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat n → (H →L[ℂ] H)}
def avg (hG : IsMatGroup G) (φ : Mat n → ℝ) (σ : Mat n → (H →L[ℂ] H)) (v : H) : H :=
  ∫ g : MG G hG, φ g.mat • σ g.mat v ∂haar
structure IsSmForm (G : Set (Mat n)) (σ : Mat n → (H →L[ℂ] H)) {ι : Type} [Fintype ι] (W : ι → List (Mat n)) (C : ℝ)
    (l : H → ℂ) : Prop where
  add : ∀ x y, IsSm G σ x → IsSm G σ y → l (x + y) = l x + l y
  smul : ∀ (c : ℂ) x, IsSm G σ x → l (c • x) = c * l x
  bd : ∀ x, IsSm G σ x → ‖l x‖ ≤ C * ∑ i, ‖dsW σ (W i) x‖
variable {ι : Type} [Fintype ι] {W : ι → List (Mat n)} {C : ℝ} {l : H → ℂ}
end One
section Two
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {σ : Mat n → (H →L[ℂ] H)} {σ' : Mat n → (H' →L[ℂ] H')}
structure IsInv (G : Set (Mat n)) (σ : Mat n → (H →L[ℂ] H)) (σ' : Mat n → (H' →L[ℂ] H')) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (W : ι → List (Mat n)) (W' : ι' → List (Mat n)) (C : ℝ) (B : H → H' → ℂ) : Prop where
  add_left : ∀ x x' y, IsSm G σ x → IsSm G σ x' → IsSm G σ' y → B (x + x') y = B x y + B x' y
  smul_left : ∀ (a : ℂ) x y, IsSm G σ x → IsSm G σ' y → B (a • x) y = a * B x y
  add_right : ∀ x y y', IsSm G σ x → IsSm G σ' y → IsSm G σ' y' → B x (y + y') = B x y + B x y'
  smul_right : ∀ (a : ℂ) x y, IsSm G σ x → IsSm G σ' y → B x (a • y) = star a * B x y
  inv : ∀ g ∈ G, ∀ x y, IsSm G σ x → IsSm G σ' y → B (σ g x) (σ' g y) = B x y
  bd : ∀ x y, IsSm G σ x → IsSm G σ' y → ‖B x y‖ ≤ C * (∑ i, ‖dsW σ (W i) x‖) * ∑ j, ‖dsW σ' (W' j) y‖
variable {ι ι' : Type} [Fintype ι] [Fintype ι'] {W : ι → List (Mat n)} {W' : ι' → List (Mat n)} {C : ℝ}
  {B : H → H' → ℂ}
def homMG (hG : IsMatGroup G) (h : RepOn G σ) : MG G hG →* (H →L[ℂ] H) where
  toFun g := σ g.mat
  map_one' := h.map_one
  map_mul' a b := h.map_mul _ a.mem _ b.mem
end Two
end CompanionTheory.D.gk.Poul


