-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:31:55.925379+00:00
-- url     : https://prove2.me/theorems/2ea1c160-871d-411f-8789-20460973f917
-- title:
--   Letter Size
-- statement:
--   Definitions and structural lemmas for Letter Size, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/LetterSize.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost
def lsz {k r : ℕ} (X : B.Mat k r) : ℝ := max 1 (mx X)
def cj (k j ρ : ℕ) (x : RC k j ρ) (Y : B.Mat k ρ) : B.Mat k (j + ρ) :=
  (Rn k j ρ x)⁻¹ * blk3 0 0 0 0 Y 0 0 0 0 * Rn k j ρ x
def dmuP (k j ρ : ℕ) (Q : Matrix (Fin j) (Fin j) ℂ) : B.Mat k (j + ρ) :=
  blk3 Q 0 0 0 0 0 0 0 (-(G.wMat j * Qᴴ * G.wMat j))
def eMat {s : ℕ} (a b : Fin s) (ε : Bool) : Matrix (Fin s) (Fin s) ℂ :=
  Matrix.of fun i j => if i = a ∧ j = b then (if ε then 1 else Complex.I) else 0
def dirZ (k : ℕ) {p s : ℕ} (ρ : ℕ) {σ : Equiv.Perm (Fin p)} (ξ : Xi k p s ρ σ) (i : Fin s × Fin s × Bool) :
    B.Mat k (p + s + ρ) :=
  (Rn k (p + s) ρ ξ.1.2)⁻¹ *
    dmuP k (p + s) ρ ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ *
      blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (eMat i.1 i.2.1 i.2.2) * blk2 1 (Matrix.of ξ.2.1.2) 0 1) *
    Rn k (p + s) ρ ξ.1.2
def coefZ {s : ℕ} (Z W : G.Mat s) (i : Fin s × Fin s × Bool) : ℝ :=
  if i.2.2 then (((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1).re
  else (((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1).im
def WordsId : Prop :=
  SliceLeft → SliceRight →
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (ξ : Xi k p s ρ σ) (Z : G.Mat s)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k (p + s + ρ) → E) (u v : List (B.Mat k ρ)),
    B.dLR u v (fun γ' => F (gaXi k ρ σ d ξ Z γ')) =
      fun γ' => B.dLR (u.map (cj k (p + s) ρ ξ.1.1)) (v.map (cj k (p + s) ρ ξ.1.2)) F (gaXi k ρ σ d ξ Z γ')
def LetterSize : Prop :=
  ∀ k j ρ : ℕ, ∃ C : ℝ, ∀ (x : RC k j ρ) (Y : B.Mat k ρ), (∀ a b, ‖Y a b‖ ≤ 1) →
    lsz (cj k j ρ x Y) ≤ C * B.gN (Rn k j ρ x) ^ 2
def StarScale : Prop :=
  ∀ (k j ρ : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F₁ : B.Mat k (j + ρ) → E)
    (A₁ : ℝ) (Q : ℕ) (B₁ : ℝ) (K : Set ℝ), Star k j ρ F₁ A₁ Q B₁ K →
    ∀ u v : List (B.Mat k (j + ρ)), (∀ X ∈ u, inLieP k j ρ X) → (∀ X ∈ v, inLieP k j ρ X) →
      u.length + v.length ≤ Q → ∀ g ∈ B.GV k (j + ρ),
      B.gN g ^ A₁ * ‖B.dLR u v F₁ g‖ ≤ B₁ * ((u ++ v).map lsz).prod
def CommLR : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E) (m : ℕ),
    B.CkOn (m : ℕ∞) (B.GV k r) f →
    ∀ u v w : List (B.Mat k r), (∀ X ∈ u, B.inLie k r X) → (∀ X ∈ v, B.inLie k r X) → (∀ X ∈ w, B.inLie k r X) →
      u.length + v.length + w.length ≤ m → ∀ g ∈ B.GV k r, B.Rw w (B.dLR u v f) g = B.dLR u (w ++ v) f g
def ZSmooth : Prop :=
  SliceMem → RadicalParam →
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (H : B.Mat k (p + s + ρ) → E) (m : ℕ),
    B.CkOn (m : ℕ∞) (B.GV k (p + s + ρ)) H →
    ∀ (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ : B.Mat k ρ), G.detM Z ≠ 0 → γ ∈ B.GV k ρ →
      gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) ∧ ContinuousAt (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z ∧
      ContDiffAt ℝ m (fun Z' : G.Mat s => H (gaXi k ρ σ d ξ Z' γ)) Z
def OffK : Prop :=
  SliceMem → RadicalParam →
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (H : B.Mat k (p + s + ρ) → E)
      (O : Set (B.Mat k (p + s + ρ))), IsOpen O → (∀ g ∈ B.GV k (p + s + ρ), g ∈ O → H g = 0) →
    ∀ (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ : B.Mat k ρ), G.detM Z ≠ 0 → γ ∈ B.GV k ρ →
      gaXi k ρ σ d ξ Z γ ∈ O → ∀ q : ℕ,
      ContDiffAt ℝ q (fun Z' : G.Mat s => H (gaXi k ρ σ d ξ Z' γ)) Z ∧
      iteratedFDeriv ℝ q (fun Z' : G.Mat s => H (gaXi k ρ σ d ξ Z' γ)) Z = 0
def ZDeriv : Prop :=
  SliceMem → RadicalParam → SliceZ →
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (H : B.Mat k (p + s + ρ) → E),
    B.CkOn 1 (B.GV k (p + s + ρ)) H →
    ∀ (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ : B.Mat k ρ), G.detM Z ≠ 0 → γ ∈ B.GV k ρ →
      ∀ W : G.Mat s, fderiv ℝ (fun Z' : G.Mat s => H (gaXi k ρ σ d ξ Z' γ)) Z W =
        ∑ i : Fin s × Fin s × Bool, coefZ Z W i • RdV (dirZ k ρ ξ i) H (gaXi k ρ σ d ξ Z γ)
def DirSize : Prop :=
  DirectionsInP → ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)), ∃ C : ℝ,
    ∀ (ξ : Xi k p s ρ σ) (i : Fin s × Fin s × Bool),
      inLieP k (p + s) ρ (dirZ k ρ ξ i) ∧
      lsz (dirZ k ρ ξ i) ≤ C * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2
def ZCost : Prop :=
  SliceMem → RadicalParam → SliceZ → DirectionsInP → SliceCoordinateSizes →
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) → 1 ≤ s →
    ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 → ∀ q : ℕ, ∃ C : ℝ,
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (H : B.Mat k (p + s + ρ) → E) (β : ℝ),
      B.CkOn (q : ℕ∞) (B.GV k (p + s + ρ)) H →
      ∀ (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ : B.Mat k ρ), G.detM Z ≠ 0 → γ ∈ B.GV k ρ →
      ‖DjU k (p + s) ρ (gaXi k ρ σ d ξ Z γ)‖ ∈ K →
      (∀ w : List (B.Mat k (p + s + ρ)), (∀ X ∈ w, inLieP k (p + s) ρ X) → w.length ≤ q →
        ‖B.Rw w H (gaXi k ρ σ d ξ Z γ)‖ ≤ β * (w.map lsz).prod) →
      ContDiffAt ℝ q (fun Z' : G.Mat s => H (gaXi k ρ σ d ξ Z' γ)) Z ∧
      ‖iteratedFDeriv ℝ q (fun Z' : G.Mat s => H (gaXi k ρ σ d ξ Z' γ)) Z‖ ≤
        C * β * B.gN (gaXi k ρ σ d ξ Z γ) ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ))
end PI.UnitaryGroupMassFormula.UsCost


