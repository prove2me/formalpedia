-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:34.819725+00:00
-- url     : https://prove2.me/theorems/22c3c0de-1d9b-512c-b645-d3d95ad543a7
-- title:
--   Is Frame Over Line
-- statement:
--   Definitions and structural lemmas for Is Frame Over Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/IsFrameOverLine.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_Example
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isUnitOn_one_762773d2e406

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
section Frames
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}
def headIdx {j N : ℕ} (h : j ≤ N) (a : Fin j) : Fin N := Fin.castLE h a
def tailIdx {j N : ℕ} (h : j ≤ N) (a : Fin (N - j)) : Fin N := ⟨j + a, by have := a.isLt; omega⟩
def IsAdaptedFrame (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (segreCoord y) N E) (F : Submodule Ω E)
    {j : ℕ} (hj : j ≤ N) (c : (k : K) → ι k) (f : Ω) (b : Fin N → E) : Prop :=
  IsFrameOver y W c f b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
    Submodule.span Ω (Set.range (b ∘ headIdx hj)) = F
def quotWedge (F : Submodule Ω E) {j : ℕ} (hj : j ≤ N) (b : Fin N → E) : ⋀[Ω]^(N - j) (E ⧸ F) :=
  exteriorPower.ιMulti Ω (N - j) fun a => F.mkQ (b (tailIdx hj a))
variable {y : (Σ k, ι k) → Ω} {W : ChartBundle ℤ (segreCoord y) N E} {Xo : Set ((Σ k, ι k) → ℂ)}
  {P : Ideal (MRing ι)} {n nc : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)} {χ : Fin nc → SncChart P n Bd}
open Classical in

def gramAt (hm : HermMetric y W Xo χ) (b : Fin N → E) (z : (Σ k, ι k) → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  if hl : ∃ l, InFrameDomain y (hm.chart l) (hm.fr l) z then
    if hS : ∃ S : Matrix (Fin N) (Fin N) Ω, ∀ q, b q = ∑ p, S p q • hm.b hl.choose p then
      (Matrix.of fun p q => valAt y (hS.choose p q) z)ᴴ * hm.gram hl.choose z *
        Matrix.of fun p q => valAt y (hS.choose p q) z
    else 0
  else 0
def quotNormSq {j : ℕ} (hj : j ≤ N) (G : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  G.det.re / (G.submatrix (headIdx hj) (headIdx hj)).det.re
end Frames
section Main
theorem ComponentData.j_le_N {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω]
    [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    (D : ComponentData II Ψ K ι Ω E) : D.j ≤ D.N :=
  D.j_le.trans (Nat.sub_le _ _)
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
structure HodgeData (D : ComponentData II Ψ K ι Ω E) where

  F : ∀ τ, Submodule Ω (E τ)

  aMu : K → ℤ

  Λ : PiTensorProduct Ω fun τ => ⋀[Ω]^(D.N - D.j) (E τ ⧸ F τ)

  locally : ∀ c : (k : K) → ι k, segreCoord D.y c ≠ 0 →
    ∃ (m : ℕ) (f cc : Fin m → Ω), (∀ l, f l ∈ chartRing ℤ (segreCoord D.y) c) ∧
      (∀ l, cc l ∈ chartRing ℤ (segreCoord D.y) c) ∧ ∑ l, cc l * f l = 1 ∧
      ∀ l, ∃ b : ∀ τ, Fin D.N → E τ,
        (∀ τ, IsAdaptedFrame D.y (D.W τ) (F τ) D.j_le_N c (f l) (b τ)) ∧
        ∃ u : Ω, IsUnitOn D.y c (f l) u ∧
          Λ = (u * chartMono D.y c aMu) • PiTensorProduct.tprod Ω fun τ => quotWedge (F τ) D.j_le_N (b τ)
variable {D : ComponentData II Ψ K ι Ω E}
structure MuFrameAt (H : HodgeData D) (z : (Σ k, ι k) → ℂ) where
  c : (k : K) → ι k
  f : Ω
  inDom : InFrameDomain D.y c f z
  b : ∀ τ, Fin D.N → E τ
  adapted : ∀ τ, IsAdaptedFrame D.y (D.W τ) (H.F τ) D.j_le_N c f (b τ)
  u : Ω
  unit : IsUnitOn D.y c f u
  eq : H.Λ = (u * chartMono D.y c H.aMu) • PiTensorProduct.tprod Ω fun τ => quotWedge (H.F τ) D.j_le_N (b τ)
def MuFrameAt.norm {H : HodgeData D} {z : (Σ k, ι k) → ℂ} (d : MuFrameAt H z) : ℝ :=
  ‖valAt D.y d.u z‖ * (∏ k, ‖z ⟨k, d.c k⟩‖ ^ H.aMu k) *
    ∏ τ, Real.sqrt (quotNormSq D.j_le_N (gramAt (D.h τ) (d.b τ) z))
open Classical in

def muMetric (H : HodgeData D) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if h : Nonempty (MuFrameAt H z) then h.some.norm else 0
def muLine (H : HodgeData D) : HermLine ι := hermOfFun ι H.aMu (muMetric H)
def phMu (H : HodgeData D) (z : (Σ k, ι k) → ℂ) : ℝ := Real.log ((muLine H).h z)
end Main
namespace Line
def lineF : Submodule Line.Ω (Fin 2 → Line.Ω) := Submodule.span Line.Ω {Pi.single 0 1}
theorem isFrameOver_line (l : Fin 2) :
    IsFrameOver yLine (trivialBundle (segreCoord yLine) 2) (fun _ : Unit => l) 1 ⇑(Pi.basisFun Line.Ω (Fin 2)) :=
  ⟨segreCoord_line_ne_zero l, one_mem _, one_ne_zero,
    (Pi.basisFun Line.Ω (Fin 2)).linearIndependent, trivial_frame_iff _ 2 _⟩
def lineHodge (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2]) :
    HodgeData (lineData II hII) where
  F _ := lineF
  aMu := 0
  Λ := PiTensorProduct.tprod Line.Ω fun _ => quotWedge lineF (lineData II hII).j_le_N (Pi.basisFun Line.Ω (Fin 2))
  locally c _ := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
    refine ⟨fun _ => Pi.basisFun Line.Ω (Fin 2), fun _ => ⟨isFrameOver_line (c ()), (Pi.basisFun Line.Ω (Fin 2)).span_eq, ?_⟩,
      1, isUnitOn_one _ _ _, ?_⟩
    · show Submodule.span Line.Ω (Set.range (⇑(Pi.basisFun Line.Ω (Fin 2)) ∘
          headIdx (show 1 ≤ 2 by decide))) = lineF
      have : Set.range (⇑(Pi.basisFun Line.Ω (Fin 2)) ∘ headIdx (show 1 ≤ 2 by decide)) =
          {Pi.single 0 1} := by
        ext v
        simp only [Set.mem_range, Function.comp_apply, Set.mem_singleton_iff]
        constructor
        · rintro ⟨a, rfl⟩
          rw [Fin.fin_one_eq_zero a]
          simp [headIdx]
        · rintro rfl
          exact ⟨0, by simp [headIdx]⟩
      rw [this]
      rfl
    · simp [chartMono]
end Line
end GroundTheory.Heights₂.Heights.LowerBoundFree


