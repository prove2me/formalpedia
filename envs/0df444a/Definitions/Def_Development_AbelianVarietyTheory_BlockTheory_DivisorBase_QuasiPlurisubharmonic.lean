-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_QuasiPlurisubharmonic
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_QuasiPlurisubharmonic
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T23:38:09.988092+00:00
-- url     : https://prove2.me/theorems/91cad1e3-54fd-4901-9c08-e6b1a098c1ff
-- title:
--   Quasi Plurisubharmonic
-- statement:
--   Definitions and structural lemmas for Quasi Plurisubharmonic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/QuasiPlurisubharmonic.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero


set_option autoImplicit false
open Matrix Filter Topology
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.HermFrame
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic
def IsPshE {D : ℕ} (U : Set (Fin D → ℂ)) (v : (Fin D → ℂ) → EReal) : Prop :=
  (∀ z ∈ U, v z ≠ ⊤) ∧ UpperSemicontinuousOn v U ∧ U ⊆ closure {z ∈ U | v z ≠ ⊥} ∧
    ∀ κ : ℝ, ReciprocityTheory.AnForm.A.IsPsh U fun z => (max (v z) ((-κ : ℝ) : EReal)).toReal
section Manifold
variable {D : ℕ} {Y : Type} [TopologicalSpace Y]
def chartPart (A : FinHolAtlas D Y) (j : Fin A.n) (S : Set Y) : Set (Fin D → ℂ) :=
  (A.chart j).target ∩ (A.chart j).symm ⁻¹' S
def IsQuasiPsh (A : FinHolAtlas D Y) (Θ : LocPot Y) (v : Y → EReal) : Prop :=
  ∀ x j, IsPshE (chartPart A j (Θ.U x)) fun z =>
    ((2 * Θ.φ x ((A.chart j).symm z) : ℝ) : EReal) + v ((A.chart j).symm z)
def leviSum (A : FinHolAtlas D Y) (Θ : LocPot Y) (u : Y → ℝ) (x : Y) (j : Fin A.n)
    (z w : Fin D → ℂ) : ℝ :=
  levi (fun z' => 2 * Θ.φ x ((A.chart j).symm z') + u ((A.chart j).symm z')) z w
def SumNonnegOn (A : FinHolAtlas D Y) (Θ : LocPot Y) (u : Y → ℝ) (S : Set Y) : Prop :=
  ∀ x j, ∀ z ∈ chartPart A j (Θ.U x ∩ S), ∀ w, 0 ≤ leviSum A Θ u x j z w
def SumZeroOn (A : FinHolAtlas D Y) (Θ : LocPot Y) (u : Y → ℝ) (S : Set Y) : Prop :=
  ∀ x j, ∀ z ∈ chartPart A j (Θ.U x ∩ S), ∀ w, leviSum A Θ u x j z w = 0
def IsBoundary (A : FinHolAtlas D Y) (L : LocPot Y) (s : Y → Y → ℂ) {m : ℕ}
    (W : Fin m → Set Y) : Prop :=
  IsPotential A L ∧ IsSection A L s ∧ IsSNC A L s (fun _ => 1) W ∧
    ∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1
def opn (s : Y → Y → ℂ) : Set Y := {y | s y y ≠ 0}
def rad (L : LocPot Y) (s : Y → Y → ℂ) (y : Y) : ℝ := Real.exp 1 - 2 * logNormSec L s y
def limsupExt (S : Set Y) (u : Y → ℝ) (y : Y) : EReal :=
  limsup (fun y' => (u y' : EReal)) (𝓝[S] y)
def tnorm (A : FinHolAtlas D Y) (Ω : LocPot Y) (j : Fin A.n) (z ξ : Fin D → ℂ) : ℝ :=
  √(levi (Ω.φ ((A.chart j).symm z) ∘ (A.chart j).symm) z ξ / Real.pi)
def IsFlagBundle (A : FinHolAtlas D Y) {n : ℕ} (U : Y → Set Y)
    (g : Y → Y → Y → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ x, IsOpen (U x) ∧ x ∈ U x) ∧
  (∀ x x' a b, A.HoloOn (U x ∩ U x') fun y => g x x' y a b) ∧
  (∀ x x', ∀ y ∈ U x ∩ U x', ∀ a b, b < a → g x x' y a b = 0) ∧
  (∀ x, ∀ y ∈ U x, g x x y = 1) ∧
  ∀ x x' x'', ∀ y ∈ U x ∩ U x' ∩ U x'', g x x' y * g x' x'' y = g x x'' y
def IsMetricOn (A : FinHolAtlas D Y) (S : Set Y) {n : ℕ} (U : Y → Set Y)
    (g : Y → Y → Y → Matrix (Fin n) (Fin n) ℂ) (H : Y → Y → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ x j, IsPosFrame (chartPart A j (U x ∩ S)) fun z => H x ((A.chart j).symm z)) ∧
  ∀ x x', ∀ y ∈ U x ∩ U x' ∩ S, H x' y = (g x x' y)ᵀ * H x y * (g x x' y)ᴴᵀ
def IsLogPair (A : FinHolAtlas D Y) (Ω L : LocPot Y) (s : Y → Y → ℂ) (μ C : ℝ) {n : ℕ}
    (U : Y → Set Y) (g : Y → Y → Y → Matrix (Fin n) (Fin n) ℂ)
    (H₀ H : Y → Y → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsFlagBundle A U g ∧ IsMetricOn A Set.univ U g H₀ ∧ IsMetricOn A (opn s) U g H ∧
  (∀ x, ∀ y ∈ U x ∩ opn s, ∀ v,
    rad L s y ^ (-μ) * (form (H₀ x y) v v).re ≤ (form (H x y) v v).re ∧
      (form (H x y) v v).re ≤ rad L s y ^ μ * (form (H₀ x y) v v).re) ∧
  ∀ x j, ∀ z ∈ chartPart A j (U x ∩ opn s), ∀ ξ v,
    gnorm (H₀ x ((A.chart j).symm z))
        ((conn (fun z' => H x ((A.chart j).symm z')) z ξ -
          conn (fun z' => H₀ x ((A.chart j).symm z')) z ξ) *ᵥ v) ≤
      C * Real.exp (rad L s ((A.chart j).symm z) / 2) * tnorm A Ω j z ξ *
        gnorm (H₀ x ((A.chart j).symm z)) v
end Manifold
def stepLog {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) : ℝ :=
  Real.log (H.submatrix (Subtype.val : {a : Fin n // a.val < i} → Fin n) Subtype.val).det.re
def fundLog {j k : ℕ} (HW : Matrix (Fin j) (Fin j) ℂ) (Hω : Matrix (Fin k) (Fin k) ℂ) (i : ℕ) : ℝ :=
  if i ≤ j then stepLog HW i else stepLog HW j + stepLog Hω (i - j)
def coeff {N : ℕ} (lam : Fin N → ℝ) (i : Fin N) : ℝ :=
  if h : i.val + 1 < N then lam i - lam ⟨i.val + 1, h⟩ else lam i
def weightDiff {Y Ψ : Type} [Fintype Ψ] {N : ℕ} {j k : Ψ → ℕ}
    (HW₀ HW : ∀ τ, Y → Y → Matrix (Fin (j τ)) (Fin (j τ)) ℂ)
    (Hω₀ Hω : ∀ τ, Y → Y → Matrix (Fin (k τ)) (Fin (k τ)) ℂ)
    (lam : Ψ → Fin N → ℝ) (y : Y) : ℝ :=
  ∑ τ, ∑ i : Fin N, coeff (lam τ) i *
    (fundLog (HW τ y y) (Hω τ y y) (i.val + 1) - fundLog (HW₀ τ y y) (Hω₀ τ y y) (i.val + 1))
def Extension : Prop :=
  ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (A : FinHolAtlas D Y)
    (L : LocPot Y) (s : Y → Y → ℂ) (m : ℕ) (W : Fin m → Set Y), IsBoundary A L s W →
    ∀ (Θ : LocPot Y) (u : Y → ℝ) (C₁ : ℝ), IsPotential A Θ → A.SmoothOn (opn s) u →
      SumNonnegOn A Θ u (opn s) → (∀ y ∈ opn s, u y ≤ C₁ * Real.log (rad L s y)) →
      (∃ M : ℝ, ∀ y ∈ opn s, u y ≤ M) ∧ (∀ y ∈ opn s, limsupExt (opn s) u y = u y) ∧
        IsQuasiPsh A Θ (limsupExt (opn s) u)
def FlatExtension : Prop :=
  ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (A : FinHolAtlas D Y)
    (L : LocPot Y) (s : Y → Y → ℂ) (m : ℕ) (W : Fin m → Set Y), IsBoundary A L s W →
    ∀ (Θ : LocPot Y) (u : Y → ℝ) (C₁ : ℝ), IsPotential A Θ → A.SmoothOn (opn s) u →
      SumZeroOn A Θ u (opn s) → (∀ y ∈ opn s, |u y| ≤ C₁ * Real.log (rad L s y)) →
      ∃ u' : Y → ℝ, A.Smooth u' ∧ (∀ y ∈ opn s, u' y = u y) ∧ SumZeroOn A Θ u' Set.univ
def GradientBound : Prop :=
  ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (A : FinHolAtlas D Y)
    (L : LocPot Y) (s : Y → Y → ℂ) (m : ℕ) (W : Fin m → Set Y), IsBoundary A L s W →
    ∀ (Ω : LocPot Y), IsPotential A Ω → IsPosPot A Ω →
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (j k : Ψ → ℕ), (∀ τ, j τ + k τ = N) →
    ∀ (μ C₂ : ℝ) (UW Uω : Ψ → Y → Set Y)
      (gW : ∀ τ, Y → Y → Y → Matrix (Fin (j τ)) (Fin (j τ)) ℂ)
      (gω : ∀ τ, Y → Y → Y → Matrix (Fin (k τ)) (Fin (k τ)) ℂ)
      (HW₀ HW : ∀ τ, Y → Y → Matrix (Fin (j τ)) (Fin (j τ)) ℂ)
      (Hω₀ Hω : ∀ τ, Y → Y → Matrix (Fin (k τ)) (Fin (k τ)) ℂ),
      (∀ τ, IsLogPair A Ω L s μ C₂ (UW τ) (gW τ) (HW₀ τ) (HW τ)) →
      (∀ τ, IsLogPair A Ω L s μ C₂ (Uω τ) (gω τ) (Hω₀ τ) (Hω τ)) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : Ψ → Fin N → ℝ,
        A.SmoothOn (opn s) (weightDiff HW₀ HW Hω₀ Hω lam) ∧
        ∀ c, ∀ z ∈ chartPart A c (opn s), ∀ ξ : Fin D → ℂ,
          |fderiv ℝ (weightDiff HW₀ HW Hω₀ Hω lam ∘ (A.chart c).symm) z ξ| ≤
            C * (∑ τ, ∑ i, |lam τ i|) * rad L s ((A.chart c).symm z) ^ ((N : ℝ) * μ) *
              Real.exp (rad L s ((A.chart c).symm z) / 2) * tnorm A Ω c z ξ
def Statement : Prop := Extension ∧ FlatExtension ∧ GradientBound
example (lam : Fin 2 → ℝ) : coeff lam 0 + coeff lam 1 = lam 0 ∧ coeff lam 1 = lam 1 := by
  simp [coeff]
example {D : ℕ} : ¬ IsPshE (Set.univ : Set (Fin D → ℂ)) fun _ => ⊥ := fun h => by
  simpa using h.2.2.1 (Set.mem_univ 0)
end GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic


