-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_UnitaryHaarVolume
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_UnitaryHaarVolume
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:57.908125+00:00
-- url     : https://prove2.me/theorems/a0d360cb-ff6a-4c4b-a7ef-4e9cd1be5f99
-- title:
--   Unitary Haar Volume
-- statement:
--   Definitions and structural lemmas for Unitary Haar Volume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/UnitaryHaarVolume.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open Formalism.L2.Pj Formalism.L2.PjFree NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open scoped ENNReal
def sgnMat (r p0 : ℕ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)
def Upq (r p0 : ℕ) : Subgroup (GL (Fin r) ℂ) where
  carrier := {g | (g : Matrix (Fin r) (Fin r) ℂ).transpose * sgnMat r p0 *
    (g : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = sgnMat r p0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.transpose_mul, Matrix.map_mul] at *
    calc _ = (b : Matrix (Fin r) (Fin r) ℂ).transpose * ((a : Matrix (Fin r) (Fin r) ℂ).transpose * sgnMat r p0 *
        (a : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ)) * (b : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : ((a⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).transpose * (a : Matrix (Fin r) (Fin r) ℂ).transpose = 1 := by
      rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
    have h2 : (a : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) *
        ((a⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      simp
    calc _ = ((a⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).transpose *
        ((a : Matrix (Fin r) (Fin r) ℂ).transpose * sgnMat r p0 * (a : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ)) *
        ((a⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) := by rw [ha]
      _ = (((a⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).transpose * (a : Matrix (Fin r) (Fin r) ℂ).transpose) *
        sgnMat r p0 * ((a : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) *
        ((a⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
set_option autoImplicit false in
open NumberField MeasureTheory in
open scoped ENNReal in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.isClosed_Upq (r p0 : ℕ) :
    IsClosed (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r p0 : Set (GL (Fin r) ℂ)) := by
  show IsClosed {g : GL (Fin r) ℂ | (g : Matrix (Fin r) (Fin r) ℂ).transpose *
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.sgnMat r p0 * (g : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.sgnMat r p0}
  have hv : Continuous fun g : GL (Fin r) ℂ => (g : Matrix (Fin r) (Fin r) ℂ) :=
    Units.continuous_val
  exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul
    (hv.matrix_map Complex.continuous_conj)) continuous_const
instance locallyCompact_Upq (r p0 : ℕ) : LocallyCompactSpace (Upq r p0) := by
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) ℂ) := inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) ℂ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin r) ℂ) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact (isClosed_Upq r p0).locallyCompactSpace
instance measurable_Upq (r p0 : ℕ) : MeasurableSpace (Upq r p0) := borel _
instance borel_Upq (r p0 : ℕ) : BorelSpace (Upq r p0) := ⟨rfl⟩
def haarU (r p0 : ℕ) : Measure (Upq r p0) := Measure.haar
section Comp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
abbrev RealGrp : Type := X.Ψ → Upq r X.p0
def haarR : Measure (RealGrp X) := Measure.pi fun _ => haarU r X.p0
def OrthFr : Set (Frame X.Ψ r) := {x | ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnMat r X.p0}
def baseFr : Frame X.Ψ r := fun τ => ((X.signature τ).choose : Matrix (Fin r) (Fin r) ℂ)
def frameOf (g : RealGrp X) : Frame X.Ψ r :=
  rmul (baseFr X) fun τ => (((g τ : Upq r X.p0) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
def InjMod (D : Set (RealGrp X)) : Prop :=
  ∀ γ ∈ X.Γ, ∀ g ∈ D, ∀ g' ∈ D, lact γ (frameOf X g) = frameOf X g' → γ = 1
def quotInt (F : Frame X.Ψ r → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (D : Set (RealGrp X)) (_ : MeasurableSet D) (_ : InjMod X D), ∫⁻ g in D, F (frameOf X g) ∂(haarR X)
end Comp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
section OneEmb
variable {σ : c.F →+* ℂ} (V : Unf Xo c σ r)
def totVol : ℝ≥0∞ := ∑ k, quotInt (V.X k) fun _ => 1
def totInt (F : ∀ k, Frame (V.X k).Ψ r → ℝ≥0∞) : ℝ≥0∞ := ∑ k, quotInt (V.X k) (F k)
def FinVol : Prop := totVol V ≠ 0 ∧ totVol V ≠ ⊤
def piFac (a : (E →+* ℂ) × ℕ → ℕ) (k : V.Comp) : ℝ :=
  ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), (2 * Real.pi * ‖relab c σ τ (V.X k).ξ0‖) ^ (-(a (τ, i) : ℝ) / 2)
def ptNorm (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (k : V.Comp) (x : Frame (V.X k).Ψ r) : ℝ :=
  piFac V a k * (V.X k).pnorm (laU V a n k) (rdU V f k) x
def sqInt (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ≥0∞ :=
  totInt V fun k x => ENNReal.ofReal (ptNorm V a n f k x ^ 2)
def petNorm (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ :=
  Real.sqrt ((sqInt V a n f).toReal / (totVol V).toReal)
def adelFn {Q : Type} (pt : Q → Σ k, Frame (V.X k).Ψ r) (mu : Q → ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (f : Rul Xo c) :
    Q → ℂ :=
  fun q => mu q * (piFac V a (pt q).1 : ℂ) * rdU V f (pt q).1 (pt q).2
def IsQuotModel {Q : Type} [MeasurableSpace Q] (ν : Measure Q) (pt : Q → Σ k, Frame (V.X k).Ψ r) (mu : Q → ℂ) : Prop :=
  IsProbabilityMeasure ν ∧ (∀ q, ‖mu q‖ = 1) ∧
    (∀ q, (pt q).2 ∈ (V.X (pt q).1).dom ∧ ∀ τ i, ‖dmin (V.X (pt q).1).Gm (pt q).2 τ i‖ = 1) ∧
    ∀ F : ∀ k, Frame (V.X k).Ψ r → ℝ≥0∞, (∀ k, Measurable (F k)) →
      (∀ k, ∀ γ ∈ (V.X k).Γ, ∀ x ∈ (V.X k).dom, F k (lact γ x) = F k x) →
      (∀ k, ∀ b ∈ Bor (V.X k).Ψ r, ∀ x ∈ (V.X k).dom, F k (rmul x b) = F k x) →
      (∫⁻ q, F (pt q).1 (pt q).2 ∂ν) * totVol V = totInt V F
end OneEmb
variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
def petAt (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ :=
  petNorm (U (goodOf c σ)) a n f
def FinVolAll : Prop := ∀ σ, GoodEmb c σ → FinVol (U σ)
def SqIntegrable : Prop :=
  ∀ a n, Dom a n → ∀ σ, GoodEmb c σ → ∀ f ∈ cusp Xo c U a n, sqInt (U σ) a n f ≠ ⊤
def Definite : Prop :=
  ∀ a n, Dom a n → ∀ σ, ∀ f ∈ cusp Xo c U a n, petAt U σ a n f = 0 → f = 0
def IsNorm : Prop :=
  ∀ a n, Dom a n → ∀ σ, IsNormOn (cusp Xo c U a n) σ (petAt U σ a n)
def LeSup : Prop :=
  ∀ x : ℝ, ∀ σ, (∀ k, ∀ τ : E →+* ℂ, ‖τ ((U (goodOf c σ)).X k).ξ0‖ = x) → ∀ a n, Dom a n →
    ∀ f ∈ cusp Xo c U a n, petAt U σ a n f ≤ supC Xo c U x (goodOf c σ) a n f
def AdelicForm : Prop :=
  ∀ a n, Dom a n → ∀ σ, GoodEmb c σ → ∀ (Q : Type) [MeasurableSpace Q] (ν : Measure Q)
    (pt : Q → Σ k, Frame ((U σ).X k).Ψ r) (mu : Q → ℂ), IsQuotModel (U σ) ν pt mu → ∀ f ∈ cusp Xo c U a n,
      eLpNorm (adelFn (U σ) pt mu a f) 2 ν ≠ ⊤ ∧
        (eLpNorm (adelFn (U σ) pt mu a f) 2 ν).toReal = petNorm (U σ) a n f
def PeterssonLaws : Prop :=
  (∀ σ, GoodEmb c σ → IsUnf (U σ)) → FinVolAll U →
    SqIntegrable U ∧ Definite U ∧ IsNorm U ∧ LeSup U ∧ AdelicForm U
example (σ σ' : c.F →+* ℂ) (h : goodOf c σ = goodOf c σ') : petAt U σ = petAt U σ' := by
  funext a n f
  unfold petAt
  rw [h]
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume


