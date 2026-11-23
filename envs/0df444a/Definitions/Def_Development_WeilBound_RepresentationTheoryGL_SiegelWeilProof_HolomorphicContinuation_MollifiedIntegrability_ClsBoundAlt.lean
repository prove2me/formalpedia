-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:46.407663+00:00
-- url     : https://prove2.me/theorems/1dde492b-b90c-44e6-a92b-7a5e59c18434
-- title:
--   Cls Bound Alt
-- statement:
--   Definitions and structural lemmas for Cls Bound Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundAlt.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
namespace PositivityTheory.Rg.Sw.WR
open PositivityTheory.Rg.Sw
variable {n : ℕ}
abbrev E (n : ℕ) := Fin n → Fin n → ℝ
def uM (s : ℂ) (y : E n) : Matrix (Fin n) (Fin n) ℂ := (1 - (Complex.I * s) • herm y)⁻¹
def vM (s : ℂ) (y : E n) : Matrix (Fin n) (Fin n) ℂ := (1 + (Complex.I * s) • herm y)⁻¹
def dP (y : E n) : ℝ := (1 + herm y * herm y).det.re
def evUV (s : ℂ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) : ℂ :=
  MvPolynomial.eval (fun k => if k.1 then vM s y k.2.1 k.2.2 else uM s y k.2.1 k.2.2) R
def cls (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) : ℂ :=
  ((dP y : ℝ) : ℂ) ^ (-z) * (uM s y).det ^ p * (vM s y).det ^ q * evUV s R y
def vkl (k l : Fin n) : Fin n → Fin n → ℂ := fun a b =>
  (if a = k ∧ b = l then (1 + Complex.I) / 2 else 0) + (if a = l ∧ b = k then (1 - Complex.I) / 2 else 0)
def dirC (f : E n → ℂ) (w : Fin n → Fin n → ℂ) (y : E n) : ℂ :=
  fderiv ℝ f y (fun a b => (w a b).re) + Complex.I * fderiv ℝ f y (fun a b => (w a b).im)
def Dkl (k l : Fin n) (f : E n → ℂ) : E n → ℂ := dirC f (vkl k l)
def Delta (f : E n → ℂ) : E n → ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange n).foldr (fun k g => Dkl k (σ k) g) f
def chr (t : ℝ) (β : E n) (y : E n) : ℂ := Complex.exp (-(Complex.I * t * ∑ a, ∑ b, β a b * y a b))
def Gauss : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → (t = c ∨ t = -c) → ∀ P : PX m n,
    ∃ R : MvPolynomial (Bool × Fin n × Fin n) ℂ, ∀ y : E n,
      secN ε c t P (herm y) = cls ((t / c : ℝ) : ℂ) 0 (Finset.univ.filter fun a => ε a = true).card
        (Finset.univ.filter fun a => ε a = false).card R y
def ClsBound : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (z : ℂ),
    ContDiff ℝ (⊤ : ℕ∞) (cls s z p q R) ∧ ∀ L : List (Fin n × Fin n), ∃ C : ℝ, ∀ y,
      ‖L.foldr (fun kl g => Dkl kl.1 kl.2 g) (cls s z p q R) y‖ ≤ C * (dP y) ^ (-(z.re + (p + q : ℝ) / 2))
def ClsGain : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (p q N : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
    ∃ (J : ℕ) (a : Fin J → Polynomial ℂ) (G : Fin J → E n → ℂ), (∀ j, Continuous (G j)) ∧
      (∃ C : ℝ, ∀ j y, ‖G j y‖ ≤ C * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2)) ∧
      ∀ z y, (Delta^[N] (cls s z p q R)) y = ((dP y : ℝ) : ℂ) ^ (-z) * ∑ j, (a j).eval z * G j y
def IBP : Prop :=
  ∀ (n : ℕ) (f : E n → ℂ) (t : ℝ) (β : E n), ContDiff ℝ (⊤ : ℕ∞) f → t ≠ 0 → (herm β).det ≠ 0 →
    (∀ L : List (Fin n × Fin n), ∃ h : E n → ℝ, Integrable h ∧ ∀ y, ‖L.foldr (fun kl g => Dkl kl.1 kl.2 g) f y‖ ≤ h y) →
    ∫ y, f y * chr t β y = (-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹ * ∫ y, Delta f y * chr t β y
def Integr : Prop :=
  ∀ (n : ℕ), (∃ c : ℝ, 0 < c ∧ ∀ y : E n, c * (1 + ∑ a, ∑ b, y a b ^ 2) ≤ dP y) ∧
    ∀ σ : ℝ, (n : ℝ) ^ 2 / 2 < σ → Integrable fun y : E n => (dP y) ^ (-σ)
def Dens : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → (t = c ∨ t = -c) → ∀ (P : PX m n) (N : ℕ),
    (n : ℝ) ^ 2 < (m + N : ℕ) →
    ∃ g : E n → ℂ, ContinuousOn g {y | (herm y).det ≠ 0} ∧
      (∀ S : Set (E n), IsCompact S → S ⊆ {y | (herm y).det ≠ 0} →
        ∫ x in gramX ε ⁻¹' (herm '' S), evX P x * gs c x = ∫ y in S, g y) ∧
      ∀ β : E n, (herm β).det ≠ 0 →
        ((2 * Real.pi / |t|) ^ (n ^ 2) : ℝ) * g β =
          ((herm β).det ^ N)⁻¹ * ((-1) ^ n / ((-(Complex.I * t)) ^ n)) ^ N *
            ∫ y, (Delta^[N] (fun y => secN ε c t P (herm y))) y * chr t β y
def WRSt : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → (t = c ∨ t = -c) → ∀ P : PX m n,
    ∃ g : E n → ℂ, ContinuousOn g {y | (herm y).det ≠ 0} ∧
      (∀ S : Set (E n), IsCompact S → S ⊆ {y | (herm y).det ≠ 0} →
        ∫ x in gramX ε ⁻¹' (herm '' S), evX P x * gs c x = ∫ y in S, g y) ∧
      ∀ β : E n, (herm β).det ≠ 0 → ∃ W : ℂ → ℂ, Differentiable ℂ W ∧
        (∃ σ₀ : ℝ, ∀ z : ℂ, σ₀ < z.re →
          Integrable (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) ∧
          W z = ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) ∧
        W 0 = ((2 * Real.pi / |t|) ^ (n ^ 2) : ℝ) * g β
end PositivityTheory.Rg.Sw.WR


