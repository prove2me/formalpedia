-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_DiscreteSeriesTopClasses_IsInvOne
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_DiscreteSeriesTopClasses_IsInvOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:55.326789+00:00
-- url     : https://prove2.me/theorems/9c488e21-5b5c-4d0f-824c-bb5902450d8b
-- title:
--   Is Inv One
-- statement:
--   Definitions and structural lemmas for Is Inv One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/DiscreteSeriesTopClasses/IsInvOne.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_DiscreteSeriesTopClasses_IsMQEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open scoped ContDiff
namespace PositivityTheory.RgTw
variable {n : ℕ}
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev G (n : ℕ) := Matrix.GeneralLinearGroup (Fin n) ℂ
abbrev Poly (n : ℕ) := MvPolynomial (Fin 4 × Fin n × Fin n) ℂ
def Xm (j : Fin 4) : Matrix (Fin n) (Fin n) (Poly n) := fun a b => X (j, a, b)
def ev (d : Mat n) : Poly n →+* ℂ := MvPolynomial.eval fun x => ![d, dᴴ, d⁻¹, dᴴ⁻¹] x.1 x.2.1 x.2.2
def dZ (Z : Mat n) : Derivation ℂ (Poly n) (Poly n) :=
  MvPolynomial.mkDerivation ℂ fun x =>
    (if (x.1 : ℕ) < 2 then -1 else 1 : Poly n) * (Z.map C * Xm x.1 + Xm x.1 * Z.map C : Matrix (Fin n) (Fin n) (Poly n)) x.2.1 x.2.2
def sigP (n : ℕ) : Matrix (Fin n) (Fin n) (Poly n) := Xm 0 * Xm 1 - Xm 3 * Xm 2
def hb (p : Fin n × Fin n) : Mat n :=
  if p.1 = p.2 then Matrix.single p.1 p.1 1
  else if p.1 < p.2 then ((Real.sqrt 2)⁻¹ : ℂ) • (Matrix.single p.1 p.2 1 + Matrix.single p.2 p.1 1)
  else (((Real.sqrt 2)⁻¹ : ℂ) * Complex.I) • (Matrix.single p.1 p.2 1 - Matrix.single p.2 p.1 1)
def sP (p : Fin n × Fin n) : Poly n := Matrix.trace (sigP n * (hb p).map C)
def uM (d : Mat n) : ℝ := (∑ p, (ev d (sP p)).re ^ 2) / 2
def th (g : G n) : G n := (star g)⁻¹
def tw (x d : G n) : G n := x⁻¹ * d * th x
def twCent (d : G n) : Subgroup (G n) where
  carrier := {x | d * th x = x * d}
  one_mem' := by simp [th]
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, th, star_mul, _root_.mul_inv_rev] at *
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq, th, star_inv, inv_inv] at *
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hx, inv_mul_cancel_right]
def IsInv (τ : Poly n) : Prop :=
  (∀ p, dZ (hb p) τ = 0) ∧ ∀ (x d : G n), ev (tw x d : G n).val τ = ev d.val τ
def IsCutFn (H : ℝ → ℝ) : Prop := ContDiff ℝ ∞ H ∧ ∃ R : ℝ, ∀ x, R ≤ x → H x = 0
def bas (H : ℝ → ℝ) (P : Poly n) (d : G n) : ℂ := (H (uM d.val) : ℂ) * ev d.val P
def adBas (p : Fin n × Fin n) (H : ℝ → ℝ) (P : Poly n) (d : G n) : ℂ :=
  bas (deriv H) ((∑ q, sP q * dZ (hb p) (sP q)) * P) d + bas H (dZ (hb p) P) d
def Shape (n m : ℕ) : Submodule ℂ (G n → ℂ) :=
  Submodule.span ℂ {φ | ∃ H P, IsCutFn H ∧ P.totalDegree ≤ m ∧ φ = bas H P}
def AdSpan (n : ℕ) : Submodule ℂ (G n → ℂ) := Submodule.span ℂ {φ | ∃ p H P, IsCutFn H ∧ φ = adBas p H P}
def fam (F : ℝ → ℝ) (τ : Poly n) (P : ℕ → Poly n) (t : ℝ) (d : G n) : ℂ :=
  ∑ k ∈ Finset.range (n * n + 1), ((t ^ (2 * (k : ℤ) - (n * n : ℕ)) : ℝ) : ℂ) *
    bas (fun x => iteratedDeriv k F (t ^ 2 * x)) (τ * P k) d
def topP (n : ℕ) : Poly n := (Matrix.of fun p q : Fin n × Fin n => dZ (hb p) (sP q)).det
def StInst : Prop :=
  ∀ n : ℕ, ∃ r : Fin n × Fin n → Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ,
    (∀ i j, (r i j)ᵀ = -r i j) ∧ (∀ i j, r j i = -r i j) ∧
    ∀ i j a, dZ (hb i) (dZ (hb j) (sP a)) - dZ (hb j) (dZ (hb i) (sP a)) = ∑ b, r i j a b • sP b
def StTopVal : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), (∀ a, ‖z a‖ = 1) →
    ev (diagonal z) (topP n) = (-4) ^ (n * n) * ∏ a, ∏ b, (1 + z a / z b)
def StHomot : Prop :=
  ∀ (n : ℕ) (F : ℝ → ℝ) (τ : Poly n) (P : ℕ → Poly n) (Q : Fin n × Fin n → ℕ → Poly n), IsCutFn F → IsInv τ →
    IsMQ (fun p => dZ (hb p)) sP P Q → ∀ t₁ t₂ : ℝ, 0 < t₁ → 0 < t₂ → fam F τ P t₁ - fam F τ P t₂ ∈ AdSpan n
end PositivityTheory.RgTw


