-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:06.324114+00:00
-- url     : https://prove2.me/theorems/85a6d878-8ee2-4b02-9dba-f0bcc3fa60ba
-- title:
--   Cay Div Of
-- statement:
--   Definitions and structural lemmas for Cay Div Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivOf.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
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
namespace PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
def SPrime : Prop :=
  ∀ (n m : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → m < n → ∀ (t : ℝ), t ≠ 0 → ∀ β : E n, (herm β).det ≠ 0 →
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧
      (∃ σ₀ : ℝ, ∀ z : ℂ, σ₀ < z.re → Integrable (fun y => cls s z m 0 1 y * chr t β y) ∧
        W z = ∫ y, cls s z m 0 1 y * chr t β y) ∧
      ∀ j < n - m, iteratedDeriv j W 0 = 0
abbrev Fm (n : ℕ) := MvPolynomial (Bool × Fin n × Fin n) (Polynomial ℂ)
def yv (b : Bool) (i j : Fin n) : Fm n := MvPolynomial.X (b, i, j)
def opH (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : Fm n →ₗ[ℂ] Fm n :=
  let c : ℂ := if b then Complex.I * s else -(Complex.I * s)
  let α : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X
  (-(c : ℂ)) • (LinearMap.mulLeft ℂ (MvPolynomial.C α * yv b l k)).restrictScalars ℂ +
    ∑ a : Fin n, ∑ d : Fin n, (-(c : ℂ)) •
      (LinearMap.mulLeft ℂ (yv b a k * yv b l d) ∘ₗ (MvPolynomial.pderiv (b, a, d)).toLinearMap.restrictScalars ℂ)
def opD (s : ℂ) (m : ℕ) (k l : Fin n) : Fm n →ₗ[ℂ] Fm n := opH s m false k l + opH s m true k l
def cayF (s : ℂ) (m : ℕ) : Fm n →ₗ[ℂ] Fm n :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange n).foldr (fun k g => opD s m k (σ k) ∘ₗ g) LinearMap.id
def DivZ (i : ℕ) (Q : Fm n) : Prop := ∀ e, Polynomial.X ^ i ∣ MvPolynomial.coeff e Q
def Comm : Prop :=
  ∀ (n : ℕ) (s : ℂ) (m : ℕ) (b b' : Bool) (k l k' l' : Fin n),
    opH s m b k l ∘ₗ opH s m b' k' l' = opH s m b' k' l' ∘ₗ opH s m b k l
def Bridge : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (m N : ℕ) (z : ℂ) (B : MC n), B ∈ OmS s →
    (cay^[N] (clsC s z m 0 1)) B = clsC s z m 0 1 B *
      MvPolynomial.eval (fun k : Bool × Fin n × Fin n => if k.1 then (1 + (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2
        else (1 - (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2) (MvPolynomial.map (Polynomial.evalRingHom z) ((cayF s m)^[N] 1))
def minorOp (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) : Fm n →ₗ[ℂ] Fm n :=
  ∑ σ : Equiv.Perm (Fin ρ), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange ρ).foldr (fun k g => opH s m b (I k) (J (σ k)) ∘ₗ g) LinearMap.id
def MinorZ : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (m i N : ℕ), i ≤ N → ∀ (I J : Fin (m + i) ↪ Fin n),
    DivZ i ((minorOp s m false I J)^[N] 1)
def MinorZ' : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (m j N : ℕ), j ≤ N → ∀ (I J : Fin j ↪ Fin n),
    DivZ j ((minorOp s m true I J)^[N] 1)
abbrev PAB (n : ℕ) := MvPolynomial (Bool × Fin n × Fin n) ℂ
def minorPolynomial (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) : PAB n :=
  Matrix.det (fun p q : Fin ρ => (MvPolynomial.X (b, I p, J q) : PAB n))
def Null : Prop :=
  ∀ (n m : ℕ), m < n → ∀ N₀ : ℕ, ∃ N : ℕ,
    (Matrix.det (fun p q : Fin n => (MvPolynomial.X (false, p, q) + MvPolynomial.X (true, p, q) : PAB n))) ^ N ∈
      Ideal.span {x : PAB n | ∃ i j : ℕ, i + j = n - m ∧
        ((i = 0 ∧ j = 0 ∧ x = 1) ∨
         (i = 0 ∧ 0 < j ∧ ∃ (I J : Fin j ↪ Fin n), x = minorPolynomial true I J ^ N₀) ∨
         (0 < i ∧ j = 0 ∧ ∃ (I J : Fin (m + i) ↪ Fin n), x = minorPolynomial false I J ^ N₀) ∨
         (0 < i ∧ 0 < j ∧ ∃ (I J : Fin (m + i) ↪ Fin n) (I' J' : Fin j ↪ Fin n),
            x = minorPolynomial false I J ^ N₀ * minorPolynomial true I' J' ^ N₀))}
def CayDiv : Prop :=
  ∀ (n m : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → m < n → ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → DivZ (n - m) ((cayF s m)^[N] (1 : Fm n))
def MinorFormula : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (m : ℕ) (b : Bool) (ρ N : ℕ) (I J : Fin ρ ↪ Fin n),
    (minorOp s m b I J)^[N] 1 =
      MvPolynomial.C (Polynomial.C (((if b then Complex.I * s else -(Complex.I * s)) ^ ρ) ^ N) *
        ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ,
          (-(if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X) - Polynomial.C ((l : ℂ) - i))) *
      (Matrix.det (fun p q : Fin ρ => yv b (J p) (I q))) ^ N
def CayDivOf : Prop := Comm → MinorZ → MinorZ' → Null → CayDiv
def SPrimeOf : Prop := Bridge → CayDiv → SPrime
end PositivityTheory.Rg.Sw.SP


