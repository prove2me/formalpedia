-- Prove2me | Definitions.Def_MTT_Arithmetic
-- name    : MTT_Arithmetic
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-05T21:58:59.591522+00:00
-- url     : https://prove2.me/theorems/17c4c3ed-e06c-488a-aa8c-33deaf9fd03b
-- title:
--   MTT: cusp forms, modular integrals, periods, and complex critical values
-- statement:
--   Analytic cusp forms with explicit nebentypus and normalized Hecke eigenform conditions; actual modular integrals and inverse-character Mellin transforms; and signed algebraic period data with a finitely generated integral lattice. Existence of this period system is a separate theorem target. The signed projections include one half.
-- source:
--   Mazur–Tate–Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), https://doi.org/10.1007/BF01388731; Chapter I, §§1–4, 7–14.

import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace MTT

abbrev Qbar := AlgebraicClosure ℚ

abbrev GammaOne (N : ℕ) :=
  (CongruenceSubgroup.Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- The classical prime Hecke operator, including U_l when l divides the level. -/
def heckePrime (k : ℕ) (εl : ℂ) (l : ℕ) (f : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) : ℂ :=
  (l : ℂ)⁻¹ * ∑ b : Fin l, f (UpperHalfPlane.ofComplex ((z + (b.val : ℂ)) / l)) +
    εl * (l : ℂ) ^ (k - 1) * f (UpperHalfPlane.ofComplex ((l : ℂ) * z))

/-- Normalized algebraic cuspidal Hecke eigenforms, with the nebentypus law explicit. -/
structure Eigenform (N k : ℕ) (ι : Qbar →+* ℂ) where
  form : CuspForm (GammaOne N) (k : ℤ)
  epsilon : DirichletCharacter Qbar N
  coeff : ℕ → Qbar
  coeff_eq : ∀ n, (UpperHalfPlane.qExpansion 1 form).coeff n = ι (coeff n)
  normalized : coeff 1 = 1
  character_law : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
    form ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
      ι (epsilon (γ.val 1 1 : ZMod N)) *
        (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * form z
  eigen : ∀ l : ℕ, l.Prime → ∀ z : UpperHalfPlane,
    heckePrime k (ι (epsilon l)) l form z = ι (coeff l) * form z

/-- MTT I.(1.2), with the polynomial specified by its coefficients. -/
def modularIntegral (f : UpperHalfPlane → ℂ) (P : Polynomial ℂ) (r : ℚ) : ℂ :=
  (2 * Real.pi : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
    f (UpperHalfPlane.ofComplex ((r : ℂ) + Complex.I * t)) *
      P.eval ((r : ℂ) + Complex.I * t)

/-- MTT I.§3(i), for P(X)=X^j. -/
def modularSymbol (f : UpperHalfPlane → ℂ) (j : ℕ) (a m : ℚ) : ℂ :=
  modularIntegral f (((m : ℂ) • Polynomial.X + Polynomial.C (a : ℂ)) ^ j) (-a / m)

/-- Boolean true denotes the plus eigenspace, false the minus eigenspace. -/
def sign (s : Bool) : ℤ := if s then 1 else -1

/-- The involution sends (P,r) to (P(-X),-r); the projection contains 1/2. -/
def signedIntegral (f : UpperHalfPlane → ℂ) (s : Bool) (j : ℕ) (r : ℚ) : ℂ :=
  (modularIntegral f (Polynomial.X ^ j) r +
    (sign s : ℂ) * (-1 : ℂ) ^ j * modularIntegral f (Polynomial.X ^ j) (-r)) / 2

/-- A period system, including a finite integral lattice of normalized signed values. -/
structure Periods (k : ℕ) (ι : Qbar →+* ℂ) (f : UpperHalfPlane → ℂ) where
  omega : Bool → ℂ
  omega_ne : ∀ s, omega s ≠ 0
  value : Bool → ℕ → ℚ → Qbar
  comparison : ∀ s j r, j ≤ k - 2 →
    ι (value s j r) = signedIntegral f s j r / omega s
  lattice_fg : (Submodule.span ℤ {v : Qbar | ∃ s j r,
    j ≤ k - 2 ∧ v = value s j r}).FG

/-- Gauss sum with the positive complex exponential, including modulus one. -/
def gaussSum (ι : Qbar →+* ℂ) (m : ℕ) [NeZero m]
    (χ : DirichletCharacter Qbar m) : ℂ :=
  ∑ a : ZMod m, ι (χ a) * Complex.exp (2 * Real.pi * Complex.I * a.val / m)

/-- The inverse-character twist: Birch's finite-translate expression f_{χ^{-1}}. -/
def inverseTwist (ι : Qbar →+* ℂ) (f : UpperHalfPlane → ℂ)
    (m : ℕ) [NeZero m] (χ : DirichletCharacter Qbar m)
    (z : UpperHalfPlane) : ℂ :=
  (gaussSum ι m χ)⁻¹ * ∑ a : ZMod m,
    ι (χ a) * f (UpperHalfPlane.ofComplex (z + (a.val : ℂ) / m))

/-- The actual complex critical L-value L(f_{χ^{-1}},j+1), defined by its Mellin integral. -/
def criticalLValue (ι : Qbar →+* ℂ) (f : UpperHalfPlane → ℂ)
    (m : ℕ) [NeZero m] (χ : DirichletCharacter Qbar m) (j : ℕ) : ℂ :=
  (2 * Real.pi : ℂ) ^ (j + 1) / (j.factorial : ℂ) *
    ∫ t in Set.Ioi (0 : ℝ),
      inverseTwist ι f m χ (UpperHalfPlane.ofComplex (Complex.I * t)) * (t : ℂ) ^ j

end MTT


