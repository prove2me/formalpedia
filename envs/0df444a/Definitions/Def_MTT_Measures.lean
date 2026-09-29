-- Prove2me | Definitions.Def_MTT_Measures
-- name    : MTT_Measures
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-05T21:59:26.298959+00:00
-- url     : https://prove2.me/theorems/dbc2ea93-2c2f-42e9-9d0b-ae7e30fc4ea0
-- title:
--   MTT: p-adic measures, disk moments, and interpolation
-- statement:
--   Cp-valued bounded measures on the actual p-adic unit group, the ordinary-root predicate, algebraic signed symbols, disk moments from MTT (10.2), and the full interpolation predicate. The complex-to-p-adic comparison uses algebraic numbers under two fixed embeddings. Continuous test functions are quantified with exact pointwise specifications. Primitive conductor and critical-exponent bounds are enforced in the interpolation predicate.
-- source:
--   Mazur–Tate–Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), https://doi.org/10.1007/BF01388731; Chapter I, §§1–4, 7–14.

import Definitions.Def_MTT_Arithmetic
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Measure.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace MTT

variable {p : ℕ} [Fact p.Prime]

/-- A bounded Cp-valued measure on the actual compact group Zp^*. -/
abbrev UnitMeasure (p : ℕ) [Fact p.Prime] :=
  AbstractMeasure (ℤ_[p])ˣ ℂ_[p] ℂ_[p]

/-- The tautological coordinate, via Qp -> Cp. -/
def coordinate (x : (ℤ_[p])ˣ) : ℂ_[p] :=
  algebraMap ℚ_[p] ℂ_[p] (x.val : ℚ_[p])

/-- The ordinary root of MTT (10.1). -/
def IsOrdinaryRoot {N k : ℕ} {ι : Qbar →+* ℂ}
    (f : Eigenform N k ι) (ιp : Qbar →+* ℂ_[p]) (α : ℂ_[p]) : Prop :=
  ‖α‖ = 1 ∧ α ^ 2 - ιp (f.coeff p) * α +
    ιp (f.epsilon p) * (p : ℂ_[p]) ^ (k - 1) = 0

/-- Algebraic signed modular symbols, obtained by expanding (mX+a)^j. -/
def algebraicSymbol {k : ℕ} {ι : Qbar →+* ℂ} {f : UpperHalfPlane → ℂ}
    (P : Periods k ι f) (s : Bool) (j : ℕ) (a m : ℚ) : Qbar :=
  ∑ t ∈ Finset.range (j + 1),
    (j.choose t : Qbar) * (m : Qbar) ^ t * (a : Qbar) ^ (j - t) *
      P.value s t (-a / m)

/-- MTT (10.2), specialized to p-power disks of positive depth; polynomial X^j. -/
def diskMoment {N k : ℕ} {ι : Qbar →+* ℂ} (f : Eigenform N k ι)
    (ιp : Qbar →+* ℂ_[p]) (P : Periods k ι f.form) (α : ℂ_[p])
    (s : Bool) (j n : ℕ) (a : ℤ) : ℂ_[p] :=
  (α ^ n)⁻¹ * ιp (algebraicSymbol P s j a (p ^ n)) -
    (ιp (f.epsilon p) * (p : ℂ_[p]) ^ (k - 2) / α ^ (n + 1)) *
      ιp (algebraicSymbol P s j a (p ^ (n - 1)))

/-- Pointwise description of X^j on a residue disk and zero elsewhere. -/
def diskFunction (n : ℕ) (a : ℤ) (j : ℕ) (x : (ℤ_[p])ˣ) : ℂ_[p] :=
  if PadicInt.toZModPow n x.val = (a : ZMod (p ^ n)) then coordinate x ^ j else 0

/-- The measure realizes every critical polynomial moment on every unit disk. -/
def RealizesMoments {N k : ℕ} {ι : Qbar →+* ℂ} (f : Eigenform N k ι)
    (ιp : Qbar →+* ℂ_[p]) (P : Periods k ι f.form) (α : ℂ_[p])
    (s : Bool) (μ : UnitMeasure p) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (a : ℤ), IsCoprime a (p : ℤ) →
    ∀ (j : ℕ), j ≤ k - 2 → ∃ g : C((ℤ_[p])ˣ, ℂ_[p]),
      (∀ x, g x = diskFunction n a j x) ∧ μ g = diskMoment f ιp P α s j n a

/-- The finite-order character times X^j, as a pointwise function. -/
def specialFunction (ιp : Qbar →+* ℂ_[p]) (n : ℕ)
    (χ : DirichletCharacter Qbar (p ^ n)) (j : ℕ) (x : (ℤ_[p])ˣ) : ℂ_[p] :=
  ιp (χ (PadicInt.toZModPow n x.val)) * coordinate x ^ j

/-- Period parity: chi(-1)(-1)^j, true for plus and false for minus. -/
def criticalSign {m : ℕ} (χ : DirichletCharacter Qbar m) (j : ℕ) : Bool :=
  by classical exact decide (χ (-1) * (-1 : Qbar) ^ j = 1)

/-- MTT I.§14 multiplier; characters are evaluated at their primitive modulus. -/
def eulerMultiplier {N k : ℕ} {ι : Qbar →+* ℂ} (f : Eigenform N k ι)
    (ιp : Qbar →+* ℂ_[p]) (α : ℂ_[p]) (n : ℕ)
    (χ : DirichletCharacter Qbar (p ^ n)) (j : ℕ) : ℂ_[p] :=
  (α ^ n)⁻¹ *
    (1 - ιp (χ⁻¹ (p : ZMod (p ^ n))) * ιp (f.epsilon p) *
      (p : ℂ_[p]) ^ (k - 2 - j) / α) *
    (1 - ιp (χ (p : ZMod (p ^ n))) * (p : ℂ_[p]) ^ j / α)

/-- The complex side after division by the appropriate period, using MTT normalization. -/
def normalizedCriticalValue {N k : ℕ} {ι : Qbar →+* ℂ} (f : Eigenform N k ι)
    (omega : Bool → ℂ) (n : ℕ) (χ : DirichletCharacter Qbar (p ^ n)) (j : ℕ) : ℂ :=
  ((p ^ n : ℕ) : ℂ) ^ (j + 1) * (j.factorial : ℂ) /
    ((-2 * Real.pi * Complex.I) ^ j * gaussSum ι (p ^ n) χ⁻¹ *
      omega (criticalSign χ j)) * criticalLValue ι f.form (p ^ n) χ j

/-- Interpolation with an explicit algebraic bridge between C and Cp.
The existential continuous function is forced pointwise to equal chi(x) x^j. -/
def Interpolates {N k : ℕ} {ι : Qbar →+* ℂ} (f : Eigenform N k ι)
    (ιp : Qbar →+* ℂ_[p]) (omega : Bool → ℂ) (α : ℂ_[p])
    (μ : UnitMeasure p) : Prop :=
  ∀ (n : ℕ) (χ : DirichletCharacter Qbar (p ^ n)), χ.IsPrimitive →
    ∀ (j : ℕ), j ≤ k - 2 → ∃ (g : C((ℤ_[p])ˣ, ℂ_[p])) (v : Qbar),
      (∀ x, g x = specialFunction ιp n χ j x) ∧
      ι v = normalizedCriticalValue f omega n χ j ∧
      μ g = eulerMultiplier f ιp α n χ j * ιp v

end MTT


