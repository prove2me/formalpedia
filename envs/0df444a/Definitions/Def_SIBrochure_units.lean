-- Prove2me | Definitions.Def_SIBrochure_units
-- name    : SIBrochure_units
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T15:07:38.364832+00:00
-- url     : https://prove2.me/theorems/0694a582-777f-4ce3-854b-ceeaf416ec3f
-- title:
--   SI quantity values, base and derived units, and the seven defining constants
-- statement:
--   A **quantity value** is a pair consisting of a real **numerical value** $x$ and a **unit monomial** $\mathrm{s}^{a_1}\mathrm{m}^{a_2}\mathrm{kg}^{a_3}\mathrm{A}^{a_4}\mathrm{K}^{a_5}\mathrm{mol}^{a_6}\mathrm{cd}^{a_7}$ with integer exponents in the seven SI base units. Products multiply numerical values and add exponent vectors; the inverse inverts the numerical value and negates the exponents; quotients and integer powers are defined accordingly; a real number $r$ acts by multiplying the numerical value. Two quantity values are equal iff their numerical values and all seven exponents coincide.
--
--   The file defines the seven base units (numerical value $1$, a single exponent $1$), the derived units
--   $$\mathrm{Hz}=\mathrm s^{-1},\ \mathrm J=\mathrm{kg\,m^2\,s^{-2}},\ \mathrm C=\mathrm{A\,s},\ \mathrm W=\mathrm{kg\,m^2\,s^{-3}},\ \mathrm{sr}=\mathrm{m^2\,m^{-2}},\ \mathrm{lm}=\mathrm{cd\,sr},$$
--   and the seven defining constants of Section 2.2:
--   $$\Delta\nu_{\mathrm{Cs}} = 9\,192\,631\,770\ \mathrm{Hz},\ c = 299\,792\,458\ \mathrm{m/s},\ h = 6.626\,070\,15\times10^{-34}\ \mathrm{J\,s},\ e = 1.602\,176\,634\times10^{-19}\ \mathrm C,$$
--   $$k = 1.380\,649\times10^{-23}\ \mathrm{J/K},\ N_A = 6.022\,140\,76\times10^{23}\ \mathrm{mol^{-1}},\ K_{\mathrm{cd}} = 683\ \mathrm{lm/W},$$
--   together with an index type for the seven constants and the map sending each index to its value.
--
--   This is the shared model for every statement of the mission: all milestones and the goal are equalities between quantity values built from these definitions.
--
--   **Formalization Note** The steradian is the unit of dimension one ($\mathrm m^2\mathrm m^{-2}$), so $\mathrm{lm}=\mathrm{cd}$ in this model. Real inversion follows Mathlib ($0^{-1}=0$).
-- source:
--   BIPM, The International System of Units (SI), 9th edition (2019), ISBN 978-92-822-2272-0, https://www.bipm.org/en/publications/si-brochure — Section 2.2 (Definition of the SI, pp. 127–128, Table 1) and Section 2.3.1 (Base units, Table 2, pp. 129–130).

import Mathlib

/-!
# The International System of Units (SI), 9th edition (2019): quantities, units and the
seven defining constants

Source: BIPM, *The International System of Units (SI)*, 9th edition (2019),
Section 2.2 (Definition of the SI, Table 1), Section 2.3.1 (Base units, Table 2).

A *quantity value* is modelled as the product of a real number (its numerical value) and a
unit monomial `s^a₁ m^a₂ kg^a₃ A^a₄ K^a₅ mol^a₆ cd^a₇` with integer exponents in the seven
SI base units. Two quantity values are equal iff they have the same numerical value and the
same exponents.
-/

noncomputable section

namespace SIBrochure

/-- The seven SI base units (Table 2 of the SI Brochure). -/
inductive BaseUnit
  | second
  | metre
  | kilogram
  | ampere
  | kelvin
  | mole
  | candela
  deriving DecidableEq, Repr

instance : Fintype BaseUnit :=
  ⟨{.second, .metre, .kilogram, .ampere, .kelvin, .mole, .candela}, by
    intro x; cases x <;> simp⟩

/-- A quantity value `num · ∏_b b ^ (exp b)`: a real numerical value times a monomial in the
seven SI base units with integer exponents. -/
@[ext]
structure Quantity where
  /-- The numerical value. -/
  num : ℝ
  /-- The exponent of each base unit. -/
  exp : BaseUnit → ℤ

namespace Quantity

instance : One Quantity := ⟨⟨1, 0⟩⟩
instance : Mul Quantity := ⟨fun q r => ⟨q.num * r.num, q.exp + r.exp⟩⟩
instance : Inv Quantity := ⟨fun q => ⟨q.num⁻¹, -q.exp⟩⟩
instance : Div Quantity := ⟨fun q r => ⟨q.num / r.num, q.exp - r.exp⟩⟩
/-- A real number `a` times a quantity value: `a • q` scales the numerical value. -/
instance : SMul ℝ Quantity := ⟨fun a q => ⟨a * q.num, q.exp⟩⟩

@[simp] lemma one_num : (1 : Quantity).num = 1 := rfl
@[simp] lemma one_exp : (1 : Quantity).exp = 0 := rfl
@[simp] lemma mul_num (q r : Quantity) : (q * r).num = q.num * r.num := rfl
@[simp] lemma mul_exp (q r : Quantity) : (q * r).exp = q.exp + r.exp := rfl
@[simp] lemma inv_num (q : Quantity) : q⁻¹.num = q.num⁻¹ := rfl
@[simp] lemma inv_exp (q : Quantity) : q⁻¹.exp = -q.exp := rfl
@[simp] lemma div_num (q r : Quantity) : (q / r).num = q.num / r.num := rfl
@[simp] lemma div_exp (q r : Quantity) : (q / r).exp = q.exp - r.exp := rfl
@[simp] lemma smul_num (a : ℝ) (q : Quantity) : (a • q).num = a * q.num := rfl
@[simp] lemma smul_exp (a : ℝ) (q : Quantity) : (a • q).exp = q.exp := rfl

/-- Integer powers: `q ^ n` raises the numerical value to the `n`-th power and multiplies
every exponent by `n`. -/
instance : DivInvMonoid Quantity where
  mul_assoc a b c := by
    ext
    · exact mul_assoc a.num b.num c.num
    · exact congrFun (add_assoc a.exp b.exp c.exp) _
  one_mul a := by
    ext
    · exact one_mul a.num
    · exact congrFun (zero_add a.exp) _
  mul_one a := by
    ext
    · exact mul_one a.num
    · exact congrFun (add_zero a.exp) _
  div_eq_mul_inv a b := by
    ext
    · exact div_eq_mul_inv a.num b.num
    · exact congrFun (sub_eq_add_neg a.exp b.exp) _
  zpow n q := ⟨q.num ^ n, n • q.exp⟩
  zpow_zero' q := by
    ext x
    · exact zpow_zero q.num
    · exact congrFun (zero_smul ℤ q.exp) x
  zpow_succ' n q := by
    ext x
    · change q.num ^ ((n.succ : ℕ) : ℤ) = q.num ^ ((n : ℕ) : ℤ) * q.num
      rw [zpow_natCast, zpow_natCast, pow_succ]
    · change ((n.succ : ℤ) • q.exp) x = ((n : ℤ) • q.exp) x + q.exp x
      simp only [Pi.smul_apply, smul_eq_mul]; push_cast; ring
  zpow_neg' n q := by
    ext x
    · change q.num ^ (Int.negSucc n) = (q.num ^ ((n.succ : ℕ) : ℤ))⁻¹
      rw [zpow_negSucc, zpow_natCast]
    · change ((Int.negSucc n) • q.exp) x = -(((n.succ : ℕ) : ℤ) • q.exp) x
      simp only [Pi.smul_apply, smul_eq_mul, Int.negSucc_eq]; push_cast; ring
  npow n q := ⟨q.num ^ n, n • q.exp⟩
  npow_zero q := by
    ext x
    · exact pow_zero q.num
    · exact congrFun (zero_smul ℕ q.exp) x
  npow_succ n q := by
    ext x
    · change q.num ^ (n + 1) = q.num ^ n * q.num
      rw [pow_succ]
    · change ((n + 1) • q.exp) x = (n • q.exp) x + q.exp x
      simp only [Pi.smul_apply, nsmul_eq_mul]; push_cast; ring

instance : CommMonoid Quantity where
  mul_comm a b := by
    ext
    · exact mul_comm a.num b.num
    · exact congrFun (add_comm a.exp b.exp) _

@[simp] lemma zpow_num (q : Quantity) (n : ℤ) : (q ^ n).num = q.num ^ n := rfl
@[simp] lemma zpow_exp (q : Quantity) (n : ℤ) : (q ^ n).exp = n • q.exp := rfl
@[simp] lemma npow_num (q : Quantity) (n : ℕ) : (q ^ n).num = q.num ^ n := rfl
@[simp] lemma npow_exp (q : Quantity) (n : ℕ) : (q ^ n).exp = n • q.exp := rfl

end Quantity

open Quantity

/-- The unit monomial `∏_b b ^ (e b)` with numerical value `1`. -/
def unitOf (e : BaseUnit → ℤ) : Quantity := ⟨1, e⟩

/-- A base unit, as a quantity value (numerical value `1`, exponent `1` in that base unit
and `0` in all others). -/
def base (b : BaseUnit) : Quantity := unitOf (Pi.single b 1)

/-! ## Base units (Table 2) -/

/-- The second, `s`. -/
def second : Quantity := base .second
/-- The metre, `m`. -/
def metre : Quantity := base .metre
/-- The kilogram, `kg`. -/
def kilogram : Quantity := base .kilogram
/-- The ampere, `A`. -/
def ampere : Quantity := base .ampere
/-- The kelvin, `K`. -/
def kelvin : Quantity := base .kelvin
/-- The mole, `mol`. -/
def mole : Quantity := base .mole
/-- The candela, `cd`. -/
def candela : Quantity := base .candela

/-! ## Derived units used in Section 2.2 -/

/-- The hertz, `Hz = s⁻¹`. -/
def hertz : Quantity := second⁻¹
/-- The joule, `J = kg m² s⁻²`. -/
def joule : Quantity := kilogram * metre ^ (2 : ℤ) * second ^ (-2 : ℤ)
/-- The coulomb, `C = A s`. -/
def coulomb : Quantity := ampere * second
/-- The watt, `W = kg m² s⁻³`. -/
def watt : Quantity := kilogram * metre ^ (2 : ℤ) * second ^ (-3 : ℤ)
/-- The steradian, `sr = m² m⁻²` (a unit of dimension one). -/
def steradian : Quantity := metre ^ (2 : ℤ) * metre ^ (-2 : ℤ)
/-- The lumen, `lm = cd sr`. -/
def lumen : Quantity := candela * steradian

/-! ## The seven defining constants (Section 2.2, Table 1) -/

/-- `ΔνCs = 9 192 631 770 Hz`: the unperturbed ground state hyperfine transition frequency
of the caesium 133 atom. -/
noncomputable def deltaNuCs : Quantity := (9192631770 : ℝ) • hertz
/-- `c = 299 792 458 m s⁻¹`: the speed of light in vacuum. -/
noncomputable def c : Quantity := (299792458 : ℝ) • (metre / second)
/-- `h = 6.626 070 15 × 10⁻³⁴ J s`: the Planck constant. -/
noncomputable def h : Quantity := (6.62607015e-34 : ℝ) • (joule * second)
/-- `e = 1.602 176 634 × 10⁻¹⁹ C`: the elementary charge. -/
noncomputable def e : Quantity := (1.602176634e-19 : ℝ) • coulomb
/-- `k = 1.380 649 × 10⁻²³ J K⁻¹`: the Boltzmann constant. -/
noncomputable def k : Quantity := (1.380649e-23 : ℝ) • (joule / kelvin)
/-- `N_A = 6.022 140 76 × 10²³ mol⁻¹`: the Avogadro constant. -/
noncomputable def NA : Quantity := (6.02214076e23 : ℝ) • mole⁻¹
/-- `K_cd = 683 lm W⁻¹`: the luminous efficacy of monochromatic radiation of frequency
`540 × 10¹² Hz`. -/
noncomputable def Kcd : Quantity := (683 : ℝ) • (lumen / watt)

/-- Indexing type for the seven defining constants. -/
inductive DefiningConstant
  | deltaNuCs
  | c
  | h
  | e
  | k
  | NA
  | Kcd
  deriving DecidableEq, Repr

instance : Fintype DefiningConstant :=
  ⟨{.deltaNuCs, .c, .h, .e, .k, .NA, .Kcd}, by intro x; cases x <;> simp⟩

/-- The value of each defining constant. -/
noncomputable def DefiningConstant.value : DefiningConstant → Quantity
  | .deltaNuCs => SIBrochure.deltaNuCs
  | .c => SIBrochure.c
  | .h => SIBrochure.h
  | .e => SIBrochure.e
  | .k => SIBrochure.k
  | .NA => SIBrochure.NA
  | .Kcd => SIBrochure.Kcd

end SIBrochure

end


