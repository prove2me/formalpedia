-- Prove2me | Definitions.Def_SI_qmodel
-- name    : SI_qmodel
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-20T13:36:41.007401+00:00
-- url     : https://prove2.me/theorems/9ede2b28-a432-4345-ad00-184e93ba17f4
-- title:
--   The quantity model of the SI: exact monomials in the defining constants
-- statement:
--   The quantity model through which the seven defining constants
--   determine the SI (section 2.2). A quantity is a monomial in the seven
--   defining constants with a rational coefficient. A model assigns to
--   each dimensional product the exponents and the numerical coefficient
--   of its expression in the constants, respecting products of dimensions.
--   The seven value fields are the seven defining statements of Table 1:
--   Δν_Cs = 9 192 631 770 Hz; c = 299 792 458 m s⁻¹;
--   h = 6.626 070 15 × 10⁻³⁴ J s; e = 1.602 176 634 × 10⁻¹⁹ C;
--   k = 1.380 649 × 10⁻²³ J K⁻¹; N_A = 6.022 140 76 × 10²³ mol⁻¹;
--   K_cd = 683 lm W⁻¹. The identifying map sends a unit to the monomial of
--   its dimension scaled by its numerical factor, and the seven monomials
--   sMono through cdMono are the exact inversions printed in section 2.3.1
--   for the second, metre, kilogram, ampere, kelvin, mole and candela.
-- source:
--   The International System of Units (SI), 9th edition, V4.01 (BIPM, 2026), section 2.2, Table 1 (the seven defining statements) and section 2.3.1 (the base units expressed through the defining constants).

import Mathlib
import Definitions.Def_SI_dim
import Definitions.Def_SI_units

/-!
# The SI: the quantity model of the defining constants

The quantity model through which the seven defining constants determine
the SI (section 2.2): a quantity is a monomial in the seven defining
constants with a rational coefficient, the numerical values of the
constants themselves are the seven exact statements of Table 1, and the
model identifies every SI unit with the exact defining-constant monomial
of its dimension. The seven value fields below are the seven defining
statements of the SI, in the coherent unit in which each fixed numerical
value is expressed; the homomorphism fields assert that exponent and
coefficient assignments respect products of dimensions. The seven
monomials sMono ... cdMono are the inverted relations printed in
section 2.3.1, expressing each base unit in terms of the defining
constants with its exact rational coefficient.
-/

namespace SI

/-- A monomial in the seven defining constants with a rational
coefficient: the exact form of a quantity of the SI as the product of a
number and powers of the defining constants. -/
structure QMono where
  /-- the numerical coefficient -/
  coef : ℚ
  /-- the exponents of the defining constants, in the order of
  constOfFin -/
  expo : Fin 7 → ℤ

/-- The product of two defining-constant monomials. -/
def qmul (a b : QMono) : QMono := ⟨a.coef * b.coef, a.expo + b.expo⟩

/-- The monomial one: the number one. -/
def qone : QMono := ⟨1, 0⟩

/-- The reciprocal of a defining-constant monomial. -/
def qinv (a : QMono) : QMono := ⟨a.coef⁻¹, -a.expo⟩

/-- A quantity model of the SI. The map expoOfDim assigns to each
dimensional product the exponents of its expression as a monomial in the
defining constants, and coefOfDim the associated numerical coefficient;
the homomorphism fields assert that both assignments respect products of
dimensions, and the seven value fields are the seven defining statements
of the SI (section 2.2, Table 1), one per defining constant. -/
structure SIModel where
  expoOfDim : Dim → (Fin 7 → ℤ)
  coefOfDim : Dim → ℚ
  /-- the exponent assignment maps the dimension one to the constant
  monomial one -/
  expoOfDim_zero : expoOfDim 0 = 0
  /-- the exponent assignment is additive in the dimension -/
  expoOfDim_add : ∀ a b : Dim, expoOfDim (a + b) = expoOfDim a + expoOfDim b
  /-- the coefficient assignment maps the dimension one to one -/
  coefOfDim_one : coefOfDim 0 = 1
  /-- the coefficient assignment is multiplicative in the dimension -/
  coefOfDim_mul : ∀ a b : Dim, coefOfDim (a + b) = coefOfDim a * coefOfDim b
  /-- Δν_Cs = 9 192 631 770 Hz, that is, Hz = Δν_Cs / 9 192 631 770:
  the dimension of the hertz is −dT -/
  hzValue : expoOfDim (-dT) = eC Const.dCs ∧
    coefOfDim (-dT) = 1 / 9192631770
  /-- c = 299 792 458 m/s, that is, m s⁻¹ = c / 299 792 458: the dimension
  of the unit m s⁻¹ is dL − dT -/
  msValue : expoOfDim (dL - dT) = eC Const.c ∧
    coefOfDim (dL - dT) = 1 / 299792458
  /-- h = 6.626 070 15 × 10⁻³⁴ J s, that is,
  J s = h / (6.626 070 15 × 10⁻³⁴): the dimension of the unit J s is
  dM + (dL + dL) − dT -/
  jsValue : expoOfDim (dM + (dL + dL) - dT) = eC Const.h ∧
    coefOfDim (dM + (dL + dL) - dT) = (10 : ℚ) ^ 42 / 662607015
  /-- e = 1.602 176 634 × 10⁻¹⁹ C, that is,
  C = e / (1.602 176 634 × 10⁻¹⁹): the dimension of the coulomb is
  dI + dT -/
  coulValue : expoOfDim (dI + dT) = eC Const.e ∧
    coefOfDim (dI + dT) = (10 : ℚ) ^ 28 / 1602176634
  /-- k = 1.380 649 × 10⁻²³ J/K, that is,
  J K⁻¹ = k / (1.380 649 × 10⁻²³): the dimension of the unit J K⁻¹ is
  dM + (dL + dL) − (dT + dT) − dTh -/
  jkValue : expoOfDim (dM + (dL + dL) - (dT + dT) - dTh) = eC Const.kB ∧
    coefOfDim (dM + (dL + dL) - (dT + dT) - dTh) = (10 : ℚ) ^ 29 / 1380649
  /-- N_A = 6.022 140 76 × 10²³ mol⁻¹, that is,
  mol⁻¹ = N_A / (6.022 140 76 × 10²³): the dimension is −dN -/
  molValue : expoOfDim (-dN) = eC Const.NA ∧
    coefOfDim (-dN) = (10 : ℚ) ^ 14 / 602214076
  /-- K_cd = 683 lm/W, that is, lm W⁻¹ = K_cd / 683: the dimension of the
  unit lm W⁻¹ is dJ − (dL + dL) − dM + (dT + dT + dT) -/
  lmwValue : expoOfDim (dJ - (dL + dL) - dM + (dT + dT + dT)) = eC Const.Kcd ∧
    coefOfDim (dJ - (dL + dL) - dM + (dT + dT + dT)) = 1 / 683

/-- The identifying map of the model: the unit u denotes the quantity
u.val times the defining-constant monomial of its dimension. Under the
seven value postulates this is an exact rational monomial in the defining
constants. -/
def toQ (M : SIModel) (u : SIUnit) : QMono :=
  ⟨u.val * M.coefOfDim u.dim, M.expoOfDim u.dim⟩

/-- The exact expression of the second: 1 s = 9 192 631 770 / Δν_Cs
(section 2.3.1, the second). -/
def sMono : QMono := ⟨9192631770, -(eC Const.dCs)⟩

/-- The exact expression of the metre:
1 m = (9 192 631 770 / 299 792 458) (c / Δν_Cs) (section 2.3.1, the metre). -/
def mMono : QMono :=
  ⟨9192631770 / 299792458, eC Const.c - eC Const.dCs⟩

/-- The exact expression of the kilogram:
1 kg = (299 792 458)² / ((6.626 070 15 × 10⁻³⁴)(9 192 631 770)) times
h Δν_Cs / c² (section 2.3.1, the kilogram). -/
def kgMono : QMono :=
  ⟨(299792458 : ℚ) * (299792458 : ℚ) * (10 : ℚ) ^ 42 / (9192631770 * 662607015),
    eC Const.h + eC Const.dCs - (eC Const.c + eC Const.c)⟩

/-- The exact expression of the ampere:
1 A = Δν_Cs e / ((9 192 631 770)(1.602 176 634 × 10⁻¹⁹))
(section 2.3.1, the ampere). -/
def AMono : QMono :=
  ⟨(10 : ℚ) ^ 28 / (9192631770 * 1602176634), eC Const.dCs + eC Const.e⟩

/-- The exact expression of the kelvin:
1 K = (1.380 649 × 10⁻²³) / ((6.626 070 15 × 10⁻³⁴)(9 192 631 770))
times Δν_Cs h / k (section 2.3.1, the kelvin). -/
def KMono : QMono :=
  ⟨(1380649 : ℚ) * (10 : ℚ) ^ 13 / (662607015 * 9192631770),
    eC Const.dCs + eC Const.h - eC Const.kB⟩

/-- The exact expression of the mole:
1 mol = 6.022 140 76 × 10²³ / N_A (section 2.3.1, the mole). -/
def molMono : QMono := ⟨(602214076 : ℚ) * (10 : ℚ) ^ 14, -(eC Const.NA)⟩

/-- The exact expression of the candela:
1 cd = (Δν_Cs)² h K_cd / ((6.626 070 15 × 10⁻³⁴)(9 192 631 770)² 683)
(section 2.3.1, the candela). -/
def cdMono : QMono :=
  ⟨(10 : ℚ) ^ 42 / (662607015 * (9192631770 : ℚ) ^ 2 * 683),
    eC Const.dCs + eC Const.dCs + eC Const.h + eC Const.Kcd⟩

end SI


