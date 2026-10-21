-- Prove2me | Definitions.Def_SI_units
-- name    : SI_units
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-20T13:36:03.431168+00:00
-- url     : https://prove2.me/theorems/91e10402-e4c1-4e20-b346-d7c7281f917c
-- title:
--   The units of the SI and quantity calculus
-- statement:
--   A unit of the SI as an element of quantity calculus: a rational
--   numerical factor together with a dimensional product. The structure
--   carries the unit one; the seven base units (second, metre, kilogram,
--   ampere, kelvin, mole, candela; Table 2); the 22 coherent derived units
--   with special names (radian through katal; Table 4), each built as a
--   product or quotient of base units; coherence as the condition that
--   the numerical factor be one (section 2.3.4); exact powers of ten and
--   the decimal prefixes (chapter 3), with the gram and the prefix rule
--   for the kilogram; and the non-SI units exactly accepted for use with
--   the SI (Table 8): minute, hour, day, litre, tonne, bar, astronomical
--   unit, nautical mile, knot, and the electronvolt.
-- source:
--   The International System of Units (SI), 9th edition, V4.01 (BIPM, 2026), chapter 2 (Tables 2, 3 and 4; section 2.3.4 on coherence), chapter 3 (decimal prefixes; the gram rule), and chapter 4, Table 8 (non-SI units accepted for use with the SI).

import Mathlib
import Definitions.Def_SI_dim

/-!
# The SI: the units and quantity calculus

The units of the International System of Units as elements of quantity
calculus (section 5.4.1: the value of a quantity is the product of a
numerical value and a unit): a unit is a numerical factor together with a
dimensional product. The seven base units (Table 2), the 22 derived units
with special names (Table 4) in their base-unit expressions, the decimal
prefixes (chapter 3), and the non-SI units exactly accepted for use with
the SI (Table 8). Coherence (section 2.3.4): the numerical factor of a
coherent derived unit is one; prefixed units are not coherent.
-/

namespace SI

/-- A unit as an element of quantity calculus: a numerical factor and a
dimensional product. -/
structure SIUnit where
  /-- the numerical factor -/
  val : ℚ
  /-- the dimensional product -/
  dim : Dim

/-- The product of two units: the factors multiply and the dimensions
add. -/
def umul (u v : SIUnit) : SIUnit := ⟨u.val * v.val, u.dim + v.dim⟩

/-- The unit one, the neutral element of quantity calculus (section
5.4.7: quantities of dimension one carry the unit one). -/
def uone : SIUnit := ⟨1, 0⟩

/-- The reciprocal of a unit. -/
def uinv (u : SIUnit) : SIUnit := ⟨u.val⁻¹, -u.dim⟩

/-- The quotient of two units. -/
def udiv (u v : SIUnit) : SIUnit := umul u (uinv v)

/-- A numerical multiple of a unit. -/
def uscale (n : ℚ) (u : SIUnit) : SIUnit := ⟨n * u.val, u.dim⟩

/-- A coherent unit (section 2.3.4): its numerical factor, when written
as a product of powers of the base units, is one. -/
def IsCoherent (u : SIUnit) : Prop := u.val = 1

/-- The second, the SI unit of time (Table 2). -/
def second : SIUnit := ⟨1, dT⟩

/-- The metre, the SI unit of length. -/
def metre : SIUnit := ⟨1, dL⟩

/-- The kilogram, the SI unit of mass. -/
def kilogram : SIUnit := ⟨1, dM⟩

/-- The ampere, the SI unit of electric current. -/
def ampere : SIUnit := ⟨1, dI⟩

/-- The kelvin, the SI unit of thermodynamic temperature. -/
def kelvin : SIUnit := ⟨1, dTh⟩

/-- The mole, the SI unit of amount of substance. -/
def mole : SIUnit := ⟨1, dN⟩

/-- The candela, the SI unit of luminous intensity. -/
def candela : SIUnit := ⟨1, dJ⟩

/-- The radian, the coherent unit of plane angle: a quantity of dimension
one, written with the symbol rad to emphasize the angle (Table 4, note b). -/
def radian : SIUnit := uone

/-- The steradian, the coherent unit of solid angle (Table 4, note c). -/
def steradian : SIUnit := uone

/-- The hertz (Table 4): the coherent derived unit of frequency, s⁻¹. -/
def hertz : SIUnit := uinv second

/-- The newton (Table 4): the coherent derived unit of force, kg m s⁻². -/
def newton : SIUnit := udiv (umul kilogram metre) (umul second second)

/-- The pascal (Table 4): the coherent derived unit of pressure and
stress, N/m², equal to kg m⁻¹ s⁻². -/
def pascal : SIUnit := udiv newton (umul metre metre)

/-- The joule (Table 4): the coherent derived unit of energy, work and
amount of heat, N m, equal to kg m² s⁻². -/
def joule : SIUnit := umul newton metre

/-- The watt (Table 4): the coherent derived unit of power and radiant
flux, J/s, equal to kg m² s⁻³. -/
def watt : SIUnit := udiv joule second

/-- The coulomb (Table 4): the coherent derived unit of electric charge,
A s. -/
def coulomb : SIUnit := umul ampere second

/-- The volt (Table 4): the coherent derived unit of electric potential
difference, W/A, equal to kg m² s⁻³ A⁻¹. -/
def volt : SIUnit := udiv watt ampere

/-- The farad (Table 4): the coherent derived unit of capacitance, C/V,
equal to kg⁻¹ m⁻² s⁴ A². -/
def farad : SIUnit := udiv coulomb volt

/-- The ohm (Table 4): the coherent derived unit of electric resistance,
V/A, equal to kg m² s⁻³ A⁻². -/
def ohm : SIUnit := udiv volt ampere

/-- The siemens (Table 4): the coherent derived unit of electric
conductance, A/V, equal to kg⁻¹ m⁻² s³ A². -/
def siemens : SIUnit := udiv ampere volt

/-- The weber (Table 4): the coherent derived unit of magnetic flux,
V s, equal to kg m² s⁻² A⁻¹. -/
def weber : SIUnit := umul volt second

/-- The tesla (Table 4): the coherent derived unit of magnetic flux
density, Wb/m², equal to kg s⁻² A⁻¹. -/
def tesla : SIUnit := udiv weber (umul metre metre)

/-- The henry (Table 4): the coherent derived unit of inductance, Wb/A,
equal to kg m² s⁻² A⁻². -/
def henry : SIUnit := udiv weber ampere

/-- The degree Celsius (Table 4): the unit of Celsius temperature, equal
in magnitude to the kelvin (section 2.3.1, the kelvin). -/
def celsius : SIUnit := kelvin

/-- The lumen (Table 4): the coherent derived unit of luminous flux,
cd sr. -/
def lumen : SIUnit := umul candela steradian

/-- The lux (Table 4): the coherent derived unit of illuminance, lm/m². -/
def lux : SIUnit := udiv lumen (umul metre metre)

/-- The becquerel (Table 4): the coherent derived unit of activity
referred to a radionuclide, s⁻¹. -/
def becquerel : SIUnit := uinv second

/-- The gray (Table 4): the coherent derived unit of absorbed dose and
kerma, J/kg, equal to m² s⁻². -/
def gray : SIUnit := udiv joule kilogram

/-- The sievert (Table 4): the coherent derived unit of dose equivalent,
J/kg, equal to m² s⁻². -/
def sievert : SIUnit := udiv joule kilogram

/-- The katal (Table 4): the coherent derived unit of catalytic activity,
mol/s. -/
def katal : SIUnit := udiv mole second

/-- The seven base units (Table 2). -/
def base7 : List SIUnit :=
  [second, metre, kilogram, ampere, kelvin, mole, candela]

/-- The 22 SI units with special names (Table 4). -/
def named22 : List SIUnit :=
  [radian, steradian, hertz, newton, pascal, joule, watt, coulomb, volt,
   farad, ohm, siemens, weber, tesla, henry, celsius, lumen, lux,
   becquerel, gray, sievert, katal]

/-- The 29 named SI units: the seven base units together with the 22
units with special names (section 2.3.4). -/
def named29 : List SIUnit := base7 ++ named22

/-- Exact powers of ten, for positive and negative exponents. -/
def pow10 : ℤ → ℚ
  | .ofNat n => (10 : ℚ) ^ n
  | .negSucc n => ((10 : ℚ) ^ n)⁻¹

/-- A prefixed unit: a decimal multiple or sub-multiple of a unit
(chapter 3). A prefixed unit is not coherent: the prefix introduces a
numerical factor other than one. -/
def prefixed (k : ℤ) (u : SIUnit) : SIUnit := ⟨u.val * pow10 k, u.dim⟩

/-- The gram. The base unit kilogram carries a prefix in its name, so
decimal multiples and sub-multiples of the unit of mass attach prefixes
to the gram (chapter 3): 1 kg = 10³ g. -/
def gram : SIUnit := uscale (1 / 1000) kilogram

/-- The minute, a non-SI unit exactly accepted for use with the SI
(Table 8): 1 min = 60 s. -/
def minute : SIUnit := uscale 60 second

/-- The hour (Table 8): 1 h = 60 min = 3600 s. -/
def hour : SIUnit := uscale 3600 second

/-- The day (Table 8): 1 d = 24 h = 86 400 s. -/
def day : SIUnit := uscale 86400 second

/-- The litre (Table 8): 1 l = 1 dm³ = 10⁻³ m³. -/
def litre : SIUnit := uscale (1 / 1000) (umul metre (umul metre metre))

/-- The tonne (Table 8): 1 t = 1 Mg = 10³ kg. -/
def tonne : SIUnit := uscale 1000 kilogram

/-- The bar (Table 8): 1 bar = 10⁵ Pa. -/
def bar : SIUnit := uscale ((10 : ℚ) ^ 5) pascal

/-- The astronomical unit (Table 8): 1 au = 149 597 870 700 m. -/
def au : SIUnit := uscale 149597870700 metre

/-- The nautical mile (Table 8): 1 nautical mile = 1852 m. -/
def nauticalMile : SIUnit := uscale 1852 metre

/-- The knot (Table 8): 1 knot = (1852/3600) m/s. -/
def knot : SIUnit := udiv nauticalMile hour

/-- The electronvolt (Table 8, note l): the kinetic energy acquired by an
electron in passing through a potential difference of one volt. Since
the numerical value of the elementary charge is fixed, the conversion
factor is exact: 1 eV = 1.602 176 634 × 10⁻¹⁹ J. -/
def eVolt : SIUnit := uscale (1602176634 / (10 : ℚ) ^ 28) joule

end SI


