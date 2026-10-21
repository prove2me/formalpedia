-- Prove2me | Definitions.Def_SI_dim
-- name    : SI_dim
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-20T13:35:33.190956+00:00
-- url     : https://prove2.me/theorems/5535df75-e028-416e-868e-858b984ec6e7
-- title:
--   The dimension space of the SI and its seven defining constants
-- statement:
--   The dimensional skeleton of the International System of Units. The
--   dimension space is the free abelian group on the seven base quantities
--   (time, length, mass, electric current, thermodynamic temperature,
--   amount of substance, luminous intensity), written additively, in the
--   order of Table 3 of section 2.3.3. The seven defining constants fixed
--   by the 26th CGPM (2018) - the caesium hyperfine transition frequency
--   Δν_Cs, the speed of light c, the Planck constant h, the elementary
--   charge e, the Boltzmann constant k, the Avogadro constant N_A, and
--   the luminous efficacy K_cd - each carry the dimension of the coherent
--   unit in which their exact numerical value is fixed: Hz, m s⁻¹, J s, C,
--   J K⁻¹, mol⁻¹, and lm W⁻¹ respectively (section 2.2, Table 1). The
--   dimension-exponent matrix of the seven constants is recorded
--   explicitly, and the dimension map sends a monomial in the constants to
--   its dimension. Its bijectivity - the unimodularity of the matrix - is
--   the arithmetic content of the completeness statement of section 2.2
--   and is proved as the first milestone of the mission.
-- source:
--   The International System of Units (SI), 9th edition, V4.01 (BIPM, 2026), section 2.2, Table 1 (the seven defining constants and the coherent units in which their exact numerical values are fixed) and section 2.3.3, Table 3 (the dimension symbols of the seven base quantities).

import Mathlib

/-!
# The SI: the dimension space and the seven defining constants

The dimensional skeleton of the International System of Units in the form
fixed by the 26th CGPM (2018) and recorded in the 9th edition of the SI
Brochure: the dimension space of the seven base quantities (section 2.3.3,
Table 3), the seven defining constants with the dimensions of the coherent
units in which their exact numerical values are expressed (section 2.2,
Table 1), and the dimension map that sends a monomial in the defining
constants to its dimension. The seven dimension vectors of the constants
span the dimension space over the integers (this is the completeness claim
of section 2.2: any unit of the SI can be written through products or
quotients of the defining constants); the spanning statement is a theorem
of the mission, proved from the explicit matrix below.
-/

namespace SI

/-- The dimension space of the SI: dimension products are written
additively, with one component per base quantity, in the order time,
length, mass, electric current, thermodynamic temperature, amount of
substance, luminous intensity (section 2.3.3, Table 3). -/
abbrev Dim : Type := Fin 7 → ℤ

/-- The dimension of the base quantity time. -/
def dT : Dim := ![1, 0, 0, 0, 0, 0, 0]

/-- The dimension of the base quantity length. -/
def dL : Dim := ![0, 1, 0, 0, 0, 0, 0]

/-- The dimension of the base quantity mass. -/
def dM : Dim := ![0, 0, 1, 0, 0, 0, 0]

/-- The dimension of the base quantity electric current. -/
def dI : Dim := ![0, 0, 0, 1, 0, 0, 0]

/-- The dimension of the base quantity thermodynamic temperature. -/
def dTh : Dim := ![0, 0, 0, 0, 1, 0, 0]

/-- The dimension of the base quantity amount of substance. -/
def dN : Dim := ![0, 0, 0, 0, 0, 1, 0]

/-- The dimension of the base quantity luminous intensity. -/
def dJ : Dim := ![0, 0, 0, 0, 0, 0, 1]

/-- The seven defining constants of the SI (section 2.2, Table 1). -/
inductive Const
  /-- the unperturbed ground state hyperfine transition frequency of the
  caesium 133 atom, Δν_Cs -/
  | dCs : Const
  /-- the speed of light in vacuum, c -/
  | c : Const
  /-- the Planck constant, h -/
  | h : Const
  /-- the elementary charge, e -/
  | e : Const
  /-- the Boltzmann constant, k -/
  | kB : Const
  /-- the Avogadro constant, N_A -/
  | NA : Const
  /-- the luminous efficacy of monochromatic radiation of frequency
  540 × 10¹² Hz, K_cd -/
  | Kcd : Const

/-- The standard exponent vector of a defining constant: the monomial
consisting of the constant itself. -/
def eC : Const → (Fin 7 → ℤ)
  | Const.dCs => ![1, 0, 0, 0, 0, 0, 0]
  | Const.c => ![0, 1, 0, 0, 0, 0, 0]
  | Const.h => ![0, 0, 1, 0, 0, 0, 0]
  | Const.e => ![0, 0, 0, 1, 0, 0, 0]
  | Const.kB => ![0, 0, 0, 0, 1, 0, 0]
  | Const.NA => ![0, 0, 0, 0, 0, 1, 0]
  | Const.Kcd => ![0, 0, 0, 0, 0, 0, 1]

/-- The dimension of each defining constant, which is the dimension of the
coherent unit in which its exact numerical value is fixed by Table 1:
Δν_Cs in Hz, c in m s⁻¹, h in J s, e in C, k in J K⁻¹, N_A in mol⁻¹,
K_cd in lm W⁻¹. -/
def dimConst : Const → Dim
  | Const.dCs => ![-1, 0, 0, 0, 0, 0, 0]
  | Const.c => ![-1, 1, 0, 0, 0, 0, 0]
  | Const.h => ![-1, 2, 1, 0, 0, 0, 0]
  | Const.e => ![1, 0, 0, 1, 0, 0, 0]
  | Const.kB => ![-2, 2, 1, 0, -1, 0, 0]
  | Const.NA => ![0, 0, 0, 0, 0, -1, 0]
  | Const.Kcd => ![3, -2, -1, 0, 0, 0, 1]

/-- The standard enumeration of the defining constants. -/
def constOfFin : Fin 7 → Const :=
  ![Const.dCs, Const.c, Const.h, Const.e, Const.kB, Const.NA, Const.Kcd]

/-- The dimension-exponent matrix of the seven defining constants. -/
def constMat : Matrix (Fin 7) (Fin 7) ℤ :=
  Matrix.of fun i j => dimConst (constOfFin j) i

/-- The dimension map: the monomial in the defining constants with
exponent vector v denotes a quantity of dimension
dimOfExpo v. Section 2.2: the units of the seven defining constants
include both base and derived units, and any unit of the SI can be
written through products or quotients of the defining constants. -/
def dimOfExpo : (Fin 7 → ℤ) → Dim := constMat.mulVec

end SI


