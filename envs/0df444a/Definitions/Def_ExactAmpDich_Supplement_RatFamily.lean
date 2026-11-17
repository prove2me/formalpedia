-- Prove2me | Definitions.Def_ExactAmpDich_Supplement_RatFamily
-- name    : ExactAmpDich_Supplement_RatFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:22:16.812001+00:00
-- url     : https://prove2.me/theorems/8e240c27-2389-4c98-9440-52bc126bbc83
-- title:
--   Rational families $G(z)$ of gate libraries, their poles, phase and real domains, and exact codes
-- statement:
--   A **rational family** $G(z)$ has a fixed library shape (gate sizes $k_j\ge1$) and entries that are rational functions of one variable; the coefficients of each reduced numerator and monic reduced denominator are algebraic.
--
--   1. A **pole** is a root of the reduced denominator of some entry; off the poles $G(z)$ is the library with entries $\mathrm{num}(z)/\mathrm{den}(z)$.
--   2. The **phase domain** is the unit circle with all poles removed; the **real domain** is the real axis with all poles removed.
--   3. An **exact code** of the family lists, for each gate, its size and for each entry a pair of exactly coded polynomials $(p,q)$, $q\ne0$, with entry $p/q$ (not necessarily in lowest terms).
--
--   These are the objects of Theorem J.3.
-- source:
--   Liu–Meng, A Dichotomy for Exact Quantum Circuit Amplitudes, STOC 2027 submission (held manuscript, sha256 40ad9c68…), Theorem J.3 and the preceding definitions, p.75 (PDF p.76)

import Mathlib
import Definitions.Def_ExactAmpDich_Supplement_Codes

set_option autoImplicit false

namespace ExactAmpDich.Supplement

open QAlgorithms BlockOrthoCSP.Decide

/-- A **rational family** `G(z)` of gate libraries: a fixed library shape whose matrix entries are
rational functions of one variable with algebraic coefficients (the coefficients of the reduced
numerator and of the monic reduced denominator are algebraic). Liu–Meng, *A Dichotomy for Exact
Quantum Circuit Amplitudes*, STOC 2027 submission (held manuscript, sha256 40ad9c68…),
Theorem J.3, p.75 (PDF p.76): "a fixed finite list of matrix-valued rational functions with
algebraic coefficients". -/
structure RatFamily where
  /-- The number of gates. -/
  t : ℕ
  /-- The number of qubits of gate `j`. -/
  k : Fin t → ℕ
  /-- Every gate acts on at least one qubit. -/
  one_le_k : ∀ j, 1 ≤ k j
  /-- The entry `(y, x)` of gate `j`. -/
  f : (j : Fin t) → Qubits (k j) → Qubits (k j) → RatFunc ℂ
  /-- Algebraic coefficients. -/
  alg : ∀ j y x n, _root_.IsAlgebraic ℚ ((f j y x).num.coeff n) ∧
    _root_.IsAlgebraic ℚ ((f j y x).denom.coeff n)

/-- `z` is a **pole** of some entry: a root of the reduced denominator of some entry. -/
def RatFamily.IsPole (F : RatFamily) (z : ℂ) : Prop :=
  ∃ j y x, (F.f j y x).denom.eval z = 0

/-- The library `G(z)` (entries `num(z)/denom(z)`; only used off the poles). -/
noncomputable def RatFamily.at (F : RatFamily) (z : ℂ) : Library where
  t := F.t
  k := F.k
  one_le_k := F.one_le_k
  U j y x := RatFunc.eval (RingHom.id ℂ) z (F.f j y x)

/-- The **phase domain**: the unit circle with all poles removed. Liu–Meng, p.75: "For a rational
family G(z), its phase domain is the unit circle with all poles of its matrix entries removed." -/
def RatFamily.phaseDomain (F : RatFamily) : Set ℂ := {z | ‖z‖ = 1 ∧ ¬ F.IsPole z}

/-- The **real domain**: the real axis with all poles removed. Liu–Meng, p.75: "For the
real-parameter version below, the domain is the real axis with those poles removed." -/
def RatFamily.realDomain (F : RatFamily) : Set ℝ := {x | ¬ F.IsPole (x : ℂ)}

/-- `cd` is an exact code of the polynomial `p`: entry `n` is a valid code of the coefficient of
`Xⁿ`, and all coefficients beyond the list vanish. -/
def PolyAlgCode.Denotes (cd : List AlgCode) (p : Polynomial ℂ) : Prop :=
  ∀ n, (∃ a, (cd[n]? = some a) ∧ a.Valid ∧ a.Denotes (p.coeff n)) ∨ ((cd[n]? = none) ∧ p.coeff n = 0)

/-- Exact code of a rational family: for each gate its size and the list of its entries (in the
order of `MatCode`), each entry a numerator code and a denominator code. -/
abbrev RatFamCode : Type := List (ℕ × List (List AlgCode × List AlgCode))

/-- `cd` is an exact code of the rational family `F`: every entry is coded as a quotient `p / q`
of coded polynomials with `q ≠ 0` (not necessarily in lowest terms). -/
def RatFamCode.Denotes (cd : RatFamCode) (F : RatFamily) : Prop :=
  cd.length = F.t ∧ ∀ j : Fin F.t, ∃ e, (cd[j.val]? = some e) ∧ e.1 = F.k j ∧
    e.2.length = 4 ^ F.k j ∧ ∀ y x, ∃ pq, (e.2[bitsIndex y * 2 ^ F.k j + bitsIndex x]? = some pq) ∧
      ∃ p q : Polynomial ℂ, q ≠ 0 ∧ PolyAlgCode.Denotes pq.1 p ∧ PolyAlgCode.Denotes pq.2 q ∧
        algebraMap (Polynomial ℂ) (RatFunc ℂ) p / algebraMap (Polynomial ℂ) (RatFunc ℂ) q =
          F.f j y x

end ExactAmpDich.Supplement


