-- Prove2me | Definitions.Def_FTheoryK3TateCore
-- name    : FTheoryK3TateCore
-- status  : Definition
-- author  : @andreaskapfer
-- created : 2026-09-22T08:35:47.864782+00:00
-- url     : https://prove2.me/theorems/a07796d2-ca5a-4c3a-8a0e-7fe478cbf498
-- title:
--   Kodaira/Tate fibre-order calculus: discriminant, type table, $E_8$ points
-- statement:
--   This bundle sets up the Kodaira/Tate fibre-order calculus for a (short) Weierstrass model $y^2 = x^3 + f\,x + g$ over the affine line, with $f, g \in k[X]$ over a field $k$.
--
--   1. **Discriminant.** $\Delta(f,g) = 4f^3 + 27g^2 \in k[X]$ (the discriminant up to the unit $-16$).
--
--   2. **K3 degree data.** `IsK3Data f g` is $\deg f \le 8$, $\deg g \le 12$, and $\Delta(f,g) \ne 0$.
--
--   3. **Kodaira types.** `Kodaira` enumerates the seven **additive-reduction** Kodaira/Tate fibre types whose discriminant order is a function of the vanishing orders $(\operatorname{ord} f, \operatorname{ord} g)$: $\mathrm{II}, \mathrm{III}, \mathrm{IV}, \mathrm{I}_0^*, \mathrm{IV}^*, \mathrm{III}^*, \mathrm{II}^*$. The multiplicative $\mathrm{I}_n$ series is deliberately omitted, since there $\operatorname{ord} f = \operatorname{ord} g = 0$ and the order $n$ is a free datum, not a function of $(\operatorname{ord} f, \operatorname{ord} g)$.
--
--   4. **discOrder.** The Tate-table discriminant order attached to each type: $\mathrm{II}\!\to\!2$, $\mathrm{III}\!\to\!3$, $\mathrm{IV}\!\to\!4$, $\mathrm{I}_0^*\!\to\!6$, $\mathrm{IV}^*\!\to\!8$, $\mathrm{III}^*\!\to\!9$, $\mathrm{II}^*\!\to\!10$.
--
--   5. **HasKodaira.** `HasKodaira f g t₀ τ` states, through vanishing orders alone, that the fibre at $t_0$ carries type $\tau$. A lower bound $\operatorname{ord}_{t_0} p \ge n$ is written as the divisibility $(X - t_0)^n \mid p$ (which also holds for $p = 0$, order $+\infty$); an exact order is written `rootMultiplicity = n`. The signatures are the Tate table: $\mathrm{II}\,(\operatorname{ord} f \ge 1, \operatorname{ord} g = 1)$, $\mathrm{III}\,(1, \ge 2)$, $\mathrm{IV}\,(\ge 2, 2)$, $\mathrm{IV}^*\,(\ge 3, 4)$, $\mathrm{III}^*\,(3, \ge 5)$, $\mathrm{II}^*\,(\ge 4, 5)$; and $\mathrm{I}_0^*$ is $(\operatorname{ord} f = 2, \operatorname{ord} g = 3)$ **together with** the reduced-discriminant nondegeneracy $4 c_2^3 + 27 d_3^2 \ne 0$, where $c_2 = (\text{taylor}_{t_0} f)_2$ and $d_3 = (\text{taylor}_{t_0} g)_3$ are the leading local (Taylor) coefficients — this is what pins the order at $6$ rather than higher.
--
--   6. **IsE8Point** is defined as type $\mathrm{II}^*$. Its clause $(X - t_0)^4 \mid f$ encodes $\operatorname{ord}_{t_0} f \ge 4$ faithfully, **including** the degenerate $f = 0$ case, which a plain `rootMultiplicity ≥ 4` encoding silently drops.
--
--   **Formalization note.** `natDegree` and `rootMultiplicity` are $0$ on the zero polynomial. Divisibility clauses therefore carry the $\operatorname{ord} = +\infty$ convention for the zero polynomial, while `rootMultiplicity = n` clauses force the polynomial to be nonzero.
-- source:
--   Kodaira classification of singular fibres and Tate's algorithm: J. Tate, "Algorithm for determining the type of a singular fiber in an elliptic pencil" (Modular Functions of One Variable IV, LNM 476, 1975); M. Schuett and T. Shioda, "Elliptic Surfaces," Adv. Stud. Pure Math. 60 (2010), arXiv:0907.0298 (Euler number = degree of the discriminant divisor = 12*deg L; elliptic K3 => 24). F-theory dictionary between Kodaira/Tate fibre types and gauge algebras (up to E8) and 7-branes: T. Weigand, "TASI Lectures on F-theory," arXiv:1806.01854.

import Mathlib

open Polynomial

namespace FTheoryK3Tate

variable {k : Type*} [Field k]

/-- Discriminant of the short Weierstrass model `y² = x³ + f x + g`
    (the usual discriminant up to the unit `-16`). -/
noncomputable def Δ (f g : k[X]) : k[X] := 4 * f ^ 3 + 27 * g ^ 2

/-- Calabi–Yau / K3 Weierstrass degree data over the affine chart, with nondegenerate
    discriminant: `deg f ≤ 8`, `deg g ≤ 12`, `Δ ≠ 0`. -/
def IsK3Data (f g : k[X]) : Prop :=
  f.natDegree ≤ 8 ∧ g.natDegree ≤ 12 ∧ Δ f g ≠ 0

/-- The seven reduced (additive-reduction) Kodaira/Tate fibre types whose discriminant
    order is pinned by the vanishing orders `(ord f, ord g)`. The multiplicative `Iₙ`
    series (where `ord f = ord g = 0` and `ord Δ = n` is the free datum) is deliberately
    excluded, as its order is not a function of `(ord f, ord g)`. -/
inductive Kodaira
  | II | III | IV | I0star | IVstar | IIIstar | IIstar

/-- The discriminant vanishing order `ord Δ` attached to each Kodaira/Tate type — the
    entries of the Tate table. The type II* (gauge algebra `E₈`) entry is `10`. -/
def Kodaira.discOrder : Kodaira → ℕ
  | .II      => 2
  | .III     => 3
  | .IV      => 4
  | .I0star  => 6
  | .IVstar  => 8
  | .IIIstar => 9
  | .IIstar  => 10

/-- `HasKodaira f g t₀ τ` : the fibre of `y² = x³ + f x + g` at the base point `t₀` has
    Kodaira/Tate type `τ`, expressed purely through the vanishing orders of `f` and `g`.

    Conventions (all Mathlib-native): `p.rootMultiplicity t₀` is `ord_{t₀} p` (with the
    zero polynomial having multiplicity `0`), and the divisibility clause `(X - C t₀)^n ∣ p`
    reads as `ord_{t₀} p ≥ n`, which — unlike `rootMultiplicity` — also holds for `p = 0`
    (order `+∞`). Exact orders (`= n`) are stated with `rootMultiplicity`, lower bounds
    (`≥ n`) with divisibility.

    For `I₀*` the two orders sit at the cancellation locus `3·ord f = 2·ord g = 6`, so the
    order is pinned at `6` only when the **reduced discriminant** `4 c₂³ + 27 d₃²` is
    nonzero, where `c₂ = (taylor t₀ f).coeff 2` and `d₃ = (taylor t₀ g).coeff 3` are the
    leading local (Taylor) coefficients of `f` and `g` at `t₀`. -/
def HasKodaira (f g : k[X]) (t₀ : k) : Kodaira → Prop
  | .II      => (X - C t₀) ∣ f ∧ g.rootMultiplicity t₀ = 1
  | .III     => f.rootMultiplicity t₀ = 1 ∧ (X - C t₀) ^ 2 ∣ g
  | .IV      => (X - C t₀) ^ 2 ∣ f ∧ g.rootMultiplicity t₀ = 2
  | .I0star  => f.rootMultiplicity t₀ = 2 ∧ g.rootMultiplicity t₀ = 3 ∧
                4 * ((taylor t₀ f).coeff 2) ^ 3 + 27 * ((taylor t₀ g).coeff 3) ^ 2 ≠ 0
  | .IVstar  => (X - C t₀) ^ 3 ∣ f ∧ g.rootMultiplicity t₀ = 4
  | .IIIstar => f.rootMultiplicity t₀ = 3 ∧ (X - C t₀) ^ 5 ∣ g
  | .IIstar  => (X - C t₀) ^ 4 ∣ f ∧ g.rootMultiplicity t₀ = 5

/-- A base point carrying a Kodaira type II* fibre — the `E₈` gauge algebra locus.
    The `(X - C t₀)^4 ∣ f` clause encodes `ord_{t₀} f ≥ 4` faithfully, **including** the
    degenerate `f = 0` case (order `+∞`), which the plain `rootMultiplicity ≥ 4` encoding
    silently excludes. -/
def IsE8Point (f g : k[X]) (t₀ : k) : Prop := HasKodaira f g t₀ Kodaira.IIstar

end FTheoryK3Tate


