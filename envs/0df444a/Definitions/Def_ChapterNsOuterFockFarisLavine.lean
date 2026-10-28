-- Prove2me | Definitions.Def_ChapterNsOuterFockFarisLavine
-- name    : ChapterNsOuterFockFarisLavine
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-24T12:36:45.026907+00:00
-- url     : https://prove2.me/theorems/98737be1-ddcb-45bb-9d6d-c706e51e2405
-- title:
--   The Lean 4 theorem `card_nsLoc` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNsOuterFockFarisLavine.lean`): generated def bundle for ChapterNsOuterFockFarisLavine. See BookProof/ChapterNsOuterFockFarisLavine.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNsOuterFockFarisLavine.lean

import Definitions.Def_ChapterSqSumOuterFamily
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Mathlib


/-!
# The gauge-fixed Navier–Stokes Hamiltonian on the outer Fock space, by Faris–Lavine

This module carries out for Navier–Stokes what
`BookProof.ChapterQgOuterFockFullFL` and `BookProof.ChapterQgOuterFockInteractionFL` do for
quantum gravity: it exhibits the gauge-fixed Hamiltonian as a *uniform* kinetic-plus-squares
family on the sectors of an outer Fock space and runs the Faris–Lavine theorem there, with
the **same comparison operator** — the lifted Friedrichs extension `dΓ(N₁)` of the positive
one-particle operator `N₁ = −Δ + ‖x‖²/4`.

## The variables

The parcel (excitation) of the Navier–Stokes thread carries the gauge-fixed field variables
of `BookProof.ChapterNavierStokesGaugeY`, *without* the space coordinate `x_j`, on which the
Hamiltonian symbol does not depend (`genX_nsSymbol`): the three velocity modes `u_i`, the
nine first-derivative modes `u_{i,j}`, the three Laplacian modes `u_{i,jj}` and the three
auxiliary coordinates `y_j` in which the field is expanded, `u_i(y) = u_i + u_{i,j} y_j`.
That is `18` coordinates per parcel (`NsLoc`), so the `n`-parcel sector is `L²(ℝ^{18n})` and
the state space is the outer Fock space `⊕ₙ L²(ℝ^{18n})`.

## The Hamiltonian

For a background advection velocity `bv`, viscosity `nu`, derivative-gauge strengths `lam`,
`mu` and `y`-gauge strength `gg`, the `n`-parcel Hamiltonian is

`H_n = ½ Σ_I π_I² + ½ Σ_r L_r²`

with, for every parcel `p`, the following four families of linear forms `L_r` (`sameVec`
gives their coefficients on the coordinates of `p`, `nextVec` those on the coordinates of
the cyclic neighbour `nextPart p`):

* **the Navier–Stokes constraint** `A_i = Σ_j bv_j u_{i,j} − nu·u_{i,jj}` — the advection
  (with background velocity `bv`) and viscous terms of the Navier–Stokes symbol, imposed as
  a squared constraint exactly as the torsion constraints are in the gravity sector;
* **the derivative gauge-fixing** `lam·(u_{i,j} + u_i − u_i^{next})` — the statement that
  the variable `u_{i,j}`, which represents a *spatial derivative of the field*, is the
  finite difference of the velocity between neighbouring parcels.  This form mixes the
  coordinates of two different parcels, so it is genuinely an **interaction term**;
* **the Laplacian gauge-fixing** `mu·(u_{i,jj} + Σ_j u_{i,j} − Σ_j u_{i,j}^{next})` — the
  same for the second-derivative variables;
* **the `y`-gauge fixing** `gg·y_j` — the gauge condition `y = 0` of the auxiliary
  expansion coordinate, whose generator `G_j = ∂/∂y_j − u_{i,j}∂/∂u_i` annihilates the
  Navier–Stokes symbol.

## What is proved

* `NsLoc`, `locU`, `locD`, `locL`, `locY`, `coordOf`, `parcelOf`, `locOf`,
  `sum_reindex_parcels` — the `18` field coordinates of a parcel and the bookkeeping of the
  `18n` coordinates of a sector;
* `sameVec`, `nextVec`, `nsVec` — the coefficient vectors of the four families of forms,
  with `nsVec_advection`, `nsVec_viscous`, `nsVec_tie_self`, `nsVec_tie_velocity`,
  `nsVec_lap_self`, `nsVec_gaugeY` reading off the individual coefficients, and
  `linForm_nsVec`, `linForm_nsConstraint`, `linForm_nsTie`, `linForm_nsLap`,
  `linForm_nsGaugeY` writing the four families out as polynomials in the field variables;
* `sum_abs_sameVec_row`, `sum_abs_nextVec_row`, `sum_abs_sameVec_col`,
  `sum_abs_nextVec_col`, `nsVec_row_le`, `nsVec_col_le` — the Schur data: every form has
  `ℓ¹` norm at most `7B` and every coordinate is touched by forms of total `ℓ¹` weight at
  most `6B`, where `B` bounds all the coefficients.  **Both bounds are independent of the
  parcel number `n`** — the locality of the gauge-fixing couplings — which is exactly the
  uniformity the `ℓ²`-direct-sum Faris–Lavine theorem needs;
* `nsFamily` — the family, as a `BookProof.SqSumOuterFamily.SqFamily`;
* `nsSectorHam`, `nsOuterHam` — the sector Hamiltonians and the full Hamiltonian on the
  finite-particle core of the outer Fock space, `nsOuterHam_symmetricOn`,
  `nsOuterHam_esa_core`;
* **`nsOuterFock_esa_farisLavine`** — the headline: the full gauge-fixed Navier–Stokes
  Hamiltonian, with its interaction (inter-parcel) terms and all its gauge-fixing terms, is
  essentially self-adjoint on the domain of the lifted Friedrichs extension of `N₁`, and
  the operator so realized extends `nsOuterHam` on the finite-particle core;
* `nsVec_coupling`, `ns_interaction_nontrivial` — the derivative gauge-fixing forms really
  do couple two different parcels, so for `lam ≠ 0` the Hamiltonian is *not* a sum of
  one-parcel operators.

## Honest boundary

The Hamiltonian is quadratic: the advection is taken with a **background velocity field
`bv`** (the Oseen linearisation), the nonlinear self-advection `u_j u_{i,j}` — a cubic term
in the canonical variables — is *not* included, and nothing here bears on global regularity
of the classical Navier–Stokes equations.  This is the same class of Hamiltonian as in the
gravity sector, and the restriction is essential: for a genuinely nonlinear transport
symbol the classical flow can leave every ball in finite time and no comparison operator
can help — the `ẋ = x²` warning of the Navier–Stokes thread, formalized in
`BookProof.ChapterNavierStokesFullEsa.exists_nsFullData_not_hasZeroDeficiencyOn`.  The Fock
space is the `ℓ²`-direct sum of the sectors (distinguishable parcels, no symmetrization),
and no spectral information is claimed.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsOuterFock

open Finset MvPolynomial
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL
open BookProof.SqSumOuterFamily

noncomputable section

/-! ## 1. The field coordinates of a parcel -/

/-- **The gauge-fixed Navier–Stokes field coordinates of one parcel**: the velocity modes
`u_i`, the first-derivative modes `u_{i,j}`, the Laplacian modes `u_{i,jj}` and the
auxiliary expansion coordinates `y_j`. -/
abbrev NsLoc : Type := Fin 3 ⊕ (Fin 3 × Fin 3) ⊕ Fin 3 ⊕ Fin 3

/-- The velocity coordinate `u_i`. -/
def locU (i : Fin 3) : NsLoc := Sum.inl i

/-- The first-derivative coordinate `u_{i,j}`. -/
def locD (i j : Fin 3) : NsLoc := Sum.inr (Sum.inl (i, j))

/-- The Laplacian coordinate `u_{i,jj}`. -/
def locL (i : Fin 3) : NsLoc := Sum.inr (Sum.inr (Sum.inl i))

/-- The auxiliary expansion coordinate `y_j`. -/
def locY (j : Fin 3) : NsLoc := Sum.inr (Sum.inr (Sum.inr j))

theorem card_nsLoc : Fintype.card NsLoc = 18 := by decide

/-- The `18` parcel coordinates, enumerated. -/
def locEquiv : NsLoc ≃ Fin 18 := Fintype.equivFinOfCardEq card_nsLoc

/-- The coordinate of the sector `L²(ℝ^{18n})` carrying the local coordinate `l` of the
parcel `p`. -/
def coordOf {n : ℕ} (p : Fin n) (l : NsLoc) : Fin (n * 18) := finProdFinEquiv (p, locEquiv l)

/-- The parcel carrying a sector coordinate. -/
def parcelOf {n : ℕ} (I : Fin (n * 18)) : Fin n := (finProdFinEquiv.symm I).1

/-- The local coordinate of a sector coordinate. -/
def locOf {n : ℕ} (I : Fin (n * 18)) : NsLoc := locEquiv.symm (finProdFinEquiv.symm I).2

@[simp] theorem parcelOf_coordOf {n : ℕ} (p : Fin n) (l : NsLoc) :
    parcelOf (coordOf p l) = p := by simp [parcelOf, coordOf]

@[simp] theorem locOf_coordOf {n : ℕ} (p : Fin n) (l : NsLoc) :
    locOf (coordOf p l) = l := by simp [locOf, coordOf]

@[simp] theorem coordOf_parcelOf_locOf {n : ℕ} (I : Fin (n * 18)) :
    coordOf (parcelOf I) (locOf I) = I := by
  simp only [coordOf, parcelOf, locOf, Equiv.apply_symm_apply, Prod.mk.eta]

/-- The sector coordinates, as parcel-times-local-coordinate pairs. -/
def coordEquiv (n : ℕ) : Fin n × NsLoc ≃ Fin (n * 18) :=
  ((Equiv.refl (Fin n)).prodCongr locEquiv).trans finProdFinEquiv



/-- Reindexing a sum over the `18n` sector coordinates as a sum over parcels and local
coordinates. -/
theorem sum_reindex_parcels {n : ℕ} {α : Type*} [AddCommMonoid α] (F : Fin (n * 18) → α) :
    ∑ I : Fin (n * 18), F I = ∑ p : Fin n, ∑ l : NsLoc, F (coordOf p l) := by
  calc ∑ I : Fin (n * 18), F I = ∑ pl : Fin n × NsLoc, F (coordOf pl.1 pl.2) :=
        (Fintype.sum_equiv (coordEquiv n) (fun pl => F (coordOf pl.1 pl.2)) F
          fun _ => rfl).symm
    _ = ∑ p : Fin n, ∑ l : NsLoc, F (coordOf p l) :=
        Fintype.sum_prod_type (fun pl : Fin n × NsLoc => F (coordOf pl.1 pl.2))

/-! ## 2. The linear forms of the gauge-fixed Navier–Stokes Hamiltonian -/

variable (bv : Fin 3 → ℝ) (nu lam mu gg : ℝ)

/-- **The coefficients of the four families of forms on the coordinates of their own
parcel.**  The first argument is the form, the second the coordinate. -/
def sameVec : NsLoc → NsLoc → ℝ
  | Sum.inl i, Sum.inr (Sum.inl (i', j)) => if i' = i then bv j else 0
  | Sum.inl i, Sum.inr (Sum.inr (Sum.inl i')) => if i' = i then -nu else 0
  | Sum.inr (Sum.inl (i, _)), Sum.inl i' => if i' = i then lam else 0
  | Sum.inr (Sum.inl (i, j)), Sum.inr (Sum.inl (i', j')) => if i' = i ∧ j' = j then lam else 0
  | Sum.inr (Sum.inr (Sum.inl i)), Sum.inr (Sum.inl (i', _)) => if i' = i then mu else 0
  | Sum.inr (Sum.inr (Sum.inl i)), Sum.inr (Sum.inr (Sum.inl i')) => if i' = i then mu else 0
  | Sum.inr (Sum.inr (Sum.inr j)), Sum.inr (Sum.inr (Sum.inr j')) => if j' = j then gg else 0
  | _, _ => 0

/-- **The coefficients of the forms on the coordinates of the neighbouring parcel.**  Only
the two gauge-fixing families for the derivative variables reach across parcels. -/
def nextVec : NsLoc → NsLoc → ℝ
  | Sum.inr (Sum.inl (i, _)), Sum.inl i' => if i' = i then -lam else 0
  | Sum.inr (Sum.inr (Sum.inl i)), Sum.inr (Sum.inl (i', _)) => if i' = i then -mu else 0
  | _, _ => 0

/-- **The coefficient vector of the form `(p, f)` of the `n`-parcel sector**: the form
lives on the coordinates of the parcel `p` and of its cyclic neighbour. -/
def nsVec (n : ℕ) (r : Fin n × NsLoc) (I : Fin (n * 18)) : ℝ :=
  if parcelOf I = r.1 then sameVec bv nu lam mu gg r.2 (locOf I)
  else if parcelOf I = nextPart r.1 then nextVec lam mu r.2 (locOf I) else 0

/-! ### Reading off the Hamiltonian -/

/-- The advection coefficient of the Navier–Stokes constraint form. -/
@[simp] theorem nsVec_advection {n : ℕ} (p : Fin n) (i j : Fin 3) :
    nsVec bv nu lam mu gg n (p, locU i) (coordOf p (locD i j)) = bv j := by
  simp [nsVec, locU, locD, sameVec]

/-- The viscous coefficient of the Navier–Stokes constraint form. -/
@[simp] theorem nsVec_viscous {n : ℕ} (p : Fin n) (i : Fin 3) :
    nsVec bv nu lam mu gg n (p, locU i) (coordOf p (locL i)) = -nu := by
  simp [nsVec, locU, locL, sameVec]

/-- The derivative gauge-fixing form contains the derivative variable it fixes. -/
@[simp] theorem nsVec_tie_self {n : ℕ} (p : Fin n) (i j : Fin 3) :
    nsVec bv nu lam mu gg n (p, locD i j) (coordOf p (locD i j)) = lam := by
  simp [nsVec, locD, sameVec]

/-- …and the velocity of its own parcel. -/
@[simp] theorem nsVec_tie_velocity {n : ℕ} (p : Fin n) (i j : Fin 3) :
    nsVec bv nu lam mu gg n (p, locD i j) (coordOf p (locU i)) = lam := by
  simp [nsVec, locD, locU, sameVec]

/-- The Laplacian gauge-fixing form contains the Laplacian variable it fixes. -/
@[simp] theorem nsVec_lap_self {n : ℕ} (p : Fin n) (i : Fin 3) :
    nsVec bv nu lam mu gg n (p, locL i) (coordOf p (locL i)) = mu := by
  simp [nsVec, locL, sameVec]

/-- The `y`-gauge-fixing form is the gauge condition `y_j = 0`. -/
@[simp] theorem nsVec_gaugeY {n : ℕ} (p : Fin n) (j : Fin 3) :
    nsVec bv nu lam mu gg n (p, locY j) (coordOf p (locY j)) = gg := by
  simp [nsVec, locY, sameVec]





/-! ### The forms, as polynomials -/











/-! ### The Schur data -/

variable {bv nu lam mu gg}
variable {B : ℝ} (hB : 0 ≤ B) (hbv : ∀ j, |bv j| ≤ B) (hnu : |nu| ≤ B) (hlam : |lam| ≤ B)
  (hmu : |mu| ≤ B) (hgg : |gg| ≤ B)

include hB hbv hnu hlam hmu hgg in
/-- Every form has `ℓ¹` norm at most `4B` on the coordinates of its own parcel. -/
theorem sum_abs_sameVec_row (f : NsLoc) :
    ∑ c : NsLoc, |sameVec bv nu lam mu gg f c| ≤ 4 * B := by
  obtain i | (⟨i, j⟩ | (i | j)) := f <;>
    simp [Fintype.sum_sum_type, Fintype.sum_prod_type, sameVec, Fin.sum_univ_three,
      apply_ite (fun t : ℝ => |t|), abs_neg] <;>
    (try fin_cases i) <;> (try fin_cases j) <;> (try simp) <;>
    linarith [hbv 0, hbv 1, hbv 2, hnu, hlam, hmu, hgg, abs_nonneg lam, abs_nonneg mu]

include hB hlam hmu in
/-- Every form has `ℓ¹` norm at most `3B` on the coordinates of the neighbouring parcel. -/
theorem sum_abs_nextVec_row (f : NsLoc) :
    ∑ c : NsLoc, |nextVec lam mu f c| ≤ 3 * B := by
  obtain i | (⟨i, j⟩ | (i | j)) := f <;>
    simp [Fintype.sum_sum_type, Fintype.sum_prod_type, nextVec, Fin.sum_univ_three,
      apply_ite (fun t : ℝ => |t|), abs_neg] <;>
    (try fin_cases i) <;> (try fin_cases j) <;> (try simp) <;>
    linarith [hlam, hmu, abs_nonneg lam, abs_nonneg mu]

include hB hbv hnu hlam hmu hgg in
/-- Every coordinate is touched by forms of its own parcel of total `ℓ¹` weight at most
`3B`. -/
theorem sum_abs_sameVec_col (c : NsLoc) :
    ∑ f : NsLoc, |sameVec bv nu lam mu gg f c| ≤ 3 * B := by
  obtain i | (⟨i, j⟩ | (i | j)) := c <;>
    simp [Fintype.sum_sum_type, Fintype.sum_prod_type, sameVec, Fin.sum_univ_three,
      apply_ite (fun t : ℝ => |t|), abs_neg] <;>
    (try fin_cases i) <;> (try fin_cases j) <;> (try simp) <;>
    linarith [hbv 0, hbv 1, hbv 2, hnu, hlam, hmu, hgg, abs_nonneg lam, abs_nonneg mu]

include hB hlam hmu in
/-- Every coordinate is touched by forms of the preceding parcel of total `ℓ¹` weight at
most `3B`. -/
theorem sum_abs_nextVec_col (c : NsLoc) :
    ∑ f : NsLoc, |nextVec lam mu f c| ≤ 3 * B := by
  obtain i | (⟨i, j⟩ | (i | j)) := c <;>
    simp [Fintype.sum_sum_type, Fintype.sum_prod_type, nextVec, Fin.sum_univ_three,
      apply_ite (fun t : ℝ => |t|), abs_neg] <;>
    (try fin_cases i) <;> (try fin_cases j) <;> (try simp) <;>
    linarith [hlam, hmu, abs_nonneg lam, abs_nonneg mu]

/-- The coefficient of a form on a coordinate is controlled by its own-parcel part and its
neighbour part. -/
theorem abs_nsVec_le {n : ℕ} (r : Fin n × NsLoc) (p : Fin n) (l : NsLoc) :
    |nsVec bv nu lam mu gg n r (coordOf p l)|
      ≤ (if p = r.1 then |sameVec bv nu lam mu gg r.2 l| else 0)
        + (if p = nextPart r.1 then |nextVec lam mu r.2 l| else 0) := by
  rw [nsVec, parcelOf_coordOf, locOf_coordOf]
  by_cases h1 : p = r.1
  · rw [if_pos h1, if_pos h1]
    have h2 : (0 : ℝ) ≤ if p = nextPart r.1 then |nextVec lam mu r.2 l| else 0 := by
      split_ifs
      · exact abs_nonneg _
      · exact le_rfl
    linarith
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : p = nextPart r.1
    · rw [if_pos h2, if_pos h2]
      simp
    · rw [if_neg h2, if_neg h2]
      simp

include hB hbv hnu hlam hmu hgg in
/-- **The row bound**: every linear form of the family has `ℓ¹` norm at most `7B`,
uniformly in the parcel number. -/
theorem nsVec_row_le (n : ℕ) (r : Fin n × NsLoc) :
    ∑ I : Fin (n * 18), |nsVec bv nu lam mu gg n r I| ≤ 7 * B := by
  set A : NsLoc → ℝ := fun l => |sameVec bv nu lam mu gg r.2 l| with hA
  set C : NsLoc → ℝ := fun l => |nextVec lam mu r.2 l| with hC
  have hstep : ∀ p : Fin n,
      ∑ l : NsLoc, ((if p = r.1 then A l else 0) + (if p = nextPart r.1 then C l else 0))
        = (if p = r.1 then ∑ l : NsLoc, A l else 0)
          + (if p = nextPart r.1 then ∑ l : NsLoc, C l else 0) := by
    intro p
    rw [Finset.sum_add_distrib]
    congr 1
    · by_cases h : p = r.1 <;> simp [h]
    · by_cases h : p = nextPart r.1 <;> simp [h]
  have hagg : ∑ p : Fin n, ∑ l : NsLoc,
      ((if p = r.1 then A l else 0) + (if p = nextPart r.1 then C l else 0))
      = (∑ l : NsLoc, A l) + ∑ l : NsLoc, C l := by
    rw [Finset.sum_congr rfl fun p _ => hstep p, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ r.1 (fun _ => ∑ l : NsLoc, A l),
      Finset.sum_ite_eq' Finset.univ (nextPart r.1) (fun _ => ∑ l : NsLoc, C l)]
    simp
  rw [sum_reindex_parcels]
  calc ∑ p : Fin n, ∑ l : NsLoc, |nsVec bv nu lam mu gg n r (coordOf p l)|
      ≤ ∑ p : Fin n, ∑ l : NsLoc,
          ((if p = r.1 then A l else 0) + (if p = nextPart r.1 then C l else 0)) :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun l _ => abs_nsVec_le r p l
    _ = (∑ l : NsLoc, A l) + ∑ l : NsLoc, C l := hagg
    _ ≤ 7 * B := by
        have h1 := sum_abs_sameVec_row hB hbv hnu hlam hmu hgg r.2
        have h2 := sum_abs_nextVec_row hB hlam hmu r.2
        rw [hA, hC]
        linarith

include hB hbv hnu hlam hmu hgg in
/-- **The column bound**: every coordinate is touched by forms of total `ℓ¹` weight at most
`6B`, uniformly in the parcel number — the couplings are nearest-neighbour, so a coordinate
belongs to one parcel and that parcel occurs in exactly two coupling blocks. -/
theorem nsVec_col_le (n : ℕ) (I : Fin (n * 18)) :
    ∑ r : Fin n × NsLoc, |nsVec bv nu lam mu gg n r I| ≤ 6 * B := by
  set b0 : Fin n := parcelOf I with hb0
  set c0 : NsLoc := locOf I with hc0
  have hI : I = coordOf b0 c0 := (coordOf_parcelOf_locOf I).symm
  have hterm : ∀ (p : Fin n) (f : NsLoc),
      |nsVec bv nu lam mu gg n (p, f) I|
        ≤ (if b0 = p then |sameVec bv nu lam mu gg f c0| else 0)
          + (if b0 = nextPart p then |nextVec lam mu f c0| else 0) := by
    intro p f
    rw [hI, nsVec, parcelOf_coordOf, locOf_coordOf]
    by_cases h1 : b0 = p
    · rw [if_pos h1, if_pos h1]
      have h2 : (0 : ℝ) ≤ if b0 = nextPart p then |nextVec lam mu f c0| else 0 := by
        split_ifs
        · exact abs_nonneg _
        · exact le_rfl
      linarith
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : b0 = nextPart p
      · rw [if_pos h2, if_pos h2]
        simp
      · rw [if_neg h2, if_neg h2]
        simp
  have hinner : ∀ p : Fin n,
      ∑ f : NsLoc, ((if b0 = p then |sameVec bv nu lam mu gg f c0| else 0)
          + (if b0 = nextPart p then |nextVec lam mu f c0| else 0))
        = (if b0 = p then ∑ f : NsLoc, |sameVec bv nu lam mu gg f c0| else 0)
          + (if b0 = nextPart p then ∑ f : NsLoc, |nextVec lam mu f c0| else 0) := by
    intro p
    rw [Finset.sum_add_distrib]
    congr 1
    · by_cases h : b0 = p <;> simp [h]
    · by_cases h : b0 = nextPart p <;> simp [h]
  have hagg : ∑ p : Fin n,
      ((if b0 = p then ∑ f : NsLoc, |sameVec bv nu lam mu gg f c0| else 0)
        + (if b0 = nextPart p then ∑ f : NsLoc, |nextVec lam mu f c0| else 0))
      = (∑ f : NsLoc, |sameVec bv nu lam mu gg f c0|)
        + ∑ f : NsLoc, |nextVec lam mu f c0| := by
    rw [Finset.sum_add_distrib,
      Finset.sum_ite_eq Finset.univ b0
        (fun _ => ∑ f : NsLoc, |sameVec bv nu lam mu gg f c0|),
      sum_comp_nextPart (fun x => if b0 = x then ∑ f : NsLoc, |nextVec lam mu f c0| else 0),
      Finset.sum_ite_eq Finset.univ b0 (fun _ => ∑ f : NsLoc, |nextVec lam mu f c0|)]
    simp
  calc ∑ r : Fin n × NsLoc, |nsVec bv nu lam mu gg n r I|
      = ∑ p : Fin n, ∑ f : NsLoc, |nsVec bv nu lam mu gg n (p, f) I| :=
        Fintype.sum_prod_type _
    _ ≤ ∑ p : Fin n, ∑ f : NsLoc,
          ((if b0 = p then |sameVec bv nu lam mu gg f c0| else 0)
            + (if b0 = nextPart p then |nextVec lam mu f c0| else 0)) :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun f _ => hterm p f
    _ = (∑ f : NsLoc, |sameVec bv nu lam mu gg f c0|)
          + ∑ f : NsLoc, |nextVec lam mu f c0| := by
        rw [Finset.sum_congr rfl fun p _ => hinner p, hagg]
    _ ≤ 6 * B := by
        have h1 := sum_abs_sameVec_col hB hbv hnu hlam hmu hgg c0
        have h2 := sum_abs_nextVec_col hB hlam hmu c0
        linarith

/-! ## 3. The family and the Faris–Lavine theorem -/

include hB hbv hnu hlam hmu hgg in
/-- **The gauge-fixed Navier–Stokes family** on the outer Fock space `⊕ₙ L²(ℝ^{18n})`: the
kinetic term `½ Σ_I π_I²` in all `18n` field variables together with the squared
Navier–Stokes constraints and the squared gauge-fixing forms, with Schur constants
`7B` and `6B` independent of the parcel number. -/
def nsFamily : SqFamily where
  dim := fun n => n * 18
  R := fun n => Fin n × NsLoc
  finR := fun _ => inferInstance
  kap := fun _ _ => 1
  vv := fun n => nsVec bv nu lam mu gg n
  km := 1
  a := 7 * B
  b := 6 * B
  km_nonneg := by norm_num
  a_nonneg := by linarith
  b_nonneg := by linarith
  kap_le := by intro n I; norm_num
  row_le := fun n r => nsVec_row_le hB hbv hnu hlam hmu hgg n r
  col_le := fun n I => nsVec_col_le hB hbv hnu hlam hmu hgg n I













end

end BookProof.NsOuterFock


