-- Prove2me | Definitions.Def_ChapterQgOuterFockInteractionFL
-- name    : ChapterQgOuterFockInteractionFL
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-21T11:23:15.477087+00:00
-- url     : https://prove2.me/theorems/066af6bf-b45d-44b1-a51a-3d517d20d78b
-- title:
--   The Lean 4 theorem `ab_nonneg` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQgOuterFockInteractionFL.lean`): generated def bundle for ChapterQgOuterFockInteractionFL. See BookProof/ChapterQgOuterFockInteractionFL.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockInteractionFL.lean

import Theorems.Thm_BookProof_QgOuterFockFL_harmFried_op_core

import Theorems.Thm_BookProof_SqSumFarisLavine_norm_sqSumOp_le

import Theorems.Thm_BookProof_SqSumFarisLavine_potFun_le_of_schur

import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib


/-!
# Interacting quantum gravity on the outer Fock space, by Faris–Lavine

`BookProof.ChapterQgOuterFockFullFL` proves that the outer-Fock second quantization of the
one-particle gauge-fixed gravity Hamiltonian is essentially self-adjoint by Faris–Lavine.
That Hamiltonian is a *sum of one-particle operators*: nothing in it couples two different
excitations.  This module removes that restriction.

## The general statement

A `QgFamily` is a family of `n`-particle Hamiltonians

`H_n = ½ Σ_I κ^{(n)}_I π_I² + ½ Σ_r (L^{(n)}_r)²`,  `L^{(n)}_r = Σ_I v^{(n)}_{rI} x_I`,

on `L²(ℝ^{84n})`, subject to **three uniform bounds**: the signature is bounded by `km`,
every linear form has `ℓ¹` norm at most `a` (a *row* bound), and every coordinate is
touched by forms of total `ℓ¹` weight at most `b` (a *column* bound).  Nothing constrains
which coordinates a form may involve: a form is free to mix the coordinates of arbitrarily
many different particles, so the resulting Hamiltonian is genuinely interacting and is
*not* a sum of one-particle operators.

`QgFamily.esa_farisLavine` is then the headline: such a Hamiltonian is essentially
self-adjoint on the domain of the lifted Friedrichs extension of the positive one-particle
operator `N₁ = −Δ + ‖x‖²/4`, and the operator so realized extends the finite-particle-core
Hamiltonian `QgFamily.outerHam`.  The two Faris–Lavine constants are

`flK = 3km/2 + 4ab`  (relative bound),  `flc = km/2 + 2ab`  (commutator bound),

and — this is the whole point — **they depend on the family only through `km`, `a`, `b`,
never through the particle number**, which is exactly the uniformity the `ℓ²`-direct-sum
Faris–Lavine theorem needs.

## The physical interacting instance

`qgIntFamily lam` is the gauge-fixed 3D gravity family with a *nearest-neighbour torsion
coupling* of strength `lam`: besides the `64` torsion forms `T_m^{(p)}` of each particle,
it carries the `64` coupling forms `lam·(T_m^{(p)} − T_m^{(p+1)})` for every particle `p`
(the successor `nextPart` is taken cyclically).  Each coupling form mixes the coordinates
of two different particles (`qgCoupling_spans_two_particles`), so for `lam ≠ 0` the
Hamiltonian is not a sum of one-particle operators; nevertheless the row bound
`2 + 4|lam|` and the column bound `64 + 128|lam|` are independent of the particle number,
because a coordinate belongs to one particle and that particle occurs in exactly two
coupling blocks.  The conclusion is

**`qgInteracting_esa_farisLavine`** — the interacting gauge-fixed 3D quantum-gravity
Hamiltonian, with the physical hyperbolic signature `qgKappa`, all `64` torsion terms per
particle and all inter-particle coupling terms, is essentially self-adjoint on the outer
Fock space by Faris–Lavine, with the lifted Friedrichs extension of `N₁` as comparison
operator.

## Honest boundary

The couplings are quadratic in the field coordinates (squares of linear forms), which is
the class the torsion potential itself belongs to, and they preserve the particle number;
the uniform column bound is a *locality* requirement, and a family in which every particle
is coupled to every other with the same strength does not satisfy it.  As everywhere in
this development, the Fock space is the `ℓ²`-direct sum of the sectors (distinguishable
excitations, no symmetrization), and no spectrum, mass gap or continuum limit is claimed.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgOuterFockInteractionFL

open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine

noncomputable section

/-- **A uniform family of kinetic-plus-squares Hamiltonians on the outer Fock sectors.**
The `n`-particle Hamiltonian is `½ Σ_I κ_I π_I² + ½ Σ_r L_r²` with `L_r` the linear form
of coefficient vector `vv n r`; the three bounds `km`, `a`, `b` are uniform in the
particle number `n`.  No structural restriction whatsoever is placed on the linear forms:
they may mix the coordinates of different particles. -/
structure QgFamily where
  /-- The index type of the linear forms of the `n`-particle sector. -/
  R : ℕ → Type
  [finR : ∀ n, Fintype (R n)]
  /-- The signature of the kinetic term of the `n`-particle sector. -/
  kap : ∀ n : ℕ, Fin (n * 84) → ℝ
  /-- The coefficient vectors of the linear forms of the `n`-particle sector. -/
  vv : ∀ n : ℕ, R n → Fin (n * 84) → ℝ
  /-- The uniform bound on the signature. -/
  km : ℝ
  /-- The uniform row (`ℓ¹`-per-form) bound. -/
  a : ℝ
  /-- The uniform column (`ℓ¹`-per-coordinate) bound. -/
  b : ℝ
  km_nonneg : 0 ≤ km
  a_nonneg : 0 ≤ a
  b_nonneg : 0 ≤ b
  kap_le : ∀ (n : ℕ) (I : Fin (n * 84)), |kap n I| ≤ km
  row_le : ∀ (n : ℕ) (r : R n), ∑ I : Fin (n * 84), |vv n r I| ≤ a
  col_le : ∀ (n : ℕ) (I : Fin (n * 84)), ∑ r : R n, |vv n r I| ≤ b

attribute [instance] QgFamily.finR

namespace QgFamily

variable (F : QgFamily)

/-- The relative-bound constant of the family. -/
def flK : ℝ := 3 / 2 * F.km + 4 * (F.a * F.b)

/-- The Faris–Lavine commutator constant of the family. -/
def flc : ℝ := F.km / 2 + 2 * (F.a * F.b)

theorem ab_nonneg : 0 ≤ F.a * F.b := mul_nonneg F.a_nonneg F.b_nonneg

theorem flK_nonneg : 0 ≤ F.flK := by
  have h := F.ab_nonneg
  have := F.km_nonneg
  rw [flK]; linarith



/-- **The `n`-particle Hamiltonian of the family**, on the Gauss–polynomial core of
`L²(ℝ^{84n})`. -/
def secHam (n : ℕ) : polyGaussCore (d := n * 84) →ₗ[ℂ] L2d (n * 84) :=
  sqSumOp (F.kap n) (F.vv n)





/-- **The relative bound**, with a constant uniform in the particle number. -/
theorem secHam_norm_le (n : ℕ) (u : polyGaussCore (d := n * 84)) :
    ‖F.secHam n u‖ ≤ F.flK * ‖QgHermiteOscillator.harmCore u + (u : L2d (n * 84))‖ := by
  have hB : ∀ x : Vd (n * 84), potFun (F.vv n) x ≤ (F.a * F.b / 2) * ‖x‖ ^ 2 :=
    fun x => potFun_le_of_schur F.a_nonneg (F.row_le n) (F.col_le n) x
  have hB0 : (0 : ℝ) ≤ F.a * F.b / 2 := by
    have := F.ab_nonneg; linarith
  have heq : 3 / 2 * F.km + 8 * (F.a * F.b / 2) = F.flK := by rw [flK]; ring
  rw [secHam, ← heq]
  exact norm_sqSumOp_le F.km_nonneg (F.kap_le n) hB0 hB u



/-! ## 2. The Hamiltonian on the outer Fock space -/

/-- **The Hamiltonian of the family on the finite-particle core of the outer Fock
space.** -/
def outerHam : qgOuterCore →ₗ[ℂ] QgOuterFock.qgOuterFock := dsOp (fun n : ℕ => F.secHam n)





/-- The Faris–Lavine core data of the `n`-particle Hamiltonian. -/
def secData (n : ℕ) : CoreData (L2d (n * 84)) where
  C := harmFried (n * 84)
  C₀ := polyGaussCore (d := n * 84)
  gc := harmFried_isGraphCore (n * 84)
  H₀ := F.secHam n
  K := F.flK
  hK := F.flK_nonneg
  rel := by
    intro p
    rw [harmFried_op_core (n * 84) p]
    exact F.secHam_norm_le n p

/-- The `n`-particle Hamiltonian, extended from the Gauss–polynomial core to the whole
domain of the sector comparison operator. -/
def secExt (n : ℕ) : (harmFried (n * 84)).dom →ₗ[ℂ] L2d (n * 84) := (F.secData n).ext













end QgFamily

/-! ## 3. The nearest-neighbour successor of a particle -/

/-- The cyclic successor of a particle index. -/
def nextPart {n : ℕ} (p : Fin n) : Fin n :=
  if h : p.val + 1 < n then ⟨p.val + 1, h⟩
  else ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le p.val) p.isLt⟩

theorem nextPart_val {n : ℕ} (p : Fin n) :
    (nextPart p).val = if p.val + 1 < n then p.val + 1 else 0 := by
  unfold nextPart; split_ifs <;> rfl

theorem nextPart_injective {n : ℕ} : Function.Injective (nextPart (n := n)) := by
  intro p q h
  have hp := p.isLt
  have hq := q.isLt
  have hv := congrArg Fin.val h
  rw [nextPart_val, nextPart_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The cyclic successor as an equivalence, used to reindex sums over particles. -/
def nextEquiv {n : ℕ} : Fin n ≃ Fin n :=
  Equiv.ofBijective nextPart (Finite.injective_iff_bijective.mp nextPart_injective)

@[simp] theorem nextEquiv_apply {n : ℕ} (p : Fin n) : nextEquiv p = nextPart p := rfl

theorem sum_comp_nextPart {n : ℕ} {M : Type*} [AddCommMonoid M] (f : Fin n → M) :
    ∑ p : Fin n, f (nextPart p) = ∑ p : Fin n, f p :=
  Equiv.sum_comp nextEquiv f



/-! ## 4. The interacting gravity family -/

/-- **The nearest-neighbour torsion coupling.**  The `m`-th coupling form of particle `p`
is `lam·(T_m^{(p)} − T_m^{(p+1)})`; it mixes the coordinates of two different
particles. -/
def qgCouplingVec (lam : ℝ) (n : ℕ) (r : Fin n × Fin 64) (I : Fin (n * 84)) : ℝ :=
  lam * (qgTorsionVecN n r I - qgTorsionVecN n (nextPart r.1, r.2) I)

/-- The full family of linear forms of the interacting gravity Hamiltonian: the torsion
forms of every particle, and the nearest-neighbour coupling forms. -/
def qgIntVec (lam : ℝ) (n : ℕ) :
    (Fin n × Fin 64) ⊕ (Fin n × Fin 64) → Fin (n * 84) → ℝ :=
  Sum.elim (qgTorsionVecN n) (qgCouplingVec lam n)

theorem qgCouplingVec_row_le (lam : ℝ) (n : ℕ) (r : Fin n × Fin 64) :
    ∑ I : Fin (n * 84), |qgCouplingVec lam n r I| ≤ 4 * |lam| := by
  have hterm : ∀ I : Fin (n * 84), |qgCouplingVec lam n r I|
      ≤ |lam| * (|qgTorsionVecN n r I| + |qgTorsionVecN n (nextPart r.1, r.2) I|) := by
    intro I
    rw [qgCouplingVec, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg lam)
  calc ∑ I : Fin (n * 84), |qgCouplingVec lam n r I|
      ≤ ∑ I : Fin (n * 84),
          |lam| * (|qgTorsionVecN n r I| + |qgTorsionVecN n (nextPart r.1, r.2) I|) :=
        Finset.sum_le_sum fun I _ => hterm I
    _ = |lam| * ((∑ I : Fin (n * 84), |qgTorsionVecN n r I|)
          + ∑ I : Fin (n * 84), |qgTorsionVecN n (nextPart r.1, r.2) I|) := by
        rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ |lam| * (2 + 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg lam)
        have h1 := qgTorsionVecN_row_le n r
        have h2 := qgTorsionVecN_row_le n (nextPart r.1, r.2)
        linarith
    _ = 4 * |lam| := by ring

theorem sum_torsion_col_next (n : ℕ) (I : Fin (n * 84)) :
    ∑ r : Fin n × Fin 64, |qgTorsionVecN n (nextPart r.1, r.2) I| ≤ 64 := by
  have hsplit : ∑ r : Fin n × Fin 64, |qgTorsionVecN n (nextPart r.1, r.2) I|
      = ∑ p : Fin n, ∑ m : Fin 64, |qgTorsionVecN n (nextPart p, m) I| :=
    Fintype.sum_prod_type (fun r : Fin n × Fin 64 => |qgTorsionVecN n (nextPart r.1, r.2) I|)
  have hre : ∑ p : Fin n, ∑ m : Fin 64, |qgTorsionVecN n (nextPart p, m) I|
      = ∑ p : Fin n, ∑ m : Fin 64, |qgTorsionVecN n (p, m) I| :=
    sum_comp_nextPart (fun q : Fin n => ∑ m : Fin 64, |qgTorsionVecN n (q, m) I|)
  have hfin : ∑ p : Fin n, ∑ m : Fin 64, |qgTorsionVecN n (p, m) I|
      = ∑ r : Fin n × Fin 64, |qgTorsionVecN n r I| :=
    (Fintype.sum_prod_type (fun r : Fin n × Fin 64 => |qgTorsionVecN n r I|)).symm
  rw [hsplit, hre, hfin]
  exact qgTorsionVecN_col_le n I

theorem qgCouplingVec_col_le (lam : ℝ) (n : ℕ) (I : Fin (n * 84)) :
    ∑ r : Fin n × Fin 64, |qgCouplingVec lam n r I| ≤ 128 * |lam| := by
  have hterm : ∀ r : Fin n × Fin 64, |qgCouplingVec lam n r I|
      ≤ |lam| * (|qgTorsionVecN n r I| + |qgTorsionVecN n (nextPart r.1, r.2) I|) := by
    intro r
    rw [qgCouplingVec, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg lam)
  calc ∑ r : Fin n × Fin 64, |qgCouplingVec lam n r I|
      ≤ ∑ r : Fin n × Fin 64,
          |lam| * (|qgTorsionVecN n r I| + |qgTorsionVecN n (nextPart r.1, r.2) I|) :=
        Finset.sum_le_sum fun r _ => hterm r
    _ = |lam| * ((∑ r : Fin n × Fin 64, |qgTorsionVecN n r I|)
          + ∑ r : Fin n × Fin 64, |qgTorsionVecN n (nextPart r.1, r.2) I|) := by
        rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ |lam| * (64 + 64) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg lam)
        have h1 := qgTorsionVecN_col_le n I
        have h2 := sum_torsion_col_next n I
        linarith
    _ = 128 * |lam| := by ring

theorem qgIntVec_row_le (lam : ℝ) (n : ℕ) (r : (Fin n × Fin 64) ⊕ (Fin n × Fin 64)) :
    ∑ I : Fin (n * 84), |qgIntVec lam n r I| ≤ 2 + 4 * |lam| := by
  have hl : (0 : ℝ) ≤ |lam| := abs_nonneg lam
  cases r with
  | inl s =>
      have h := qgTorsionVecN_row_le n s
      have he : ∀ I : Fin (n * 84), qgIntVec lam n (Sum.inl s) I = qgTorsionVecN n s I :=
        fun _ => rfl
      simp only [he]
      linarith
  | inr s =>
      have h := qgCouplingVec_row_le lam n s
      have he : ∀ I : Fin (n * 84), qgIntVec lam n (Sum.inr s) I = qgCouplingVec lam n s I :=
        fun _ => rfl
      simp only [he]
      linarith

theorem qgIntVec_col_le (lam : ℝ) (n : ℕ) (I : Fin (n * 84)) :
    ∑ r : (Fin n × Fin 64) ⊕ (Fin n × Fin 64), |qgIntVec lam n r I| ≤ 64 + 128 * |lam| := by
  rw [Fintype.sum_sum_type]
  have h1 : ∑ s : Fin n × Fin 64, |qgIntVec lam n (Sum.inl s) I|
      = ∑ s : Fin n × Fin 64, |qgTorsionVecN n s I| := rfl
  have h2 : ∑ s : Fin n × Fin 64, |qgIntVec lam n (Sum.inr s) I|
      = ∑ s : Fin n × Fin 64, |qgCouplingVec lam n s I| := rfl
  rw [h1, h2]
  have ha := qgTorsionVecN_col_le n I
  have hb := qgCouplingVec_col_le lam n I
  linarith

/-- **The interacting gauge-fixed 3D quantum-gravity family**: the physical hyperbolic
signature `qgKappa` in every particle's block, all `64` torsion forms of every particle,
and the nearest-neighbour torsion couplings of strength `lam`. -/
def qgIntFamily (lam : ℝ) : QgFamily where
  R n := (Fin n × Fin 64) ⊕ (Fin n × Fin 64)
  kap := qgKappaN
  vv := qgIntVec lam
  km := 1 / 16
  a := 2 + 4 * |lam|
  b := 64 + 128 * |lam|
  km_nonneg := by norm_num
  a_nonneg := by have := abs_nonneg lam; linarith
  b_nonneg := by have := abs_nonneg lam; linarith
  kap_le := qgKappaN_abs_le
  row_le := qgIntVec_row_le lam
  col_le := qgIntVec_col_le lam





/-! ## 5. Non-vacuity: the couplings really do mix two particles -/









end

end BookProof.QgOuterFockInteractionFL


