-- Prove2me | Definitions.Def_ChapterFockDifferingBasesEsa
-- name    : ChapterFockDifferingBasesEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-04T04:43:01.837942+00:00
-- url     : https://prove2.me/theorems/688cf32b-3d72-4103-a51d-649dd8f6af3c
-- title:
--   Chapter FockDifferingBasesEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFockDifferingBasesEsa.lean`): generated def bundle for ChapterFockDifferingBasesEsa. See BookProof/ChapterFockDifferingBasesEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFockDifferingBasesEsa.lean

import Theorems.Thm_BookProof_OperatorSeries_commForm_add

import Theorems.Thm_BookProof_OperatorSeries_commForm_eq_neg_two_im

import Theorems.Thm_BookProof_OperatorSeries_essentiallySelfAdjointOn_finiteModes_of_bounds

import Theorems.Thm_BookProof_OperatorSeries_seriesOp_commForm_le

import Theorems.Thm_BookProof_OperatorSeries_seriesOp_norm_le

import Theorems.Thm_BookProof_OperatorSeries_seriesOp_symmetricOn

import Theorems.Thm_BookProof_FockQuadratic_freeOp_symmetricOn

import Theorems.Thm_BookProof_FockQuadratic_freeOp_commForm

import Theorems.Thm_BookProof_FockQuadratic_freeOp_norm_le

import Theorems.Thm_BookProof_FockQuadratic_sig_tgt

import Theorems.Thm_BookProof_FockQuadratic_pairOp_symmetricOn

import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_quadForm_nonneg

import Theorems.Thm_BookProof_FockQuadratic_wsum_add

import Theorems.Thm_BookProof_FockQuadratic_wsum_single

import Theorems.Thm_BookProof_FockQuadratic_wsum_tsub_of_le

import Definitions.Def_ChapterCarlemanSimplex

import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Mathlib


/-!
# Sums of one-particle Hamiltonians in *differing* bases: Faris–Lavine with a diagonal `N`

`DESIGN_QG32_FARISLAVINE_DIFFERING_BASES.md` (plan item **QG-3.2-exec** of
`CONSOLIDATED_PLAN.md`) asks for the essential self-adjointness of a coupling

```text
H = ∑_ℓ dΓ(h_ℓ),
```

where each one-particle Hamiltonian `h_ℓ` is Hermitian and diagonalizable **in its own
basis**, so that no single alphabet diagonalizes the sum.  `ChapterQgCouplingDGammaSum`
settled the case in which the *total* one-particle operator happens to be diagonal in the
working basis.  This module removes that restriction, in the direction the design
identifies as the substance of the problem: the summands are genuinely non-diagonal, they
do not commute, and the comparison operator stays **diagonal**.

The mechanism is the one the physics dictates: a Hamiltonian built from one-particle
operators **conserves the particle number**, so it commutes with the number operator
exactly.  Faris–Lavine (Nelson's commutator theorem) then applies with the positive
diagonal comparison operator `N = dΓ(ω) + 𝒩 + 1` and commutator constant `c = 0`; the
non-commutativity of the summands never enters, because the commutator that has to be
estimated is the one with `N`, not the ones among the summands.

## The hop-conservation hypothesis

`ChapterFockQuadraticEsa` builds every quadratic monomial `a^{†P}a^{Q}` on the maximal
domain of the comparison symbol `σ(α) = ω(α) + |α| + 1` and proves the general estimate
`|commForm (pairOp g P Q) N| ≤ 4‖g‖(ω(P) + ω(Q) + 2)·quadForm N`, whose constant is what
forces the weighted `ℓ¹` gate `∑ₖ ‖gₖ‖(ω(Pₖ) + ω(Qₖ) + 2) < ∞` of that chapter.  Here we
observe that the constant is `0` — the commutator form vanishes *identically* — as soon as
the hop is **balanced**:

```text
Balanced ω P Q :  ω(P) + |P| = ω(Q) + |Q|,
```

which is exactly the statement that the comparison symbol is unchanged along the hop,
`σ(β − P + Q) = σ(β)`.  Number-conserving exchange terms `a_p†a_q` with `ω p = ω q` — in
particular *all* exchange terms when the free dispersion is absent — are balanced.

## What is proved

* `Balanced`, `sig_tgt_eq_of_balanced` — the balance condition and its meaning.
* **`pairOp_commForm_eq_zero`** — a balanced Hermitian monomial has *identically vanishing*
  commutator form against the diagonal comparison operator.  (The proof identifies the two
  matrix elements of the Hermitian pair as complex conjugates of each other.)
* `xIdx`, `balanced_xIdx` — the exchange (number-conserving) monomials `a_p†a_q` and their
  balance under resonance `ω p = ω q`.
* `balancedH`, `balancedH_symmetricOn`, `balancedH_norm_le`,
  **`balancedH_commForm_eq_zero`**, **`balancedH_essentiallySelfAdjointOn_core`** — the free
  Hamiltonian plus an arbitrary family of balanced Hermitian couplings is symmetric,
  relatively bounded by `N`, commutes with `N` exactly, and is therefore essentially
  self-adjoint on the finite-particle core under the *unweighted* gate `∑ₖ ‖gₖ‖ < ∞`.  This
  is strictly weaker than the weighted gate of `ChapterFockQuadraticEsa`: however large the
  dispersion `ω`, balanced couplings need no `ω`-weights.
* `exchangeH`, **`exchangeH_essentiallySelfAdjointOn_core`** — the number-conserving
  specialization: hops `gₖ a_{pₖ}†a_{qₖ} + conj(gₖ) a_{qₖ}†a_{pₖ}` on top of an arbitrary
  non-negative dispersion, resonant mode by mode.
* `specEntry`, `specAmp`, `summable_specAmp`,
  **`spectralFamily_essentiallySelfAdjointOn_core`** — the differing-bases headline: a
  family of one-particle Hermitian operators `h_ℓ = ∑_r λ_{ℓr} |v_{ℓr}⟩⟨v_{ℓr}|`, each
  presented in **its own** eigenbasis and none of them diagonal in the working alphabet, is
  essentially self-adjoint on the finite-particle core as soon as
  `∑_{ℓ,r} |λ_{ℓr}|·‖v_{ℓr}‖₁² < ∞`; for finitely many finitely-supported eigenvectors — the
  case of a concrete finite-dimensional coefficient algebra — the gate is automatic
  (`spectralFamily_finite_essentiallySelfAdjointOn_core`), and
  `sumOfTwo_essentiallySelfAdjointOn_core` is the two-summand case in closed form.
* `specEntry_ne_zero`, `specEntry_not_commute` — non-vacuity: the summands covered are
  genuinely non-diagonal in the working alphabet and genuinely non-commuting.
* `nestedFock_essentiallySelfAdjointOn_core` — the same statement when the one-particle
  space is itself a Fock space (`ι := Idx ι₀`), i.e. a nested Fock space with an
  outer-number-conserving Hamiltonian.

## Honest boundary

The comparison operator is diagonal and the commutator constant is `0`; what the coupling
family must still satisfy is the *unweighted* summability `∑ₖ ‖gₖ‖ < ∞` of its matrix
elements in the working alphabet, which is what makes the series of monomials converge on
the maximal domain and gives the relative bound.  Nothing here asserts essential
self-adjointness of `dΓ(h)` for an arbitrary bounded, non-`ℓ¹` one-particle `h`, and
nothing here computes a spectrum.  The operators are the monomial series of
`ChapterFockQuadraticEsa` on `ℓ²(ι →₀ ℕ)`; the identification with the algebraic `dΓ` of
`ChapterFockSecondQuantization` is not carried out (the two chapters use different models
of the same Fock space).

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.FockDifferingBases

open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries BookProof.FockQuadratic

noncomputable section

variable {ι κ : Type*} {ω : ι → ℝ}

/-! ## 0. The served facts this bundle stands on

`wsum_add`, `wsum_tsub_of_le` and `sig_tgt` are declared by the served
`Def_ChapterFockQuadraticEsa` bundle as definitions and by its published theorem modules as
statements; `commForm_add`, `commForm_eq_neg_two_im`, `freeOp_symmetricOn`, `freeOp_norm_le`
and `essentiallySelfAdjointOn_finiteModes_of_bounds` live only in the latter (the served
`Def_ChapterOperatorSeriesEsa` and `Def_ChapterFockQuadraticEsa` carry their definitions but
none of their API).  All eight are published modules this bundle imports; nothing is restated
here, so there is exactly one provider per name.
-/

/-! ## 1. Balanced hops -/

/-- **A balanced hop**: the monomial `a^{†P}a^{Q}` moves the comparison symbol
`σ(α) = ω(α) + |α| + 1` by `ω(Q) + |Q| − ω(P) − |P|`, so it leaves it unchanged exactly
when `ω(P) + |P| = ω(Q) + |Q|`.  Number-conserving, energy-resonant hops are balanced. -/
def Balanced (ω : ι → ℝ) (P Q : Idx ι) : Prop :=
  wsum ω P + (deg P : ℝ) = wsum ω Q + (deg Q : ℝ)

/-- A balanced hop conserves the comparison symbol. -/
theorem sig_tgt_eq_of_balanced {P Q : Idx ι} (h : Balanced ω P Q) {b : Idx ι} (hb : P ≤ b) :
    sig ω (tgt P Q b) = sig ω b := by
  rw [sig_tgt hb]
  unfold Balanced at h
  linarith

/-! ## 2. A balanced Hermitian monomial commutes with the comparison operator -/

/-- **The key vanishing.**  For a balanced hop the Hermitian combination
`g a^{†P}a^{Q} + conj(g) a^{†Q}a^{P}` has *identically zero* commutator form against the
diagonal comparison operator: the two matrix elements `⟪a^{†P}a^{Q}x, Nx⟫` and
`⟪a^{†Q}a^{P}x, Nx⟫` are complex conjugates of each other, so the Hermitian combination has
a real matrix element. -/
theorem pairOp_commForm_eq_zero (hω : ∀ i, 0 ≤ ω i) (g : ℂ) (P Q : Idx ι)
    (hPQ : deg P + deg Q ≤ 2) (hbal : Balanced ω P Q) (x : maxDom (sig ω)) :
    commForm (pairOp hω g P Q hPQ) (diagMax (sig ω)) x = 0 := by
  classical
  have hQP : deg Q + deg P ≤ 2 := by omega
  set xb : Idx ι → ℂ := ((x : L2I (Idx ι)) : Idx ι → ℂ) with hxb
  set t : Idx ι → ℂ := hopT P Q xb with htdef
  set A : ℂ := inner ℂ (hopOp hω P Q hPQ x : L2I (Idx ι))
    (diagMax (sig ω) x : L2I (Idx ι)) with hAdef
  set B : ℂ := inner ℂ (hopOp hω Q P hQP x : L2I (Idx ι))
    (diagMax (sig ω) x : L2I (Idx ι)) with hBdef
  have hA : HasSum (fun b : {b : Idx ι // P ≤ b} =>
      (sig ω (b : Idx ι) : ℂ) * t (b : Idx ι)) A := by
    have h := lp.hasSum_inner (𝕜 := ℂ) (hopOp hω P Q hPQ x : L2I (Idx ι))
      (diagMax (sig ω) x : L2I (Idx ι))
    have hvan : ∀ b : Idx ι, b ∉ Set.range (Subtype.val : {b : Idx ι // P ≤ b} → Idx ι) →
        (inner ℂ (((hopOp hω P Q hPQ x : L2I (Idx ι)) : Idx ι → ℂ) b)
          (((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) b) : ℂ) = 0 := by
      intro b hb
      have hnp : ¬ P ≤ b := fun hle => hb ⟨⟨b, hle⟩, rfl⟩
      simp [RCLike.inner_apply, amp_eq_zero_of_not_le hnp]
    have h2 := ((Subtype.coe_injective (p := fun b : Idx ι => P ≤ b)).hasSum_iff hvan).mpr h
    refine h2.congr_fun ?_
    intro b
    simp only [Function.comp_apply, RCLike.inner_apply, hopOp_coe, diagMax_coe, htdef, hopT,
      map_mul, Complex.conj_ofReal, hxb]
    ring
  have hB : HasSum (fun b : {b : Idx ι // P ≤ b} =>
      (sig ω (tgt P Q (b : Idx ι)) : ℂ) * (starRingEnd ℂ) (t (b : Idx ι))) B := by
    have h := lp.hasSum_inner (𝕜 := ℂ) (hopOp hω Q P hQP x : L2I (Idx ι))
      (diagMax (sig ω) x : L2I (Idx ι))
    have hvan : ∀ a : Idx ι,
        a ∉ Set.range (fun b : {b : Idx ι // P ≤ b} => tgt P Q (b : Idx ι)) →
        (inner ℂ (((hopOp hω Q P hQP x : L2I (Idx ι)) : Idx ι → ℂ) a)
          (((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) a) : ℂ) = 0 := by
      intro a ha
      have hnq : ¬ Q ≤ a := fun hle => ha ⟨⟨tgt Q P a, le_tgt Q P a⟩, tgt_tgt hle⟩
      simp [RCLike.inner_apply, amp_eq_zero_of_not_le hnq]
    have h2 := ((hop_injective P Q).hasSum_iff hvan).mpr h
    refine h2.congr_fun ?_
    intro b
    simp only [Function.comp_apply, RCLike.inner_apply, hopOp_coe, diagMax_coe]
    rw [amp_symm b.2, tgt_tgt b.2]
    simp only [htdef, hopT, map_mul, Complex.conj_ofReal, Complex.conj_conj, hxb]
    ring
  -- with the balance hypothesis the second sum is the conjugate of the first
  have hBconj : B = (starRingEnd ℂ) A := by
    refine hB.unique ?_
    have hstar := hA.star
    refine hstar.congr_fun ?_
    intro b
    rw [sig_tgt_eq_of_balanced hbal b.2]
    simp [RCLike.star_def, Complex.conj_ofReal]
  have hinner : (inner ℂ (pairOp hω g P Q hPQ x : L2I (Idx ι))
      (diagMax (sig ω) x : L2I (Idx ι)) : ℂ) = (starRingEnd ℂ) g * A + g * B := by
    simp only [pairOp, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_smul_left,
      hAdef, hBdef, Complex.conj_conj]
  have hreal : ((starRingEnd ℂ) g * A + g * B).im = 0 := by
    rw [hBconj]
    have hrw : (starRingEnd ℂ) g * A + g * (starRingEnd ℂ) A
        = ((starRingEnd ℂ) g * A) + (starRingEnd ℂ) ((starRingEnd ℂ) g * A) := by
      simp [map_mul]
    rw [hrw, Complex.add_conj]
    simp
  rw [commForm_eq_neg_two_im, hinner, hreal]
  ring

/-! ## 3. Exchange (number-conserving) monomials -/

/-- The one-particle multi-index of the mode `p`. -/
def xIdx (p : ι) : Idx ι := Finsupp.single p 1

@[simp] theorem deg_xIdx (p : ι) : deg (xIdx p) = 1 := deg_single p 1

@[simp] theorem wsum_xIdx (ω : ι → ℝ) (p : ι) : wsum ω (xIdx p) = ω p := by
  simp [xIdx, wsum_single]

theorem deg_xIdx_add (p q : ι) : deg (xIdx q) + deg (xIdx p) = 2 := by simp

/-- **Exchange hops are balanced when they are resonant**: `a_p†a_q` conserves the
comparison symbol as soon as the two modes carry the same free energy — in particular
always, if there is no free dispersion. -/
theorem balanced_xIdx {p q : ι} (h : ω p = ω q) : Balanced ω (xIdx q) (xIdx p) := by
  simp [Balanced, h]

/-! ## 4. The Hamiltonian: free part plus a family of balanced couplings -/

/-- The family of Hermitian coupling terms. -/
def couplingT (hω : ∀ i, 0 ≤ ω i) (P Q : κ → Idx ι) (g : κ → ℂ)
    (hPQ : ∀ k, deg (P k) + deg (Q k) ≤ 2) :
    κ → (maxDom (sig ω) →ₗ[ℂ] L2I (Idx ι)) :=
  fun k => pairOp hω (g k) (P k) (Q k) (hPQ k)

theorem couplingT_norm_le (hω : ∀ i, 0 ≤ ω i) (P Q : κ → Idx ι) (g : κ → ℂ)
    (hPQ : ∀ k, deg (P k) + deg (Q k) ≤ 2) (k : κ) (x : maxDom (sig ω)) :
    ‖(couplingT hω P Q g hPQ k x : L2I (Idx ι))‖
      ≤ (4 * ‖g k‖) * ‖(diagMax (sig ω) x : L2I (Idx ι))‖ :=
  pairOp_norm_le hω (g k) (P k) (Q k) (hPQ k) x

/-- **The Hamiltonian**: the free dispersion `∑ᵢ ωᵢ aᵢ†aᵢ` plus an absolutely summable
family of Hermitian coupling monomials.  No weights appear in the summability hypothesis:
for balanced couplings the plain `ℓ¹` bound on the amplitudes suffices. -/
def balancedH (hω : ∀ i, 0 ≤ ω i) (P Q : κ → Idx ι) (g : κ → ℂ)
    (hPQ : ∀ k, deg (P k) + deg (Q k) ≤ 2) (hsum : Summable fun k => ‖g k‖) :
    maxDom (sig ω) →ₗ[ℂ] L2I (Idx ι) :=
  freeOp hω +
    seriesOp (couplingT hω P Q g hPQ) (fun k => 4 * ‖g k‖)
      (couplingT_norm_le hω P Q g hPQ) (hsum.mul_left 4)

theorem balancedH_symmetricOn (hω : ∀ i, 0 ≤ ω i) (P Q : κ → Idx ι) (g : κ → ℂ)
    (hPQ : ∀ k, deg (P k) + deg (Q k) ≤ 2) (hsum : Summable fun k => ‖g k‖) :
    SymmetricOn (maxDom (sig ω)) (balancedH hω P Q g hPQ hsum) := by
  intro x y
  have h1 := freeOp_symmetricOn hω x y
  have h2 := seriesOp_symmetricOn (couplingT_norm_le hω P Q g hPQ) (hsum.mul_left 4)
    (fun k => pairOp_symmetricOn hω (g k) (P k) (Q k) (hPQ k)) x y
  simp only [balancedH, LinearMap.add_apply, inner_add_left, inner_add_right, h1, h2]

/-- **The relative bound** against the diagonal comparison operator. -/
theorem balancedH_norm_le (hω : ∀ i, 0 ≤ ω i) (P Q : κ → Idx ι) (g : κ → ℂ)
    (hPQ : ∀ k, deg (P k) + deg (Q k) ≤ 2) (hsum : Summable fun k => ‖g k‖)
    (x : maxDom (sig ω)) :
    ‖(balancedH hω P Q g hPQ hsum x : L2I (Idx ι))‖
      ≤ (1 + ∑' k, 4 * ‖g k‖) * ‖(diagMax (sig ω) x : L2I (Idx ι))‖ := by
  have h1 := freeOp_norm_le hω x
  have h2 := seriesOp_norm_le (couplingT_norm_le hω P Q g hPQ) (hsum.mul_left 4) x
  have hn : (0 : ℝ) ≤ ‖(diagMax (sig ω) x : L2I (Idx ι))‖ := norm_nonneg _
  have hadd : ‖(balancedH hω P Q g hPQ hsum x : L2I (Idx ι))‖
      ≤ ‖(freeOp hω x : L2I (Idx ι))‖
        + ‖(seriesOp (couplingT hω P Q g hPQ) (fun k => 4 * ‖g k‖)
              (couplingT_norm_le hω P Q g hPQ) (hsum.mul_left 4) x : L2I (Idx ι))‖ := by
    simpa only [balancedH, LinearMap.add_apply] using
      norm_add_le (freeOp hω x : L2I (Idx ι))
        (seriesOp (couplingT hω P Q g hPQ) (fun k => 4 * ‖g k‖)
          (couplingT_norm_le hω P Q g hPQ) (hsum.mul_left 4) x : L2I (Idx ι))
  nlinarith [hadd, h1, h2]

/-- **The Faris–Lavine commutator hypothesis holds with constant `0`.**  A Hamiltonian all
of whose terms are balanced — in particular one built from particle-number-conserving
one-particle Hamiltonians — commutes exactly with the diagonal comparison operator. -/
theorem balancedH_commForm_eq_zero (hω : ∀ i, 0 ≤ ω i) (P Q : κ → Idx ι) (g : κ → ℂ)
    (hPQ : ∀ k, deg (P k) + deg (Q k) ≤ 2) (hsum : Summable fun k => ‖g k‖)
    (hbal : ∀ k, Balanced ω (P k) (Q k)) (x : maxDom (sig ω)) :
    commForm (balancedH hω P Q g hPQ hsum) (diagMax (sig ω)) x = 0 := by
  have hc0 : ∀ b : Idx ι, 0 ≤ sig ω b := fun b => sig_nonneg hω b
  have hsplit := commForm_add (freeOp hω)
    (seriesOp (couplingT hω P Q g hPQ) (fun k => 4 * ‖g k‖)
      (couplingT_norm_le hω P Q g hPQ) (hsum.mul_left 4)) (diagMax (sig ω)) x
  have hfree := freeOp_commForm hω x
  have hser := seriesOp_commForm_le (couplingT_norm_le hω P Q g hPQ) (hsum.mul_left 4)
    (b := fun _ : κ => (0 : ℝ)) summable_zero
    (fun k y => by
      rw [couplingT, pairOp_commForm_eq_zero hω (g k) (P k) (Q k) (hPQ k) (hbal k) y]
      simp)
    (fun y => diagMax_quadForm_nonneg (sig ω) hc0 y) x
  simp only [tsum_zero, zero_mul, abs_nonpos_iff] at hser
  have : commForm (balancedH hω P Q g hPQ hsum) (diagMax (sig ω)) x
      = commForm (freeOp hω) (diagMax (sig ω)) x
        + commForm (seriesOp (couplingT hω P Q g hPQ) (fun k => 4 * ‖g k‖)
            (couplingT_norm_le hω P Q g hPQ) (hsum.mul_left 4)) (diagMax (sig ω)) x := hsplit
  rw [this, hfree, hser, add_zero]

/-- **Headline of the balanced case.**  The free Hamiltonian plus an arbitrary absolutely
summable family of *balanced* Hermitian quadratic couplings is essentially self-adjoint on
the finite-particle core of the Fock space.  The Faris–Lavine data are the diagonal
comparison operator `N = dΓ(ω) + 𝒩 + 1`, the relative bound `balancedH_norm_le`, and the
commutator constant `0`. -/
theorem balancedH_essentiallySelfAdjointOn_core (hω : ∀ i, 0 ≤ ω i) (P Q : κ → Idx ι)
    (g : κ → ℂ) (hPQ : ∀ k, deg (P k) + deg (Q k) ≤ 2) (hsum : Summable fun k => ‖g k‖)
    (hbal : ∀ k, Balanced ω (P k) (Q k)) :
    EssentiallySelfAdjointOn (lpFiniteModes (Idx ι))
      ((balancedH hω P Q g hPQ hsum).comp
        (Submodule.inclusion (finiteModes_le_maxDom (sig ω)))) := by
  refine essentiallySelfAdjointOn_finiteModes_of_bounds (sig ω) (fun b => sig_nonneg hω b)
    _ (1 + ∑' k, 4 * ‖g k‖) 0 le_rfl (balancedH_symmetricOn hω P Q g hPQ hsum)
    (balancedH_norm_le hω P Q g hPQ hsum) (fun x => ?_)
  rw [balancedH_commForm_eq_zero hω P Q g hPQ hsum hbal x]
  simp

/-! ## 5. The number-conserving specialization -/

/-- **The number-conserving Hamiltonian**: the free dispersion plus exchange couplings
`gₖ a_{qₖ}†a_{pₖ} + conj(gₖ) a_{pₖ}†a_{qₖ}`, one Hermitian pair of one-particle hops for
each index `k`. -/
def exchangeH (hω : ∀ i, 0 ≤ ω i) (p q : κ → ι) (g : κ → ℂ)
    (hsum : Summable fun k => ‖g k‖) : maxDom (sig ω) →ₗ[ℂ] L2I (Idx ι) :=
  balancedH hω (fun k => xIdx (q k)) (fun k => xIdx (p k)) g
    (fun k => le_of_eq (deg_xIdx_add (p k) (q k))) hsum

/-- The exchange Hamiltonian commutes exactly with the diagonal comparison operator. -/
theorem exchangeH_commForm_eq_zero (hω : ∀ i, 0 ≤ ω i) (p q : κ → ι) (g : κ → ℂ)
    (hsum : Summable fun k => ‖g k‖) (hres : ∀ k, ω (p k) = ω (q k))
    (x : maxDom (sig ω)) :
    commForm (exchangeH hω p q g hsum) (diagMax (sig ω)) x = 0 :=
  balancedH_commForm_eq_zero hω _ _ g _ hsum (fun k => balanced_xIdx (hres k)) x

/-- **Essential self-adjointness of a number-conserving Hamiltonian.**  Arbitrary
non-negative dispersion `ω`, arbitrary family of resonant exchange couplings, and the only
hypothesis on the amplitudes is the *unweighted* `∑ₖ ‖gₖ‖ < ∞`. -/
theorem exchangeH_essentiallySelfAdjointOn_core (hω : ∀ i, 0 ≤ ω i) (p q : κ → ι) (g : κ → ℂ)
    (hsum : Summable fun k => ‖g k‖) (hres : ∀ k, ω (p k) = ω (q k)) :
    EssentiallySelfAdjointOn (lpFiniteModes (Idx ι))
      ((exchangeH hω p q g hsum).comp
        (Submodule.inclusion (finiteModes_le_maxDom (sig ω)))) :=
  balancedH_essentiallySelfAdjointOn_core hω _ _ g _ hsum (fun k => balanced_xIdx (hres k))

/-! ## 6. Differing bases: a family of one-particle Hamiltonians, each in its own basis -/

/-- The matrix entry, in the working alphabet, of the one-particle operator
`lam · |v⟩⟨v|` — the rank-one Hermitian operator with eigenvalue `lam` and eigenvector `v`.
For a general `v` this matrix is **not** diagonal: the operator is diagonal in its own
basis only. -/
def specEntry (lam : ℝ) (v : ι → ℂ) (p q : ι) : ℂ :=
  (lam : ℂ) * (v p * (starRingEnd ℂ) (v q))

theorem specEntry_herm (lam : ℝ) (v : ι → ℂ) (p q : ι) :
    (starRingEnd ℂ) (specEntry lam v q p) = specEntry lam v p q := by
  simp only [specEntry, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

theorem norm_specEntry (lam : ℝ) (v : ι → ℂ) (p q : ι) :
    ‖specEntry lam v p q‖ = |lam| * (‖v p‖ * ‖v q‖) := by
  simp [specEntry, Complex.norm_real, Real.norm_eq_abs]

/-- The amplitude family of a spectral presentation: the index `k` runs over all
(operator, eigenvalue) pairs of the whole collection, and `(p, q)` over the working
alphabet.  The factor `1/2` is the Hermitian-pair convention of `pairOp`: the family
contains both `(p, q)` and `(q, p)`. -/
def specAmp (lam : κ → ℝ) (v : κ → ι → ℂ) : κ × ι × ι → ℂ :=
  fun z => specEntry (lam z.1 / 2) (v z.1) z.2.1 z.2.2

/-- **The gate for a spectral presentation.**  Absolute summability of the amplitudes is
implied by summability of `|λ|·‖v‖₁²` over the spectral data — a condition on each operator
*in its own basis*, with no reference to a common eigenbasis. -/
theorem summable_specAmp {lam : κ → ℝ} {v : κ → ι → ℂ}
    (hv : ∀ k, Summable fun p => ‖v k p‖)
    (hlam : Summable fun k => |lam k| * (∑' p, ‖v k p‖) ^ 2) :
    Summable fun z : κ × ι × ι => ‖specAmp lam v z‖ := by
  have hpt : ∀ z : κ × ι × ι, ‖specAmp lam v z‖
      = (|lam z.1| / 2) * (‖v z.1 z.2.1‖ * ‖v z.1 z.2.2‖) := by
    intro z
    rw [specAmp, norm_specEntry, abs_div]
    simp
  have hnn : (0 : κ × ι × ι → ℝ) ≤ fun z => ‖specAmp lam v z‖ := fun z => norm_nonneg _
  refine (summable_prod_of_nonneg hnn).mpr ⟨fun k => ?_, ?_⟩
  · have hprod : Summable fun w : ι × ι => ‖v k w.1‖ * ‖v k w.2‖ :=
      (hv k).mul_of_nonneg (hv k) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    refine ((hprod.mul_left (|lam k| / 2)).congr fun w => ?_)
    rw [hpt (k, w)]
  · have heq : ∀ k, (∑' w : ι × ι, ‖specAmp lam v (k, w)‖)
        = (|lam k| / 2) * (∑' p, ‖v k p‖) ^ 2 := by
      intro k
      have hprod : Summable fun w : ι × ι => ‖v k w.1‖ * ‖v k w.2‖ :=
        (hv k).mul_of_nonneg (hv k) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      have hmul : (∑' p, ‖v k p‖) * (∑' p, ‖v k p‖)
          = ∑' w : ι × ι, ‖v k w.1‖ * ‖v k w.2‖ :=
        tsum_mul_tsum_of_summable_norm (f := fun p => ‖v k p‖) (g := fun p => ‖v k p‖)
          (by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hv k)
          (by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hv k)
      calc (∑' w : ι × ι, ‖specAmp lam v (k, w)‖)
          = ∑' w : ι × ι, (|lam k| / 2) * (‖v k w.1‖ * ‖v k w.2‖) := by
            exact tsum_congr fun w => hpt (k, w)
        _ = (|lam k| / 2) * ∑' w : ι × ι, (‖v k w.1‖ * ‖v k w.2‖) := by
            rw [tsum_mul_left]
        _ = (|lam k| / 2) * (∑' p, ‖v k p‖) ^ 2 := by rw [← hmul]; ring
    refine ((hlam.mul_left (1 / 2)).congr fun k => ?_)
    rw [heq k]
    ring

/-- **The differing-bases headline.**  Let `{(λ_k, v_k)}` be the spectral data of a
collection of one-particle Hermitian operators — each operator contributing its own
eigenvalues and eigenvectors, with *no* common eigenbasis assumed and no relation between
the bases of different operators.  If `∑_k |λ_k|·‖v_k‖₁² < ∞`, then the number-conserving
monomial series whose amplitudes are the matrix entries of `∑_k λ_k |v_k⟩⟨v_k|` in the
working alphabet is essentially self-adjoint on the finite-particle core of the Fock space.

The comparison operator is the *diagonal* `𝒩 + 1`; the commutator form vanishes
identically because every term conserves the particle number. -/
theorem spectralFamily_essentiallySelfAdjointOn_core {lam : κ → ℝ} {v : κ → ι → ℂ}
    (hv : ∀ k, Summable fun p => ‖v k p‖)
    (hlam : Summable fun k => |lam k| * (∑' p, ‖v k p‖) ^ 2) :
    EssentiallySelfAdjointOn (lpFiniteModes (Idx ι))
      ((exchangeH (ω := fun _ : ι => (0 : ℝ)) (fun _ => le_rfl)
          (fun z : κ × ι × ι => z.2.1) (fun z => z.2.2) (specAmp lam v)
          (summable_specAmp hv hlam)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (sig (fun _ : ι => (0 : ℝ)))))) :=
  exchangeH_essentiallySelfAdjointOn_core _ _ _ _ _ (fun _ => rfl)

/-- For finitely many spectral components the gate is automatic. -/
theorem summable_specGate_of_finite [Finite κ] (lam : κ → ℝ) (v : κ → ι → ℂ) :
    Summable fun k => |lam k| * (∑' p, ‖v k p‖) ^ 2 := Summable.of_finite

/-- The finite case: finitely many one-particle operators with finitely many spectral
components each, every eigenvector `ℓ¹` in the working alphabet.  The gate is then
automatic — this is the situation of a concrete finite-dimensional coefficient algebra
whose blocks are diagonalized in mutually different bases. -/
theorem spectralFamily_finite_essentiallySelfAdjointOn_core [Finite κ] {lam : κ → ℝ}
    {v : κ → ι → ℂ} (hv : ∀ k, Summable fun p => ‖v k p‖) :
    EssentiallySelfAdjointOn (lpFiniteModes (Idx ι))
      ((exchangeH (ω := fun _ : ι => (0 : ℝ)) (fun _ => le_rfl)
          (fun z : κ × ι × ι => z.2.1) (fun z => z.2.2) (specAmp lam v)
          (summable_specAmp hv (summable_specGate_of_finite lam v))).comp
        (Submodule.inclusion (finiteModes_le_maxDom (sig (fun _ : ι => (0 : ℝ)))))) :=
  spectralFamily_essentiallySelfAdjointOn_core hv (summable_specGate_of_finite lam v)

/-- The two-element spectral family is `ℓ¹` mode by mode. -/
theorem summable_pairData {v₁ v₂ : ι → ℂ} (hv₁ : Summable fun p => ‖v₁ p‖)
    (hv₂ : Summable fun p => ‖v₂ p‖) (k : Fin 2) :
    Summable fun p => ‖(![v₁, v₂] : Fin 2 → ι → ℂ) k p‖ := by
  fin_cases k
  · simpa using hv₁
  · simpa using hv₂

/-- **The case the design asks about literally: a sum of two one-particle Hamiltonians
diagonal in different bases.**  `h₁ = λ₁|v₁⟩⟨v₁|` and `h₂ = λ₂|v₂⟩⟨v₂|` with unrelated
(and in general non-orthogonal, non-commuting) eigenvectors: the second quantization of
their sum is essentially self-adjoint on the finite-particle core. -/
theorem sumOfTwo_essentiallySelfAdjointOn_core (lam₁ lam₂ : ℝ) (v₁ v₂ : ι → ℂ)
    (hv₁ : Summable fun p => ‖v₁ p‖) (hv₂ : Summable fun p => ‖v₂ p‖) :
    EssentiallySelfAdjointOn (lpFiniteModes (Idx ι))
      ((exchangeH (ω := fun _ : ι => (0 : ℝ)) (fun _ => le_rfl)
          (fun z : Fin 2 × ι × ι => z.2.1) (fun z => z.2.2)
          (specAmp ![lam₁, lam₂] ![v₁, v₂])
          (summable_specAmp (summable_pairData hv₁ hv₂)
            (summable_specGate_of_finite _ _))).comp
        (Submodule.inclusion (finiteModes_le_maxDom (sig (fun _ : ι => (0 : ℝ)))))) :=
  spectralFamily_finite_essentiallySelfAdjointOn_core (summable_pairData hv₁ hv₂)

/-! ## 7. Non-vacuity: the summands really are non-diagonal and non-commuting -/

/-- A rank-one one-particle operator whose eigenvector is spread over two modes has
non-zero off-diagonal entries: it is **not** diagonal in the working alphabet. -/
theorem specEntry_ne_zero {lam : ℝ} {v : ι → ℂ} {p q : ι}
    (hlam : lam ≠ 0) (hp : v p ≠ 0) (hq : v q ≠ 0) : specEntry lam v p q ≠ 0 := by
  simp only [specEntry, ne_eq, mul_eq_zero, not_or]
  exact ⟨by simpa using hlam, hp, by simpa using hq⟩

/-- The product of two one-particle matrices. -/
def matMul [Fintype ι] (a b : ι → ι → ℂ) : ι → ι → ℂ := fun p q => ∑ r, a p r * b r q



/-! ## 8. Nested Fock spaces -/

/-- **Nested Fock spaces.**  Nothing in the argument constrains the one-particle index set,
so it may itself be the configuration set of an inner Fock space: with `ι := Idx ι₀` the
theorem reads as essential self-adjointness, on the outer finite-particle core, of a
Hamiltonian built from one-particle Hamiltonians of the inner Fock space, each diagonal in
its own basis.  The outer particle number is conserved, which is exactly what makes the
outer number operator an admissible Faris–Lavine comparison operator. -/
theorem nestedFock_essentiallySelfAdjointOn_core {ι₀ : Type*} {lam : κ → ℝ}
    {v : κ → Idx ι₀ → ℂ} (hv : ∀ k, Summable fun p => ‖v k p‖)
    (hlam : Summable fun k => |lam k| * (∑' p, ‖v k p‖) ^ 2) :
    EssentiallySelfAdjointOn (lpFiniteModes (Idx (Idx ι₀)))
      ((exchangeH (ω := fun _ : Idx ι₀ => (0 : ℝ)) (fun _ => le_rfl)
          (fun z : κ × Idx ι₀ × Idx ι₀ => z.2.1) (fun z => z.2.2) (specAmp lam v)
          (summable_specAmp hv hlam)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (sig (fun _ : Idx ι₀ => (0 : ℝ)))))) :=
  spectralFamily_essentiallySelfAdjointOn_core hv hlam

end

end BookProof.FockDifferingBases


