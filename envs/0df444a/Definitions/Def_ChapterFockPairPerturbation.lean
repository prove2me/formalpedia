-- Prove2me | Definitions.Def_ChapterFockPairPerturbation
-- name    : ChapterFockPairPerturbation
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-20T16:34:29.55998+00:00
-- url     : https://prove2.me/theorems/753119c7-e72b-4448-a3cf-98e2f2927063
-- title:
--   Chapter FockPairPerturbation
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFockPairPerturbation.lean`): generated def bundle for ChapterFockPairPerturbation. See BookProof/ChapterFockPairPerturbation.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFockPairPerturbation.lean

import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Mathlib
import Theorems.Thm_BookProof_FockSecondQuantization_ccr_annA_creA
import Theorems.Thm_BookProof_FockSecondQuantization_ccr_annA_creA_of_ne
import Theorems.Thm_BookProof_FockSecondQuantization_up_of_ne
import Theorems.Thm_BookProof_FockFieldPerturbation_annVec_apply
import Theorems.Thm_BookProof_FockSecondQuantization_creVec_apply
import Theorems.Thm_BookProof_FockFieldPerturbation_inner_creVec_annVec
import Theorems.Thm_BookProof_FockFieldPerturbation_numberQuad_nonneg
import Theorems.Thm_BookProof_FockFieldPerturbation_l2norm_nonneg
import Theorems.Thm_BookProof_FockFieldPerturbation_norm_annVec_le
import Theorems.Thm_BookProof_FockNumberPreservingGap_number_quadForm_ge
import Theorems.Thm_BookProof_FockFieldPerturbation_number_le_dGamma_quadForm
import Theorems.Thm_BookProof_YangMillsFockGapChain_isPosCol_shiftCol_opCol_of_form_gap
import Theorems.Thm_BookProof_FockOneParticleGap_norm_toLp_sq
import Theorems.Thm_BookProof_FockSecondQuantization_annA_apply
import Theorems.Thm_BookProof_FockSecondQuantization_creA_apply
import Theorems.Thm_BookProof_YangMillsFockGapChain_ym_isPosCol_shiftCol
import Theorems.Thm_BookProof_FockSecondQuantization_annA_single
import Theorems.Thm_BookProof_FockSecondQuantization_dn_up


/-!
# Chapter FockPairPerturbation — a *quadratic*, pair-creating unbounded perturbation

`ChapterFockFieldPerturbation` covers the coupling `Φ(f) = a†(f) + a(f)`, which is *linear*
in the creation/annihilation operators and changes the particle number by one.  The plan's
honest boundary recorded there is that Yang–Mills interaction terms are of higher degree in
the field, so the linear result does not reach them.

This chapter takes the next degree: the **pair operator**

  `P(f,g) = a†(f) a†(g) + a(g) a(f)`,

which is quadratic in the field, symmetric, unbounded, and changes the particle number by
*two* — it creates and destroys pairs, so neither the number-preserving lift of
`ChapterFockNumberPreservingGap` nor the bounded theory of
`ChapterFockInteractionStability` applies to it, and neither does the `N^{1/2}` estimate of
`ChapterFockFieldPerturbation`, which is not strong enough for a quadratic term.

## Deliverables

* `annA_creA` — the canonical commutation relation in the form
  `a_i a_j† = a_j† a_i + δ_ij`, and `annVec_creVec`, its vector form
  `a(g) a†(g) = a†(g) a(g) + ‖g‖²`;
* **`norm_creVec_sq`** — the resulting exact identity `‖a†(g)u‖² = ‖a(g)u‖² + ‖g‖²‖u‖²`, and
  **`norm_creVec_le`** — `‖a†(g)u‖ ≤ ‖g‖ (⟪u, N u⟫ + ‖u‖²)^{1/2}`, the `(N+1)^{1/2}` estimate
  that a quadratic term needs;
* **`abs_re_inner_pairVec_le`** — the form estimate
  `|Re⟪u, P(f,g)u⟫| ≤ 2‖f‖‖g‖ ⟪u,N u⟫^{1/2}(⟪u,N u⟫ + ‖u‖²)^{1/2}`;
* **`pairVec_relative_form_bound`** — the domination by the free form: on vacuum-orthogonal
  states, with a one-particle gap `h − μ ≥ 0` and `μ > 0`,
  `|Re⟪u, P(f,g)u⟫| ≤ (2√2‖f‖‖g‖/μ)·Re⟪u, dΓ(h)u⟫`.  Note the relative bound is
  *proportional to the coupling*, with no `‖u‖²` remainder: a pair term is form-bounded by
  the number operator with no additive constant on the vacuum-orthogonal sector;
* **`fock_gap_of_pair_perturbation`** — the conclusion: with `2√2‖f‖‖g‖ ≤ μ`, every
  vacuum-orthogonal finite-particle state has `dΓ(h) + P(f,g)` energy at least
  `(μ − 2√2‖f‖‖g‖)‖u‖²`; `fock_gap_of_pair_perturbation_pos` records strict positivity, and
  `fock_gap_of_one_particle_form_gap_pair` feeds it directly from the certificate chain's
  one-particle form gap;
* `pairVec_vac`, `pairVec_unbounded` — `P(f,g)` really does move the vacuum into the
  two-particle sector and really is unbounded;
* **`ym_fock_gap_of_pair_perturbation`** — the same conclusion for the concrete gauge-fixed
  Yang–Mills chain of `ChapterYangMillsFockGapChain`, conditional as always on the
  one-particle form gap on the Gauss–polynomial core.

## Honest boundary

`P(f,g)` is quadratic in the field.  The cubic and quartic Yang–Mills interaction terms are
still not covered, and the smallness condition `2√2‖f‖‖g‖ < μ` is a genuine restriction: a
large pair term can close the gap.  `1.932` remains a certified truncated number; no mass
gap of the physical Hamiltonian is claimed.

Everything is `sorry`-free and introduces no axioms.
-/

noncomputable section

namespace BookProof.FockSecondQuantization

/-- `creA_single` — the creation operator applied to a single basis vector.  The published
`Def_ChapterFockSecondQuantization` text predates this lemma, so it is restated here for
the consumer. -/
@[simp] theorem up_self (j : ℕ) (α : Conf) : up j α j = α j + 1 := by
  simp [up]

@[simp] theorem creA_single (j : ℕ) (β : Conf) (c : ℂ) :
    creA j (Finsupp.single β c)
      = c • Finsupp.single (up j β) ((Real.sqrt ((β j : ℝ) + 1) : ℝ) : ℂ) := by
  simp [creA, LinearMap.toSpanSingleton]

end BookProof.FockSecondQuantization

namespace BookProof.FockPairPerturbation

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.FockFieldPerturbation

/-! ## 1. The canonical commutation relation in vector form -/

/-- The canonical commutation relation `a_i a_j† = a_j† a_i + δ_ij`. -/
theorem annA_creA (i j : ℕ) (u : FockAlg) :
    annA i (creA j u) = creA j (annA i u) + (if i = j then u else 0) := by
  rcases eq_or_ne i j with rfl | h
  · have := ccr_annA_creA i u
    rw [if_pos rfl]
    linear_combination (norm := module) this
  · rw [if_neg h, add_zero, ccr_annA_creA_of_ne h]

/-- The squared `ℓ²` norm of a finitely supported one-particle vector. -/
def l2sq (g : ℕ →₀ ℂ) : ℝ := ∑ j ∈ g.support, ‖g j‖ ^ 2

theorem l2sq_nonneg (g : ℕ →₀ ℂ) : 0 ≤ l2sq g :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem l2norm_sq (g : ℕ →₀ ℂ) : l2norm g ^ 2 = l2sq g :=
  Real.sq_sqrt (l2sq_nonneg g)

/-- **The vector form of the canonical commutation relation**:
`a(g) a†(g) = a†(g) a(g) + ‖g‖²`. -/
theorem annVec_creVec (g : ℕ →₀ ℂ) (u : FockAlg) :
    annVec g (creVec g u) = creVec g (annVec g u) + ((l2sq g : ℝ) : ℂ) • u := by
  classical
  have hL : annVec g (creVec g u)
      = ∑ i ∈ g.support, ∑ j ∈ g.support,
          (((starRingEnd ℂ) (g i)) * g j)
            • (creA j (annA i u) + (if i = j then u else (0 : FockAlg))) := by
    rw [annVec_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [creVec_apply, map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_smul, annA_creA]
  have hR : creVec g (annVec g u)
      = ∑ i ∈ g.support, ∑ j ∈ g.support,
          (((starRingEnd ℂ) (g i)) * g j) • creA j (annA i u) := by
    rw [creVec_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [annVec_apply, map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_smul, mul_comm]
  have hdiag : ∑ i ∈ g.support, ∑ j ∈ g.support,
      (((starRingEnd ℂ) (g i)) * g j) • (if i = j then u else (0 : FockAlg))
        = ((l2sq g : ℝ) : ℂ) • u := by
    have hterm : ∀ i ∈ g.support, ∑ j ∈ g.support,
        (((starRingEnd ℂ) (g i)) * g j) • (if i = j then u else (0 : FockAlg))
          = ((‖g i‖ ^ 2 : ℝ) : ℂ) • u := by
      intro i hi
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, RCLike.conj_mul]
        norm_cast
      · intro j _ hj
        rw [if_neg (fun h : i = j => hj h.symm), smul_zero]
      · intro hi'; exact absurd hi hi'
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, l2sq]
    norm_cast
  calc annVec g (creVec g u)
      = ∑ i ∈ g.support, ∑ j ∈ g.support,
          ((((starRingEnd ℂ) (g i)) * g j) • creA j (annA i u)
            + (((starRingEnd ℂ) (g i)) * g j) • (if i = j then u else (0 : FockAlg))) := by
        rw [hL]
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => smul_add _ _ _
    _ = creVec g (annVec g u) + ((l2sq g : ℝ) : ℂ) • u := by
        rw [← hdiag, hR, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib

/-! ## 2. The `(N+1)^{1/2}` estimate for the creation operator -/

/-- `⟪a†(g) v, u⟫ = ⟪v, a(g) u⟫`, the mirror of `inner_creVec_annVec`. -/
theorem inner_creVec_left (g : ℕ →₀ ℂ) (v u : FockAlg) :
    (inner ℂ (toLp (creVec g v)) (toLp u) : ℂ) = inner ℂ (toLp v) (toLp (annVec g u)) := by
  have h := inner_creVec_annVec g u v
  have := congrArg (starRingEnd ℂ) h
  rwa [inner_conj_symm, inner_conj_symm] at this

/-- **The exact `a†`/`a` norm identity** `‖a†(g)u‖² = ‖a(g)u‖² + ‖g‖²‖u‖²`. -/
theorem norm_creVec_sq (g : ℕ →₀ ℂ) (u : FockAlg) :
    ‖toLp (creVec g u)‖ ^ 2 = ‖toLp (annVec g u)‖ ^ 2 + l2sq g * ‖toLp u‖ ^ 2 := by
  have hadd : ∀ a b : FockAlg, toLp (a + b) = toLp a + toLp b := fun a b => map_add toLpL a b
  have hsmul : ∀ (c : ℂ) (a : FockAlg), toLp (c • a) = c • toLp a := fun c a =>
    map_smul toLpL c a
  have key : (inner ℂ (toLp (creVec g u)) (toLp (creVec g u)) : ℂ)
      = inner ℂ (toLp (annVec g u)) (toLp (annVec g u))
        + ((l2sq g : ℝ) : ℂ) * inner ℂ (toLp u) (toLp u) := by
    rw [inner_creVec_annVec g (creVec g u) u, annVec_creVec g u, hadd, hsmul,
      inner_add_left, inner_smul_left, inner_creVec_left g (annVec g u) u,
      Complex.conj_ofReal]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at key
  have hcast : ((‖toLp (creVec g u)‖ ^ 2 : ℝ) : ℂ)
      = ((‖toLp (annVec g u)‖ ^ 2 + l2sq g * ‖toLp u‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact key
  exact_mod_cast hcast

/-- **The `(N+1)^{1/2}` estimate** `‖a†(g)u‖ ≤ ‖g‖ (⟪u, N u⟫ + ‖u‖²)^{1/2}`. -/
theorem norm_creVec_le (g : ℕ →₀ ℂ) (u : FockAlg) :
    ‖toLp (creVec g u)‖ ≤ l2norm g * Real.sqrt (numberQuad u + ‖toLp u‖ ^ 2) := by
  have hNq : 0 ≤ numberQuad u := numberQuad_nonneg u
  have hg : 0 ≤ l2norm g := l2norm_nonneg g
  have hid := norm_creVec_sq g u
  have hann := norm_annVec_le g u
  have hsq : Real.sqrt (numberQuad u) ^ 2 = numberQuad u := Real.sq_sqrt hNq
  have hsq2 : Real.sqrt (numberQuad u + ‖toLp u‖ ^ 2) ^ 2 = numberQuad u + ‖toLp u‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hannsq : ‖toLp (annVec g u)‖ ^ 2 ≤ l2sq g * numberQuad u := by
    have h0 : 0 ≤ ‖toLp (annVec g u)‖ := norm_nonneg _
    have := l2norm_sq g
    nlinarith [Real.sqrt_nonneg (numberQuad u)]
  have hle : ‖toLp (creVec g u)‖ ^ 2
      ≤ (l2norm g * Real.sqrt (numberQuad u + ‖toLp u‖ ^ 2)) ^ 2 := by
    rw [mul_pow, hsq2, l2norm_sq]
    nlinarith [l2sq_nonneg g, sq_nonneg (‖toLp u‖)]
  have hrhs : 0 ≤ l2norm g * Real.sqrt (numberQuad u + ‖toLp u‖ ^ 2) := by positivity
  nlinarith [norm_nonneg (toLp (creVec g u))]

/-! ## 3. The pair operator and its form estimate -/

/-- **The pair operator** `P(f,g) = a†(f) a†(g) + a(g) a(f)`: quadratic in the field, and
changing the particle number by two. -/
def pairVec (f g : ℕ →₀ ℂ) : FockAlg →ₗ[ℂ] FockAlg :=
  (creVec f).comp (creVec g) + (annVec g).comp (annVec f)

theorem pairVec_apply (f g : ℕ →₀ ℂ) (x : FockAlg) :
    pairVec f g x = creVec f (creVec g x) + annVec g (annVec f x) := rfl

/-- **The pair form estimate**
`|Re⟪u, P(f,g)u⟫| ≤ 2‖f‖‖g‖ ⟪u,N u⟫^{1/2} (⟪u,N u⟫ + ‖u‖²)^{1/2}`. -/
theorem abs_re_inner_pairVec_le (f g : ℕ →₀ ℂ) (u : FockAlg) :
    |(inner ℂ (toLp u) (toLp (pairVec f g u)) : ℂ).re|
      ≤ 2 * (l2norm f * l2norm g)
          * (Real.sqrt (numberQuad u) * Real.sqrt (numberQuad u + ‖toLp u‖ ^ 2)) := by
  have hadd : ∀ a b : FockAlg, toLp (a + b) = toLp a + toLp b := fun a b => map_add toLpL a b
  have hsplit : (inner ℂ (toLp u) (toLp (pairVec f g u)) : ℂ)
      = inner ℂ (toLp u) (toLp (creVec f (creVec g u)))
        + inner ℂ (toLp u) (toLp (annVec g (annVec f u))) := by
    rw [pairVec_apply, hadd, inner_add_right]
  have hbnd : ‖toLp (annVec f u)‖ * ‖toLp (creVec g u)‖
      ≤ l2norm f * l2norm g
          * (Real.sqrt (numberQuad u) * Real.sqrt (numberQuad u + ‖toLp u‖ ^ 2)) := by
    have h := mul_le_mul (norm_annVec_le f u) (norm_creVec_le g u) (norm_nonneg _)
      (mul_nonneg (l2norm_nonneg f) (Real.sqrt_nonneg _))
    calc ‖toLp (annVec f u)‖ * ‖toLp (creVec g u)‖
        ≤ (l2norm f * Real.sqrt (numberQuad u))
            * (l2norm g * Real.sqrt (numberQuad u + ‖toLp u‖ ^ 2)) := h
      _ = _ := by ring
  have h1 : |(inner ℂ (toLp u) (toLp (creVec f (creVec g u))) : ℂ).re|
      ≤ l2norm f * l2norm g
          * (Real.sqrt (numberQuad u) * Real.sqrt (numberQuad u + ‖toLp u‖ ^ 2)) := by
    rw [inner_creVec_annVec f u (creVec g u)]
    calc |(inner ℂ (toLp (annVec f u)) (toLp (creVec g u)) : ℂ).re|
        ≤ ‖(inner ℂ (toLp (annVec f u)) (toLp (creVec g u)) : ℂ)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖toLp (annVec f u)‖ * ‖toLp (creVec g u)‖ := norm_inner_le_norm _ _
      _ ≤ _ := hbnd
  have h2 : |(inner ℂ (toLp u) (toLp (annVec g (annVec f u))) : ℂ).re|
      ≤ l2norm f * l2norm g
          * (Real.sqrt (numberQuad u) * Real.sqrt (numberQuad u + ‖toLp u‖ ^ 2)) := by
    rw [← inner_creVec_left g u (annVec f u)]
    calc |(inner ℂ (toLp (creVec g u)) (toLp (annVec f u)) : ℂ).re|
        ≤ ‖(inner ℂ (toLp (creVec g u)) (toLp (annVec f u)) : ℂ)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖toLp (creVec g u)‖ * ‖toLp (annVec f u)‖ := norm_inner_le_norm _ _
      _ = ‖toLp (annVec f u)‖ * ‖toLp (creVec g u)‖ := mul_comm _ _
      _ ≤ _ := hbnd
  rw [hsplit, Complex.add_re]
  calc |(inner ℂ (toLp u) (toLp (creVec f (creVec g u))) : ℂ).re
          + (inner ℂ (toLp u) (toLp (annVec g (annVec f u))) : ℂ).re|
      ≤ |(inner ℂ (toLp u) (toLp (creVec f (creVec g u))) : ℂ).re|
        + |(inner ℂ (toLp u) (toLp (annVec g (annVec f u))) : ℂ).re| := abs_add_le _ _
    _ ≤ _ := by linarith

/-! ## 4. The relative form bound and the surviving gap -/

/-- **The pair term is relatively form bounded by the free energy, with no remainder.**  On
the vacuum-orthogonal sector, with a one-particle gap `h − μ ≥ 0` and `μ > 0`,
`|Re⟪u, P(f,g)u⟫| ≤ (2√2‖f‖‖g‖/μ)·Re⟪u, dΓ(h)u⟫`. -/
theorem pairVec_relative_form_bound {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 < mu)
    (hgap : IsPosCol (shiftCol col mu)) (f g : ℕ →₀ ℂ) {u : FockAlg} (h0 : u 0 = 0) :
    |(inner ℂ (toLp u) (toLp (pairVec f g u)) : ℂ).re|
      ≤ (2 * Real.sqrt 2 * (l2norm f * l2norm g) / mu)
          * (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re := by
  have hNq : 0 ≤ numberQuad u := numberQuad_nonneg u
  have hn : ‖toLp u‖ ^ 2 ≤ numberQuad u := number_quadForm_ge h0
  have hcf : 0 ≤ l2norm f := l2norm_nonneg f
  have hcg : 0 ≤ l2norm g := l2norm_nonneg g
  have hq := number_le_dGamma_quadForm hgap u
  have hsqrt2 : Real.sqrt (numberQuad u + ‖toLp u‖ ^ 2)
      ≤ Real.sqrt 2 * Real.sqrt (numberQuad u) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hprod : Real.sqrt (numberQuad u) * Real.sqrt (numberQuad u + ‖toLp u‖ ^ 2)
      ≤ Real.sqrt 2 * numberQuad u := by
    have hs : Real.sqrt (numberQuad u) ^ 2 = numberQuad u := Real.sq_sqrt hNq
    have h := mul_le_mul_of_nonneg_left hsqrt2 (Real.sqrt_nonneg (numberQuad u))
    nlinarith [Real.sqrt_nonneg (numberQuad u), Real.sqrt_nonneg 2]
  have hbound := abs_re_inner_pairVec_le f g u
  have hstep : |(inner ℂ (toLp u) (toLp (pairVec f g u)) : ℂ).re|
      ≤ 2 * Real.sqrt 2 * (l2norm f * l2norm g) * numberQuad u := by
    have hc : 0 ≤ 2 * (l2norm f * l2norm g) := by
      have := mul_nonneg (l2norm_nonneg f) (l2norm_nonneg g); linarith
    nlinarith [mul_le_mul_of_nonneg_left hprod hc]
  rw [div_mul_eq_mul_div, le_div_iff₀ hmu]
  have hc2 : 0 ≤ 2 * Real.sqrt 2 * (l2norm f * l2norm g) :=
    mul_nonneg (by positivity) (mul_nonneg hcf hcg)
  nlinarith [mul_le_mul_of_nonneg_left hq hc2, mul_le_mul_of_nonneg_right hstep hmu.le]

/-- **The gap survives an unbounded pair-creating perturbation.**  With the one-particle gap
`h − μ ≥ 0`, `μ > 0`, and `2√2‖f‖‖g‖ ≤ μ`, every vacuum-orthogonal finite-particle state has
`dΓ(h) + P(f,g)` energy at least `(μ − 2√2‖f‖‖g‖)‖u‖²`. -/
theorem fock_gap_of_pair_perturbation {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 < mu)
    (hgap : IsPosCol (shiftCol col mu)) {f g : ℕ →₀ ℂ}
    (hfg : 2 * Real.sqrt 2 * (l2norm f * l2norm g) ≤ mu) {u : FockAlg} (h0 : u 0 = 0) :
    (mu - 2 * Real.sqrt 2 * (l2norm f * l2norm g)) * ‖toLp u‖ ^ 2
      ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
        + (inner ℂ (toLp u) (toLp (pairVec f g u)) : ℂ).re := by
  have hNq : 0 ≤ numberQuad u := numberQuad_nonneg u
  have hn : ‖toLp u‖ ^ 2 ≤ numberQuad u := number_quadForm_ge h0
  have hq := number_le_dGamma_quadForm hgap u
  have hqge : mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re := by
    nlinarith
  have hrel := pairVec_relative_form_bound hmu hgap f g h0
  have hlow := (abs_le.mp hrel).1
  have hvm : -((2 * Real.sqrt 2 * (l2norm f * l2norm g))
        * (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re)
      ≤ (inner ℂ (toLp u) (toLp (pairVec f g u)) : ℂ).re * mu := by
    have h := mul_le_mul_of_nonneg_right hlow hmu.le
    calc -((2 * Real.sqrt 2 * (l2norm f * l2norm g))
            * (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re)
        = -((2 * Real.sqrt 2 * (l2norm f * l2norm g) / mu)
            * (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re) * mu := by
          field_simp
      _ ≤ _ := h
  have hmul : ((mu - 2 * Real.sqrt 2 * (l2norm f * l2norm g)) * ‖toLp u‖ ^ 2) * mu
      ≤ ((inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
          + (inner ℂ (toLp u) (toLp (pairVec f g u)) : ℂ).re) * mu := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqge) (sub_nonneg.mpr hfg)]
  exact le_of_mul_le_mul_right hmul hmu

/-- The surviving gap is strictly positive exactly when the pair coupling is quantitatively
smaller than `μ/(2√2)`. -/
theorem fock_gap_of_pair_perturbation_pos {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 < mu)
    (hgap : IsPosCol (shiftCol col mu)) {f g : ℕ →₀ ℂ}
    (hfg : 2 * Real.sqrt 2 * (l2norm f * l2norm g) < mu) {u : FockAlg} (h0 : u 0 = 0) :
    0 < mu - 2 * Real.sqrt 2 * (l2norm f * l2norm g) ∧
      (mu - 2 * Real.sqrt 2 * (l2norm f * l2norm g)) * ‖toLp u‖ ^ 2
        ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
          + (inner ℂ (toLp u) (toLp (pairVec f g u)) : ℂ).re :=
  ⟨by linarith, fock_gap_of_pair_perturbation hmu hgap hfg.le h0⟩

/-! ## 5. Fed by the certificate chain -/

section FormGap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

open BookProof.HermiteGalerkin BookProof.FarisLavine

/-- **The certificate chain's one-particle form gap survives the pair perturbation.**  If the
one-particle Hamiltonian on the finite-mode core satisfies `⟪x, h x⟫ ≥ μ‖x‖²` with `μ > 0`,
and the pair coupling obeys `2√2‖f‖‖g‖ ≤ μ`, then every vacuum-orthogonal finite-particle
state has `dΓ(h) + P(f,g)` energy at least `(μ − 2√2‖f‖‖g‖)‖u‖²`. -/
theorem fock_gap_of_one_particle_form_gap_pair (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) {mu : ℝ} (hmu : 0 < mu)
    (hform : ∀ x : finiteModeDomain b,
      mu * ‖(x : F)‖ ^ 2 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x)
    {f g : ℕ →₀ ℂ} (hfg : 2 * Real.sqrt 2 * (l2norm f * l2norm g) ≤ mu)
    {u : FockAlg} (h0 : u 0 = 0) :
    (mu - 2 * Real.sqrt 2 * (l2norm f * l2norm g)) * ‖toLp u‖ ^ 2
      ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b A) u)) : ℂ).re
        + (inner ℂ (toLp u) (toLp (pairVec f g u)) : ℂ).re :=
  fock_gap_of_pair_perturbation hmu
    (BookProof.YangMillsFockGapChain.isPosCol_shiftCol_opCol_of_form_gap b A hform) hfg h0

end FormGap

/-! ## 6. The perturbation is genuinely quadratic and genuinely unbounded -/

/-- The annihilation part kills the vacuum. -/
theorem annVec_vac (f : ℕ →₀ ℂ) : annVec f vac = 0 := by
  classical
  rw [annVec_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [vac, annA_single]
  simp

/-- For the unit coupling vector `e_k`, `a†(e_k) = a_k†`. -/
theorem creVec_single_one (k : ℕ) (w : FockAlg) :
    creVec (Finsupp.single k (1 : ℂ)) w = creA k w := by
  classical
  rw [creVec_apply, Finsupp.support_single_ne_zero k one_ne_zero]
  simp

/-- For the unit coupling vector `e_k`, `a(e_k) = a_k`. -/
theorem annVec_single_one (k : ℕ) (w : FockAlg) :
    annVec (Finsupp.single k (1 : ℂ)) w = annA k w := by
  classical
  rw [annVec_apply, Finsupp.support_single_ne_zero k one_ne_zero]
  simp

/-- `P(f,g)` moves the vacuum into the **two**-particle sector: it changes the particle
number by two. -/
theorem pairVec_vac (k : ℕ) :
    pairVec (Finsupp.single k 1) (Finsupp.single k 1) vac
      = Finsupp.single (Finsupp.single k 2) ((Real.sqrt 2 : ℝ) : ℂ) := by
  classical
  have hup0 : up k (0 : Conf) = Finsupp.single k 1 := by
    refine Finsupp.ext fun i => ?_
    rcases eq_or_ne i k with rfl | h
    · simp [up]
    · rw [up_of_ne _ h]; simp [h]
  have hup1 : up k (Finsupp.single k (1 : ℕ)) = Finsupp.single k 2 := by
    refine Finsupp.ext fun i => ?_
    rcases eq_or_ne i k with rfl | h
    · simp [up]
    · rw [up_of_ne _ h]; simp [h]
  rw [pairVec_apply, annVec_vac, map_zero, add_zero, creVec_single_one, creVec_single_one,
    vac, creA_single, one_smul, hup0, creA_single, hup1]
  norm_num

/-- **`P(f,g)` is not a bounded operator.** -/
theorem pairVec_unbounded (k : ℕ) (C : ℝ) :
    ∃ u : FockAlg, ‖toLp u‖ = 1 ∧
      C ≤ ‖toLp (pairVec (Finsupp.single k 1) (Finsupp.single k 1) u)‖ := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ 2)
  set al : Conf := Finsupp.single k n with hal
  set u : FockAlg := Finsupp.single al 1 with hu
  have halk : al k = n := by simp [hal]
  have husupp : u.support = {al} := Finsupp.support_single_ne_zero al one_ne_zero
  have hval : u al = 1 := by simp [hu]
  have hu1 : ‖toLp u‖ = 1 := by
    have h : ‖toLp u‖ ^ 2 = 1 := by
      rw [norm_toLp_sq, husupp, Finset.sum_singleton, hval]
      simp
    have hx : (0 : ℝ) ≤ ‖toLp u‖ := norm_nonneg _
    nlinarith
  refine ⟨u, hu1, ?_⟩
  set v : FockAlg := pairVec (Finsupp.single k (1 : ℂ)) (Finsupp.single k (1 : ℂ)) u with hv
  have hvsplit : v = creA k (creA k u) + annA k (annA k u) := by
    rw [hv, pairVec_apply, creVec_single_one, creVec_single_one, annVec_single_one,
      annVec_single_one]
  set be : Conf := up k (up k al) with hbe
  have hbek : be k = n + 2 := by rw [hbe, up_self, up_self, halk]
  have hupalk : (up k al) k = n + 1 := by rw [up_self, halk]
  have hann : annA k (annA k u) be = 0 := by
    rw [annA_apply, annA_apply]
    have hzero : u (up k (up k be)) = 0 := by
      have hne : up k (up k be) ≠ al := by
        intro hcontra
        have := congrArg (fun β : Conf => β k) hcontra
        simp only [up_self, hbek, halk] at this
        omega
      simp [hu, Ne.symm hne]
    rw [hzero]
    ring
  have hcre : creA k (creA k u) be
      = ((Real.sqrt ((n : ℝ) + 2) : ℝ) : ℂ) * ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) := by
    rw [creA_apply, creA_apply, dn_up, hbek, hupalk, dn_up, hval, mul_one]
    push_cast
    ring_nf
  have hcoord : v be
      = ((Real.sqrt ((n : ℝ) + 2) : ℝ) : ℂ) * ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) := by
    rw [hvsplit, Finsupp.add_apply, hann, hcre, add_zero]
  have hnormcoord : ‖v be‖ ^ 2 = ((n : ℝ) + 2) * ((n : ℝ) + 1) := by
    rw [hcoord, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hcoordne : v be ≠ 0 := by
    intro hzero
    rw [hzero] at hnormcoord
    simp only [norm_zero] at hnormcoord
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hmem : be ∈ v.support := Finsupp.mem_support_iff.mpr hcoordne
  have hge : ((n : ℝ) + 2) * ((n : ℝ) + 1) ≤ ‖toLp v‖ ^ 2 := by
    rw [norm_toLp_sq]
    calc ((n : ℝ) + 2) * ((n : ℝ) + 1) = ‖v be‖ ^ 2 := hnormcoord.symm
      _ ≤ ∑ β ∈ v.support, ‖v β‖ ^ 2 :=
          Finset.single_le_sum (f := fun β => ‖v β‖ ^ 2) (fun _ _ => sq_nonneg _) hmem
  have hvn : (0 : ℝ) ≤ ‖toLp v‖ := norm_nonneg _
  nlinarith [sq_nonneg C, Nat.cast_nonneg (α := ℝ) n]

/-! ## 7. The gauge-fixed Yang–Mills instance -/

section YangMills

open BookProof.FarisLavine BookProof.HermiteGalerkin
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFockGapChain

variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)

/-- **The concrete gauge-fixed Yang–Mills chain under a pair perturbation.**  Given a
one-particle form gap `⟪x, H₁ x⟫ ≥ μ‖x‖²` on the Gauss–polynomial core and a pair coupling
with `2√2‖f‖‖g‖ < μ`, the final nested-Fock Hamiltonian `dΓ(H₁) + P(f,g)` still has a
strictly positive gap on every vacuum-orthogonal finite-particle state.  As everywhere in
this chain, the one-particle form gap is a hypothesis, not a theorem. -/
theorem ym_fock_gap_of_pair_perturbation {mu : ℝ} (hmu : 0 < mu)
    (hgap : ∀ x : finiteModeDomain (coreBasis e),
      mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x)
    {f g : ℕ →₀ ℂ} (hfg : 2 * Real.sqrt 2 * (l2norm f * l2norm g) < mu)
    {u : FockAlg} (h0 : u 0 = 0) :
    0 < mu - 2 * Real.sqrt 2 * (l2norm f * l2norm g) ∧
      (mu - 2 * Real.sqrt 2 * (l2norm f * l2norm g)) * ‖toLp u‖ ^ 2
        ≤ (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re
          + (inner ℂ (toLp u) (toLp (pairVec f g u)) : ℂ).re :=
  fock_gap_of_pair_perturbation_pos hmu (ym_isPosCol_shiftCol e fabc hgap) hfg h0

end YangMills

/-! ## 8. Axiom audit -/

section Audit

#print axioms annVec_creVec
#print axioms norm_creVec_sq
#print axioms norm_creVec_le
#print axioms abs_re_inner_pairVec_le
#print axioms pairVec_relative_form_bound
#print axioms fock_gap_of_pair_perturbation
#print axioms fock_gap_of_one_particle_form_gap_pair
#print axioms pairVec_vac
#print axioms pairVec_unbounded
#print axioms ym_fock_gap_of_pair_perturbation

end Audit

end BookProof.FockPairPerturbation

end


