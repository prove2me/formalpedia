-- Prove2me | Definitions.Def_ChapterScalaronFockGapChain
-- name    : ChapterScalaronFockGapChain
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T05:06:39.754034+00:00
-- url     : https://prove2.me/theorems/d37f2179-efe5-48a8-898f-a29cabe01710
-- title:
--   Chapter ScalaronFockGapChain
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterScalaronFockGapChain.lean`): generated def bundle for ChapterScalaronFockGapChain. See BookProof/ChapterScalaronFockGapChain.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronFockGapChain.lean

import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockFieldPerturbation
import Theorems.Thm_BookProof_FockFieldPerturbation_fock_gap_of_field_perturbation_pos
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Theorems.Thm_BookProof_FockNumberPreservingGap_fock_gap_of_one_particle_form_gap
import Theorems.Thm_BookProof_FockNumberPreservingGap_shiftCol_opCol
import Theorems.Thm_BookProof_FockSecondQuantization_isPosCol_opCol
import Theorems.Thm_BookProof_FockSecondQuantization_secondQuantization_friedrichs
import Theorems.Thm_BookProof_FockCubicQuarticStability_dGamma_multiMode_cubic_quartic_bounded_below


/-!
# Chapter ScalaronFockGapChain — the gap chain for the R² (scalaron) sector

`CONSOLIDATED_PLAN.md`, next step 3 of the top work package, asks for the abstract gap
chain to be run "for the other sectors under the enclosure doctrine", and singles out the
`R²`-vielbein quantum-gravity case: for the scalaron sector the one-particle operator may
be taken to be the *positive constant* `m = 1/√(12α)`, in which case the outer Fock gap
`m·N` is **unconditional** — no certificate, no Ritz data, no form-gap hypothesis.  This
chapter carries that out.

The gauge-fixed Yang–Mills instantiation `ChapterYangMillsFockGapChain` had to leave its
one-particle form gap as a hypothesis.  Here the form gap is an identity, so every
conclusion of the chain becomes a theorem.

## Deliverables

* `constOnePart b m` — the constant one-particle operator `m·1` on the finite-mode core of
  a one-particle Hilbert space with basis `b`, and `constOnePart_quadForm`, its quadratic
  form `m‖x‖²`;
* **`const_fock_gap`** — for `m ≥ 0`: `dΓ(m·1)` annihilates the outer vacuum and has energy
  at least `m‖u‖²` on every vacuum-orthogonal finite-particle state, *unconditionally*;
* **`const_fock_mass_gap`** — for `m > 0`: the same together with the positive self-adjoint
  (Friedrichs) extension of `dΓ(m·1)` and the strict positivity of the non-vacuum energy;
* **`const_fock_gap_of_field_perturbation`** — the gap survives the unbounded,
  number-changing linear field coupling `Φ(f)` of `ChapterFockFieldPerturbation` whenever
  `2‖f‖ < m`, with the surviving gap `(m − 2‖f‖)‖u‖²`;
* **`const_fock_cubic_quartic_bounded_below`** — with the cubic mode couplings and their
  normal-ordered quartic partners of `ChapterFockCubicQuarticStability` added, the energy is
  still bounded below, by `-|S|(2lam² + (2lam² + ½ − m)²/2)‖u‖²`;
* `scalaronMass α = 1/√(12α)` and the instantiation of all of the above at the scalaron mass
  on the Hermite basis of `L²(ℝ)`: **`scalaron_fock_mass_gap`**,
  `scalaron_fock_gap_of_field_perturbation`, `scalaron_fock_cubic_quartic_bounded_below`.

## Honest boundary

What is unconditional here is the *lift*: given that the scalaron sector's one-particle
operator is the constant `m = 1/√(12α)` — the mass of the Starobinsky scalaron, i.e. the
model in which the sector's one-particle energy is that constant — the outer nested-Fock
Hamiltonian has the gap `m` and keeps it under the perturbations listed above.  That the
full one-particle operator of the `R²` theory reduces to this constant is a modelling
statement of the plan's enclosure doctrine, not something proved here; the TEGR kinetic
sector is not covered, and neither is any claim about the Yang–Mills mass gap.

Everything is `sorry`-free and introduces no axioms.
-/

noncomputable section

namespace BookProof.ScalaronFockGapChain

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicQuarticStability BookProof.FockCubicUnbounded
open BookProof.FockInteractionStability
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin
open BookProof.HermiteCore

/-! ## 1. The constant one-particle operator -/

section General

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **The constant one-particle operator** `m·1` on the finite-mode core: the one-particle
energy of a free sector of mass `m`. -/
def constOnePart (b : HilbertBasis ℕ ℂ F) (m : ℝ) :
    finiteModeDomain b →ₗ[ℂ] finiteModeDomain b :=
  ((m : ℝ) : ℂ) • LinearMap.id

/-- Its quadratic form is `m‖x‖²`; in particular the one-particle form gap holds with
`μ = m`, as an identity. -/
theorem constOnePart_quadForm (b : HilbertBasis ℕ ℂ F) (m : ℝ)
    (x : finiteModeDomain b) :
    quadForm ((finiteModeDomain b).subtype.comp (constOnePart b m)) x = m * ‖(x : F)‖ ^ 2 := by
  simp only [quadForm, constOnePart, LinearMap.coe_comp, Function.comp_apply,
    Submodule.subtype_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul,
    inner_smul_right, Complex.re_ofReal_mul, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The constant one-particle operator is symmetric on the core. -/
theorem constOnePart_symmetricOn (b : HilbertBasis ℕ ℂ F) (m : ℝ) :
    SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp (constOnePart b m)) := by
  intro x y
  simp only [constOnePart, LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal]

/-- **The unconditional Fock gap of a constant one-particle energy.**  The final Hamiltonian
`dΓ(m·1)` annihilates the outer vacuum and has energy at least `m‖u‖²` on every
vacuum-orthogonal finite-particle state.  Unlike the Yang–Mills instantiation, no form-gap
hypothesis is needed: for a constant one-particle operator the form gap is an identity. -/
theorem const_fock_gap (b : HilbertBasis ℕ ℂ F) {m : ℝ} (hm : 0 ≤ m) :
    dGamma (opCol b (constOnePart b m)) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        m * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b (constOnePart b m)) u)) : ℂ).re :=
  fock_gap_of_one_particle_form_gap b (constOnePart b m) hm
    fun x => (constOnePart_quadForm b m x).ge

/-- The matrix gap condition `h − m ≥ 0` for the constant one-particle operator, the input
the unbounded-perturbation theorems consume. -/
theorem const_isPosCol_shiftCol (b : HilbertBasis ℕ ℂ F) (m : ℝ) :
    IsPosCol (shiftCol (opCol b (constOnePart b m)) m) := by
  have hpos : ∀ x : finiteModeDomain b,
      0 ≤ quadForm ((finiteModeDomain b).subtype.comp
        (constOnePart b m - ((m : ℝ) : ℂ) • LinearMap.id)) x := by
    intro x
    have hval : quadForm ((finiteModeDomain b).subtype.comp
        (constOnePart b m - ((m : ℝ) : ℂ) • LinearMap.id)) x
        = quadForm ((finiteModeDomain b).subtype.comp (constOnePart b m)) x
          - m * ‖(x : F)‖ ^ 2 := by
      simp only [quadForm, LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_sub,
        Submodule.coe_smul, inner_sub_right, inner_smul_right, Complex.sub_re,
        Complex.re_ofReal_mul, inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [hval, constOnePart_quadForm]
    linarith
  rw [shiftCol_opCol]
  exact isPosCol_opCol hpos

/-- **The unconditional Fock mass gap of a constant one-particle energy.**  For `m > 0`,
`dΓ(m·1)` has a positive self-adjoint (Friedrichs) extension, annihilates the outer vacuum,
and has strictly positive energy on every nonzero vacuum-orthogonal finite-particle
state. -/
theorem const_fock_mass_gap (b : HilbertBasis ℕ ℂ F) {m : ℝ} (hm : 0 < m) :
    (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
        IsPositiveSelfAdjointExtension (dGammaOp (opCol b (constOnePart b m))) A) ∧
      dGamma (opCol b (constOnePart b m)) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 → u ≠ 0 →
        0 < (inner ℂ (toLp u) (toLp (dGamma (opCol b (constOnePart b m)) u)) : ℂ).re := by
  obtain ⟨hvac, hgap⟩ := const_fock_gap b hm.le
  refine ⟨?_, hvac, fun u h0 hu => ?_⟩
  · refine secondQuantization_friedrichs b (constOnePart b m) (constOnePart_symmetricOn b m)
      fun x => ?_
    rw [constOnePart_quadForm]
    have : (0 : ℝ) ≤ ‖(x : F)‖ ^ 2 := sq_nonneg _
    nlinarith
  · have hnorm : 0 < ‖toLp u‖ := by
      have : toLp u ≠ 0 := fun hc => hu <|
        Finsupp.ext fun α => by
          have h := congrArg (fun f : Fock => (f : Conf → ℂ) α) hc
          simpa [toLp] using h
      exact norm_pos_iff.mpr this
    have hquad := hgap u h0
    have hpos : 0 < m * ‖toLp u‖ ^ 2 := by positivity
    linarith

/-- **The gap survives an unbounded linear field coupling.**  With `2‖f‖ < m` the perturbed
Hamiltonian `dΓ(m·1) + Φ(f)` still has energy at least `(m − 2‖f‖)‖u‖² > 0` on every
vacuum-orthogonal finite-particle state.  `Φ(f)` is neither bounded nor number-preserving,
so this is not a corollary of the bounded interaction theory. -/
theorem const_fock_gap_of_field_perturbation (b : HilbertBasis ℕ ℂ F) {m : ℝ} (hm : 0 < m)
    {f : ℕ →₀ ℂ} (hf : 2 * l2norm f < m) {u : FockAlg} (h0 : u 0 = 0) :
    0 < m - 2 * l2norm f ∧
      (m - 2 * l2norm f) * ‖toLp u‖ ^ 2
        ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b (constOnePart b m)) u)) : ℂ).re
          + (inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re :=
  fock_gap_of_field_perturbation_pos hm (const_isPosCol_shiftCol b m) hf h0

/-- **The cubic-plus-quartic interaction keeps the energy bounded below.**  Adding, for
every mode of a finite set `S`, the cubic coupling `C_k` and its normal-ordered quartic
partner `Q_k`, the Hamiltonian `dΓ(m·1) + ∑_{k ∈ S}(lam·C_k + Q_k)` is bounded below by
`-|S|(2lam² + (2lam² + ½ − m)²/2)‖u‖²` on all finite states. -/
theorem const_fock_cubic_quartic_bounded_below (b : HilbertBasis ℕ ℂ F) {m : ℝ} (hm : 0 < m)
    (S : Finset ℕ) (lam : ℝ) (u : FockAlg) :
    -(S.card * (2 * lam ^ 2 + (2 * lam ^ 2 + 1 / 2 - m) ^ 2 / 2)) * ‖toLp u‖ ^ 2
      ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b (constOnePart b m)) u)) : ℂ).re
        + ∑ k ∈ S, (lam * (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re
            + (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re) :=
  dGamma_multiMode_cubic_quartic_bounded_below S hm (const_isPosCol_shiftCol b m) u

end General

/-! ## 2. The scalaron sector -/

/-- **The Starobinsky scalaron mass** `m = 1/√(12α)` of the `R + αR²` theory. -/
def scalaronMass (alpha : ℝ) : ℝ := 1 / Real.sqrt (12 * alpha)

theorem scalaronMass_pos {alpha : ℝ} (halpha : 0 < alpha) : 0 < scalaronMass alpha := by
  have h : 0 < Real.sqrt (12 * alpha) := Real.sqrt_pos.mpr (by linarith)
  exact div_pos one_pos h

/-- The scalaron one-particle operator of the enclosure doctrine: the constant
`m = 1/√(12α)` on the finite-mode core of `L²(ℝ)` in the Hermite basis. -/
def scalaronOnePart (alpha : ℝ) :
    finiteModeDomain hermiteBasis →ₗ[ℂ] finiteModeDomain hermiteBasis :=
  constOnePart hermiteBasis (scalaronMass alpha)

/-- **The unconditional scalaron Fock mass gap.**  For `α > 0` the final nested-Fock
Hamiltonian `dΓ(m·1)` of the scalaron sector, `m = 1/√(12α)`, has a positive self-adjoint
(Friedrichs) extension, annihilates the outer vacuum, and has strictly positive energy on
every nonzero vacuum-orthogonal finite-particle state — with no certificate hypothesis and
no Ritz data, the one-particle form gap being an identity for a constant one-particle
energy. -/
theorem scalaron_fock_mass_gap {alpha : ℝ} (halpha : 0 < alpha) :
    (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
        IsPositiveSelfAdjointExtension (dGammaOp (opCol hermiteBasis (scalaronOnePart alpha)))
          A) ∧
      dGamma (opCol hermiteBasis (scalaronOnePart alpha)) vac = 0 ∧
      (∀ u : FockAlg, u 0 = 0 →
        scalaronMass alpha * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u)
              (toLp (dGamma (opCol hermiteBasis (scalaronOnePart alpha)) u)) : ℂ).re) ∧
      ∀ u : FockAlg, u 0 = 0 → u ≠ 0 →
        0 < (inner ℂ (toLp u)
            (toLp (dGamma (opCol hermiteBasis (scalaronOnePart alpha)) u)) : ℂ).re := by
  obtain ⟨hfried, hvac, hpos⟩ := const_fock_mass_gap hermiteBasis (scalaronMass_pos halpha)
  obtain ⟨-, hgap⟩ := const_fock_gap hermiteBasis (scalaronMass_pos halpha).le
  exact ⟨hfried, hvac, hgap, hpos⟩

/-- The scalaron Fock gap survives an unbounded linear field coupling with `2‖f‖ < m`. -/
theorem scalaron_fock_gap_of_field_perturbation {alpha : ℝ} (halpha : 0 < alpha)
    {f : ℕ →₀ ℂ} (hf : 2 * l2norm f < scalaronMass alpha) {u : FockAlg} (h0 : u 0 = 0) :
    0 < scalaronMass alpha - 2 * l2norm f ∧
      (scalaronMass alpha - 2 * l2norm f) * ‖toLp u‖ ^ 2
        ≤ (inner ℂ (toLp u)
              (toLp (dGamma (opCol hermiteBasis (scalaronOnePart alpha)) u)) : ℂ).re
          + (inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re :=
  const_fock_gap_of_field_perturbation hermiteBasis (scalaronMass_pos halpha) hf h0

/-- The scalaron Fock Hamiltonian stays bounded below when the cubic mode couplings and
their normal-ordered quartic partners are added. -/
theorem scalaron_fock_cubic_quartic_bounded_below {alpha : ℝ} (halpha : 0 < alpha)
    (S : Finset ℕ) (lam : ℝ) (u : FockAlg) :
    -(S.card * (2 * lam ^ 2 + (2 * lam ^ 2 + 1 / 2 - scalaronMass alpha) ^ 2 / 2))
        * ‖toLp u‖ ^ 2
      ≤ (inner ℂ (toLp u)
            (toLp (dGamma (opCol hermiteBasis (scalaronOnePart alpha)) u)) : ℂ).re
        + ∑ k ∈ S, (lam * (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re
            + (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re) :=
  const_fock_cubic_quartic_bounded_below hermiteBasis (scalaronMass_pos halpha) S lam u

/-! ## 3. Axiom audit -/

section Audit

#print axioms constOnePart_quadForm
#print axioms const_fock_gap
#print axioms const_fock_mass_gap
#print axioms const_fock_gap_of_field_perturbation
#print axioms const_fock_cubic_quartic_bounded_below
#print axioms scalaron_fock_mass_gap
#print axioms scalaron_fock_gap_of_field_perturbation
#print axioms scalaron_fock_cubic_quartic_bounded_below

end Audit

end BookProof.ScalaronFockGapChain

end


