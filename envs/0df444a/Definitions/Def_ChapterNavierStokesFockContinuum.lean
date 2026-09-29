-- Prove2me | Definitions.Def_ChapterNavierStokesFockContinuum
-- name    : ChapterNavierStokesFockContinuum
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-15T11:33:12.128091+00:00
-- url     : https://prove2.me/theorems/892a4754-3f44-403d-8e33-e51f1a207e49
-- title:
--   The continuum limit: the second-quantized Hamiltonian on a parcel sector
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesFockContinuum`, source chapter `BookProof/ChapterNavierStokesFockContinuum.lean`): The continuum limit: the second-quantized Hamiltonian on a parcel sector
--
--   `BookProof.ChapterNavierStokesFockEsa` proves essential self-adjointness of the transformed (Lagrangian) Navier–Stokes Hamiltonian on the Fock space of a Fock space in the occupation-number representation, where the one-parcel symbol is *diagonal* in the chosen mode basis. The genuinely continuum situation is the opposite one: the one-parcel operator is multiplication by a field `w` on the parcel domain `Ω`, so it has **continuous spectrum** and no eigenvectors at all, and the second-quantized Hamiltonian
--
--   `ĥ = ∫_Ω w(ξ) a†(ξ) a(ξ) dξ`
--
--   acts on the `n`-parcel sector `L²(Ωⁿ)` of the Fock space as multiplication by the total energy `E(ξ₁,…,ξₙ) = ∑ₖ w(ξₖ)`.
--
--   This module proves essential self-adjointness in that situation.
--
--   * `boundedEnergyCore` — the core of states supported where the energy is bounded, together with `boundedEnergyCore_dense`: it is a dense domain. * `multOp` — multiplication by a real measurable function on that core, with `multOp_isSymmetricDom`. * `multOp_hasZeroDeficiencyOn` — **the headline: multiplication by an arbitrary real measurable function is essentially self-adjoint on the bounded-energy core.** Unlike the occupation-number picture this covers operators with purely continuous spectrum. The argument tests the deficiency identity against the truncations of `(g ∓ i)w` itself. * `sectorEnergy`, `sectorHamiltonian_hasZeroDeficiencyOn` — the application: on the `n`-parcel sector of the continuum Fock space over the infinite continuous domain `ℝ`, the second-quantized Hamiltonian `∫ w(ξ)a†(ξ)a(ξ)dξ` — that is, multiplication by `∑ₖ w(ξₖ)` — is essentially self-adjoint.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockContinuum.lean

import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa


/-!
# The continuum limit: the second-quantized Hamiltonian on a parcel sector

`BookProof.ChapterNavierStokesFockEsa` proves essential self-adjointness of the
transformed (Lagrangian) Navier–Stokes Hamiltonian on the Fock space of a Fock
space in the occupation-number representation, where the one-parcel symbol is
*diagonal* in the chosen mode basis.  The genuinely continuum situation is the
opposite one: the one-parcel operator is multiplication by a field `w` on the
parcel domain `Ω`, so it has **continuous spectrum** and no eigenvectors at all,
and the second-quantized Hamiltonian

`ĥ = ∫_Ω w(ξ) a†(ξ) a(ξ) dξ`

acts on the `n`-parcel sector `L²(Ωⁿ)` of the Fock space as multiplication by
the total energy `E(ξ₁,…,ξₙ) = ∑ₖ w(ξₖ)`.

This module proves essential self-adjointness in that situation.

* `boundedEnergyCore` — the core of states supported where the energy is
  bounded, together with `boundedEnergyCore_dense`: it is a dense domain.
* `multOp` — multiplication by a real measurable function on that core, with
  `multOp_isSymmetricDom`.
* `multOp_hasZeroDeficiencyOn` — **the headline: multiplication by an arbitrary
  real measurable function is essentially self-adjoint on the bounded-energy
  core.**  Unlike the occupation-number picture this covers operators with
  purely continuous spectrum.  The argument tests the deficiency identity
  against the truncations of `(g ∓ i)w` itself.
* `sectorEnergy`, `sectorHamiltonian_hasZeroDeficiencyOn` — the application: on
  the `n`-parcel sector of the continuum Fock space over the infinite continuous
  domain `ℝ`, the second-quantized Hamiltonian `∫ w(ξ)a†(ξ)a(ξ)dξ` — that is,
  multiplication by `∑ₖ w(ξₖ)` — is essentially self-adjoint.
-/

open MeasureTheory

namespace BookProof.NavierStokesFlow

namespace FockContinuum

open BookProof.NavierStokesFlow.FullEsa

variable {X : Type*} [MeasurableSpace X]

/-! ## The bounded-energy core -/

/-- The states supported (almost everywhere) where the energy `g` is bounded:
the natural core of the multiplication operator. -/
def boundedEnergyCore (μ : Measure X) (g : X → ℝ) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | ∃ n : ℕ, ∀ᵐ x ∂μ, ¬ (|g x| ≤ (n : ℝ)) → (f : X → ℂ) x = 0}
  add_mem' := by
    rintro f h ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, ?_⟩
    filter_upwards [hn, hm, Lp.coeFn_add f h] with x hx hy hadd hbig
    have hn' : ¬ (|g x| ≤ (n : ℝ)) := fun hle =>
      hbig (le_trans hle (by exact_mod_cast Nat.cast_le.2 (le_max_left n m)))
    have hm' : ¬ (|g x| ≤ (m : ℝ)) := fun hle =>
      hbig (le_trans hle (by exact_mod_cast Nat.cast_le.2 (le_max_right n m)))
    rw [hadd, Pi.add_apply, hx hn', hy hm', add_zero]
  zero_mem' := by
    refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x hx _
    rw [hx]; rfl
  smul_mem' := by
    rintro c f ⟨n, hn⟩
    refine ⟨n, ?_⟩
    filter_upwards [hn, Lp.coeFn_smul c f] with x hx hsmul hbig
    rw [hsmul, Pi.smul_apply, hx hbig, smul_zero]



/-! ### The core is dense -/





/-- Multiplying a bounded-energy state by the energy stays square-integrable. -/
theorem memLp_mul {μ : Measure X} {g : X → ℝ} (hg : Measurable g) {f : Lp ℂ 2 μ}
    (hf : f ∈ boundedEnergyCore μ g) :
    MemLp (fun x => (g x : ℂ) * (f : X → ℂ) x) 2 μ := by
  obtain ⟨n, hn⟩ := hf
  have hmeas : AEStronglyMeasurable (fun x => (g x : ℂ) * (f : X → ℂ) x) μ :=
    (Complex.measurable_ofReal.comp hg).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  have hbound : ∀ᵐ x ∂μ, ‖(g x : ℂ) * (f : X → ℂ) x‖ ≤ ((n : ℝ)) * ‖(f : X → ℂ) x‖ := by
    filter_upwards [hn] with x hx
    by_cases h : |g x| ≤ (n : ℝ)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
    · rw [hx h]; simp
  exact MemLp.of_le_mul (Lp.memLp f) hmeas hbound

theorem mul_mem_boundedEnergyCore {μ : Measure X} {g : X → ℝ} (hg : Measurable g)
    {f : Lp ℂ 2 μ} (hf : f ∈ boundedEnergyCore μ g) :
    (memLp_mul hg hf).toLp _ ∈ boundedEnergyCore μ g := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, ?_⟩
  filter_upwards [hn,
    (memLp_mul hg (⟨n, hn⟩ : f ∈ boundedEnergyCore μ g)).coeFn_toLp] with x hx hcoe hbig
  rw [hcoe, hx hbig, mul_zero]

/-- **Multiplication by a real measurable function** on the bounded-energy core:
the second-quantized Hamiltonian in the configuration representation. -/
noncomputable def multOp (μ : Measure X) {g : X → ℝ} (hg : Measurable g) :
    boundedEnergyCore μ g →ₗ[ℂ] boundedEnergyCore μ g where
  toFun f := ⟨(memLp_mul hg f.2).toLp _, mul_mem_boundedEnergyCore hg f.2⟩
  map_add' f h := by
    refine Subtype.ext (Lp.ext ?_)
    simp only [Submodule.coe_add]
    filter_upwards [(memLp_mul hg (show ((f : Lp ℂ 2 μ) + (h : Lp ℂ 2 μ)) ∈ boundedEnergyCore μ g
        from (f + h).2)).coeFn_toLp,
      (memLp_mul hg f.2).coeFn_toLp, (memLp_mul hg h.2).coeFn_toLp,
      Lp.coeFn_add ((f : Lp ℂ 2 μ)) ((h : Lp ℂ 2 μ)),
      Lp.coeFn_add ((memLp_mul hg f.2).toLp _) ((memLp_mul hg h.2).toLp _)] with x h1 h2 h3 h4 h5
    rw [h1, h5]
    simp only [Pi.add_apply]
    rw [h2, h3, h4]
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    refine Subtype.ext (Lp.ext ?_)
    simp only [Submodule.coe_smul, RingHom.id_apply]
    filter_upwards [(memLp_mul hg (show (c • (f : Lp ℂ 2 μ)) ∈ boundedEnergyCore μ g
        from (c • f).2)).coeFn_toLp,
      (memLp_mul hg f.2).coeFn_toLp, Lp.coeFn_smul c ((f : Lp ℂ 2 μ)),
      Lp.coeFn_smul c ((memLp_mul hg f.2).toLp _)] with x h1 h2 h3 h4
    rw [h1, h4]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h2, h3]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring







/-! ## Essential self-adjointness -/



/-! ## The `n`-parcel sector of the continuum Fock space -/

section Sector

/-- The total energy of an `n`-parcel configuration `(ξ₁,…,ξₙ)` of the continuum
Fock space, for the one-parcel field `w` on the parcel domain `ℝ`:
`E(ξ) = ∑ₖ w(ξₖ)`.  This is how the second-quantized Hamiltonian
`∫ w(ξ) a†(ξ)a(ξ) dξ` acts on the `n`-parcel sector. -/
noncomputable def sectorEnergy (w : ℝ → ℝ) (n : ℕ) : (Fin n → ℝ) → ℝ :=
  fun ξ => ∑ k : Fin n, w (ξ k)







end Sector

end FockContinuum

end BookProof.NavierStokesFlow


