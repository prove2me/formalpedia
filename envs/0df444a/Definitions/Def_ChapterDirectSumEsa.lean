-- Prove2me | Definitions.Def_ChapterDirectSumEsa
-- name    : ChapterDirectSumEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-15T13:51:46.294427+00:00
-- url     : https://prove2.me/theorems/68a6eb2b-11d4-437b-bda8-15bf837a67c9
-- title:
--   Fibrewise essential self-adjointness glues: the orthogonal direct sum What is proved Honest boundary
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.DirectSumEsa`, source chapter `BookProof/ChapterDirectSumEsa.lean`): Fibrewise essential self-adjointness glues: the orthogonal direct sum What is proved Honest boundary
--
--   Essential self-adjointness is a statement about **two deficiency spaces**, and a deficiency space of an orthogonal direct sum is the direct sum of the fibre deficiency spaces. So the step that passes essential self-adjointness from the fibres of a decomposition to the whole space — the discrete form of the direct-integral gluing — is available in complete generality, for *any* family of fibre operators, with no relative bound, no comparison operator and no commutator estimate.
--
--   This module proves that, and applies it to the continuum Navier–Stokes Fock space.
--
--   * `dsCore` — the algebraic direct sum `⊕ᵃˡᵍ Dᵢ` of a family of fibre cores, a submodule of the Hilbert direct sum `ℓ²(i, Gᵢ)`, and `dsOp` — the direct sum `⊕ᵢ Hᵢ` of a family of fibre operators on it; * `dsOp_single`, `dsOp_symmetricOn` — the operator on a single-fibre state is the fibre operator, and symmetry is fibrewise; * `dsOp_deficiencyTrivialAt` — **the gluing step**: testing the deficiency identity against single-fibre states shows every coordinate of a deficiency vector vanishes; * `dsOp_essentiallySelfAdjointOn` — **the instrument**: if every fibre operator is essentially self-adjoint on its core, the direct sum is essentially self-adjoint on the algebraic direct sum of the cores; * `dsOpD`, `dsOpD_hasZeroDeficiencyOn`, `dsOpD_isSymmetricDom` — the same for *domain-preserving* fibre operators, in the `HasZeroDeficiencyOn` formulation used by the Navier–Stokes chapters; * `dsCore_dense` — the glued core is dense as soon as every fibre core is; * `dsOpD_stone_flow` — the glued operator therefore selects a unique self-adjoint extension and generates a complete unitary group on the direct sum; * `fockCore`, `fockH`, `fockH_hasZeroDeficiencyOn`, `fockH_stone_flow` — **the payoff**: on the *whole* continuum Fock space `⊕ₙ L²(ℝⁿ)` of the parcel picture, the second-quantized Hamiltonian `ĥ = ∫ w(ξ) a†(ξ) a(ξ) dξ` — multiplication by the total energy `∑ₖ w(ξₖ)` on the `n`-parcel sector — is symmetric, densely defined and has vanishing adjoint deficiency on the direct sum of the bounded-energy cores. `BookProof.ChapterNavierStokesFockContinuum` proved this one sector at a time; this is the statement on the Fock space itself, for an arbitrary measurable field `w`, with no boundedness assumption and with (in general) purely continuous spectrum. Running the Stone bridge on it gives `fockH_stone_flow`, the complete unitary group `e^{−itĥ}` on the continuum Fock space.
--
--   The decomposition is an *orthogonal direct sum*: the fibres must be mutually orthogonal subspaces and the operator must preserve each of them. Nothing here glues fibres of a genuine direct *integral* over a continuous parameter, and nothing here provides a decomposition — only the passage from fibres to the whole once one is given. As elsewhere in this development, no claim is made about global regularity of the classical Navier–Stokes equation.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterDirectSumEsa.lean

import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa


/-!
# Fibrewise essential self-adjointness glues: the orthogonal direct sum

Essential self-adjointness is a statement about **two deficiency spaces**, and a deficiency
space of an orthogonal direct sum is the direct sum of the fibre deficiency spaces.  So the
step that passes essential self-adjointness from the fibres of a decomposition to the whole
space — the discrete form of the direct-integral gluing — is available in complete
generality, for *any* family of fibre operators, with no relative bound, no comparison
operator and no commutator estimate.

This module proves that, and applies it to the continuum Navier–Stokes Fock space.

## What is proved

* `dsCore` — the algebraic direct sum `⊕ᵃˡᵍ Dᵢ` of a family of fibre cores, a submodule of
  the Hilbert direct sum `ℓ²(i, Gᵢ)`, and `dsOp` — the direct sum `⊕ᵢ Hᵢ` of a family of
  fibre operators on it;
* `dsOp_single`, `dsOp_symmetricOn` — the operator on a single-fibre state is the fibre
  operator, and symmetry is fibrewise;
* `dsOp_deficiencyTrivialAt` — **the gluing step**: testing the deficiency identity against
  single-fibre states shows every coordinate of a deficiency vector vanishes;
* `dsOp_essentiallySelfAdjointOn` — **the instrument**: if every fibre operator is
  essentially self-adjoint on its core, the direct sum is essentially self-adjoint on the
  algebraic direct sum of the cores;
* `dsOpD`, `dsOpD_hasZeroDeficiencyOn`, `dsOpD_isSymmetricDom` — the same for
  *domain-preserving* fibre operators, in the `HasZeroDeficiencyOn` formulation used by the
  Navier–Stokes chapters;
* `dsCore_dense` — the glued core is dense as soon as every fibre core is;
* `dsOpD_stone_flow` — the glued operator therefore selects a unique self-adjoint
  extension and generates a complete unitary group on the direct sum;
* `fockCore`, `fockH`, `fockH_hasZeroDeficiencyOn`, `fockH_stone_flow` — **the payoff**:
  on the *whole* continuum Fock space `⊕ₙ L²(ℝⁿ)` of the parcel picture, the
  second-quantized Hamiltonian `ĥ = ∫ w(ξ) a†(ξ) a(ξ) dξ` — multiplication by the total
  energy `∑ₖ w(ξₖ)` on the `n`-parcel sector — is symmetric, densely defined and has
  vanishing adjoint deficiency on the direct sum of the bounded-energy cores.
  `BookProof.ChapterNavierStokesFockContinuum` proved this one sector at a time; this is
  the statement on the Fock space itself, for an arbitrary measurable field `w`, with no
  boundedness assumption and with (in general) purely continuous spectrum.  Running the
  Stone bridge on it gives `fockH_stone_flow`, the complete unitary group `e^{−itĥ}` on
  the continuum Fock space.

## Honest boundary

The decomposition is an *orthogonal direct sum*: the fibres must be mutually orthogonal
subspaces and the operator must preserve each of them.  Nothing here glues fibres of a
genuine direct *integral* over a continuous parameter, and nothing here provides a
decomposition — only the passage from fibres to the whole once one is given.  As
elsewhere in this development, no claim is made about global regularity of the classical
Navier–Stokes equation.
-/

open scoped ENNReal

namespace BookProof.DirectSumEsa

open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

/-- **The algebraic direct sum of the fibre cores.** -/
def dsCore (D : ∀ i, Submodule ℂ (G i)) : Submodule ℂ (lp G 2) where
  carrier := {f | {i | (f : ∀ i, G i) i ≠ 0}.Finite ∧ ∀ i, (f : ∀ i, G i) i ∈ D i}
  add_mem' := by
    rintro f g ⟨hf, hfD⟩ ⟨hg, hgD⟩
    constructor
    · refine Set.Finite.subset (hf.union hg) (fun i hi => ?_)
      simp only [Set.mem_setOf_eq, lp.coeFn_add, Pi.add_apply] at hi
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
      exact hi (by rw [hcon.1, hcon.2, add_zero])
    · intro i
      simp only [lp.coeFn_add, Pi.add_apply]
      exact Submodule.add_mem _ (hfD i) (hgD i)
  zero_mem' := by
    constructor
    · refine Set.Finite.subset (Set.finite_empty) (fun i hi => ?_)
      simp only [Set.mem_setOf_eq, lp.coeFn_zero, Pi.zero_apply, ne_eq, not_true_eq_false] at hi
    · intro i
      simp only [lp.coeFn_zero, Pi.zero_apply]
      exact Submodule.zero_mem _
  smul_mem' := by
    rintro c f ⟨hf, hfD⟩
    constructor
    · refine Set.Finite.subset hf (fun i hi => ?_)
      simp only [Set.mem_setOf_eq, lp.coeFn_smul, Pi.smul_apply] at hi ⊢
      intro h0
      exact hi (by rw [h0, smul_zero])
    · intro i
      simp only [lp.coeFn_smul, Pi.smul_apply]
      exact Submodule.smul_mem _ _ (hfD i)



omit [∀ i, InnerProductSpace ℂ (G i)] in
theorem memLp_of_finite_support {f : ∀ i, G i} (h : {i | f i ≠ 0}.Finite) : Memℓp f 2 := by
  classical
  refine memℓp_gen (summable_of_ne_finset_zero (s := h.toFinset) fun i hi => ?_)
  have hzero : f i = 0 := by
    by_contra hne
    exact hi (h.mem_toFinset.mpr hne)
  simp [hzero]

variable {D : ∀ i, Submodule ℂ (G i)}

/-- **The direct sum of a family of fibre operators**, on the algebraic direct sum of the
fibre cores. -/
def dsOp (H : ∀ i, D i →ₗ[ℂ] G i) : dsCore D →ₗ[ℂ] lp G 2 where
  toFun x := ⟨fun i => H i ⟨(x : lp G 2) i, x.2.2 i⟩, by
    refine memLp_of_finite_support (Set.Finite.subset x.2.1 (fun i hi => ?_))
    simp only [Set.mem_setOf_eq] at hi ⊢
    intro h0
    refine hi ?_
    have : (⟨((x : lp G 2) : ∀ i, G i) i, x.2.2 i⟩ : D i) = 0 := Subtype.ext h0
    rw [this, map_zero]⟩
  map_add' x y := by
    refine lp.ext (funext fun i => ?_)
    simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
    exact map_add (H i) ⟨((x : lp G 2)) i, x.2.2 i⟩ ⟨((y : lp G 2)) i, y.2.2 i⟩
  map_smul' c x := by
    refine lp.ext (funext fun i => ?_)
    simp only [RingHom.id_apply, SetLike.val_smul, lp.coeFn_smul, Pi.smul_apply]
    exact map_smul (H i) c ⟨((x : lp G 2)) i, x.2.2 i⟩



/-! ## The single-fibre states -/





/-! ## Symmetry and the deficiency spaces -/







/-! ## 3. The domain-preserving form -/

section DomainPreserving

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]





end DomainPreserving

/-- **The direct sum of a family of domain-preserving fibre operators.** -/
def dsOpD (A : ∀ i, D i →ₗ[ℂ] D i) : dsCore D →ₗ[ℂ] dsCore D :=
  LinearMap.codRestrict (dsCore D) (dsOp (fun i => (D i).subtype.comp (A i)))
    (fun x => by
      constructor
      · refine Set.Finite.subset x.2.1 (fun i hi => ?_)
        simp only [Set.mem_setOf_eq] at hi ⊢
        intro h0
        refine hi ?_
        have hz : (⟨((x : lp G 2) : ∀ i, G i) i, x.2.2 i⟩ : D i) = 0 := Subtype.ext h0
        have hval : ((dsOp (fun i => (D i).subtype.comp (A i)) x : lp G 2) : ∀ i, G i) i
            = ((A i) ⟨((x : lp G 2) : ∀ i, G i) i, x.2.2 i⟩ : G i) := rfl
        rw [hval, hz, map_zero]
        rfl
      · intro i
        exact (A i ⟨((x : lp G 2) : ∀ i, G i) i, x.2.2 i⟩).2)









/-! ## 4. The glued core is dense -/





/-! ## 5. The payoff: the continuum Fock space of the parcel picture -/

section FockSpace

open MeasureTheory BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum

/-- The measurability of the total energy `∑ₖ w(ξₖ)` of an `n`-parcel
configuration, travelling with this bundle.

A definition bundle is compiled against the published bundles and nothing else,
and `sectorEnergy`'s measurability is a *theorem* of the source chapter
(`BookProof/ChapterNavierStokesFockContinuum.lean`), which
`Definitions.Def_ChapterNavierStokesFockContinuum` does not carry -- only its
definitions.  A `def` whose body needs that proof therefore cannot be published
unless the proof travels with it, which is what this is: the chapter's proof,
verbatim.  `private` keeps the name out of the cumulative environment, where the
chapter's own theorem bundle declares the public `sectorEnergy_measurable`; the
mangled private name cannot collide with it. -/
private theorem sectorEnergy_measurable {w : ℝ → ℝ} (hw : Measurable w) (n : ℕ) :
    Measurable (sectorEnergy w n) :=
  Finset.univ.measurable_sum fun k _ => hw.comp (measurable_pi_apply k)

/-- The `n`-parcel sector `L²(ℝⁿ)` of the continuum Fock space. -/
abbrev parcelSector (n : ℕ) := Lp ℂ 2 (volume : Measure (Fin n → ℝ))

/-- **The continuum Fock space** `⊕ₙ L²(ℝⁿ)` of the parcel picture. -/
abbrev fockSpace := lp (fun n : ℕ => parcelSector n) 2

/-- The bounded-energy core of the `n`-parcel sector. -/
def sectorCore (w : ℝ → ℝ) (n : ℕ) : Submodule ℂ (parcelSector n) :=
  boundedEnergyCore (volume : Measure (Fin n → ℝ)) (sectorEnergy w n)

/-- **The core of the Fock Hamiltonian**: the algebraic direct sum of the bounded-energy
cores of the sectors. -/
def fockCore (w : ℝ → ℝ) : Submodule ℂ fockSpace := dsCore (sectorCore w)

/-- **The second-quantized Hamiltonian on the whole continuum Fock space**: on the
`n`-parcel sector it is multiplication by the total energy `∑ₖ w(ξₖ)`. -/
def fockH {w : ℝ → ℝ} (hw : Measurable w) : fockCore w →ₗ[ℂ] fockCore w :=
  dsOpD (fun n => multOp (volume : Measure (Fin n → ℝ)) (sectorEnergy_measurable hw n))











end FockSpace

end

end BookProof.DirectSumEsa


