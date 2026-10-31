-- Prove2me | Definitions.Def_ChapterGradedHashimoto
-- name    : ChapterGradedHashimoto
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-30T08:37:44.597385+00:00
-- url     : https://prove2.me/theorems/9f47bb59-a299-41ca-9853-58c47075ff60
-- title:
--   Chapter GradedHashimoto
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGradedHashimoto.lean`): generated def bundle for ChapterGradedHashimoto. See BookProof/ChapterGradedHashimoto.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGradedHashimoto.lean

import Definitions.Def_ChapterGradedFriedrichs
import Definitions.Def_ChapterStoneBridge
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_positive
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFermionFock
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterGradedFock
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib


/-!
# Chapter GradedHashimoto — the graded Hamiltonian is even, and the SIRK limit selects it

`BookProof.ChapterGradedFriedrichs` proved the analytic half of §10.6.2 item 3 of
`CONSOLIDATED_PLAN.md`: the total graded Hamiltonian

`H(A, B) = dΓˢ(A) ⊗ 1 + 1 ⊗ dΓᵃ(B)`

is densely defined, symmetric and positive on `ℓ²(Conf × FConf) ≅ Γˢ ⊗ Γᵃ` itself, hence
has a positive self-adjoint (Friedrichs) extension.  Two things that the bosonic
(`ChapterFockSecondQuantization`) and fermionic (`ChapterFermionFock`) factors each carry
were still missing on the graded space, and are proved here.

## Deliverables

**1. The Hamiltonian respects the `ℤ₂` grading.**  `support_parityF`, `modesF_parityF`
and `parityF_creVecF` (creation of a one-particle vector is odd) give
`parityF_dGammaF`: the fermionic second quantization is **even**, being a sum of products
of two odd operators.  With `liftFst_liftSnd_comm` this yields the headline
`gradeOp_gradedHamiltonianAlg`: `(−1)^{N_f} H = H (−1)^{N_f}`, so `H` commutes with the
grading operator and therefore preserves the even and the odd subspace separately
(`gradedHamiltonianAlg_evenPart`, `gradedHamiltonianAlg_oddPart`) — the graded Hamiltonian
is an *even* element of the superalgebra, as a physical Hamiltonian must be.

**2. The Hashimoto/SIRK shift-invert limit selects the Friedrichs extension** of the
graded Hamiltonian, exactly as it does factorwise: `gradedHamiltonianB` is the operator
read on the finite-mode domain of the canonical basis of `ℓ²(Conf × FConf)` re-indexed by
`ℕ`, and `graded_hashimoto_selects` gives the positive self-adjoint extension `A`, the
shift-invert resolvent `R = (A + γ)⁻¹` with `‖R‖ ≤ γ⁻¹`, the strong and resolvent-sense
convergence of the Galerkin truncations, and the *uniqueness* clause: any operator with
the same shift-invert resolvent is `A`.  `gradedSecondQuantization_hashimoto_selects`
phrases it for arbitrary symmetric positive one-particle operators given in Hilbert bases,
and `gradedNumber_hashimoto_selects` is the concrete instance for the total number
operator `N_b ⊗ 1 + 1 ⊗ N_f`, with `gradedEnum` a concrete enumeration of
`Conf × FConf` so that nothing here is vacuous.

**3. Energies add on elementary tensors.**  `gradedHamiltonianAlg_otimes`:
`H (v ⊗ w) = dΓˢ(A)v ⊗ w + v ⊗ dΓᵃ(B)w`.

**4. The graded flow.**  `graded_stone_flow` and `gradedNumber_stone_flow` push the
selected extension through the Stone bridge: the graded Hamiltonian generates a global
unitary one-parameter group on `ℓ²(Conf × FConf)` solving the Schrödinger equation on its
domain.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).

**Honest boundary.**  The one-particle space is still the abstract `ℓ²(ℕ)` of a Hilbert
basis, not the gravity space `L²(ℝ⁸⁴ × ℤ₂¹⁹)` (§10.6.2 item 4), positivity of the
one-particle matrices is a hypothesis, and no essential self-adjointness of the graded
Hamiltonian is claimed.
-/

namespace BookProof.GradedHashimoto

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization BookProof.FermionFock BookProof.GradedFock
open BookProof.GradedFriedrichs
open BookProof.ChapterStoneResolvent BookProof.StoneBridge

noncomputable section

/-! ## 1. Energies add on an elementary tensor -/

/-- **The Leibniz rule of second quantization on the graded space**:
`H (v ⊗ w) = dΓˢ(A)v ⊗ w + v ⊗ dΓᵃ(B)w`. -/
theorem gradedHamiltonianAlg_otimes (colB colF : ℕ → (ℕ →₀ ℂ)) (v : FockAlg) (w : FermiAlg) :
    gradedHamiltonianAlg colB colF (otimes v w)
      = otimes (dGamma colB v) w + otimes v (dGammaF colF w) := by
  change liftFst (dGamma colB) (otimes v w) + liftSnd (dGammaF colF) (otimes v w) = _
  rw [liftFst_otimes, liftSnd_otimes]

/-! ## 2. The graded Hamiltonian is even -/

/-- The parity operator does not change which configurations occur. -/
theorem support_parityF (u : FermiAlg) : (parityF u).support ⊆ u.support := by
  intro S hS
  rw [Finsupp.mem_support_iff] at hS ⊢
  intro h
  exact hS (by rw [parityF_apply, h, mul_zero])

theorem modesF_parityF (u : FermiAlg) : modesF (parityF u) ⊆ modesF u :=
  Finset.biUnion_subset_biUnion_of_subset_left _ (support_parityF u)

/-- **Creation of a one-particle vector is odd**: it anticommutes with the parity. -/
theorem parityF_creVecF (v : ℕ →₀ ℂ) (x : FermiAlg) :
    parityF (creVecF v x) = - creVecF v (parityF x) := by
  rw [creVecF_apply, map_sum, creVecF_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, parityF_creF, smul_neg]

/-- **The fermionic second quantization is even**: it is a sum of products of two odd
operators, so it commutes with the fermion-number parity `(−1)^{N_f}`. -/
theorem parityF_dGammaF (col : ℕ → (ℕ →₀ ℂ)) (u : FermiAlg) :
    parityF (dGammaF col u) = dGammaF col (parityF u) := by
  classical
  rw [dGammaF_eq_sum col (K := modesF u) (Finset.Subset.refl _),
    dGammaF_eq_sum col (K := modesF u) (modesF_parityF u), map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [parityF_creVecF, parityF_annF, map_neg, neg_neg]

/-- **The graded Hamiltonian is an even operator**: it commutes with the `ℤ₂` grading
`(−1)^{N_f}` of the graded Fock space. -/
theorem gradeOp_gradedHamiltonianAlg (colB colF : ℕ → (ℕ →₀ ℂ)) :
    gradeOp * gradedHamiltonianAlg colB colF
      = gradedHamiltonianAlg colB colF * gradeOp := by
  have hF : (parityF : Module.End ℂ FermiAlg) * dGammaF colF
      = (dGammaF colF : Module.End ℂ FermiAlg) * parityF :=
    LinearMap.ext fun u => parityF_dGammaF colF u
  have h1 : gradeOp * liftFst (β := FConf) (dGamma colB)
      = liftFst (β := FConf) (dGamma colB) * gradeOp := (liftFst_liftSnd_comm _ _).symm
  have h2 : gradeOp * liftSnd (α := Conf) (dGammaF colF)
      = liftSnd (α := Conf) (dGammaF colF) * gradeOp := by
    rw [gradeOp, liftSnd_mul, liftSnd_mul, hF]
  rw [gradedHamiltonianAlg, mul_add, add_mul, h1, h2]

theorem gradeOp_gradedHamiltonianAlg_apply (colB colF : ℕ → (ℕ →₀ ℂ)) (u : GradedAlg) :
    gradeOp (gradedHamiltonianAlg colB colF u)
      = gradedHamiltonianAlg colB colF (gradeOp u) := by
  have := congrArg (fun T : Module.End ℂ GradedAlg => T u)
    (gradeOp_gradedHamiltonianAlg colB colF)
  simpa only [Module.End.mul_apply] using this

/-- **The Hamiltonian preserves the even subspace.** -/
theorem gradedHamiltonianAlg_evenPart (colB colF : ℕ → (ℕ →₀ ℂ)) (u : GradedAlg) :
    gradedHamiltonianAlg colB colF (evenPart u) = evenPart (gradedHamiltonianAlg colB colF u) := by
  rw [evenPart, evenPart, map_smul, map_add, gradeOp_gradedHamiltonianAlg_apply]

/-- **The Hamiltonian preserves the odd subspace.** -/
theorem gradedHamiltonianAlg_oddPart (colB colF : ℕ → (ℕ →₀ ℂ)) (u : GradedAlg) :
    gradedHamiltonianAlg colB colF (oddPart u) = oddPart (gradedHamiltonianAlg colB colF u) := by
  rw [oddPart, oddPart, map_smul, map_sub, gradeOp_gradedHamiltonianAlg_apply]

/-! ## 3. The Hashimoto/SIRK selection on the graded space -/

section Selection

open Filter Topology

/-- The graded Hamiltonian on the finite-mode domain of the canonical basis of
`ℓ²(Conf × FConf)` re-indexed by `ℕ` — the form in which the abstract Hashimoto theorem
is stated. -/
def gradedHamiltonianB (ε : ℕ ≃ GConf) (colB colF : ℕ → (ℕ →₀ ℂ)) :
    finiteModeDomain (l2BasisN ε) →ₗ[ℂ] GFock :=
  (gradedHamiltonian colB colF).comp
    (LinearEquiv.ofEq _ _ (finiteModeDomain_l2BasisN ε)).toLinearMap

theorem gradedHamiltonianB_symmetricOn {ε : ℕ ≃ GConf} {colB colF : ℕ → (ℕ →₀ ℂ)}
    (hb : IsHermCol colB) (hf : IsHermCol colF) :
    SymmetricOn (finiteModeDomain (l2BasisN ε)) (gradedHamiltonianB ε colB colF) := by
  intro x y
  exact gradedHamiltonian_symmetricOn hb hf
    (LinearEquiv.ofEq _ _ (finiteModeDomain_l2BasisN ε) x)
    (LinearEquiv.ofEq _ _ (finiteModeDomain_l2BasisN ε) y)

theorem gradedHamiltonianB_quadForm_nonneg {ε : ℕ ≃ GConf} {colB colF : ℕ → (ℕ →₀ ℂ)}
    (hb : IsPosCol colB) (hf : IsPosCol colF) (x : finiteModeDomain (l2BasisN ε)) :
    0 ≤ quadForm (gradedHamiltonianB ε colB colF) x :=
  gradedHamiltonian_quadForm_nonneg hb hf
    (LinearEquiv.ofEq _ _ (finiteModeDomain_l2BasisN ε) x)

/-- **The Hashimoto/SIRK shift-invert limit selects the Friedrichs extension of the
graded Hamiltonian `dΓˢ(A) ⊗ 1 + 1 ⊗ dΓᵃ(B)`** on `ℓ²(Conf × FConf)`. -/
theorem graded_hashimoto_selects (ε : ℕ ≃ GConf) {colB colF : ℕ → (ℕ →₀ ℂ)}
    (hbherm : IsHermCol colB) (hbpos : IsPosCol colB)
    (hfherm : IsHermCol colF) (hfpos : IsPosCol colF) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ GFock) (A : Dom →ₗ[ℂ] GFock) (R : GFock →L[ℂ] GFock),
      IsPositiveSelfAdjointExtension (gradedHamiltonianB ε colB colF) A ∧
        IsShiftInvert A γ R ∧ ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
        (∀ u : GFock, Tendsto (fun k : ℕ => galerkinCompression R (l2BasisN ε) k u)
          atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : GFock,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R (l2BasisN ε) k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ GFock) (A' : Dom' →ₗ[ℂ] GFock), IsShiftInvert A' γ R →
          Dom' = Dom ∧ ∀ (x : GFock) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
            A' ⟨x, hx'⟩ = A ⟨x, hx⟩) :=
  friedrichs_hashimoto_selects (l2BasisN ε) (gradedHamiltonianB ε colB colF)
    (gradedHamiltonianB_symmetricOn hbherm hfherm)
    (gradedHamiltonianB_quadForm_nonneg hbpos hfpos) hγ

/-- A concrete enumeration of the graded configurations, so that the selection theorem is
not vacuous. -/
def gradedEnum : ℕ ≃ GConf :=
  letI : Denumerable GConf := Denumerable.ofEncodableOfInfinite _
  (Denumerable.eqv GConf).symm

/-- **The Hashimoto/SIRK algorithm selects the Friedrichs extension of the graded second
quantization of a pair of arbitrary symmetric positive one-particle operators.** -/
theorem gradedSecondQuantization_hashimoto_selects {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (ε : ℕ ≃ GConf) (bB : HilbertBasis ℕ ℂ F) (bF : HilbertBasis ℕ ℂ G)
    (A : finiteModeDomain bB →ₗ[ℂ] finiteModeDomain bB)
    (B : finiteModeDomain bF →ₗ[ℂ] finiteModeDomain bF)
    (hA : SymmetricOn (finiteModeDomain bB) ((finiteModeDomain bB).subtype.comp A))
    (hAp : ∀ x, 0 ≤ quadForm ((finiteModeDomain bB).subtype.comp A) x)
    (hB : SymmetricOn (finiteModeDomain bF) ((finiteModeDomain bF).subtype.comp B))
    (hBp : ∀ x, 0 ≤ quadForm ((finiteModeDomain bF).subtype.comp B) x)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ GFock) (A' : Dom →ₗ[ℂ] GFock) (R : GFock →L[ℂ] GFock),
      IsPositiveSelfAdjointExtension
          (gradedHamiltonianB ε (opCol bB A) (opCol bF B)) A' ∧
        IsShiftInvert A' γ R ∧ ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
        (∀ u : GFock, Tendsto (fun k : ℕ => galerkinCompression R (l2BasisN ε) k u)
          atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : GFock,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R (l2BasisN ε) k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ GFock) (A'' : Dom' →ₗ[ℂ] GFock), IsShiftInvert A'' γ R →
          Dom' = Dom ∧ ∀ (x : GFock) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
            A'' ⟨x, hx'⟩ = A' ⟨x, hx⟩) :=
  graded_hashimoto_selects ε (isHermCol_opCol hA) (isPosCol_opCol hAp)
    (isHermCol_opCol hB) (isPosCol_opCol hBp) hγ

/-- **The concrete instance**: the Hashimoto/SIRK limit selects the Friedrichs extension
of the total graded number operator `N_b ⊗ 1 + 1 ⊗ N_f`, whose eigenvalue on a
one-boson/one-fermion state is `2` (`gradedNumber_one_particle`). -/
theorem gradedNumber_hashimoto_selects {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ GFock) (A : Dom →ₗ[ℂ] GFock) (R : GFock →L[ℂ] GFock),
      IsPositiveSelfAdjointExtension (gradedHamiltonianB gradedEnum idCol idCol) A ∧
        IsShiftInvert A γ R ∧ ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
        (∀ u : GFock, Tendsto (fun k : ℕ => galerkinCompression R (l2BasisN gradedEnum) k u)
          atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : GFock,
          Tendsto (fun k : ℕ =>
            resolvent (galerkinCompression R (l2BasisN gradedEnum) k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ GFock) (A' : Dom' →ₗ[ℂ] GFock), IsShiftInvert A' γ R →
          Dom' = Dom ∧ ∀ (x : GFock) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
            A' ⟨x, hx'⟩ = A ⟨x, hx⟩) :=
  graded_hashimoto_selects gradedEnum isHermCol_idCol isPosCol_idCol
    isHermCol_idCol isPosCol_idCol hγ

end Selection

/-! ## 4. The unitary flow of the graded Hamiltonian -/

/-- **The graded Hamiltonian generates a complete unitary flow.**  Its Friedrichs
extension is self-adjoint, so Stone's theorem gives a one-parameter group `U t` on
`ℓ²(Conf × FConf)` — global in `t`, unitary, and solving `d/dt (U t x) = -i A (U t x)` on
the domain. -/
theorem graded_stone_flow {colB colF : ℕ → (ℕ →₀ ℂ)}
    (hbherm : IsHermCol colB) (hbpos : IsPosCol colB)
    (hfherm : IsHermCol colF) (hfpos : IsPosCol colF) :
    ∃ (Dom : Submodule ℂ GFock) (A : Dom →ₗ[ℂ] GFock) (T : UnboundedSelfAdjoint GFock)
      (U : ℝ → (GFock →L[ℂ] GFock)),
      IsPositiveSelfAdjointExtension (gradedHamiltonian colB colF) A ∧
        T.domain = Dom ∧ HEq T.op A ∧ IsStoneFlow T U := by
  obtain ⟨Dom, A, hA⟩ := gradedHamiltonian_friedrichs_extension hbherm hbpos hfherm hfpos
  obtain ⟨T, U, hdom, hop, hflow⟩ :=
    exists_stone_flow_of_positive (Hc := gradedHamiltonian colB colF)
      lpFiniteModes_dense hA
  exact ⟨Dom, A, T, U, hA, hdom, hop, hflow⟩

/-- **The concrete instance**: the total graded number operator `N_b ⊗ 1 + 1 ⊗ N_f`
generates a complete unitary flow on the graded Fock space. -/
theorem gradedNumber_stone_flow :
    ∃ (Dom : Submodule ℂ GFock) (A : Dom →ₗ[ℂ] GFock) (T : UnboundedSelfAdjoint GFock)
      (U : ℝ → (GFock →L[ℂ] GFock)),
      IsPositiveSelfAdjointExtension (gradedHamiltonian idCol idCol) A ∧
        T.domain = Dom ∧ HEq T.op A ∧ IsStoneFlow T U :=
  graded_stone_flow isHermCol_idCol isPosCol_idCol isHermCol_idCol isPosCol_idCol

end

end BookProof.GradedHashimoto


