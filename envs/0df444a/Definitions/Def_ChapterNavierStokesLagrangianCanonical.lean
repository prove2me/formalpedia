-- Prove2me | Definitions.Def_ChapterNavierStokesLagrangianCanonical
-- name    : ChapterNavierStokesLagrangianCanonical
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T12:39:59.92345+00:00
-- url     : https://prove2.me/theorems/ed0b5a8e-ce81-4172-abf2-fa29859f922e
-- title:
--   The Eulerian strand of the Navier–Stokes thread has a canonical/ladder reading of its full quadratic symbol (`BookProof. ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesLagrangianCanonical`, source chapter `BookProof/ChapterNavierStokesLagrangianCanonical.lean`).
--
--   The Eulerian strand of the Navier–Stokes thread has a canonical/ladder reading of its full quadratic symbol (`BookProof.ChapterNavierStokesCanonicalVector`) and a Hermite realization of the fiber generator (`BookProof.ChapterNavierStokesHermiteCanonical`). The Lagrangian (parcel) strand had essential self-adjointness (`ChapterNavierStokesLagrangianKatoRellich`), the Hashimoto/SIRK selection, the Fock-of-Fock lifting and the Stone flow, but its positive second-order part
--
--   `T = ½ ∑ᵢ Pᵢ² + ν ∑ᵢ Qᵢ²`
--
--   was realized concretely only on the abstract *diagonal* instance `diagKR` of `ℓ²(ℕ)`, where `Pᵢ` and `Qᵢ` commute. This module removes that asymmetry: it realizes the parcel momenta `Pᵢ` and the viscous gradients `Qᵢ` as the genuinely **non-commuting** canonical pairs of a Hermite basis of the trajectory space `ℓ²(Fin 3 → ℕ)`, and proves the second-order part is essentially self-adjoint there.
--
--   For a viscosity `ν > 0` put `ω = √(2ν)` and, out of the Hermite ladder operators `a_i`, `a_i†` of `BookProof.NavierStokesFlow.CanonicalVector`,
--
--   `Qᵢ = ω^{-1/2} · (a_i + a_i†)/√2`, `Pᵢ = ω^{1/2} · i(a_i† − a_i)/√2`.
--
--   These are the position and momentum of the oscillator of frequency `ω`; the canonical commutation relations survive the rescaling (`comm_lagP_lagQ`, `comm_lagP_lagQ_of_ne`), so `Pᵢ` and `Qᵢ` genuinely fail to commute — the point on which the diagonal instance `diagKR` was silent.
--
--   The identity that makes the module work is
--
--   `½ Pᵢ² + ν Qᵢ² = (ω/2)(πᵢ² + uᵢ²) = ω (a_i† a_i + ½)`,
--
--   which is exactly the choice `ω = √(2ν)` (`lagT_eq_number`). Summed over the three parcel directions the Lagrangian second-order part is therefore the number operator of the trajectory-space Hermite basis, `T = ω(N + 3/2)`, whose eigenvectors are the Hermite states `e_β` (`lagT_coreState`) — a total family, so `T` is essentially self-adjoint on the Hermite core (`lagT_esa`), unbounded (`lagT_not_bounded`).
--
--   * `lagQ`, `lagP` — the canonical pairs of the trajectory space, with `comm_lagP_lagQ` (`[Pᵢ, Qᵢ] = −i`), `comm_lagP_lagQ_of_ne` and the symmetry statements `lagQ_isSymmetricDom`, `lagP_isSymmetricDom` (from the adjoint relation `inner_ann_cre` between the ladder operators); * `lagT_eq_number` — `½ ∑Pᵢ² + ν ∑Qᵢ² = ω (N + 3/2)`, `N = ∑ a_i† a_i`; * `lagT_coreState`, `lagT_esa`, `lagT_not_bounded` — the Hermite states diagonalize it, it is essentially self-adjoint on the Hermite core and it is unbounded; * `lagCanData` — the resulting `LagrangianFullData` on `ℓ²(Fin 3 → ℕ)`: the canonical/ladder realization of the transformed Navier–Stokes Hamiltonian, with the physical drift `Dᵢ = Pᵢ` and an arbitrary external force; * `lagCan_secondOrder_eq`, `lagCan_esa` — its second-order part is the operator above and the **full** transformed Hamiltonian is essentially self-adjoint on the Hermite core, by the Kato–Rellich relative bound of `ChapterNavierStokesLagrangianKatoRellich`; * `lagCan_stone_flow` — hence the canonical Lagrangian Hamiltonian generates a complete unitary flow (Stone), bringing the Lagrangian strand to the same realization level as the Eulerian one.
--
--   Unchanged (Contention D5): nothing here claims global regularity of the *classical* Navier–Stokes PDE. The trajectory space is the Hermite (occupation-number) realization `ℓ²(Fin 3 → ℕ)` of the parcel coordinates, in which `Qᵢ` is the coordinate and `Pᵢ = −i∂/∂Xᵢ` the momentum, exactly as on the Eulerian side.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesLagrangianCanonical.lean

import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterStoneBridge
import Mathlib

import Mathlib

/-!
# The canonical (ladder) realization of the Lagrangian Navier–Stokes Hamiltonian

The Eulerian strand of the Navier–Stokes thread has a canonical/ladder reading of
its full quadratic symbol (`BookProof.ChapterNavierStokesCanonicalVector`) and a
Hermite realization of the fiber generator
(`BookProof.ChapterNavierStokesHermiteCanonical`).  The Lagrangian (parcel)
strand had essential self-adjointness (`ChapterNavierStokesLagrangianKatoRellich`),
the Hashimoto/SIRK selection, the Fock-of-Fock lifting and the Stone flow, but its
positive second-order part

`T = ½ ∑ᵢ Pᵢ² + ν ∑ᵢ Qᵢ²`

was realized concretely only on the abstract *diagonal* instance `diagKR` of
`ℓ²(ℕ)`, where `Pᵢ` and `Qᵢ` commute.  This module removes that asymmetry: it
realizes the parcel momenta `Pᵢ` and the viscous gradients `Qᵢ` as the genuinely
**non-commuting** canonical pairs of a Hermite basis of the trajectory space
`ℓ²(Fin 3 → ℕ)`, and proves the second-order part is essentially self-adjoint
there.

## The construction

For a viscosity `ν > 0` put `ω = √(2ν)` and, out of the Hermite ladder operators
`a_i`, `a_i†` of `BookProof.NavierStokesFlow.CanonicalVector`,

`Qᵢ = ω^{-1/2} · (a_i + a_i†)/√2`,   `Pᵢ = ω^{1/2} · i(a_i† − a_i)/√2`.

These are the position and momentum of the oscillator of frequency `ω`; the
canonical commutation relations survive the rescaling (`comm_lagP_lagQ`,
`comm_lagP_lagQ_of_ne`), so `Pᵢ` and `Qᵢ` genuinely fail to commute — the point
on which the diagonal instance `diagKR` was silent.

The identity that makes the module work is

`½ Pᵢ² + ν Qᵢ² = (ω/2)(πᵢ² + uᵢ²) = ω (a_i† a_i + ½)`,

which is exactly the choice `ω = √(2ν)` (`lagT_eq_number`).  Summed over the
three parcel directions the Lagrangian second-order part is therefore the
number operator of the trajectory-space Hermite basis, `T = ω(N + 3/2)`, whose
eigenvectors are the Hermite states `e_β` (`lagT_coreState`) — a total family,
so `T` is essentially self-adjoint on the Hermite core (`lagT_esa`), unbounded
(`lagT_not_bounded`).

## What is proved

* `lagQ`, `lagP` — the canonical pairs of the trajectory space, with
  `comm_lagP_lagQ` (`[Pᵢ, Qᵢ] = −i`), `comm_lagP_lagQ_of_ne` and the symmetry
  statements `lagQ_isSymmetricDom`, `lagP_isSymmetricDom` (from the adjoint
  relation `inner_ann_cre` between the ladder operators);
* `lagT_eq_number` — `½ ∑Pᵢ² + ν ∑Qᵢ² = ω (N + 3/2)`, `N = ∑ a_i† a_i`;
* `lagT_coreState`, `lagT_esa`, `lagT_not_bounded` — the Hermite states
  diagonalize it, it is essentially self-adjoint on the Hermite core and it is
  unbounded;
* `lagCanData` — the resulting `LagrangianFullData` on `ℓ²(Fin 3 → ℕ)`: the
  canonical/ladder realization of the transformed Navier–Stokes Hamiltonian,
  with the physical drift `Dᵢ = Pᵢ` and an arbitrary external force;
* `lagCan_secondOrder_eq`, `lagCan_esa` — its second-order part is the operator
  above and the **full** transformed Hamiltonian is essentially self-adjoint on
  the Hermite core, by the Kato–Rellich relative bound of
  `ChapterNavierStokesLagrangianKatoRellich`;
* `lagCan_stone_flow` — hence the canonical Lagrangian Hamiltonian generates a
  complete unitary flow (Stone), bringing the Lagrangian strand to the same
  realization level as the Eulerian one.

## Honest boundary

Unchanged (Contention D5): nothing here claims global regularity of the
*classical* Navier–Stokes PDE.  The trajectory space is the Hermite
(occupation-number) realization `ℓ²(Fin 3 → ℕ)` of the parcel coordinates, in
which `Qᵢ` is the coordinate and `Pᵢ = −i∂/∂Xᵢ` the momentum, exactly as on the
Eulerian side.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace LagrangianCanonical

open LpNat FarisLavine IkebeKato FullEsa LagrangianEsa LagrangianKatoRellich
open CanonicalVector ThreeComponent


namespace BookProof.NavierStokesFlow

namespace CanonicalVector

@[simp] theorem lower_raise (i : Fin 3) (β : Vel) : lower i (raise i β) = β := by
  funext j
  by_cases hji : j = i
  · subst hji; rw [lower_self, raise_self]; omega
  · rw [lower_of_ne hji, raise_of_ne hji]

end CanonicalVector

end BookProof.NavierStokesFlow

/-! ## The adjoint relation between the ladder operators -/

theorem raise_injective (i : Fin 3) : Function.Injective (raise i) := by
  intro β γ h
  have := congrArg (lower i) h
  simpa using this

/-- Off the range of `raise i` — i.e. at the multi-indices with `β i = 0` — the
creation amplitude vanishes. -/
theorem cFun_vanishes_off_range (i : Fin 3) (X : Vel → ℂ) {β : Vel}
    (h : β ∉ Set.range (raise i)) (Y : Vel → ℂ) :
    (Real.sqrt (β i) : ℂ) * X (lower i β) * Y β = 0 := by
  have hzero : β i = 0 := by
    by_contra hne
    exact h ⟨lower i β, raise_lower i (Nat.one_le_iff_ne_zero.mpr hne)⟩
  simp [hzero]

/-- **The ladder operators are mutually adjoint** on the finite-mode core:
`⟪x, a_i y⟫ = ⟪a_i† x, y⟫`. -/
theorem inner_ann_cre (i : Fin 3) (x y : lpFiniteModes Vel) :
    (inner ℂ ((x : L2I Vel)) ((ann i y : lpFiniteModes Vel) : L2I Vel) : ℂ)
      = inner ℂ ((cre i x : lpFiniteModes Vel) : L2I Vel) ((y : L2I Vel)) := by
  classical
  have hL := lp.hasSum_inner (𝕜 := ℂ) ((x : L2I Vel)) ((ann i y : lpFiniteModes Vel) : L2I Vel)
  have hR := lp.hasSum_inner (𝕜 := ℂ) ((cre i x : lpFiniteModes Vel) : L2I Vel) ((y : L2I Vel))
  have hLfun : (fun β => (inner ℂ (((x : L2I Vel) : Vel → ℂ) β)
        ((((ann i y : lpFiniteModes Vel) : L2I Vel) : Vel → ℂ) β) : ℂ))
      = fun β => (Real.sqrt ((β i : ℝ) + 1) : ℂ)
          * (starRingEnd ℂ) (((x : L2I Vel) : Vel → ℂ) β)
          * ((y : L2I Vel) : Vel → ℂ) (raise i β) := by
    funext β
    have hcoe : ((((ann i y : lpFiniteModes Vel) : L2I Vel) : Vel → ℂ) β)
        = (Real.sqrt ((β i : ℝ) + 1) : ℂ) * ((y : L2I Vel) : Vel → ℂ) (raise i β) := rfl
    simp only [RCLike.inner_apply, hcoe]
    ring
  have hRfun : (fun β => (inner ℂ ((((cre i x : lpFiniteModes Vel) : L2I Vel) : Vel → ℂ) β)
        (((y : L2I Vel) : Vel → ℂ) β) : ℂ))
      = fun β => (Real.sqrt (β i : ℝ) : ℂ)
          * (starRingEnd ℂ) (((x : L2I Vel) : Vel → ℂ) (lower i β))
          * ((y : L2I Vel) : Vel → ℂ) β := by
    funext β
    have hcoe : (((cre i x : lpFiniteModes Vel) : L2I Vel) : Vel → ℂ) β
        = (Real.sqrt (β i : ℝ) : ℂ) * ((x : L2I Vel) : Vel → ℂ) (lower i β) := rfl
    simp only [RCLike.inner_apply, hcoe, map_mul, Complex.conj_ofReal]
    ring
  rw [hLfun] at hL
  rw [hRfun] at hR
  -- the two summand families agree after the reindexing `β ↦ raise i β`
  set g : Vel → ℂ := fun β => (Real.sqrt (β i : ℝ) : ℂ)
      * (starRingEnd ℂ) (((x : L2I Vel) : Vel → ℂ) (lower i β))
      * ((y : L2I Vel) : Vel → ℂ) β with hg
  have hsupp : Function.support g ⊆ Set.range (raise i) := by
    intro β hβ
    by_contra hnot
    exact hβ (cFun_vanishes_off_range i
      (fun γ => (starRingEnd ℂ) (((x : L2I Vel) : Vel → ℂ) γ)) hnot _)
  have hcomp : (fun γ => g (raise i γ))
      = fun β => (Real.sqrt ((β i : ℝ) + 1) : ℂ)
          * (starRingEnd ℂ) (((x : L2I Vel) : Vel → ℂ) β)
          * ((y : L2I Vel) : Vel → ℂ) (raise i β) := by
    funext γ
    simp only [hg, raise_self, BookProof.NavierStokesFlow.CanonicalVector.lower_raise]
    push_cast
    ring
  have hkey : ∑' γ, g (raise i γ) = ∑' β, g β :=
    (raise_injective i).tsum_eq hsupp
  rw [hcomp] at hkey
  rw [← hL.tsum_eq, ← hR.tsum_eq]
  exact hkey

/-- The mirror form: `⟪x, a_i† y⟫ = ⟪a_i x, y⟫`. -/
theorem inner_cre_ann (i : Fin 3) (x y : lpFiniteModes Vel) :
    (inner ℂ ((x : L2I Vel)) ((cre i y : lpFiniteModes Vel) : L2I Vel) : ℂ)
      = inner ℂ ((ann i x : lpFiniteModes Vel) : L2I Vel) ((y : L2I Vel)) := by
  have h := inner_ann_cre i y x
  have h1 := congrArg (starRingEnd ℂ) h
  rw [inner_conj_symm, inner_conj_symm] at h1
  exact h1.symm

/-- The fiber coordinate is symmetric. -/
theorem pos_isSymmetricDom (i : Fin 3) : IsSymmetricDom (pos i) := by
  intro x y
  simp only [pos, LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul,
    Submodule.coe_add, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    Complex.conj_ofReal]
  rw [inner_cre_ann i x y, inner_ann_cre i x y]
  ring

/-- The momentum is symmetric. -/
theorem mom_isSymmetricDom (i : Fin 3) : IsSymmetricDom (mom i) := by
  intro x y
  simp only [mom, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul,
    Submodule.coe_sub, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [inner_cre_ann i x y, inner_ann_cre i x y]
  ring

/-! ## The number operator of the Hermite basis -/

/-- The **number operator** of the mode `i`: `N_i = a_i† a_i`. -/
noncomputable def numOp (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  (cre i).comp (ann i)







/-! ## The canonical pairs of the trajectory space -/

variable (nu : ℝ)

/-- The oscillator frequency selected by the viscosity, `ω = √(2ν)`. -/
noncomputable def omega (nu : ℝ) : ℝ := Real.sqrt (2 * nu)





/-- **The viscous gradient** `Qᵢ = ω^{-1/2} uᵢ` — the parcel coordinate in the
oscillator normalization selected by the viscosity. -/
noncomputable def lagQ (nu : ℝ) (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  (((Real.sqrt (omega nu))⁻¹ : ℝ) : ℂ) • pos i

/-- **The parcel momentum** `Pᵢ = ω^{1/2} πᵢ`, `πᵢ = -i∂/∂Xᵢ`. -/
noncomputable def lagP (nu : ℝ) (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  ((Real.sqrt (omega nu) : ℝ) : ℂ) • mom i

theorem lagQ_isSymmetricDom (i : Fin 3) : IsSymmetricDom (lagQ nu i) :=
  IsSymmetricDom.real_smul (pos_isSymmetricDom i) _

theorem lagP_isSymmetricDom (i : Fin 3) : IsSymmetricDom (lagP nu i) :=
  IsSymmetricDom.real_smul (mom_isSymmetricDom i) _





/-! ## The second-order part is the number operator -/



/-! ## The canonical Lagrangian data, and its essential self-adjointness -/

/-- **The Lagrangian (parcel) Navier–Stokes data in the canonical realization**:
the trajectory space is the Hermite space `ℓ²(Fin 3 → ℕ)` of the three parcel
coordinates, the parcel momenta and viscous gradients are the canonical pairs
`Pᵢ`, `Qᵢ` above (so they do **not** commute), the drift is the physical
`Dᵢ = Pᵢ` and there is no constraint term. -/
noncomputable def lagCanData (nu : ℝ) (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    LagrangianFullData (L2I Vel) where
  D := lpFiniteModes Vel
  P := lagP nu
  Q := lagQ nu
  drive := lagP nu
  force := f
  constraintOp := 0
  nu := nu
  dense := lpFiniteModes_dense
  P_symm := lagP_isSymmetricDom nu
  Q_symm := lagQ_isSymmetricDom nu
  drive_symm := lagP_isSymmetricDom nu
  constraint_symm := by intro x y; simp
  nu_nonneg := le_of_lt hnu



/-- The Lagrangian second-order part in its diagonal form: `ω(N + 3/2)`. -/
noncomputable def lagT (nu : ℝ) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  ((omega nu : ℝ) : ℂ) • (∑ i : Fin 3, numOp i)
    + ((3 * omega nu / 2 : ℝ) : ℂ) • LinearMap.id



/-! ## Diagonalization by the Hermite states -/





/-- The eigenvalue of the second-order part at the Hermite state `e_β`:
`ω(|β| + 3/2)`. -/
noncomputable def lagLam (nu : ℝ) (β : Vel) : ℝ :=
  omega nu * (∑ i : Fin 3, (β i : ℝ)) + 3 * omega nu / 2













/-! ## Unboundedness, and the complete unitary flow -/







end LagrangianCanonical

end BookProof.NavierStokesFlow


