-- Prove2me | Definitions.Def_ChapterNavierStokesAffineBlockEsa
-- name    : ChapterNavierStokesAffineBlockEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T06:28:26.769148+00:00
-- url     : https://prove2.me/theorems/17bb0b88-3d4e-40da-990e-3c7d765bd4b5
-- title:
--   The Lean 4 theorem `shiftProd_injective` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesAffineBlockEsa.lean`): generated def bundle for ChapterNavierStokesAffineBlockEsa. See BookProof/ChapterNavierStokesAffineBlockEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesAffineBlockEsa.lean

import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_hFun_add

import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_hFun_smul


import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_support_hFun


import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesEsa
import Mathlib


/-!
# The bilinear Navier–Stokes generator **with the viscous and cross terms**

`BookProof.ChapterNavierStokesBilinearEsa` proves essential self-adjointness of
the bilinear (quadratic-symbol) Navier–Stokes generator on `ℓ²(ℕ × J)` by
splitting it into blocks indexed by the spectrum `J` of the derivative field: in
the block `j` the symbol becomes the *linear* fiber field `V(u) = κ_j u`.  Its
recorded boundary was the *affine* fiber field

`V(u) = κ_j u + c_j`,

which is what the viscous term `−ν u_{i,jj}` and the cross terms `u_j u_{i,j}`
with `j ≠ i` contribute: those are constants in the velocity mode `u_i` that the
momentum `π_i` differentiates, and — like the strain rates — they are functions
of the derivative field, hence constant on each block.

`BookProof.ChapterNavierStokesAffineFiberEsa` removes that boundary at the level
of one fiber.  This module runs the block decomposition again with the affine
fiber Hamiltonian in place of the linear one, and so covers the viscous and
cross terms.

## What is proved

* `affBlockH` — the Navier–Stokes generator on the finite-mode core of
  `ℓ²(ℕ × J)` whose block `j` is the **affine** fiber Hamiltonian
  `½(π V + V π)` with `V(u) = κ_j u + c_j`, for arbitrary families
  `κ, c : J → ℝ` of non-negative strain rates and constants (no boundedness, no
  finiteness of `J`);
* `affFun_embFun` and `blockVec_affBlockH` — the block identification: on the
  block `j` the operator *is* `AffineFiber.affH (κ j) (c j)`;
* `affBlockH_symmetricOn` — it is symmetric on the finite-mode core;
* `deficiencyTrivialAt_affBlockH` — the block reduction of the deficiency
  problem;
* `affBlockH_essentiallySelfAdjointOn_core` — **the headline**: it is
  essentially self-adjoint on the finite-mode core;
* `affBlockH_not_bounded` — and it is genuinely unbounded as soon as the strain
  rates are.

## Honest boundary

`c_j ≥ 0` is assumed, for the reason recorded in
`ChapterNavierStokesAffineFiberEsa` (a `ShiftData` amplitude must be
non-negative); the sign-flip unitary that would remove it is not formalized.
Only one velocity component is carried: the three coupled components of the full
symbol are not.  Everything is stated on the abstract space `ℓ²(ℕ × J)` with the
block operator given by its matrix in the Hermite basis of the fiber; the
differential realization on `L²(du)` is not built here.  Nothing here claims
global regularity for the classical Navier–Stokes equation, which remains the
recorded scope cut.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace AffineBlock

open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber BilinearEsa

variable {J : Type*}

/-! ## The generator -/

/-- The coordinates of the Navier–Stokes generator with affine fiber fields: in
the block `j` it is the sum of the `±2`-hopping of `κ_j` and the `±1`-hopping of
`c_j`. -/
noncomputable def affFun (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j)
    (X : ℕ × J → ℂ) : ℕ × J → ℂ :=
  fun p => (affData (hκ p.2) (hc p.2)).fst.hFun (fun n => X (n, p.2)) p.1
    + (affData (hκ p.2) (hc p.2)).snd.hFun (fun n => X (n, p.2)) p.1

theorem shiftProd_injective (k : ℕ) :
    Function.Injective (fun p : ℕ × J => (p.1 + k, p.2)) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Prod.mk.injEq]
  exact ⟨by omega, h2⟩

theorem support_affFun (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j)
    (X : ℕ × J → ℂ) :
    Function.support (affFun κ c hκ hc X)
      ⊆ (((fun p : ℕ × J => (p.1 + 2, p.2)) '' Function.support X)
          ∪ ((fun p : ℕ × J => (p.1 + 2, p.2)) ⁻¹' Function.support X))
        ∪ (((fun p : ℕ × J => (p.1 + 1, p.2)) '' Function.support X)
          ∪ ((fun p : ℕ × J => (p.1 + 1, p.2)) ⁻¹' Function.support X)) := by
  rintro ⟨m, j⟩ hp
  simp only [Function.mem_support, affFun] at hp
  by_cases h1 : (affData (hκ j) (hc j)).fst.hFun (fun n => X (n, j)) m = 0
  · have h2 : (affData (hκ j) (hc j)).snd.hFun (fun n => X (n, j)) m ≠ 0 := by
      intro h
      exact hp (by rw [h1, h]; ring)
    have hmem := support_hFun (affData (hκ j) (hc j)).snd (fun n => X (n, j)) h2
    rcases hmem with ⟨a, ha, hae⟩ | hpre
    · refine Or.inr (Or.inl ⟨(a, j), ha, ?_⟩)
      simp only [Prod.mk.injEq]
      exact ⟨hae, trivial⟩
    · exact Or.inr (Or.inr hpre)
  · have hmem := support_hFun (affData (hκ j) (hc j)).fst (fun n => X (n, j)) h1
    rcases hmem with ⟨a, ha, hae⟩ | hpre
    · refine Or.inl (Or.inl ⟨(a, j), ha, ?_⟩)
      simp only [Prod.mk.injEq]
      exact ⟨hae, trivial⟩
    · exact Or.inl (Or.inr hpre)

theorem affFun_finite_support (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j)
    (x : lpFiniteModes (ℕ × J)) :
    (Function.support (affFun κ c hκ hc (((x : L2I (ℕ × J))) : ℕ × J → ℂ))).Finite := by
  have hx := mem_lpFiniteModes.mp x.2
  refine Set.Finite.subset
    (((hx.image _).union (Set.Finite.preimage (shiftProd_injective 2).injOn hx)).union
      ((hx.image _).union (Set.Finite.preimage (shiftProd_injective 1).injOn hx)))
    (support_affFun κ c hκ hc _)

/-- **The Navier–Stokes generator with affine fiber fields** on the finite-mode
core of `ℓ²(ℕ × J)`: block `j` carries the field `V(u) = κ_j u + c_j`, the
constant `c_j` being the contribution of the viscous term and of the cross
terms. -/
noncomputable def affBlockH (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) :
    lpFiniteModes (ℕ × J) →ₗ[ℂ] L2I (ℕ × J) where
  toFun x := ⟨affFun κ c hκ hc (((x : L2I (ℕ × J))) : ℕ × J → ℂ),
    memLpTwo_of_finite_support (affFun_finite_support κ c hκ hc x)⟩
  map_add' x y := by
    refine lp.ext (funext fun p => ?_)
    simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply, affFun]
    rw [hFun_add, hFun_add]
    ring
  map_smul' a x := by
    refine lp.ext (funext fun p => ?_)
    simp only [Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      affFun]
    rw [hFun_smul, hFun_smul]
    ring

@[simp] theorem affBlockH_coe (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j)
    (x : lpFiniteModes (ℕ × J)) (p : ℕ × J) :
    ((affBlockH κ c hκ hc x : L2I (ℕ × J)) : ℕ × J → ℂ) p
      = affFun κ c hκ hc (((x : L2I (ℕ × J))) : ℕ × J → ℂ) p := rfl

/-! ## The block identification -/







/-! ## Symmetry -/



/-! ## Essential self-adjointness -/





/-! ## Non-vacuity -/





end AffineBlock

end BookProof.NavierStokesFlow


