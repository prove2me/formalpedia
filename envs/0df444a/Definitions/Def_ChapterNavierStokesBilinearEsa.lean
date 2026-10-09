-- Prove2me | Definitions.Def_ChapterNavierStokesBilinearEsa
-- name    : ChapterNavierStokesBilinearEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-08T15:20:00.785466+00:00
-- url     : https://prove2.me/theorems/3d013827-f1a1-41d8-ac9f-2819727577a1
-- title:
--   The Lean 4 theorem `support_embFun` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesBilinearEsa.lean`): generated def bundle for ChapterNavierStokesBilinearEsa. See BookProof/ChapterNavierStokesBilinearEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesBilinearEsa.lean

import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_summable_normSq

import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesEsa
import Mathlib


/-!
# The **bilinear** (quadratic-symbol) Navier–Stokes generator is essentially
self-adjoint

`BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine
inequalities, and hence essential self-adjointness, for the Navier–Stokes fiber
Hamiltonian `H = ½(π V + V π)` with a **linear** advection field `V(u) = κ u`
and a *fixed* strain rate `κ`.  The residual recorded in the plan
(`CONSOLIDATED_PLAN.md` §9, "what is missing from the NS-FLOW plan") is the same
statement for the genuinely **quadratic** Navier–Stokes symbol

`A_i = ∑_j u_j u_{i,j} − ν u_{i,jj}`,

in the *Eulerian derivatives-as-fields* picture.  This module closes that
residual for the bilinear advection term, in the following precise sense.

## Why the quadratic symbol is a direct sum of linear ones

In the derivatives-as-fields construction the derivative modes `u_{i,j}` are
**independent field coordinates**, and — this is the structural point — the
Hamiltonian of the book carries momenta only for the velocity modes,
`H = ∑_i (π_i A_i + A_i π_i)` with `π_i = −i ∂/∂u_i`.  The derivative field is
therefore a *constant of the motion*: it commutes with `H`.  Diagonalising it,
the Hilbert space splits as `ℓ²(ℕ) ⊗ ℓ²(J) = ℓ²(ℕ × J)` — the Hermite levels of
the velocity fiber times the (joint) spectrum `J` of the derivative field — and
in the block `j` the bilinear symbol `A = u_{,1} · u` becomes the **linear**
field `V(u) = κ_j u`, with `κ_j` the eigenvalue of the derivative field.  The
strain rate is no longer a constant: it ranges over `J` and is in general
**unbounded**, which is exactly why no single pair of Faris–Lavine constants can
serve, and why the block decomposition, not a global Faris–Lavine estimate, is
the right instrument.

## What is proved

* `bilH` — the bilinear Navier–Stokes Hamiltonian on `ℓ²(ℕ × J)`, on the
  finite-mode core, for an **arbitrary** family of non-negative strain rates
  `κ : J → ℝ` (no boundedness, no finiteness of `J`);
* `bilFun_embFun` and `blockVec_bilH_apply` — the block identification: on the
  block `j` the operator *is* the fiber Hamiltonian `nsH (κ j)` of
  `ChapterNavierStokesHermiteFarisLavine`;
* `hasSum_inner_blocks` — the inner product of `ℓ²(ℕ × J)` is the sum of the
  fiber inner products over the blocks;
* `bilH_symmetricOn` — the Hamiltonian is symmetric on the finite-mode core;
* `deficiencyTrivialAt_bilH` — the block reduction of the deficiency problem: a
  deficiency vector of the whole operator restricts to a deficiency vector of
  each block;
* `bilH_essentiallySelfAdjointOn_core` — **the headline**: the bilinear
  Navier–Stokes Hamiltonian is essentially self-adjoint on the finite-mode core,
  for every family of strain rates, bounded or not;
* `bilH_not_bounded` — and it is genuinely unbounded as soon as the strain rates
  are, so the conclusion is not a boundedness phenomenon.

## Honest boundary

Everything below is stated on the abstract space `ℓ²(ℕ × J)`, with the block
operator given by its matrix in the Hermite basis of the fiber; the concrete
differential realization on `L²(du)` is not built here, exactly as in
`ChapterNavierStokesHermiteFarisLavine`.  The blocks handled are the ones whose
fiber field is `V(u) = κ_j u`.  The viscous term `−ν u_{i,jj}` and the cross
terms `u_j u_{i,j}` with `j ≠ i` add a *constant* (in `u_i`) to the fiber field,
making it affine, `V(u) = κ_j u + c_j`.  Covering that needs a `±1`-shift on top
of the `±2`-shift, and it is done in
`BookProof.ChapterNavierStokesAffineFiberEsa` (one fiber) and
`BookProof.ChapterNavierStokesAffineBlockEsa` (the block decomposition again,
with the affine fiber Hamiltonian in place of the linear one), for `c_j ≥ 0`.
Only one velocity component is carried: the three coupled components of the full
symbol are not.  Nothing here claims global regularity for the classical
Navier–Stokes equation, which remains the recorded scope cut.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace BilinearEsa

open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

/-! ## Blocks of `ℓ²(ℕ × J)` -/

/-- The `j`-th block of a state of `ℓ²(ℕ × J)`: the velocity-fiber state
obtained by freezing the derivative field at its eigenvalue `κ j`. -/
noncomputable def blockVec (w : L2I (ℕ × J)) (j : J) : L2I ℕ :=
  ⟨fun n => (w : ℕ × J → ℂ) (n, j), by
    refine memLpTwo_of_summable_normSq ?_
    have hs : Summable fun k : ℕ × J => ‖(w : ℕ × J → ℂ) k‖ ^ 2 := summable_normSq w
    have hinj : Function.Injective fun n : ℕ => (n, j) := by
      intro a b hab
      simpa using hab
    exact hs.comp_injective hinj⟩

@[simp] theorem blockVec_coe (w : L2I (ℕ × J)) (j : J) (n : ℕ) :
    ((blockVec w j : L2I ℕ) : ℕ → ℂ) n = (w : ℕ × J → ℂ) (n, j) := rfl

open scoped Classical in
/-- The coordinates of the embedding of a velocity-fiber state into the block
`j`. -/
noncomputable def embFun (j : J) (a : ℕ → ℂ) : ℕ × J → ℂ :=
  fun p => if p.2 = j then a p.1 else 0

@[simp] theorem embFun_self (j : J) (a : ℕ → ℂ) (n : ℕ) : embFun j a (n, j) = a n := by
  simp [embFun]



theorem support_embFun (j : J) (a : ℕ → ℂ) :
    Function.support (embFun j a) ⊆ (fun n : ℕ => (n, j)) '' Function.support a := by
  rintro ⟨n, j'⟩ hp
  simp only [Function.mem_support, embFun] at hp
  by_cases hj : j' = j
  · subst hj
    simp only at hp
    exact ⟨n, hp, rfl⟩
  · simp [hj] at hp

theorem embFun_finite_support (j : J) (u : lpFiniteModes ℕ) :
    (Function.support (embFun j (((u : L2I ℕ)) : ℕ → ℂ))).Finite :=
  Set.Finite.subset (Set.Finite.image _ (mem_lpFiniteModes.mp u.2)) (support_embFun _ _)

/-- The embedding of a finite-mode velocity state as the `j`-th block. -/
noncomputable def blockEmb (j : J) (u : lpFiniteModes ℕ) : lpFiniteModes (ℕ × J) :=
  ⟨⟨embFun j (((u : L2I ℕ)) : ℕ → ℂ), memLpTwo_of_finite_support (embFun_finite_support j u)⟩,
    embFun_finite_support j u⟩

@[simp] theorem blockEmb_coe (j : J) (u : lpFiniteModes ℕ) (p : ℕ × J) :
    (((blockEmb j u : lpFiniteModes (ℕ × J)) : L2I (ℕ × J)) : ℕ × J → ℂ) p
      = embFun j (((u : L2I ℕ)) : ℕ → ℂ) p := rfl



/-! ## The bilinear Navier–Stokes Hamiltonian -/

/-- The coordinates of the bilinear Navier–Stokes Hamiltonian: in the block `j`
it is the `±2`-shift `hFun (κ j)` of the Hermite representation. -/
noncomputable def bilFun (κ : J → ℝ) (X : ℕ × J → ℂ) : ℕ × J → ℂ :=
  fun p => hFun (κ p.2) (fun n => X (n, p.2)) p.1

theorem support_bilFun (κ : J → ℝ) (X : ℕ × J → ℂ) :
    Function.support (bilFun κ X) ⊆
      (fun p : ℕ × J => (p.1 + 2, p.2)) '' Function.support X ∪
      (fun p : ℕ × J => (p.1 - 2, p.2)) '' Function.support X := by
  rintro ⟨m, j⟩ hp
  simp only [Function.mem_support, bilFun, hFun] at hp
  by_cases h2 : X (m + 2, j) = 0
  · left
    have hs : shift2 (fun n => ((amp (κ j) n : ℂ)) * X (n, j)) m ≠ 0 := by
      intro h
      apply hp
      rw [h, h2]
      ring
    have hm : 2 ≤ m := by
      by_contra hcon
      exact hs (by simp [shift2, hcon])
    have hs' : ((amp (κ j) (m - 2) : ℂ)) * X (m - 2, j) ≠ 0 := by
      simpa [shift2, hm] using hs
    refine ⟨(m - 2, j), ?_, ?_⟩
    · simp only [Function.mem_support]
      intro h
      exact hs' (by rw [h]; ring)
    · simp only [Prod.mk.injEq, and_true]
      omega
  · right
    exact ⟨(m + 2, j), h2, by simp⟩

theorem bilFun_finite_support (κ : J → ℝ) (x : lpFiniteModes (ℕ × J)) :
    (Function.support (bilFun κ (((x : L2I (ℕ × J))) : ℕ × J → ℂ))).Finite := by
  have hx := mem_lpFiniteModes.mp x.2
  exact Set.Finite.subset ((hx.image _).union (hx.image _)) (support_bilFun _ _)

/-- **The bilinear Navier–Stokes Hamiltonian** on the finite-mode core of
`ℓ²(ℕ × J)`: `H = ½(π A + A π)` with the bilinear symbol `A = u_{,1} · u`, the
derivative field diagonalised with (arbitrary, possibly unbounded) eigenvalues
`κ : J → ℝ`. -/
noncomputable def bilH (κ : J → ℝ) : lpFiniteModes (ℕ × J) →ₗ[ℂ] L2I (ℕ × J) where
  toFun x := ⟨bilFun κ (((x : L2I (ℕ × J))) : ℕ × J → ℂ),
    memLpTwo_of_finite_support (bilFun_finite_support κ x)⟩
  map_add' x y := by
    refine lp.ext (funext fun p => ?_)
    simp only [lp.coeFn_add, Pi.add_apply, Submodule.coe_add, bilFun, hFun, shift2]
    by_cases h : 2 ≤ p.1 <;> simp [h] <;> ring
  map_smul' a x := by
    refine lp.ext (funext fun p => ?_)
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Submodule.coe_smul,
      bilFun, hFun, shift2]
    by_cases h : 2 ≤ p.1 <;> simp [h] <;> ring

@[simp] theorem bilH_coe (κ : J → ℝ) (x : lpFiniteModes (ℕ × J)) (p : ℕ × J) :
    ((bilH κ x : L2I (ℕ × J)) : ℕ × J → ℂ) p
      = bilFun κ (((x : L2I (ℕ × J))) : ℕ × J → ℂ) p := rfl





/-! ## Symmetry -/









/-! ## Essential self-adjointness -/









/-! ## The operator is genuinely unbounded -/



end BilinearEsa

end BookProof.NavierStokesFlow


