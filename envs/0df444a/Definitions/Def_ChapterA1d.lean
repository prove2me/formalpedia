-- Prove2me | Definitions.Def_ChapterA1d
-- name    : ChapterA1d
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T06:33:44.255406+00:00
-- url     : https://prove2.me/theorems/e2ccd33e-dab7-4b03-be6e-f515a2482387
-- title:
--   Chapter A1d
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA1d.lean`): generated def bundle for ChapterA1d. See BookProof/ChapterA1d.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA1d.lean

import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA1b
import Definitions.Def_ChapterA1c
import Definitions.Def_Complexification
import Mathlib


/-!
# Chapter A, §A.1 — the realification correspondence (work-package N1)

This file supplies the *dual* construction to `BookProof/ChapterA1b.lean`: where
that file complexified a **real** system and reduced real irreducibility to the
conjugation-stable part of the complexified subspace lattice, here we
**realify** a **complex** system `(M, V)` and reduce complex irreducibility to
the `J`-invariant part of the realified subspace lattice.  This is the
`(M, V^r)` / `J u := i·u` half of the Def 10 / Prop 12 machinery in
`FORMALIZATION_ROADMAP.md` (§A.1).

The real inner-product structure on a complex Hilbert space `V` is supplied by
Mathlib's `InnerProductSpace.rclikeToReal ℂ V`, registered here as a **local**
instance (never global, to avoid the well-known real/complex diamond).  On top
of it:

* `rxMap`/`rxSystem` — the realification of a complex operator / system
  (restriction of scalars);
* `Jmap` — the canonical R-imaginary operator `J u := i·u`, an `ℝ`-linear
  isometric involution-up-to-sign (`Jmap_sq : J (J x) = -x`), and
  `Jmap_isRImaginary` (Def 8.2): `J` is R-imaginary of the realified system;
* the correspondence `realSub`/`cplxSub` between complex subspaces of `V` and
  `J`-invariant real subspaces of `V^r`, with both round-trips and subsystem
  preservation; and the headline
  `complex_irreducible_iff_no_Jinvariant_subsystem`: `(M, V)` is irreducible as
  a **complex** system iff its realification `(M, V^r)` has no proper
  non-trivial `J`-invariant subsystem.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace BookProof.ChapterA

-- The real inner-product structure on a complex inner-product space, from
-- `InnerProductSpace.rclikeToReal`.  Registered **locally** only.
attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## Realification of a complex operator and system -/

/-- **Realification of a complex operator.** `rxMap m` is `m` viewed as an
`ℝ`-linear bounded operator (restriction of scalars). -/
noncomputable def rxMap (m : V →L[ℂ] V) : V →L[ℝ] V := m.restrictScalars ℝ

@[simp] lemma rxMap_apply (m : V →L[ℂ] V) (x : V) : rxMap m x = m x := rfl

/-- **Realification of a complex system.** `rxSystem M` has as operators the
realifications of the operators of `M`. -/
noncomputable def rxSystem [CompleteSpace V] (M : System ℂ V) : System ℝ V where
  ops := (fun m => rxMap m) '' M.ops

/-! ## The canonical R-imaginary operator `J u := i·u` -/

/-- **The R-imaginary operator `J`.** Multiplication by `i`, an `ℝ`-linear
isometric equivalence of the realification `V^r`. -/
noncomputable def Jmap : V ≃ₗᵢ[ℝ] V where
  toFun x := (Complex.I : ℂ) • x
  invFun x := (-Complex.I : ℂ) • x
  map_add' x y := by simp [smul_add]
  map_smul' r x := by dsimp; rw [smul_comm]
  left_inv x := by dsimp; rw [smul_smul]; simp
  right_inv x := by dsimp; rw [smul_smul]; simp
  norm_map' x := by dsimp; rw [norm_smul]; simp

@[simp] lemma Jmap_apply (x : V) : Jmap x = (Complex.I : ℂ) • x := rfl





/-! ## The correspondence between complex subspaces and `J`-invariant real ones -/

/-- **Real part of a complex subspace.** `realSub X` is `X` viewed as a real
subspace of `V^r` (restriction of scalars). -/
noncomputable def realSub (X : Submodule ℂ V) : Submodule ℝ V := X.restrictScalars ℝ

@[simp] lemma mem_realSub {X : Submodule ℂ V} {x : V} : x ∈ realSub X ↔ x ∈ X :=
  Submodule.restrictScalars_mem ℝ X x

/-- `realSub X` is `J`-invariant. -/
lemma realSub_Jinvariant (X : Submodule ℂ V) : ∀ x ∈ realSub X, Jmap x ∈ realSub X := by
  intro x hx
  rw [mem_realSub] at *
  exact X.smul_mem _ hx

/-- **Complexification of a `J`-invariant real subspace.** A real subspace `Y`
closed under `J = i·` is automatically a complex subspace. -/
noncomputable def cplxSub (Y : Submodule ℝ V) (hJ : ∀ y ∈ Y, (Complex.I : ℂ) • y ∈ Y) :
    Submodule ℂ V where
  carrier := Y
  add_mem' := Y.add_mem
  zero_mem' := Y.zero_mem
  smul_mem' := by
    intro z y hy
    have hz : z • y = (z.re : ℝ) • y + (z.im : ℝ) • ((Complex.I : ℂ) • y) := by
      have : z • y = (z.re : ℂ) • y + (z.im : ℂ) • ((Complex.I : ℂ) • y) := by
        rw [smul_smul]
        rw [← add_smul]
        congr 1
        apply Complex.ext <;> simp
      simpa using this
    rw [hz]
    exact Y.add_mem (Y.smul_mem _ hy) (Y.smul_mem _ (hJ y hy))

@[simp] lemma mem_cplxSub {Y : Submodule ℝ V} {hJ : ∀ y ∈ Y, (Complex.I : ℂ) • y ∈ Y}
    {x : V} : x ∈ cplxSub Y hJ ↔ x ∈ Y := Iff.rfl

/-- Round-trip: `realSub (cplxSub Y hJ) = Y`. -/
@[simp] lemma realSub_cplxSub (Y : Submodule ℝ V) (hJ : ∀ y ∈ Y, (Complex.I : ℂ) • y ∈ Y) :
    realSub (cplxSub Y hJ) = Y := by
  ext x; simp [mem_realSub]

/-- Round-trip: `cplxSub (realSub X) _ = X`. -/
@[simp] lemma cplxSub_realSub (X : Submodule ℂ V) :
    cplxSub (realSub X) (realSub_Jinvariant X) = X := by
  ext x; exact mem_cplxSub.trans mem_realSub

/-! ### Extremal values -/

@[simp] lemma realSub_bot : realSub (⊥ : Submodule ℂ V) = ⊥ := by
  ext x; simp [mem_realSub]

@[simp] lemma realSub_top : realSub (⊤ : Submodule ℂ V) = ⊤ := by
  ext x; simp

/-! ### Subsystem preservation -/





/-! ## Headline: complex irreducibility via the `J`-invariant lattice -/



end BookProof.ChapterA


