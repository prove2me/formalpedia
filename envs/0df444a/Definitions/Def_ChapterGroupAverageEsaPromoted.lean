-- Prove2me | Definitions.Def_ChapterGroupAverageEsaPromoted
-- name    : ChapterGroupAverageEsaPromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-09T10:42:56.386128+00:00
-- url     : https://prove2.me/theorems/6e92f080-52f4-48f5-a208-aa41b7d96c11
-- title:
--   Group averages: avgProj, commutation and reduction to invariants
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGroupAverageEsa.lean`): the platform's served `Def_ChapterGroupAverageEsa` copy is a skeleton (no declarations), so consumers that cite `avgProj`, `commutes_avgProj` and the group-average lemmas die with `unknown identifier`, and published bundles are immutable, so the fix is a new bundle name that keeps the original namespace (the new-name route, PIPELINE_PLAN §2.13). This bundle re-carries the chapter's full body in `BookProof.GroupAverage`: the finite-group average projection `avgProj` of a unitary representation, its idempotence and symmetry, the criterion for an operator to commute with the average, and the reduction of a symmetric essentially self-adjoint operator to the invariant subspace. It imports the promoted reducing-subspace and graph-core bundles, whose declarations the proofs cite. Consumers add a single `import Definitions.Def_ChapterGroupAverageEsaPromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGroupAverageEsa.lean

-- §2.13 new-name route (Session 40): the platform's served `Def_ChapterGroupAverageEsa` copy is a
-- skeleton (no declarations at all), so `open BookProof.GroupAverage` in every consumer statement
-- dies with `unknown namespace`.  `submit-definition` cannot update an existing
-- name, so this bundle carries the chapter's DEFINITIONS in the original
-- namespace; its theorem facts stay problem nodes.  Consumers add a single
-- `import Definitions.Def_ChapterGroupAverageEsaPromoted`.
import Definitions.Def_ChapterReducingSubspaceEsaPromoted
import Definitions.Def_ChapterGraphCoreTransferPromoted
import Mathlib


/-!
# Averaging over a finite group of symmetries: the invariant sector

`BookProof.ReducedEsa` reduces an operator to the range of a single reducing projection, and
treats the two sectors of one self-inverse isometry.  The symmetric (bosonic) and
antisymmetric (fermionic) sectors of an `n`-particle space are the ranges of the *averages*
of a whole finite group of unitaries — the symmetric group acting by permutation of the
factors, possibly twisted by the sign character.  This module supplies the corresponding
instrument in general:

> **Group averaging.**  Let a finite group `G` act on a complex inner product space `F` by
> inner-product-preserving linear maps (a `UnitaryRep`).  Then the average
> `P = |G|⁻¹ Σ_g ρ(g)` is a reducing projection in the sense of
> `BookProof.ReducedEsa.IsReducingProjection`, its range is exactly the joint fixed space of
> the action, and if every `ρ(g)` preserves the domain of an operator `T` and commutes with
> it, then `T` is essentially self-adjoint on the invariant sector as soon as it is
> essentially self-adjoint on its domain.

## Contents

* `UnitaryRep` — a finite-group action by inner-product-preserving linear maps.
* `avgProj` — the average `|G|⁻¹ Σ_g ρ(g)`; `avgProj_apply_of_invariant`,
  `avgProj_smul_invariant` (the average is itself invariant), `mem_range_avgProj_iff` (the
  range is the joint fixed space).
* `isReducingProjection_avgProj` — the average is idempotent and symmetric.
* `commutes_avgProj` — it commutes with any operator each `ρ(g)` commutes with.
* **`essentiallySelfAdjointOn_invariantSector`** — essential self-adjointness on the
  invariant sector, and `symmetricOn_invariantSector` for the symmetry.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.GroupAverage

open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [Group G] [Fintype G]

/-- A finite group acting on an inner product space by inner-product-preserving linear maps.
Unitarity is stated as preservation of the inner product, which for an invertible map is the
same thing; invertibility comes from the group law. -/
structure UnitaryRep (G : Type*) [Group G] (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] where
  /-- the operator attached to a group element -/
  act : G → (F →ₗ[ℂ] F)
  /-- the unit acts as the identity -/
  act_one : ∀ x, act 1 x = x
  /-- the action is multiplicative -/
  act_mul : ∀ g h x, act (g * h) x = act g (act h x)
  /-- every operator of the action preserves the inner product -/
  act_inner : ∀ g x y, (inner ℂ (act g x) (act g y) : ℂ) = inner ℂ x y

namespace UnitaryRep

variable (rep : UnitaryRep G F)

omit [Fintype G] in
/-- The adjoint of `ρ(g)` is `ρ(g⁻¹)`. -/
theorem inner_act_left (g : G) (x y : F) :
    (inner ℂ (rep.act g x) y : ℂ) = inner ℂ x (rep.act g⁻¹ y) := by
  have h := rep.act_inner g x (rep.act g⁻¹ y)
  rw [← rep.act_mul, mul_inv_cancel, rep.act_one] at h
  exact h

variable (G) in
/-- The order of the group, as a nonzero complex scalar. -/
theorem card_ne_zero : (Fintype.card G : ℂ) ≠ 0 := by
  have : 0 < Fintype.card G := Fintype.card_pos
  exact_mod_cast Nat.cast_ne_zero.mpr this.ne'

/-- The **average** `|G|⁻¹ Σ_g ρ(g)` of the action. -/
def avgProj : F →ₗ[ℂ] F := ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, rep.act g

theorem avgProj_apply (x : F) :
    rep.avgProj x = ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, rep.act g x := by
  simp [avgProj, LinearMap.sum_apply]

/-- Translating the average by a group element does not change it. -/
theorem act_sum (h : G) (x : F) :
    rep.act h (∑ g : G, rep.act g x) = ∑ g : G, rep.act g x := by
  rw [map_sum]
  have : ∀ g : G, rep.act h (rep.act g x) = rep.act (h * g) x := by
    intro g; rw [rep.act_mul]
  simp only [this]
  exact Fintype.sum_bijective (fun g => h * g) (Group.mulLeft_bijective h) _ _ (fun g => rfl)

/-- The average lands in the joint fixed space. -/
theorem act_avgProj (h : G) (x : F) : rep.act h (rep.avgProj x) = rep.avgProj x := by
  rw [avgProj_apply, map_smul, rep.act_sum h x]

/-- On an invariant vector the average is the identity. -/
theorem avgProj_of_invariant {x : F} (hx : ∀ g : G, rep.act g x = x) : rep.avgProj x = x := by
  rw [avgProj_apply]
  simp only [hx]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ (card_ne_zero G), one_smul]

/-- **The range of the average is exactly the joint fixed space.** -/
theorem mem_range_avgProj_iff {x : F} :
    x ∈ LinearMap.range rep.avgProj ↔ ∀ g : G, rep.act g x = x := by
  constructor
  · rintro ⟨u, rfl⟩ g
    exact rep.act_avgProj g u
  · intro hx
    exact ⟨x, rep.avgProj_of_invariant hx⟩

/-- **The average is a reducing projection**: idempotent and symmetric. -/
theorem isReducingProjection_avgProj : IsReducingProjection rep.avgProj where
  idem x := rep.avgProj_of_invariant (fun g => rep.act_avgProj g x)
  symm x y := by
    rw [avgProj_apply, avgProj_apply, inner_smul_left, inner_smul_right,
      map_inv₀, Complex.conj_natCast, sum_inner, inner_sum]
    congr 1
    refine Fintype.sum_bijective (fun g : G => g⁻¹) (Equiv.inv G).bijective _ _ (fun g => ?_)
    exact rep.inner_act_left g x y

variable {D : Submodule ℂ F}

/-- If every operator of the action preserves the domain, so does the average. -/
theorem avgProj_mem (hD : ∀ (g : G) (x : F), x ∈ D → rep.act g x ∈ D) :
    ∀ x ∈ D, rep.avgProj x ∈ D := by
  intro x hx
  rw [avgProj_apply]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun g _ => hD g x hx))

variable {T : D →ₗ[ℂ] F}

/-- If every operator of the action commutes with `T`, so does the average. -/
theorem commutes_avgProj {hD : ∀ (g : G) (x : F), x ∈ D → rep.act g x ∈ D}
    (hT : ∀ (g : G) (x : D), T ⟨rep.act g (x : F), hD g _ x.2⟩ = rep.act g (T x)) :
    Commutes T (rep.avgProj_mem hD) where
  comm x := by
    have hsplit : (⟨rep.avgProj (x : F), rep.avgProj_mem hD _ x.2⟩ : D)
        = ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, (⟨rep.act g (x : F), hD g _ x.2⟩ : D) := by
      apply Subtype.ext
      simp [avgProj_apply]
    rw [hsplit, map_smul, map_sum, avgProj_apply]
    congr 1
    exact Finset.sum_congr rfl (fun g _ => hT g x)

/-- **Essential self-adjointness on the invariant sector.** -/
theorem essentiallySelfAdjointOn_invariantSector
    {hD : ∀ (g : G) (x : F), x ∈ D → rep.act g x ∈ D}
    (hT : ∀ (g : G) (x : D), T ⟨rep.act g (x : F), hD g _ x.2⟩ = rep.act g (T x))
    (hesa : EssentiallySelfAdjointOn D T) :
    EssentiallySelfAdjointOn (redDom rep.avgProj D)
      (redOp T rep.isReducingProjection_avgProj (rep.commutes_avgProj hT)) :=
  essentiallySelfAdjointOn_red _ _ hesa

/-- The part of a symmetric operator inside the invariant sector is symmetric. -/
theorem symmetricOn_invariantSector
    {hD : ∀ (g : G) (x : F), x ∈ D → rep.act g x ∈ D}
    (hT : ∀ (g : G) (x : D), T ⟨rep.act g (x : F), hD g _ x.2⟩ = rep.act g (T x))
    (hsym : SymmetricOn D T) :
    SymmetricOn (redDom rep.avgProj D)
      (redOp T rep.isReducingProjection_avgProj (rep.commutes_avgProj hT)) :=
  symmetricOn_redOp _ _ hsym

end UnitaryRep

/-! ## The two-element group: the average is the symmetrizing projection -/

/-- In the two-element group, the product of two non-units is the unit. -/
theorem mul_eq_one_of_ne_one : ∀ g h : Multiplicative (ZMod 2), g ≠ 1 → h ≠ 1 → g * h = 1 := by
  decide

theorem univ_two : (Finset.univ : Finset (Multiplicative (ZMod 2)))
    = {1, Multiplicative.ofAdd 1} := by decide

/-- A self-inverse isometry is a unitary action of the two-element group. -/
def repOfInvolution (U : F →ₗ[ℂ] F) (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) :
    UnitaryRep (Multiplicative (ZMod 2)) F where
  act g := if g = 1 then LinearMap.id else U
  act_one x := by simp
  act_mul g h x := by
    by_cases hg : g = 1
    · subst hg; simp
    · by_cases hh : h = 1
      · subst hh; simp
      · rw [if_neg hg, if_neg hh, if_pos (mul_eq_one_of_ne_one g h hg hh)]
        simp [hU2]
  act_inner g x y := by
    by_cases h : g = 1 <;> simp [h, hUi]

/-- **Consistency with `BookProof.ReducedEsa`**: for the two-element group the average is the
symmetrizing projection `(1 + U)/2`, so the sector of this module is the symmetric sector of
that one. -/
theorem avgProj_repOfInvolution (U : F →ₗ[ℂ] F) (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) (x : F) :
    (repOfInvolution U hU2 hUi).avgProj x = symProj U x := by
  have hne : (1 : Multiplicative (ZMod 2)) ≠ Multiplicative.ofAdd 1 := by decide
  have hcard : (Fintype.card (Multiplicative (ZMod 2)) : ℂ) = 2 := by simp
  rw [UnitaryRep.avgProj_apply, univ_two, Finset.sum_pair hne, hcard]
  have h1 : (repOfInvolution U hU2 hUi).act 1 x = x := by simp [repOfInvolution]
  have h2 : (repOfInvolution U hU2 hUi).act (Multiplicative.ofAdd 1) x = U x := by
    simp [repOfInvolution, hne.symm]
  rw [h1, h2]
  simp [symProj]

end

end BookProof.GroupAverage


