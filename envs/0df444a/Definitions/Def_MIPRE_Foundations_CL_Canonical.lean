-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_Canonical
-- name    : MIPRE_Foundations_CL_Canonical
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:26.766982+00:00
-- url     : https://prove2.me/theorems/92c10466-4da4-4df5-9ff5-88b00e3e4c03
-- title:
--   Definitions of Canonical: Canonical complements and canonical linear maps The paper's `preliminaries.tex`, `sec:linear-spaces`: two different…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.Canonical` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Canonical complements and canonical linear maps. The paper's `preliminaries.tex`, `sec:linear-spaces`: two different "perps", both needed by the seeded CL low-degree test, whose questions are `(u₀, s)` and `(u₀, s, v)` with `u₀ = L^Ln_v(u)` the canonical representative of a line. * **The orthogonal complement** `Sᗮ` for the standard dot product (`def` before `lem:perp_perp`). Over a finite field this is *not* a direct-sum complement --- `span{(1,1)}` over `𝔽₂` is orthogonal to itself --- but `dim S + dim Sᗮ = n` and `(Sᗮ)ᗮ = S` hold over every field (`lem:perp_perp`). Here it is Mathlib's…
--
--   **Definitions** (10): `MIPRE.CL.canonCompl` (The **canonical complement** of `S` (`def:canonical-complement`): the span of the standard basis vectors off the pivot set.); `MIPRE.CL.canonLin` (The **canonical linear map with kernel `S`** (`def:cl-canonical`): the projector onto the canonical complement of `S`, parallel to `S`.); `MIPRE.CL.coordSub` (`coordSub J`, the vectors vanishing on `J`: the span of `{eⱼ : j ∉ J}`.); `MIPRE.CL.dimTail` (`uⱼ = dim (S ⊓ tail j)`, the dimension sequence of `rk:cancomp`.); `MIPRE.CL.dotForm` (The standard dot product on `Fin n → F`, as a bilinear form.); `MIPRE.CL.lperp` (`L^⊥` of `def:Lperp`: the canonical linear map whose kernel is `(ker L)ᗮ`.); `MIPRE.CL.perp` (The **orthogonal complement** of `S` for the dot product.); `MIPRE.CL.pivots` (The pivot set `J` of `S`: the indices at which the dimension sequence drops.); `MIPRE.CL.projTo` (The projection onto the coordinates in `J`.); `MIPRE.CL.tail` (`tail j = span {eᵢ : i ≥ j}`, the vectors whose coordinates below `j` vanish.).
--
--   **Embedded lemmas** (25): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `card_pivots`, `dimTail_add_card_pivots`, `dimTail_antitone`, `dimTail_le_succ`, `dimTail_top`, `dimTail_zero`, `dotForm_apply`, `finrank_coordSub`, `isCompl_canonCompl`, `ker_canonLin`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.Canonical` (`MIPRE/Foundations/CL/Canonical.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Canonical.lean; blueprint def:cl-canonical, lem:cl-canonical

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Canonical.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register

/-!
# Canonical complements and canonical linear maps

The paper's `preliminaries.tex`, `sec:linear-spaces`: two different "perps", both needed by the
seeded CL low-degree test, whose questions are `(u₀, s)` and `(u₀, s, v)` with
`u₀ = L^Ln_v(u)` the canonical representative of a line.

* **The orthogonal complement** `Sᗮ` for the standard dot product (`def` before
  `lem:perp_perp`). Over a finite field this is *not* a direct-sum complement --- `span{(1,1)}`
  over `𝔽₂` is orthogonal to itself --- but `dim S + dim Sᗮ = n` and `(Sᗮ)ᗮ = S` hold over
  every field (`lem:perp_perp`). Here it is Mathlib's `LinearMap.BilinForm.orthogonal` of
  `dotForm`, and the lemma is Mathlib's, once `dotForm` is shown reflexive and nondegenerate.
* **The canonical complement** `F^⊥` of a *set* `F` of linearly independent vectors
  (`def:canonical-complement`), which *is* a direct-sum complement (`lem:canonical-complement`)
  and is a set of standard basis vectors.

The paper defines the canonical complement by reduced row echelon form. This file uses the
equivalent characterization `rk:cancomp` credits to a referee, which is what makes the
construction formalizable and its well-definedness immediate: with
`uⱼ = dim (S ⊓ span {eᵢ : i ≥ j})`, the complement is `{eⱼ : uⱼ = u_{j+1}}`. It depends on the
subspace `S = span F` alone, with no echelon form, no choice of basis and no ordering of `F` to
quotient by --- so `canonLin`, the projector onto that complement parallel to `S`
(`def:cl-canonical`), is a function of `S`, which is exactly what `rk:cancomp` has to argue.

`pivots S` is the paper's set `J` of pivot columns, and `#(pivots S) = dim S`
(`card_pivots`): the two characterizations agree.
-/

namespace MIPRE.CL

open Finset Module Submodule LinearMap

variable {F : Type*} [Field F] {n : ℕ}

/-! ## Coordinate subspaces cut out by vanishing -/

/-- `coordSub J`, the vectors vanishing on `J`: the span of `{eⱼ : j ∉ J}`. -/
def coordSub (J : Finset (Fin n)) : Submodule F (Fin n → F) where
  carrier := {x | ∀ j ∈ J, x j = 0}
  add_mem' hx hy j hj := by simp [hx j hj, hy j hj]
  zero_mem' _ _ := rfl
  smul_mem' c x hx j hj := by simp [hx j hj]

@[simp] theorem mem_coordSub {J : Finset (Fin n)} {x : Fin n → F} :
    x ∈ coordSub (F := F) J ↔ ∀ j ∈ J, x j = 0:= Iff.rfl

/-- The projection onto the coordinates in `J`. -/
def projTo (J : Finset (Fin n)) : (Fin n → F) →ₗ[F] (J → F) :=
  LinearMap.pi fun j => LinearMap.proj (R := F) (φ := fun _ : Fin n => F) j.1

@[simp] theorem projTo_apply (J : Finset (Fin n)) (x : Fin n → F) (j : J) :
    projTo J x j = x j.1 := rfl

theorem ker_projTo (J : Finset (Fin n)) : ker (projTo (F := F) J) = coordSub J := by
  ext x
  simp [projTo, LinearMap.mem_ker, funext_iff, Subtype.forall]

theorem surjective_projTo (J : Finset (Fin n)) : Function.Surjective (projTo (F := F) J) := by
  intro y
  classical
  refine ⟨fun i => if h : i ∈ J then y ⟨i, h⟩ else 0, ?_⟩
  funext j
  simp [projTo, j.2]

theorem finrank_coordSub (J : Finset (Fin n)) :
    finrank F (coordSub (F := F) J) = n - J.card := by
  have hr : range (projTo (F := F) J) = ⊤ := range_eq_top.mpr (surjective_projTo J)
  have h := LinearMap.finrank_range_add_finrank_ker (projTo (F := F) J)
  rw [hr, ker_projTo] at h
  have h1 : finrank F (⊤ : Submodule F (J → F)) = J.card := by
    simp [finrank_top, Module.finrank_fintype_fun_eq_card]
  have h2 : finrank F (Fin n → F) = n := by simp [Module.finrank_fintype_fun_eq_card]
  omega

/-! ## The tail subspaces and the pivot set -/

/-- `tail j = span {eᵢ : i ≥ j}`, the vectors whose coordinates below `j` vanish. -/
def tail (n j : ℕ) : Submodule F (Fin n → F) := coordSub (univ.filter fun i : Fin n => i.val < j)

@[simp] theorem mem_tail {j : ℕ} {x : Fin n → F} :
    x ∈ tail (F := F) n j ↔ ∀ i : Fin n, i.val < j → x i = 0 := by
  simp [tail]

@[simp] theorem tail_zero : tail (F := F) n 0 = ⊤ := by
  ext x; simp

@[simp] theorem tail_card : tail (F := F) n n = ⊥ := by
  ext x
  simp only [mem_tail, Submodule.mem_bot, funext_iff]
  exact ⟨fun h i => h i i.isLt, fun h i _ => by simp [h]⟩

theorem tail_mono {j k : ℕ} (h : j ≤ k) : tail (F := F) n k ≤ tail n j := by
  intro x hx
  rw [mem_tail] at hx ⊢
  exact fun i hi => hx i (lt_of_lt_of_le hi h)

/-- `uⱼ = dim (S ⊓ tail j)`, the dimension sequence of `rk:cancomp`. -/
noncomputable def dimTail (S : Submodule F (Fin n → F)) (j : ℕ) : ℕ :=
  finrank F (S ⊓ tail n j : Submodule F (Fin n → F))

/-- The pivot set `J` of `S`: the indices at which the dimension sequence drops. -/
noncomputable def pivots (S : Submodule F (Fin n → F)) : Finset (Fin n) :=
  univ.filter fun j => dimTail S (j.val + 1) < dimTail S j.val

theorem mem_pivots {S : Submodule F (Fin n → F)} {j : Fin n} :
    j ∈ pivots S ↔ dimTail S (j.val + 1) < dimTail S j.val := by
  simp [pivots]

/- `pivots` is a `Finset.filter` over a `Nat` inequality between `finrank`s, so it carries a
`Decidable` instance that no tactic can evaluate. Unfolding it is never useful and, at the
membership hypotheses of the counting argument below, `isDefEq` chases it until it gives up.
Everything past this point goes through `mem_pivots`. -/
attribute [irreducible] MIPRE.CL.pivots

theorem dimTail_antitone (S : Submodule F (Fin n → F)) {j k : ℕ} (h : j ≤ k) :
    dimTail S k ≤ dimTail S j :=
  Submodule.finrank_mono (inf_le_inf_left _ (tail_mono h))

theorem tail_eq_bot {j : ℕ} (h : n ≤ j) : tail (F := F) n j = ⊥ :=
  le_bot_iff.mp (tail_card (F := F) (n := n) ▸ tail_mono h)

theorem dimTail_le_succ (S : Submodule F (Fin n → F)) (j : ℕ) :
    dimTail S j ≤ dimTail S (j + 1) + 1 := by
  rcases lt_or_ge j n with hj | hj
  · -- The `j`-th coordinate, as a linear functional on `S ⊓ tail j`, has kernel
    -- `S ⊓ tail (j+1)` and one-dimensional codomain.
    have hQP : (S ⊓ tail (F := F) n (j + 1)) ≤ S ⊓ tail n j :=
      inf_le_inf_left _ (tail_mono (Nat.le_succ j))
    let g : (S ⊓ tail (F := F) n j : Submodule F (Fin n → F)) →ₗ[F] F :=
      { toFun := fun x => (x : Fin n → F) ⟨j, hj⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hker : ker g = Submodule.comap (S ⊓ tail (F := F) n j).subtype
        (S ⊓ tail n (j + 1)) := by
      ext x
      have hxS : (x : Fin n → F) ∈ S := (Submodule.mem_inf.mp x.2).1
      have hxT : ∀ i : Fin n, i.val < j → (x : Fin n → F) i = 0 :=
        mem_tail.mp (Submodule.mem_inf.mp x.2).2
      simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype,
        Submodule.mem_inf, mem_tail, g, LinearMap.coe_mk, AddHom.coe_mk]
      refine ⟨fun h => ⟨hxS, fun i hi => ?_⟩, fun h => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
        · exact hxT i hi'
        · have : i = ⟨j, hj⟩ := Fin.ext hi'
          rw [this]; exact h
      · exact h.2 ⟨j, hj⟩ (Nat.lt_succ_self j)
    have h1 : finrank F (ker g) = dimTail S (j + 1) := by
      rw [hker]
      exact (Submodule.comapSubtypeEquivOfLe hQP).finrank_eq
    have h2 : finrank F (range g) ≤ 1 := by
      simpa using Submodule.finrank_le (range g)
    have h3 := LinearMap.finrank_range_add_finrank_ker g
    rw [h1] at h3
    simp only [dimTail] at h3 ⊢
    omega
  · rw [dimTail, dimTail, tail_eq_bot hj, tail_eq_bot (le_trans hj (Nat.le_succ j)),
      inf_bot_eq, finrank_bot]
    omega

@[simp] theorem dimTail_zero (S : Submodule F (Fin n → F)) : dimTail S 0 = finrank F S := by
  rw [dimTail, tail_zero, inf_top_eq]

@[simp] theorem dimTail_top (S : Submodule F (Fin n → F)) : dimTail S n = 0 := by
  simp [dimTail]

/-- Counting the pivots below `j + 1`, for an arbitrary index set, in the two cases separately.
Stated for a *variable* `Finset`, and with no `if`, on purpose: `pivots S` is a
`Finset.filter` over a `Nat` inequality between `finrank`s, so it carries a `Decidable`
instance that cannot be evaluated, and either letting `simp` see through it or asking `rw` to
unify it against a `Classical` instance costs a `whnf` timeout. -/
theorem card_filter_lt_succ_of_mem (P : Finset (Fin n)) {j : ℕ} (hj : j < n)
    (hp : (⟨j, hj⟩ : Fin n) ∈ P) :
    (P.filter fun i : Fin n => i.val < j + 1).card
      = (P.filter fun i : Fin n => i.val < j).card + 1 := by
  classical
  have hfil : (P.filter fun i : Fin n => i.val < j + 1)
      = insert (⟨j, hj⟩ : Fin n) (P.filter fun i : Fin n => i.val < j) := by
    ext i
    simp only [mem_filter, mem_insert]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h.2 with h' | h'
      · exact Or.inr ⟨h.1, h'⟩
      · exact Or.inl (Fin.ext h')
    · rintro (rfl | h)
      · exact ⟨hp, Nat.lt_succ_self j⟩
      · exact ⟨h.1, by omega⟩
  rw [hfil, Finset.card_insert_of_notMem (by simp)]

theorem card_filter_lt_succ_of_notMem (P : Finset (Fin n)) {j : ℕ} (hj : j < n)
    (hp : (⟨j, hj⟩ : Fin n) ∉ P) :
    (P.filter fun i : Fin n => i.val < j + 1)
      = (P.filter fun i : Fin n => i.val < j) := by
  classical
  ext i
  simp only [mem_filter]
  refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, by omega⟩⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp h.2 with h' | h'
  · exact h'
  · exact absurd ((Fin.ext h' : i = (⟨j, hj⟩ : Fin n)) ▸ h.1) hp

theorem filter_lt_of_le (P : Finset (Fin n)) {j : ℕ} (hj : n ≤ j) :
    (P.filter fun i : Fin n => i.val < j) = P := by
  classical
  exact Finset.filter_true_of_mem fun i _ => lt_of_lt_of_le i.isLt hj

theorem dimTail_add_card_pivots (S : Submodule F (Fin n → F)) (j : ℕ) :
    dimTail S j + ((pivots S).filter fun i : Fin n => i.val < j).card = finrank F S := by
  induction j with
  | zero => simp
  | succ j ih =>
    rcases lt_or_ge j n with hj | hj
    · rcases Classical.em ((⟨j, hj⟩ : Fin n) ∈ pivots S) with hp | hp
      · rw [card_filter_lt_succ_of_mem (pivots S) hj hp]
        -- `j` is given explicitly: leaving it to unification asks the elaborator to solve
        -- `Fin.val ?j =?= j`, which it cannot invert and will not give up on cheaply.
        have hlt : dimTail S (j + 1) < dimTail S j :=
          (mem_pivots (S := S) (j := ⟨j, hj⟩)).mp hp
        have hle : dimTail S j ≤ dimTail S (j + 1) + 1 := dimTail_le_succ S j
        omega
      · rw [card_filter_lt_succ_of_notMem (pivots S) hj hp]
        have heq : dimTail S (j + 1) = dimTail S j := by
          have h1 : dimTail S (j + 1) ≤ dimTail S j := dimTail_antitone S (Nat.le_succ j)
          have h2 : ¬ dimTail S (j + 1) < dimTail S j := fun h => hp (mem_pivots.mpr h)
          omega
        rw [heq]; exact ih
    · rw [filter_lt_of_le (pivots S) (le_trans hj (Nat.le_succ j))]
      rw [filter_lt_of_le (pivots S) hj] at ih
      have h1 : dimTail S (j + 1) = 0 := by
        rw [dimTail, tail_eq_bot (le_trans hj (Nat.le_succ j)), inf_bot_eq, finrank_bot]
      have h2 : dimTail S j = 0 := by rw [dimTail, tail_eq_bot hj, inf_bot_eq, finrank_bot]
      rw [h1]
      rw [h2] at ih
      exact ih

theorem card_pivots (S : Submodule F (Fin n → F)) : (pivots S).card = finrank F S := by
  classical
  have h := dimTail_add_card_pivots S n
  rw [dimTail_top] at h
  have hfilter : ((pivots S).filter fun i : Fin n => i.val < n) = pivots S :=
    Finset.filter_true_of_mem fun i _ => i.isLt
  rw [hfilter] at h
  omega

/-! ## The canonical complement and the canonical linear map -/

/-- The **canonical complement** of `S` (`def:canonical-complement`): the span of the standard
basis vectors off the pivot set. -/
noncomputable def canonCompl (S : Submodule F (Fin n → F)) : Submodule F (Fin n → F) :=
  coordSub (pivots S)

/-- **`lem:canonical-complement`**: `S` and its canonical complement are complementary. -/
theorem isCompl_canonCompl (S : Submodule F (Fin n → F)) : IsCompl S (canonCompl S) := by
  classical
  have hdisj : S ⊓ canonCompl S = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxT⟩ := hx
    by_contra hne
    have hex : (univ.filter fun i : Fin n => x i ≠ 0).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
      exact hne (funext fun i => not_not.mp (hcon (mem_univ i)))
    set j := (univ.filter fun i : Fin n => x i ≠ 0).min' hex with hj
    have hxj : x j ≠ 0 := (Finset.mem_filter.mp ((univ.filter fun i : Fin n =>
      x i ≠ 0).min'_mem hex)).2
    have hmin : ∀ i : Fin n, i.val < j.val → x i = 0 := by
      intro i hi
      by_contra h
      have := (univ.filter fun i : Fin n => x i ≠ 0).min'_le i
        (Finset.mem_filter.mpr ⟨mem_univ i, h⟩)
      rw [← hj] at this
      exact absurd (Fin.le_def.mp this) (by omega)
    have hmemP : x ∈ S ⊓ tail (F := F) n j.val :=
      ⟨hxS, mem_tail.mpr hmin⟩
    have hnotQ : x ∉ S ⊓ tail (F := F) n (j.val + 1) := by
      intro h
      exact hxj ((mem_tail.mp h.2) j (Nat.lt_succ_self _))
    have hlt : (S ⊓ tail (F := F) n (j.val + 1)) < S ⊓ tail n j.val :=
      lt_of_le_of_ne (inf_le_inf_left _ (tail_mono (Nat.le_succ _)))
        (fun h => hnotQ (h ▸ hmemP))
    have : j ∈ pivots S := mem_pivots.mpr (Submodule.finrank_lt_finrank_of_lt hlt)
    exact hxj (hxT j this)
  have hdim : finrank F S + finrank F (canonCompl (F := F) S) = n := by
    have hle : (pivots S).card ≤ n := by simpa using (pivots S).card_le_univ
    have h1 : finrank F (canonCompl (F := F) S) = n - (pivots S).card := by
      rw [canonCompl, finrank_coordSub]
    rw [h1, ← card_pivots S]
    omega
  refine ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr ?_⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq S (canonCompl (F := F) S)
  rw [hdisj, finrank_bot, add_zero, hdim] at hsup
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [hsup]
  simp [Module.finrank_fintype_fun_eq_card]

/-- The **canonical linear map with kernel `S`** (`def:cl-canonical`): the projector onto the
canonical complement of `S`, parallel to `S`. It is a function of `S` alone, which is what
`rk:cancomp` argues. -/
noncomputable def canonLin (S : Submodule F (Fin n → F)) : (Fin n → F) →ₗ[F] (Fin n → F) :=
  (canonCompl S).projection S (isCompl_canonCompl S).symm

/-- The canonical linear map has kernel exactly `S`: it is "the canonical linear map with
kernel `S`" of `def:cl-canonical`. -/
@[simp] theorem ker_canonLin (S : Submodule F (Fin n → F)) : ker (canonLin S) = S :=
  Submodule.ker_projection _

@[simp] theorem range_canonLin (S : Submodule F (Fin n → F)) :
    range (canonLin S) = canonCompl S :=
  Submodule.range_projection _

/-! ## The dot product and orthogonal complements

The paper's other perp: the orthogonal complement for the standard dot product. Over a finite
field it need not be a direct-sum complement, but `lem:perp_perp` holds over every field.
-/

/-- The standard dot product on `Fin n → F`, as a bilinear form. -/
def dotForm (F : Type*) [Field F] (n : ℕ) : LinearMap.BilinForm F (Fin n → F) :=
  LinearMap.mk₂ F (fun x y => ∑ i, x i * y i)
    (fun x y z => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc])
    (fun x y z => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_left_comm])

@[simp] theorem dotForm_apply (x y : Fin n → F) : dotForm F n x y = ∑ i, x i * y i := rfl

/-- The **orthogonal complement** of `S` for the dot product. Over a finite field this need
not be a complement of `S` --- `span{(1,1)}` over `𝔽₂` is orthogonal to itself --- which is
exactly why the canonical complement above exists. -/
def perp (S : Submodule F (Fin n → F)) : Submodule F (Fin n → F) :=
  (dotForm F n).orthogonal S

/-! ## `L^⊥` -/

/-- `L^⊥` of `def:Lperp`: the canonical linear map whose kernel is `(ker L)ᗮ`. -/
noncomputable def lperp (L : (Fin n → F) →ₗ[F] (Fin n → F)) : (Fin n → F) →ₗ[F] (Fin n → F) :=
  canonLin (perp (ker L))

/-- **`lem:L_perp_perp`**: `ker (L^⊥) = (ker L)ᗮ`. -/
@[simp] theorem ker_lperp (L : (Fin n → F) →ₗ[F] (Fin n → F)) :
    ker (lperp L) = perp (ker L) :=
  ker_canonLin _

end MIPRE.CL


