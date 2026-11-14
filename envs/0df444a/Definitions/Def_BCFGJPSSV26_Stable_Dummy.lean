-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Dummy
-- name    : BCFGJPSSV26_Stable_Dummy
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:36.03921+00:00
-- url     : https://prove2.me/theorems/4cd17cba-39f2-41a7-ad82-0e21c61780e8
-- title:
--   BCFGJPSSV26.Stable.Dummy — Dummies and mixed center sets
-- statement:
--   This is module `BCFGJPSSV26.Stable.Dummy` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26b, Section 3.1]: a **dummy** `λ = (ℓ, r)` is a point `ℓ` (its leader, a client or a
--   facility) with a radius `r`; a point `a` is at distance `d(a, λ) = d(a, ℓ) + r` from it
--   (`BCFGJPSSV26.Stable.Dummy.dist`), and its **ball** is the set of facilities within `r` of `ℓ`
--   (`BCFGJPSSV26.Stable.Dummy.ball`). Every facility of the ball is at least as near to every point
--   as the dummy (`BCFGJPSSV26.Stable.Dummy.dd_le_dist_of_mem_ball`), so a set of facilities that
--   meets every ball serves every client at least as well as the dummies.
--
--   A **mixed set** is a set `F` of facilities with a list `Λ` of dummies; the distance to it is the
--   least distance to one of them, `dMax` if both are empty (`BCFGJPSSV26.Stable.dMix`). Its cluster
--   of a facility `c ∈ F` is the set of clients nearest to `c` among the facilities (ties broken by
--   index) and at least as near to `c` as to every dummy: facilities win ties against dummies
--   (`BCFGJPSSV26.Stable.clusterMix`).
--
--   **Contents.** The module is published as a whole: 19 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Dummy`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Dummy.lean

module

public import Definitions.Def_BCFGJPSSV26_Basic_Metric

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Dummy` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Dummies and mixed center sets

[BCFGJPSSV26b, Section 3.1]: a **dummy** `λ = (ℓ, r)` is a point `ℓ` (its leader, a client or a
facility) with a radius `r`; a point `a` is at distance `d(a, λ) = d(a, ℓ) + r` from it
(`BCFGJPSSV26.Stable.Dummy.dist`), and its **ball** is the set of facilities within `r` of `ℓ`
(`BCFGJPSSV26.Stable.Dummy.ball`). Every facility of the ball is at least as near to every point
as the dummy (`BCFGJPSSV26.Stable.Dummy.dd_le_dist_of_mem_ball`), so a set of facilities that
meets every ball serves every client at least as well as the dummies.

A **mixed set** is a set `F` of facilities with a list `Λ` of dummies; the distance to it is the
least distance to one of them, `dMax` if both are empty (`BCFGJPSSV26.Stable.dMix`). Its cluster
of a facility `c ∈ F` is the set of clients nearest to `c` among the facilities (ties broken by
index) and at least as near to `c` as to every dummy: facilities win ties against dummies
(`BCFGJPSSV26.Stable.clusterMix`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

/-- A **dummy**: a leader and a radius. -/
structure Dummy (I : Instance) where
  /-- The leader, a client or a facility. -/
  leader : I.Pt
  /-- The radius. -/
  radius : ℝ

namespace Dummy

/-- The distance `d(a, λ) = d(a, ℓ) + r` from a point to a dummy. -/
noncomputable def dist (l : Dummy I) (a : I.Pt) : ℝ := I.dd a l.leader + l.radius

open Classical in
/-- The **ball** of a dummy: the facilities within its radius of its leader. -/
noncomputable def ball (l : Dummy I) : Finset (Fin I.m) :=
  univ.filter fun i ↦ I.dd l.leader (.inr i) ≤ l.radius

theorem mem_ball {l : Dummy I} {i : Fin I.m} : i ∈ l.ball ↔ I.dd l.leader (.inr i) ≤ l.radius := by
  classical
  simp [ball]

/-- **A facility of the ball is at least as near as the dummy.** -/
theorem dd_le_dist_of_mem_ball (hv : I.Valid) {l : Dummy I} {i : Fin I.m} (hi : i ∈ l.ball)
    (a : I.Pt) : I.dd a (.inr i) ≤ l.dist a := by
  have h := Instance.dd_triangle hv a l.leader (.inr i)
  have := mem_ball.1 hi
  unfold dist
  linarith

/-- `d(a, λ) ≤ d(a, c) + d(c, ℓ) + r`. -/
theorem dist_le (hv : I.Valid) (l : Dummy I) (a c : I.Pt) :
    l.dist a ≤ I.dd a c + I.dd c l.leader + l.radius := by
  have := Instance.dd_triangle hv a c l.leader
  unfold dist
  linarith

end Dummy

variable (I) in
/-- The distance from `a` to the nearest dummy of `Λ`, and `dMax` if there is none. -/
noncomputable def dDums (a : I.Pt) (Λ : List (Dummy I)) : ℝ :=
  Λ.foldr (fun l acc ↦ min (l.dist a) acc) I.dMax

variable (I) in
/-- The distance from `a` to the mixed set `(F, Λ)`. -/
noncomputable def dMix (a : I.Pt) (F : Finset (Fin I.m)) (Λ : List (Dummy I)) : ℝ :=
  min (I.dSet a F) (dDums I a Λ)

variable (I) in
/-- The cost of the clients of `D` in the mixed set `(F, Λ)`. -/
noncomputable def costMixOn (F : Finset (Fin I.m)) (Λ : List (Dummy I)) (D : Finset (Fin I.n)) :
    ℝ :=
  ∑ j ∈ D, dMix I (.inl j) F Λ

variable (I) in
/-- The cost of the mixed set `(F, Λ)`. -/
noncomputable def costMix (F : Finset (Fin I.m)) (Λ : List (Dummy I)) : ℝ :=
  costMixOn I F Λ univ

variable (I) in
open Classical in
/-- The **cluster** of the facility `c` in the mixed set `(F, Λ)`: its cluster in `F`, without the
clients strictly nearer to a dummy. -/
noncomputable def clusterMix (F : Finset (Fin I.m)) (Λ : List (Dummy I)) (c : Fin I.m) :
    Finset (Fin I.n) :=
  (I.cluster F c).filter fun j ↦ I.dSet (.inl j) F ≤ dDums I (.inl j) Λ

theorem dDums_le {Λ : List (Dummy I)} {l : Dummy I} (hl : l ∈ Λ) (a : I.Pt) :
    dDums I a Λ ≤ l.dist a := by
  induction Λ with
  | nil => simp at hl
  | cons l' Λ ih =>
    unfold dDums
    rw [List.foldr_cons]
    rcases List.mem_cons.1 hl with rfl | hl
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hl)

theorem dDums_nil (a : I.Pt) : dDums I a [] = I.dMax := rfl

theorem dDums_nonneg (hv : I.Valid) {Λ : List (Dummy I)} (hΛ : ∀ l ∈ Λ, 0 ≤ l.radius)
    (a : I.Pt) : 0 ≤ dDums I a Λ := by
  induction Λ with
  | nil => exact (Instance.dMax_pos hv).le
  | cons l Λ ih =>
    unfold dDums
    rw [List.foldr_cons]
    refine le_min ?_ (ih fun l' hl' ↦ hΛ l' (List.mem_cons_of_mem _ hl'))
    unfold Dummy.dist
    have := Instance.dd_nonneg hv a l.leader
    have := hΛ l List.mem_cons_self
    linarith

theorem dMix_nonneg (hv : I.Valid) {Λ : List (Dummy I)} (hΛ : ∀ l ∈ Λ, 0 ≤ l.radius)
    (a : I.Pt) (F : Finset (Fin I.m)) : 0 ≤ dMix I a F Λ :=
  le_min (Instance.dSet_nonneg hv a F) (dDums_nonneg hv hΛ a)

theorem dMix_le_dSet (a : I.Pt) (F : Finset (Fin I.m)) (Λ : List (Dummy I)) :
    dMix I a F Λ ≤ I.dSet a F := min_le_left _ _

theorem dMix_le_dist {Λ : List (Dummy I)} {l : Dummy I} (hl : l ∈ Λ) (a : I.Pt)
    (F : Finset (Fin I.m)) : dMix I a F Λ ≤ l.dist a :=
  (min_le_right _ _).trans (dDums_le hl a)

/-- **The triangle inequality for mixed sets.** -/
theorem dMix_triangle (hv : I.Valid) (a b : I.Pt) (F : Finset (Fin I.m))
    (Λ : List (Dummy I)) : dMix I a F Λ ≤ I.dd a b + dMix I b F Λ := by
  have hD : dDums I a Λ ≤ I.dd a b + dDums I b Λ := by
    induction Λ with
    | nil =>
      rw [dDums_nil, dDums_nil]
      linarith [Instance.dd_nonneg hv a b]
    | cons l Λ ih =>
      unfold dDums at ih ⊢
      rw [List.foldr_cons, List.foldr_cons, add_min]
      refine min_le_min ?_ ih
      unfold Dummy.dist
      linarith [Instance.dd_triangle hv a b l.leader]
  unfold dMix
  rw [add_min]
  exact min_le_min (Instance.dSet_triangle hv a b F) hD

/-- **A set meeting every ball serves every point as well as the dummies**: if `X` meets every
ball of `Λ`, then `d(a, F ∪ X) ≤ d(a, (F, Λ))`. -/
theorem dSet_union_le_dMix (hv : I.Valid) {Λ : List (Dummy I)} {X : Finset (Fin I.m)}
    (hX : ∀ l ∈ Λ, ∃ i ∈ X, i ∈ l.ball) (a : I.Pt) (F : Finset (Fin I.m)) :
    I.dSet a (F ∪ X) ≤ dMix I a F Λ := by
  have hD : I.dSet a (F ∪ X) ≤ dDums I a Λ := by
    induction Λ with
    | nil => exact Instance.dSet_le_dMax hv a _
    | cons l Λ ih =>
      unfold dDums at ih ⊢
      rw [List.foldr_cons]
      refine le_min ?_ (ih fun l' hl' ↦ hX l' (List.mem_cons_of_mem _ hl'))
      obtain ⟨i, hi, hil⟩ := hX l List.mem_cons_self
      exact (Instance.dSet_le (mem_union_right F hi) a).trans
        (Dummy.dd_le_dist_of_mem_ball hv hil a)
  exact le_min (Instance.dSet_anti hv subset_union_left a) hD

end BCFGJPSSV26.Stable


