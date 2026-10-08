-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem21b_PathsAndWalks
-- name    : APSPSource_ThreeSumApsp_Sec3_Theorem21b_PathsAndWalks
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:09:08.614823+00:00
-- url     : https://prove2.me/theorems/663bc95f-c00a-4b23-9804-6ad829900e27
-- title:
--   Converting optional edge weights and shortest-path outputs
-- statement:
--   Let $w(i,j)$ be an optional integer weight on each ordered pair of a finite vertex set. Convert a present weight $z$ to $z$ in $\mathbb Z\cup\{+\infty\}$ and an absent edge to $+\infty$:
--
--   $$\widehat w(i,j)=\begin{cases}z,&w(i,j)=\operatorname{some}(z),\\+\infty,&w(i,j)=\operatorname{none}.\end{cases}$$
--
--   The supporting representation lemmas relate the source's inductive weighted-path predicate to finite lists of visited vertices:
--
--   $$\operatorname{Path}_w(i,j,d)\iff\exists r,\ \operatorname{end}(i,r)=j\ \land\ \operatorname{weight}_{\widehat w}(i,r)=d,$$
--
--   for integer $d$. These paths may repeat vertices. Nonnegativity of every closed finite-weight path therefore supplies the corresponding no-negative-cycle condition on walks.
--
--   If $D$ is a distance matrix for $\widehat w$, a finite entry $D_{ij}=d$ is attained by a path and is no larger than any path weight; an entry $+\infty$ excludes every finite path. Consequently the pair of integer output cells for $(i,j)$ may store $(1,d)$ for a finite distance or a zero flag for an unreachable pair. The final adapter assembles this per-pair condition into the APSP output specification.
--
--   These are representation and output-conversion interfaces. They assume a distance matrix when using its entries and do not assert that an algorithm has computed one.
--
--   References:
--
--   1. [Source formalization, lines 36–84](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/PathsAndWalks.lean#L36-L84).
--   2. [Source formalization, lines 88–134](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/PathsAndWalks.lean#L88-L134).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/PathsAndWalks.lean#L36-L84; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/PathsAndWalks.lean#L88-L134

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace EndStatement
end EndStatement


/-!
# Paths of the end statement and walks with weights in `WithTop ℤ`

The end statement speaks of a directed graph as a function into `Option ℤ` and of
`EndStatement.Path`, an inductive predicate.  The definitions for APSP in `PaperStatements.lean`
speak of weights in `WithTop ℤ`, of walks as lists of vertices, and of `IsDistanceMatrix`.  This
file shows that the two agree.

* A missing edge is the weight `⊤` (`toTop`).
* A path of weight `d` is a walk of weight `d`, and a walk of finite weight is a path
  (`exists_walk_of_path`, `path_of_walk`).
* So "no negative cycles" carries over (`noNegativeCycle_toTop`), and a distance matrix has `⊤`
  where there is no path and the least weight of a path elsewhere (`not_path_of_dist_eq_top`,
  `isLeast_path_of_dist_eq_coe`).
* `reachable_or_not` says this of two numbers that are written down for a pair of vertices, and
  `output_apsp` is the output condition of `EndStatement.APSP`.
-/

public section

namespace ThreeSumApsp

open EndStatement (Path)

variable {n : ℕ} {w : Fin n → Fin n → Option ℤ}

/-- An optional weight, as a weight or `⊤`. -/
 def toTop : Option ℤ → WithTop ℤ
  | some z => (z : WithTop ℤ)
  | none => ⊤

/-- A path of weight `d` is a walk of weight `d`. -/
theorem exists_walk_of_path {i j : Fin n} {d : ℤ} (h : Path w i j d) :
    ∃ rest : List (Fin n), walkEnd i rest = j ∧
      walkWeight (fun a b => toTop (w a b)) i rest = (d : WithTop ℤ) := by
  induction h with
  | nil i => exact ⟨[], rfl, rfl⟩
  | @cons i j k d e hd _ ih =>
    obtain ⟨rest, hend, hw⟩ := ih
    refine ⟨j :: rest, hend, ?_⟩
    rw [walkWeight, hw, hd]
    rfl

/-- A walk of finite weight `d` is a path of weight `d`. -/
theorem path_of_walk : ∀ (rest : List (Fin n)) (i : Fin n) (d : ℤ),
    walkWeight (fun a b => toTop (w a b)) i rest = (d : WithTop ℤ) → Path w i (walkEnd i rest) d
  | [], i, d, h => by
    obtain rfl : d = 0 := by
      rw [walkWeight] at h
      exact_mod_cast h.symm
    exact .nil i
  | k :: rest, i, d, h => by
    rw [walkWeight] at h
    cases hk : w i k with
    | none => simp [hk, toTop] at h
    | some a =>
      cases hr : walkWeight (fun a b => toTop (w a b)) k rest with
      | top => simp [hr] at h
      | coe b =>
        rw [hk, hr] at h
        obtain rfl : d = a + b := by
          have : ((a + b : ℤ) : WithTop ℤ) = (d : WithTop ℤ) := h
          exact_mod_cast this.symm
        exact .cons hk (path_of_walk rest k b hr)

/-- No closed path of negative weight: no closed walk of negative weight. -/
theorem noNegativeCycle_toTop (hneg : ∀ i d, Path w i i d → 0 ≤ d) :
    NoNegativeCycle fun i j => toTop (w i j) := by
  intro i rest hend
  cases hw : walkWeight (fun a b => toTop (w a b)) i rest with
  | top => exact le_top
  | coe z =>
    have hp := path_of_walk rest i z hw
    rw [hend] at hp
    exact_mod_cast hneg i z hp

variable {dist : Fin n → Fin n → WithTop ℤ}

/-- The distance is at most the weight of every path. -/
theorem dist_le_of_path (hdist : IsDistanceMatrix (fun i j => toTop (w i j)) dist)
    {i j : Fin n} {d : ℤ} (hp : Path w i j d) : dist i j ≤ (d : WithTop ℤ) :=
  (hdist i j).2 (exists_walk_of_path hp)

/-- Where the distance is `⊤` there is no path. -/
theorem not_path_of_dist_eq_top (hdist : IsDistanceMatrix (fun i j => toTop (w i j)) dist)
    {i j : Fin n} (htop : dist i j = ⊤) (d : ℤ) : ¬ Path w i j d := by
  intro hp
  have hle := dist_le_of_path hdist hp
  rw [htop] at hle
  exact absurd hle (by simp)

/-- A finite distance is the weight of a path, and no path is lighter. -/
theorem isLeast_path_of_dist_eq_coe (hdist : IsDistanceMatrix (fun i j => toTop (w i j)) dist)
    {i j : Fin n} {z : ℤ} (hz : dist i j = (z : WithTop ℤ)) :
    Path w i j z ∧ ∀ e, Path w i j e → z ≤ e := by
  obtain ⟨rest, hend, hw⟩ := (hdist i j).1
  rw [hz] at hw
  have hp := path_of_walk rest i z hw
  rw [hend] at hp
  refine ⟨hp, fun e he => ?_⟩
  have hle := dist_le_of_path hdist he
  rw [hz] at hle
  exact_mod_cast hle

/-- Two numbers written down for the pair `(i, j)` as APSP asks: 0 if the distance is `⊤`, and 1 and
the distance otherwise.  Then either the first is 1 and the second is the least weight of a path, or
the first is 0 and there is no path. -/
theorem reachable_or_not (hdist : IsDistanceMatrix (fun i j => toTop (w i j)) dist) {i j : Fin n}
    {flag d : ℤ} (htop : dist i j = ⊤ → flag = 0)
    (hfin : ∀ z : ℤ, dist i j = (z : WithTop ℤ) → flag = 1 ∧ d = z) :
    (flag = 1 ∧ Path w i j d ∧ ∀ e, Path w i j e → d ≤ e) ∨ (flag = 0 ∧ ∀ e, ¬ Path w i j e) := by
  cases hd : dist i j with
  | top => exact Or.inr ⟨htop hd, not_path_of_dist_eq_top hdist hd⟩
  | coe z =>
    obtain ⟨hflag, rfl⟩ := hfin z hd
    exact Or.inl ⟨hflag, isLeast_path_of_dist_eq_coe hdist hd⟩

/-- The output condition of `EndStatement.APSP` is the either-or of `reachable_or_not` for every
pair of vertices. -/
theorem output_apsp (x : EndStatement.APSP.Instance n) (out : ℕ → ℤ)
    (h : ∀ i j : Fin n,
      (out (2 * (i.val * n + j.val)) = 1 ∧ Path x.1 i j (out (2 * (i.val * n + j.val) + 1)) ∧
          ∀ e, Path x.1 i j e → out (2 * (i.val * n + j.val) + 1) ≤ e) ∨
        (out (2 * (i.val * n + j.val)) = 0 ∧ ∀ e, ¬ Path x.1 i j e)) :
    EndStatement.APSP.output x out := h

end ThreeSumApsp


