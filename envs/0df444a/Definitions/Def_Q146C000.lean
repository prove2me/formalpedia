-- Prove2me | Definitions.Def_Q146C000
-- name    : Q146C000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T05:03:54.946719+00:00
-- url     : https://prove2.me/theorems/a1c0bc75-ac59-4713-b6b9-99ef7b9808b7
-- title:
--   Definitions bundle Q146C000 of the split of OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 978 declarations of OpenAI's Lean: 140 definitions, 18 inductive types or structures, 3 instances and 817 theorems. The definitions and types are `Graph.Connected`, `Graph.CrosscutEnclosesOff`, `Graph.CrosscutExists`, `Graph.Descent`, `Graph.Encloses`, `Graph.Finite`, `Graph.HasFaceCycles`, `Graph.HasThreeVertices`, `Graph.IsArcK33`, `Graph.IsArcK33.arcDrawing`, `Graph.IsCycleCrosscut`, `Graph.IsCycleThrough`, `Graph.IsDrawing`, `Graph.IsFaceCycle`, `Graph.IsK33Config`, `Graph.IsPath`, `Graph.IsPreHexCrosscut`, `Graph.IsWalk`, `Graph.LiesOnCycle`, `Graph.Reaches`, `Graph.arcA`, `Graph.arcAPairs`, `Graph.arcB`, `Graph.arcBPairs`, `Graph.chainUnion`, `Graph.coveredVertices`, `Graph.cycleGraph`, `Graph.edgeArc`, `Graph.edgeFinset`, `Graph.edgesCover`, `Graph.edgesOutside`, `Graph.exterior`, `Graph.face`, `Graph.hexDetour`, `Graph.hexList`, `Graph.hexPairs`, `Graph.hexSet`, `Graph.k33Graph`, `Graph.pathGraphOf`, `Graph.pointSet` and 118 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Bounded`, `CircleDomains_Probability_MeasurableArcIndex`, `CircleDomains_Selection_DisjointDustContours`, `CombinatorialInvariance`, `Concatenate`, `CrosscutCells`, `CrosscutEncloses`, `Curve`, `Direction`, `FaceCycles`, `FaceCyclesProof`, `Graph_Cycle`, `Graph_CycleJordan`, `Graph_Degree`, `Graph_Drawing`, `Graph_K33`, `Graph_K33Closed`, `Graph_K33Land`, `Graph_K33Planar`, `Graph_PathGraph`, `Graph_Redrawing`, `Graph_Relabel`, `Graph_RelativeEar`, `Graph_TwoConnected`, `Graph_Walk`, `LocalGrid`, `OuterChain`, `Overlay`, `OverlayGraph`, `Parity`, `ParitySplitting`, `Plane`, `PolyPath`, `PolygonBridge`, `Polygonal`, `PolygonalCrosscut`, `PolygonalJordan`, `PrePolygonArc`, `PrePolygonSep`, `Realization`, `SegmentCut`, `SegmentOrder`, `SimpleArc`, `Square`, `Strip`, `StripConnected`, `StripConstants`, `StripLocal`, `Subarc`, `Subdivide`, `Topology`, `UniformBound`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `Q146C003`, `Q146C004` and `Q146C005`.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.Q146_CD.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q146_CD.Plane
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The plane, and the compactness toolkit

The plane is `EuclideanSpace ℝ (Fin 2)`. This module fixes that choice, supplies the
orientation form `det` and the right-angle rotation `perp` used to keep track of the two
sides of a polygonal curve, and collects the elementary consequences of compactness and
connectedness that the rest of the development uses without comment.

## Blueprint

* `det`, `perp` — Appendix C, item 1.
* `Plane.notMem_of_mem_segment_of_isMinOn` — Lemma 1.3 (nearest-point segment).
* `Plane.exists_thickening_subset`, `Plane.exists_dist_pos`, `Plane.exists_ball_subset_diff`
  — Lemma 1.4 (a), (b), (c) (compact separation).
* `Plane.eq_singleton_iInter_of_diam_tendsto_zero` — Lemma 1.6 (nested compact singleton).
* `Plane.connectedComponentIn_eq_of_frontier_disjoint` — Lemma 1.7 (recognizing a component).

Lemma 1.5 (closure and diameter) is `Metric.diam_closure` in Mathlib.
-/

open Metric Set

namespace Schoenflies

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

namespace Plane

/-- Build a point of the plane from its two coordinates. -/
abbrev mk (x y : ℝ) : Plane := !₂[x, y]

@[simp] theorem mk_zero (x y : ℝ) : mk x y 0 = x := rfl
@[simp] theorem mk_one (x y : ℝ) : mk x y 1 = y := rfl

/-! ### The orientation form and the right-angle rotation -/

/-- The orientation form `det (a, b) = a₁b₂ - a₂b₁`. It is positive exactly when `b` lies
counterclockwise of `a`. -/
def det (a b : Plane) : ℝ := a 0 * b 1 - a 1 * b 0

/-- `u` turned counterclockwise through a right angle. -/
def perp (u : Plane) : Plane := mk (-u 1) (u 0)

@[simp] theorem perp_zero (u : Plane) : perp u 0 = -u 1 := rfl
@[simp] theorem perp_one (u : Plane) : perp u 1 = u 0 := rfl

@[simp] theorem det_self (a : Plane) : det a a = 0 := by simp [det] <;> ring

theorem det_comm (a b : Plane) : det a b = -det b a := by simp [det] <;> ring

@[simp] theorem det_smul_left (r : ℝ) (a b : Plane) : det (r • a) b = r * det a b := by
  simp [det] <;> ring

@[simp] theorem det_smul_right (r : ℝ) (a b : Plane) : det a (r • b) = r * det a b := by
  simp [det] <;> ring

theorem det_add_left (a b c : Plane) : det (a + b) c = det a c + det b c := by
  simp [det] <;> ring

theorem det_add_right (a b c : Plane) : det a (b + c) = det a b + det a c := by
  simp [det] <;> ring

/-- The defining property of `perp`: it is the counterclockwise right-angle rotation, so it
pairs positively with its argument. -/
@[simp] theorem det_perp_self (u : Plane) : det u (perp u) = ‖u‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [det, Fin.sum_univ_two]
  ring

theorem inner_eq (u v : Plane) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- Turning twice reverses. -/
@[simp] theorem perp_perp (u : Plane) : perp (perp u) = -u := by
  ext i; fin_cases i <;> simp

@[simp] theorem inner_perp_self (u : Plane) : inner ℝ u (perp u) = 0 := by
  rw [inner_eq]; simp <;> ring

/-- Against `perp` on the right, `det` becomes the inner product. Together with
`det_perp_left` this is what lets the strip lemma trade one for the other. -/
@[simp] theorem det_perp_right (u v : Plane) : det u (perp v) = inner ℝ u v := by
  rw [inner_eq]; simp [det]

@[simp] theorem det_perp_left (u v : Plane) : det (perp u) v = -inner ℝ u v := by
  rw [inner_eq]; simp [det] <;> ring

@[simp] theorem det_perp_perp (u v : Plane) : det (perp u) (perp v) = det u v := by
  simp [det] <;> ring

@[simp] theorem norm_perp (u : Plane) : ‖perp u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_two, sq_abs]
  ring

/-- Two vectors are parallel exactly when the orientation form kills them. This is the
angle-free reading of "`u` and `v` point along one line". -/
theorem det_eq_zero_iff_smul (u v : Plane) (hu : u ≠ 0) :
    det u v = 0 ↔ ∃ r : ℝ, v = r • u := by
  constructor
  · intro h
    -- `u ≠ 0` means some coordinate is nonzero; solve for the ratio there.
    have hcoord : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hu (by ext i; fin_cases i <;> simp [hc.1, hc.2])
    simp only [det, sub_eq_zero] at h
    rcases hcoord with h0 | h1
    · refine ⟨v 0 / u 0, ?_⟩
      ext i
      fin_cases i <;> simp <;> field_simp <;> linarith
    · refine ⟨v 1 / u 1, ?_⟩
      ext i
      fin_cases i <;> simp <;> field_simp <;> linarith
  · rintro ⟨r, rfl⟩
    simp

/-! ### Compactness -/

variable {K L U V : Set Plane} {x a y : Plane}

/-- Lemma 1.3 (nearest-point segment). If `a` is a point of `K` nearest to `x ∉ K`, then the
half-open segment `[x, a)` misses `K`. -/
theorem notMem_of_mem_segment_of_isMinOn (haK : a ∈ K) (hxK : x ∉ K)
    (hmin : ∀ b ∈ K, dist x a ≤ dist x b) (hy : y ∈ segment ℝ x a) (hya : y ≠ a) :
    y ∉ K := by
  intro hyK
  -- `a ≠ x`, since `a ∈ K` and `x ∉ K`, so the segment is nondegenerate.
  have hax : a ≠ x := fun h => hxK (h ▸ haK)
  have hpos : 0 < dist x a := dist_pos.2 (Ne.symm hax)
  -- Write `y = x + t • (a - x)` with `0 ≤ t ≤ 1`; `t = 1` is excluded by `y ≠ a`.
  rw [segment_eq_image' ℝ x a] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  have ht1 : t < 1 := by
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact h
    · exact absurd (by rw [h]; module) hya
  -- Then `dist x y = t * dist x a < dist x a`, contradicting minimality.
  have hdist : dist x (x + t • (a - x)) = t * dist x a := by
    rw [dist_eq_norm, dist_eq_norm]
    have : x - (x + t • (a - x)) = t • (x - a) := by module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have := hmin _ hyK
  rw [hdist] at this
  nlinarith

/-- Lemma 1.4 (a) (compact separation). A compact set inside an open set has a uniform
neighbourhood inside it. Empty `K` is allowed: `thickening ρ ∅ = ∅`. -/
theorem exists_thickening_subset (hK : IsCompact K) (hU : IsOpen U) (h : K ⊆ U) :
    ∃ ρ > 0, thickening ρ K ⊆ U :=
  hK.exists_thickening_subset_open hU h

/-- Lemma 1.4 (b) (compact separation). Two disjoint nonempty compact sets have positive
distance. -/
theorem exists_dist_pos (hK : IsCompact K) (hL : IsCompact L) (hd : Disjoint K L) :
    ∃ ρ > 0, ∀ p ∈ K, ∀ q ∈ L, ρ ≤ dist p q := by
  obtain ⟨ρ, hρ, hsub⟩ :=
    hK.exists_thickening_subset_open hL.isClosed.isOpen_compl (disjoint_left.1 hd)
  refine ⟨ρ, hρ, fun p hp q hq => ?_⟩
  by_contra hlt
  exact hsub (mem_thickening_iff.2 ⟨p, hp, by rw [dist_comm]; exact not_le.1 hlt⟩) hq

/-- Lemma 1.7 (recognizing a component). A region inside an open set whose frontier misses that
open set is a connected component of it. -/
theorem connectedComponentIn_eq_of_frontier_disjoint (hU : IsOpen U) (hUconn : IsPreconnected U)
    (hsub : U ⊆ V) (hfr : frontier U ∩ V = ∅) (hx : x ∈ U) :
    connectedComponentIn V x = U := by
  -- `U` is closed in `V`: `closure U ∩ V = (U ∪ ∂U) ∩ V = U`.
  have hclosed : closure U ∩ V ⊆ U := by
    rintro z ⟨hz1, hz2⟩
    by_contra hzU
    have : z ∈ frontier U ∩ V := ⟨by rw [hU.frontier_eq]; exact ⟨hz1, hzU⟩, hz2⟩
    rw [hfr] at this
    exact this
  refine subset_antisymm ?_ (hUconn.subset_connectedComponentIn hx hsub)
  -- The component `C` is covered by the disjoint open sets `U` and `(closure U)ᶜ`, and meets `U`.
  have hcover : connectedComponentIn V x ⊆ U ∪ (closure U)ᶜ := by
    intro z hz
    by_cases h : z ∈ closure U
    · exact Or.inl (hclosed ⟨h, connectedComponentIn_subset V x hz⟩)
    · exact Or.inr h
  have hmeet : (connectedComponentIn V x ∩ U).Nonempty :=
    ⟨x, mem_connectedComponentIn (hsub hx), hx⟩
  have hempty : ¬ (connectedComponentIn V x ∩ (closure U)ᶜ).Nonempty := by
    intro hne
    obtain ⟨z, hz⟩ :=
      isPreconnected_connectedComponentIn U (closure U)ᶜ hU isClosed_closure.isOpen_compl
        hcover hmeet hne
    exact hz.2.2 (subset_closure hz.2.1)
  intro z hz
  by_contra hzU
  exact hempty ⟨z, hz, fun h => hzU (hclosed ⟨h, connectedComponentIn_subset V x hz⟩)⟩

end Plane

end Schoenflies
end

section
-- module Solutions.Q146_CD.Square
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The sup metric and axis-parallel squares

The blueprint takes the Euclidean norm as primary and uses the sup norm for the
axis-parallel objects the polygonal work is built on: grids of small squares, the vertex
squares of the redrawing argument, and the large square a bounded set is caught inside.
Appendix C item 1 asks for the comparison `‖x‖∞ ≤ ‖x‖ ≤ √2 ‖x‖∞`, which is `supNorm_le_norm`
and `norm_le_sqrt_two_mul_supNorm` here.

The one theorem of substance is `isConnected_beyondSquare`: the plane outside a closed
square is connected. It is a *square* and not a disk on purpose — the outside of a square is
exactly a union of four half-planes, each convex, with consecutive ones sharing a point,
whereas the outside of a disk would need the polar decomposition this development withholds.

## Blueprint

* `supNorm`, `supDist` — Appendix C, item 1 (the sup metric).
* `supNorm_le_norm`, `norm_le_sqrt_two_mul_supNorm` — the comparison, used without comment.
* `closedSquare`, `openSquare` — the axis-parallel square about a point.
* `isConnected_beyondSquare` — the outside of a square is connected; what makes exactly one
  face of a plane graph unbounded.
-/

open Metric Set

namespace Schoenflies

namespace Plane

/-! ### Coordinates -/

theorem sub_apply (x y : Plane) (i : Fin 2) : (x - y) i = x i - y i := rfl

theorem smul_add_apply (a b : ℝ) (x y : Plane) (i : Fin 2) :
    (a • x + b • y) i = a * x i + b * y i := by simp

/-! ### The sup norm -/

/-- The sup norm `‖x‖∞ = max |x₁| |x₂|`. -/
noncomputable def supNorm (x : Plane) : ℝ := max |x 0| |x 1|

/-- The sup distance. -/
noncomputable def supDist (x y : Plane) : ℝ := supNorm (x - y)

theorem supNorm_nonneg (x : Plane) : 0 ≤ supNorm x :=
  le_trans (abs_nonneg _) (le_max_left _ _)

@[simp] theorem supDist_self (x : Plane) : supDist x x = 0 := by
  simp [supDist, supNorm]

theorem abs_zero_le_supNorm (x : Plane) : |x 0| ≤ supNorm x := le_max_left _ _

theorem abs_one_le_supNorm (x : Plane) : |x 1| ≤ supNorm x := le_max_right _ _

theorem norm_sq_eq (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]; simp [Fin.sum_univ_two]

/-- Half of Appendix C item 1's comparison: the sup norm is at most the Euclidean norm. -/
theorem supNorm_le_norm (x : Plane) : supNorm x ≤ ‖x‖ := by
  have h0 : |x 0| ≤ ‖x‖ := by
    have : |x 0| ^ 2 ≤ ‖x‖ ^ 2 := by rw [sq_abs, norm_sq_eq]; nlinarith [sq_nonneg (x 1)]
    nlinarith [abs_nonneg (x 0), norm_nonneg x]
  have h1 : |x 1| ≤ ‖x‖ := by
    have : |x 1| ^ 2 ≤ ‖x‖ ^ 2 := by rw [sq_abs, norm_sq_eq]; nlinarith [sq_nonneg (x 0)]
    nlinarith [abs_nonneg (x 1), norm_nonneg x]
  exact max_le h0 h1

/-- The other half: the Euclidean norm is at most `√2` times the sup norm. -/
theorem norm_le_sqrt_two_mul_supNorm (x : Plane) : ‖x‖ ≤ Real.sqrt 2 * supNorm x := by
  have h0 : x 0 ^ 2 ≤ supNorm x ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_zero_le_supNorm x, abs_nonneg (x 0)]
  have h1 : x 1 ^ 2 ≤ supNorm x ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_one_le_supNorm x, abs_nonneg (x 1)]
  have hbound : ‖x‖ ^ 2 ≤ (Real.sqrt 2 * supNorm x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), norm_sq_eq]
    linarith
  nlinarith [norm_nonneg x, mul_nonneg (Real.sqrt_nonneg 2) (supNorm_nonneg x)]

/-! ### Coordinate half-planes

One convexity proof per direction serves all four sides of a square, and the outside of a
square is four of them. -/

theorem convex_coord_lt (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | x i < r} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; nlinarith
  · nlinarith [mul_lt_mul_of_pos_left hx ha', mul_le_mul_of_nonneg_left hy.le hb]

theorem convex_coord_gt (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | r < x i} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; nlinarith
  · nlinarith [mul_lt_mul_of_pos_left hx ha', mul_le_mul_of_nonneg_left hy.le hb]

/-! ### Axis-parallel squares -/

/-- The closed axis-parallel square of radius `r` about `c`. -/
def closedSquare (c : Plane) (r : ℝ) : Set Plane := {x | supDist x c ≤ r}

/-! ### The outside of a square -/

/-- The plane outside the closed square of radius `r` about the origin. -/
def beyondSquare (r : ℝ) : Set Plane := {x | r < |x 0| ∨ r < |x 1|}

/-- The outside of a square is connected.

Four half-planes, each convex and hence connected, with consecutive ones sharing a corner.
No polar decomposition, and no arbitrary union of connected sets. The radius needs no sign
condition: for `r < 0` the four half-planes already cover the plane. -/
theorem isConnected_beyondSquare (r : ℝ) : IsConnected (beyondSquare r) := by
  set R : Set Plane := {x : Plane | r < x 0} with hR
  set L : Set Plane := {x : Plane | x 0 < -r} with hL
  set T : Set Plane := {x : Plane | r < x 1} with hT
  set B : Set Plane := {x : Plane | x 1 < -r} with hB
  have hcover : beyondSquare r = R ∪ T ∪ L ∪ B := by
    ext x
    simp only [beyondSquare, hR, hL, hT, hB, mem_setOf_eq, mem_union, lt_abs]
    constructor
    · rintro (h | h) <;> rcases h with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inr (by linarith))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr (by linarith)
    · rintro (((h | h) | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr (by linarith))
      · exact Or.inr (Or.inr (by linarith))
  -- Consecutive sides share a corner. Membership unfolds definitionally, so `show` states
  -- the inequality the corner satisfies and `linarith` closes it.
  have hRT : mk (r + 1) (r + 1) ∈ R ∩ T :=
    ⟨show r < r + 1 by linarith, show r < r + 1 by linarith⟩
  have hTL : mk (-r - 1) (r + 1) ∈ T ∩ L :=
    ⟨show r < r + 1 by linarith, show -r - 1 < -r by linarith⟩
  have hLB : mk (-r - 1) (-r - 1) ∈ L ∩ B :=
    ⟨show -r - 1 < -r by linarith, show -r - 1 < -r by linarith⟩
  have cR : IsConnected R :=
    (convex_coord_gt 0 r).isConnected ⟨mk (r + 1) 0, show r < r + 1 by linarith⟩
  have cL : IsConnected L :=
    (convex_coord_lt 0 (-r)).isConnected ⟨mk (-r - 1) 0, show -r - 1 < -r by linarith⟩
  have cT : IsConnected T :=
    (convex_coord_gt 1 r).isConnected ⟨mk 0 (r + 1), show r < r + 1 by linarith⟩
  have cB : IsConnected B :=
    (convex_coord_lt 1 (-r)).isConnected ⟨mk 0 (-r - 1), show -r - 1 < -r by linarith⟩
  have c1 : IsConnected (R ∪ T) := cR.union ⟨mk (r + 1) (r + 1), hRT.1, hRT.2⟩ cT
  have c2 : IsConnected (R ∪ T ∪ L) :=
    c1.union ⟨mk (-r - 1) (r + 1), Or.inr hTL.1, hTL.2⟩ cL
  have c3 : IsConnected (R ∪ T ∪ L ∪ B) :=
    c2.union ⟨mk (-r - 1) (-r - 1), Or.inr hLB.1, hLB.2⟩ cB
  rw [hcover]
  exact c3

end Plane

end Schoenflies
end

section
-- module Solutions.Q146_CD.Bounded
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Catching a bounded set inside a square

The outer face of a plane graph is found by catching the whole drawing — finitely many points
and finitely many compact arcs — inside one axis-parallel square, and then observing that the
outside of that square is connected (`isConnected_beyondSquare`) and therefore lies in a single
face. This module is the "catching" half.

The key identity is `beyondSquare_eq_compl`: the outside of a square, as defined by a
coordinate inequality, *is* the complement of the closed square. It is what lets the
connectedness theorem be applied to a complement.

## Blueprint

* `beyondSquare_eq_compl` — the outside of a square is the complement of the closed square.
* `exists_closedSquare_of_isBounded`, `IsCompact.exists_closedSquare` — a bounded set is caught
  inside a square about the origin.
* `isOpen_compl_of_finite_isCompact` — the complement of a finite union of compact sets is
  open; the exterior of a plane graph is open for this reason.
-/

open Metric Set

namespace Schoenflies

namespace Plane

@[simp] theorem supDist_zero (x : Plane) : supDist x 0 = supNorm x := by
  simp [supDist, supNorm]

/-- The outside of a square is exactly the complement of the closed square. -/
theorem beyondSquare_eq_compl (r : ℝ) : beyondSquare r = (closedSquare 0 r)ᶜ := by
  ext x
  simp only [beyondSquare, closedSquare, mem_setOf_eq, mem_compl_iff, supDist_zero, supNorm,
    max_le_iff, not_and_or, not_le]

/-- A bounded set sits inside a closed square about the origin, of nonnegative radius. -/
theorem exists_closedSquare_of_isBounded {s : Set Plane} (hs : Bornology.IsBounded s) :
    ∃ r : ℝ, 0 ≤ r ∧ s ⊆ closedSquare 0 r := by
  obtain ⟨R, hR⟩ := hs.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  have hnorm : ‖x‖ ≤ R := by simpa using hR hx
  have : supNorm x ≤ R := le_trans (supNorm_le_norm x) hnorm
  simpa [closedSquare, supDist_zero] using le_trans this (le_max_left _ _)

theorem IsCompact.exists_closedSquare {s : Set Plane} (hs : IsCompact s) :
    ∃ r : ℝ, 0 ≤ r ∧ s ⊆ closedSquare 0 r :=
  exists_closedSquare_of_isBounded hs.isBounded

end Plane

end Schoenflies
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasurableArcIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Borel version of the explicit index, including a value on the
coincidence set. Its deck identity holds everywhere, before averaging. -/

open Set Function Filter MeasureTheory
open scoped Topology Classical

/-! d13f23b's Borel structure on `C(X, Y)` (missing in our Mathlib), with `measurable_iff_eval`
proved here for a compact metric domain. -/
instance _root_.ContinuousMap.measurableSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _

instance _root_.ContinuousMap.borelSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) where
  measurable_eq := rfl

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_DisjointDustContours
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous contours for finitely many clopen dust pieces

Disjoint compact physical pieces have disjoint open neighborhoods. Regular
contours and the outer subfamily of their combined family have disjoint
closed fills inside the prescribed connected-complement containers.
-/

open Set Filter Function
open scoped Topology Manifold ContDiff

theorem _root_.Finset.frontier_biUnion_subset {X ι : Type*} [TopologicalSpace X] (I : Finset ι)
    (s : ι → Set X) : frontier (⋃ i ∈ I, s i) ⊆ ⋃ i ∈ I, frontier (s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih =>
    simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
    refine (frontier_union_subset _ _).trans ?_
    rintro x (hx | hx)
    · exact Or.inl hx.1
    · exact Or.inr (ih hx.2)

end OAI
end

section
-- module Solutions.Q146_CD.Curve
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Arcs and Jordan curves

A simple arc is the image of an injective continuous map from `[0, 1]`; a Jordan curve is
the image of a map on `[0, 1]` which is injective before it returns to its start. Those are
the blueprint's definitions verbatim.

The parameter domain is a *subset of `ℝ`*, not a type: an arc is carried by an ordinary
`f : ℝ → Plane` together with `ContinuousOn f unitInterval` and `InjOn f unitInterval`.
Mathlib's `Path` bundles a map out of `↥unitInterval` instead, which is the right choice
when paths are to be composed up to homotopy, and the wrong one here: subarcs are taken at
arbitrary parameter pairs, reparametrisation is composition on `ℝ` with nothing to extract,
and a Jordan curve's theorems are all about *its parameters*. Taking the circle as the
domain would need a traversal of the circle by an interval, which is exactly what a
trigonometry-free development does not have.

`IsArcBetween` is the set-level reading — an arc *between two named points* — and is the
form most of the development speaks, since gluing and cutting are stated about endpoints.

## Blueprint

* `IsArc`, `IsJordanCurve` — §1, the definitions of a simple arc and a Jordan curve.
* `IsArcBetween` — an arc between two named points.
* `IsLoop` — the parametrisation underlying a Jordan curve.
-/

open Set unitInterval

namespace Schoenflies

/-! ### Arcs -/

/-- An arc between two named points: the set-level reading, and the form gluing and cutting
are stated in. -/
def IsArcBetween (A : Set Plane) (p q : Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ InjOn f I ∧ f '' I = A ∧ f 0 = p ∧ f 1 = q

/-- A loop: continuous on `[0, 1]`, returning to its start, and injective before it does. -/
structure IsLoop (f : ℝ → Plane) : Prop where
  continuousOn : ContinuousOn f I
  closes : f 0 = f 1
  injOn : InjOn f (Ico 0 1)

/-- A Jordan curve: the image of a loop. -/
def IsJordanCurve (C : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, IsLoop f ∧ f '' I = C

/-! ### The unit interval, as a subset of `ℝ` -/

theorem zero_mem_I : (0 : ℝ) ∈ I := ⟨le_refl 0, zero_le_one⟩

theorem one_mem_I : (1 : ℝ) ∈ I := ⟨zero_le_one, le_refl 1⟩

theorem isCompact_I : IsCompact I := isCompact_Icc

/-! ### Elementary properties -/

namespace IsArcBetween

variable {A : Set Plane} {p q : Plane}

theorem left_mem (h : IsArcBetween A p q) : p ∈ A := by
  obtain ⟨f, -, -, rfl, rfl, -⟩ := h
  exact mem_image_of_mem f zero_mem_I

theorem right_mem (h : IsArcBetween A p q) : q ∈ A := by
  obtain ⟨f, -, -, rfl, -, rfl⟩ := h
  exact mem_image_of_mem f one_mem_I

/-- Running a piece the other way round. -/
theorem reverse (h : IsArcBetween A p q) : IsArcBetween A q p := by
  obtain ⟨f, hc, hi, him, hp, hq⟩ := h
  refine ⟨fun t => f (1 - t), ?_, ?_, ?_, by simpa using hq, by simpa using hp⟩
  · -- `t ↦ 1 - t` maps the interval to itself, continuously.
    refine hc.comp (by fun_prop) fun t ht => ?_
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro s hs t ht hst
    have hs' : 1 - s ∈ I := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have ht' : 1 - t ∈ I := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have := hi hs' ht' hst
    linarith
  · rw [← him]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by ring_nf⟩

end IsArcBetween

namespace IsJordanCurve

variable {C : Set Plane}

theorem isCompact (h : IsJordanCurve C) : IsCompact C := by
  obtain ⟨f, hf, rfl⟩ := h
  exact isCompact_I.image_of_continuousOn hf.continuousOn

theorem isClosed (h : IsJordanCurve C) : IsClosed C := h.isCompact.isClosed

end IsJordanCurve

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_Degree
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Degree and the handshake lemma

Degree counting on Mathlib's multigraph `Graph α β`, for graphs with finitely many vertices
and finitely many edges.

## Carrying finiteness

`V(G)` and `E(G)` are `Set α` and `Set β`, not types, so finiteness has to be carried
somehow. The choice made here — and inherited by every later graph module — is a
`Prop`-valued class

```
class Graph.Finite (G : Graph α β) : Prop
```

bundling `V(G).Finite` and `E(G).Finite`, with `G.vertexFinset` and `G.edgeFinset` derived
from it. The reasons:

* It is a `Prop`, so it is proof irrelevant. `G.vertexFinset` and `G.degree` therefore do not
  depend on *which* finiteness proof is in scope, and two lemmas proved with different
  instances still compose. A bundled `Finset`-valued structure would not have that property:
  it duplicates the `vertexSet` data and forces a `↑G.vertexFinset = V(G)` side condition at
  every call site.
* It is a class, so it is silent at the call site — the statements below read like ordinary
  graph theory instead of dragging two `Set.Finite` hypotheses through every signature. The
  price is that a subgraph does not get an instance for free; `Graph.Finite.of_le` produces
  one, and `haveI` installs it locally. That is the right trade: in this development
  finiteness is a standing assumption on the ambient graph and subgraphs are formed
  constantly.
* `Finite ↥V(G)` and `Finite ↥E(G)` instances are provided too, so Mathlib's own machinery
  (`Set.Finite.subset`, `Set.toFinite`, ...) fires without help.

Counts are `Set.ncard`. `Set.ncard` is total — it is `0` on an infinite set — so `G.degree`
is defined for every graph and needs no instance argument; finiteness enters only where a
theorem actually needs it.

## Degree

`G.degree x` is the number of *edge ends* at `x`:

```
G.degree x = (G.incidenceSet x).ncard + (G.loopSet x).ncard
```

A non-loop edge at `x` is counted once, by the first summand. A loop at `x` is counted
twice, once by each summand. This is the definition the handshake lemma needs, and it agrees
with `SimpleGraph.degree` on loopless graphs.

## Blueprint

* `Graph.sum_degree_eq_two_mul_ncard_edgeSet` — "the degree sum is twice the number of
  edges", the counting step in the proof of Lemma `lem:three-leaf-tree` (Trees with three
  leaves). The whole content is `Graph.ncard_inc_add_ncard_isLoopAt`: an edge has exactly two
  ends.
* `Graph.IsLeaf` — "the vertices of degree one are the leaves", same lemma.

## Namespace

Everything lives in the root `Graph` namespace rather than in `Schoenflies`, so that dot
notation `G.degree`, `G.IsLeaf`, `G.vertexFinset` works on a `G : Graph α β`. Later graph
modules should do the same.
-/

open scoped Graph

namespace Graph

variable {α β : Type*} {G H : Graph α β} {e f : β} {x y : α}

/-! ### Finiteness -/

/-- `G.Finite` says that the multigraph `G` has finitely many vertices and finitely many
edges. Both halves are needed: the vertex set does not bound the edge set (parallel edges)
and the edge set does not bound the vertex set (isolated vertices). -/
class Finite (G : Graph α β) : Prop where
  /-- A finite graph has finitely many vertices. -/
  finite_vertexSet : V(G).Finite
  /-- A finite graph has finitely many edges. -/
  finite_edgeSet : E(G).Finite

theorem finite_vertexSet (G : Graph α β) [G.Finite] : V(G).Finite := Finite.finite_vertexSet

theorem finite_edgeSet (G : Graph α β) [G.Finite] : E(G).Finite := Finite.finite_edgeSet

/-- A subgraph of a finite graph is finite. This is not an instance — `H` cannot be
recovered from the goal — so install it with `haveI := Graph.Finite.of_le h`. -/
theorem Finite.of_le (h : H ≤ G) [G.Finite] : H.Finite :=
  ⟨(_root_.Graph.finite_vertexSet G).subset h.vertexSet_mono,
   (_root_.Graph.finite_edgeSet G).subset h.edgeSet_mono⟩

/-- The vertex set of a finite graph, as a `Finset`. -/
noncomputable def vertexFinset (G : Graph α β) [G.Finite] : Finset α :=
  (finite_vertexSet G).toFinset

/-- The edge set of a finite graph, as a `Finset`. -/
noncomputable def edgeFinset (G : Graph α β) [G.Finite] : Finset β :=
  (finite_edgeSet G).toFinset

@[simp]
theorem mem_vertexFinset [G.Finite] : x ∈ G.vertexFinset ↔ x ∈ V(G) :=
  Set.Finite.mem_toFinset _

@[simp]
theorem mem_edgeFinset [G.Finite] : e ∈ G.edgeFinset ↔ e ∈ E(G) :=
  Set.Finite.mem_toFinset _

@[simp, norm_cast]
theorem coe_vertexFinset [G.Finite] : (G.vertexFinset : Set α) = V(G) :=
  Set.Finite.coe_toFinset _

@[simp, norm_cast]
theorem coe_edgeFinset [G.Finite] : (G.edgeFinset : Set β) = E(G) :=
  Set.Finite.coe_toFinset _

@[simp]
theorem card_vertexFinset [G.Finite] : G.vertexFinset.card = V(G).ncard := by
  rw [← Set.ncard_coe_finset, coe_vertexFinset]

@[simp]
theorem card_edgeFinset [G.Finite] : G.edgeFinset.card = E(G).ncard := by
  rw [← Set.ncard_coe_finset, coe_edgeFinset]

/-! ### Incidence sets, unfolded -/

/-! ### Degree -/

/-! ### An edge has exactly two ends

This is the entire content of the handshake lemma: summed over the vertices, the number of
ends an edge has there is two, whether the edge is a loop (two ends at one vertex) or not
(one end at each of two vertices).
-/

/-! ### The handshake lemma -/

/-! ### Leaves -/

end Graph
end

section
-- module Solutions.Q146_CD.Topology
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Topology of the plane: the gaps Mathlib leaves

Appendix C of the blueprint lists the topology imported without proof. Almost all of it is in
Mathlib: compactness and Heine–Borel, the compact-to-Hausdorff homeomorphism criterion,
connectedness and its stability under images, unions through a common point, adjoining closure
points (`IsPreconnected.subset_closure`), a connected set inside a disjoint union of two opens
(`IsPreconnected.subset_left_of_subset_union`), `Metric.diam_closure`, thickenings, and the
two-piece pasting lemma (`continuousOn_union_iff_of_isClosed`).

This module collects the few that are not stated in the form the development uses.

## Blueprint

* `isOpen_connectedComponentIn` — Appendix C item 4: components of open subsets of the plane
  are open. The plane is locally connected, so this is Mathlib's, restated at `Plane` so that
  the instance is found once here rather than at every call site.
* `frontier_connectedComponentIn_compl_subset` — Appendix C item 5: the boundary of a component
  of the complement of a closed set lies in that closed set. This is the form Part I uses to
  recognize that a region's frontier sits on the curve.
* `continuousOn_union_of_isClosed` — Appendix C item 6, the pasting lemma, in the two-piece
  form the development pastes with.
-/

open Metric Set

namespace Schoenflies

namespace Plane

variable {U K : Set Plane} {x : Plane}

/-- Components of an open subset of the plane are open. The plane is locally connected. -/
theorem isOpen_connectedComponentIn (hU : IsOpen U) : IsOpen (connectedComponentIn U x) :=
  hU.connectedComponentIn

/-- Appendix C item 5. The frontier of a component of the complement of a closed set lies in
that closed set.

A frontier point off `K` would be a point of the open set `Kᶜ` in the closure of the
component; adjoining it keeps the component connected, so it was in the component already. -/
theorem frontier_connectedComponentIn_compl_subset (hK : IsClosed K) (x : Plane) :
    frontier (connectedComponentIn Kᶜ x) ⊆ K := by
  set C := connectedComponentIn Kᶜ x with hC
  have hCopen : IsOpen C := isOpen_connectedComponentIn hK.isOpen_compl
  intro z hz
  by_contra hzK
  -- `z` is a frontier point of the open set `C`, so it lies in `closure C` but not in `C`.
  rw [hCopen.frontier_eq] at hz
  obtain ⟨hzclosure, hzC⟩ := hz
  -- `C` is nonempty, since it has a frontier point in its closure.
  have hxU : x ∈ Kᶜ := by
    by_contra hx
    rw [hC, connectedComponentIn_eq_empty hx] at hzclosure
    simp at hzclosure
  -- Adjoining `z` keeps it connected and inside `Kᶜ`, so `z` was in the component already.
  have hsub : C ∪ {z} ⊆ Kᶜ := by
    refine union_subset (connectedComponentIn_subset _ _) ?_
    simpa using hzK
  have hconn : IsPreconnected (C ∪ {z}) :=
    (isPreconnected_connectedComponentIn (F := Kᶜ) (x := x)).subset_closure
      subset_union_left (union_subset subset_closure (by simpa using hzclosure))
  have : C ∪ {z} ⊆ C :=
    hconn.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn hxU)) hsub
  exact hzC (this (Or.inr rfl))

end Plane

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_Drawing
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Plane graphs

There is no `PlaneGraph` type. A plane graph is an abstract `G : Graph Plane β` **together
with** a drawing `drawing : β → ℝ → Plane`, related by `IsDrawing G drawing`. The abstract
graph stays itself, so every combinatorial theorem of `Schoenflies/Graph/` applies with
nothing to project through, and "a plane graph realises an abstract finite graph" is true by
construction rather than by a theorem. Bundling would put a record projection inside every
combinatorial citation.

The vertices being plane points is what makes the definition short: that the vertices are
distinct is not a clause, it is what `V(G) : Set Plane` already means.

`IsDrawing` has three clauses. Each edge is drawn by an injective continuous parametrization on
`[0, 1]` whose endpoint values are the two ends of that edge; an edge's arc meets the vertex set
only at those two ends; and two distinct edges meet only at vertices incident with both. The
second and third are the blueprint's "distinct edges of a plane graph meet only at shared
vertices", split so that `unique_edge_at` — away from the vertices a point of the drawing lies
on exactly one edge — falls out directly. That corollary is the form the polygonal overlay
wants.

The first clause names the *parametrization*, not merely its image. The weaker reading — "the
point set of an edge is an arc between its ends" — suffices for everything about faces, and
fails for the polygonal redrawing, which must speak of the last parameter at which an edge is
inside a given square. `edge_isArcBetween` recovers the weaker reading, so consumers needing
only that are unaffected.

## Blueprint

* `IsDrawing` — a plane graph, as an abstract graph plus a drawing.
* `IsDrawing.edge_param`, `IsDrawing.edge_isArcBetween` — the parametrization, and its image.
* `IsDrawing.arcs_meet_at_vertex`, `IsDrawing.unique_edge_at` — distinct edges meet only at
  shared vertices; away from the vertices, a point lies on exactly one edge.
* `pointSet`, `IsDrawing.isCompact_pointSet`, `exterior`, `isOpen_exterior` — what a plane
  graph occupies, and the open set its faces live in.
* `face` — the component of the exterior through a point off the drawing. Named by a point
  rather than indexed, so no face has to be produced before it is spoken about.
-/

open Metric Set Schoenflies unitInterval
open scoped _root_.Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {base : Plane}

/-- The point set of a single edge: the image of its parametrization on `[0, 1]`. -/
def edgeArc (drawing : β → ℝ → Plane) (e : β) : Set Plane := drawing e '' I

/-- A drawing of an abstract graph in the plane.

The vertices are already plane points, so a drawing only has to say how the edges run. -/
structure IsDrawing (G : Graph Plane β) (drawing : β → ℝ → Plane) : Prop where
  /-- Each edge is drawn by an injective continuous parametrization on `[0, 1]` whose two
  endpoints are the ends of that edge.

  This says more than "the point set `edgeArc drawing e` is an arc between the ends". That
  weaker clause makes two drawings with the same point sets indistinguishable, which is fine
  for the face theory and useless for the redrawing argument: "the last parameter at which
  this edge is inside the square at `v`" is meaningless unless `drawing e` is itself the
  parametrization. `edge_isArcBetween` below recovers the weaker statement.

  Stated orientation-free — `G.IsLink e (drawing e 0) (drawing e 1)` — because `IsLink` is
  symmetric, so pinning `drawing e 0` to a *named* end of a *given* link would force the two
  ends to coincide. -/
  edge_param : ∀ ⦃e⦄, e ∈ E(G) →
    ContinuousOn (drawing e) I ∧ InjOn (drawing e) I ∧ G.IsLink e (drawing e 0) (drawing e 1)

  /-- An edge's arc meets the vertex set only at its own two ends. -/
  vertex_mem_edgeArc : ∀ ⦃e x y v⦄, G.IsLink e x y → v ∈ V(G) → v ∈ edgeArc drawing e →
    v = x ∨ v = y
  /-- Two distinct edges meet only at vertices incident with both. -/
  edge_inter : ∀ ⦃e f : β⦄, e ∈ E(G) → f ∈ E(G) → e ≠ f →
    ∀ ⦃p⦄, p ∈ edgeArc drawing e → p ∈ edgeArc drawing f →
      p ∈ V(G) ∧ G.Inc e p ∧ G.Inc f p

namespace IsDrawing

/-- The point set of an edge is an arc between its two ends — the weaker reading of
`edge_param`, and the one the face theory uses. -/
theorem edge_isArcBetween (h : IsDrawing G drawing) ⦃e x y⦄ (hl : G.IsLink e x y) :
    IsArcBetween (edgeArc drawing e) x y := by
  obtain ⟨hc, hi, hlink⟩ := h.edge_param hl.edge_mem
  have base : IsArcBetween (edgeArc drawing e) (drawing e 0) (drawing e 1) :=
    ⟨drawing e, hc, hi, rfl, rfl, rfl⟩
  rcases hl.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact base
  · exact base.reverse

end IsDrawing

/-! ### What a plane graph occupies -/

/-- The point set of a plane graph: its vertices together with all of its edge arcs. -/
def pointSet (G : Graph Plane β) (drawing : β → ℝ → Plane) : Set Plane :=
  V(G) ∪ ⋃ e ∈ E(G), edgeArc drawing e

theorem vertexSet_subset_pointSet : V(G) ⊆ pointSet G drawing := subset_union_left

theorem edgeArc_subset_pointSet {e : β} (he : e ∈ E(G)) :
    edgeArc drawing e ⊆ pointSet G drawing :=
  subset_union_of_subset_right (subset_biUnion_of_mem he) _

/-- The exterior of a plane graph: everything the drawing does not occupy. -/
def exterior (G : Graph Plane β) (drawing : β → ℝ → Plane) : Set Plane :=
  (pointSet G drawing)ᶜ

/-- A face of a plane graph, named by a point of the exterior rather than indexed: no face has
to be produced before it can be spoken about. -/
def face (G : Graph Plane β) (drawing : β → ℝ → Plane) (base : Plane) : Set Plane :=
  connectedComponentIn (exterior G drawing) base

end Graph
end

section
-- module Solutions.Q146_CD.Graph_Walk
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Walks and paths in a multigraph

Mathlib's `Graph α β` carries incidence (`G.IsLink e x y`) and nothing that moves along it.
This file is the bottom of the combinatorial layer: walks, paths, reachability and
connectedness, all of which the plane development consumes through one theorem —
`Graph.IsWalk.contains_path`, the blueprint's "shorten an arbitrary walk at repeated
vertices".

## A walk is a list of edges

`G.IsWalk u W v` says the edge list `W` walks from `u` to `v`, each edge taken from the vertex
the previous one arrived at. It names its **edges**, not its vertices. That is forced by
parallel edges: two edges with the same ends are distinguishable only by name, and a walk
along one of them must be able to say which it took — a two-vertex cycle, which the plane
layer builds out of a Jordan curve cut at two points, is exactly such a graph. Nothing is
lost by naming edges, because an edge determines where taking it arrives
(`Graph.IsLink.right_unique` upstream, `Graph.IsWalk.target_unique` here).

It is an **inductive family**, not a recursion over the list. Every consumer argues by
induction along the walk, and the inductive gives that directly, naming the waypoint of each
step; a recursion `fun u (e :: W) v => ∃ w, G.IsLink e u w ∧ IsWalk G w W v` would force
every proof to generalize the source vertex by hand and to destructure an existential at each
step. The relation is built at the **source** end, since that is the end a list is extended
at; concatenation (`Graph.IsWalk.append`) and reversal (`Graph.IsWalk.reverse`) are proved
here once, and after that no argument has to care.

The empty walk demands `x ∈ V(G)`. This buys the whole file: every vertex a walk visits is a
vertex of the graph with *no* side hypothesis, because Mathlib's `Graph` already forces the
ends of an edge into `V(G)`.

## A path carries its own freshness

`G.IsPath u W v` is a walk with one clause added at each step: the vertex the step departs
from is not among those the rest of the path visits. The condition travels with the
induction, instead of being imposed afterwards on a separately computed vertex list — which
would have to be computed, and would need the graph to be loopless before it was even
correct.

## Loops

Mathlib's `Graph` allows an edge with both ends equal; the blueprint's graphs have none.
**Walks tolerate loops and paths exclude them automatically** — no hypothesis on `G` anywhere
in this file. A step of a path from `u` along `e` to `w` requires `u ∉ G.walkVertices w W`,
and `w` is always in that set, so `u ≠ w`: the freshness clause already says a path's step is
not a loop (`Graph.IsPath.not_isLoopAt`). Imposing looplessness on the graph instead would
put a hypothesis on every statement in the layer to rule out something the definitions
already rule out.

## Namespace

Declarations live in the root `Graph` namespace, extending Mathlib's, rather than in
`Schoenflies`: `G.IsWalk`, `hW.append`, `hP.isWalk` are the spellings every consumer wants,
and dot notation on a Mathlib type resolves through the type's own namespace.

## Blueprint

The blueprint uses finite graphs as an imported foundation (§"Imported facts", *Finite
graphs*: "in a finite connected graph, any two vertices are joined by a simple path, obtained
by shortening an arbitrary walk at repeated vertices"). This file supplies that import.

* `Graph.IsWalk.contains_path` — shortening a walk to a path; used at
  `lem:polygonal-connected` ("take a simple path in the resulting finite graph"),
  `lem:finite-polygonal-union` ("a simple graph path has the required realization") and
  `lem:skeleton-crosscuts` ("the resulting finite graph is connected, so it contains a
  simple graph path `P` from `a` to `b`").
* `Graph.Reaches`, `Graph.Connected` — the connectedness those three lemmas invoke.
* `Graph.IsPath.nodup` — a simple path repeats no edge; underneath the finiteness arguments
  that bound a path's length.
* `Graph.IsPath.reverse`, `Graph.IsPath.split` — a path backwards, and a path cut in two at a
  vertex it visits; what `lem:subdivision-ear-preserve` and `lem:relative-ear` run on.
-/

open Set

variable {α β : Type*} {G H : Graph α β} {u v w x y z : α} {e f : β} {W W₁ W₂ P : List β}

namespace Graph

/-! ### The vertices an edge list touches -/

/-- The vertices lying on at least one edge of `W`. -/
def coveredVertices (G : Graph α β) (W : List β) : Set α := {x | ∃ e ∈ W, G.Inc e x}

/-- The vertices a walk from `u` along `W` visits: its source, plus the ends of every edge it
takes. Defined for any edge list, not just for one that walks — the freshness clause of a
path reads it about the *rest* of the path before that rest is known to be a walk at all. -/
def walkVertices (G : Graph α β) (u : α) (W : List β) : Set α := insert u (G.coveredVertices W)

theorem mem_coveredVertices_iff : x ∈ G.coveredVertices W ↔ ∃ e ∈ W, G.Inc e x := Iff.rfl

theorem mem_walkVertices_iff : x ∈ G.walkVertices u W ↔ x = u ∨ x ∈ G.coveredVertices W :=
  Set.mem_insert_iff

@[simp]
theorem coveredVertices_nil : G.coveredVertices ([] : List β) = ∅ := by
  simp [coveredVertices]

@[simp]
theorem walkVertices_nil : G.walkVertices u ([] : List β) = {u} := by
  simp [walkVertices]

theorem mem_walkVertices_self : u ∈ G.walkVertices u W := Set.mem_insert _ _

theorem mem_walkVertices_of_mem_covered (hx : x ∈ G.coveredVertices W) :
    x ∈ G.walkVertices u W :=
  Set.mem_insert_of_mem _ hx

theorem coveredVertices_mono (h : W₁ ⊆ W₂) : G.coveredVertices W₁ ⊆ G.coveredVertices W₂ :=
  fun _ ⟨e, he, hx⟩ ↦ ⟨e, h he, hx⟩

theorem walkVertices_mono (h : W₁ ⊆ W₂) : G.walkVertices u W₁ ⊆ G.walkVertices u W₂ :=
  Set.insert_subset_insert (coveredVertices_mono h)

@[simp]
theorem coveredVertices_reverse : G.coveredVertices W.reverse = G.coveredVertices W := by
  simp [coveredVertices]

@[simp]
theorem walkVertices_reverse : G.walkVertices u W.reverse = G.walkVertices u W := by
  simp [walkVertices]

theorem coveredVertices_append :
    G.coveredVertices (W₁ ++ W₂) = G.coveredVertices W₁ ∪ G.coveredVertices W₂ := by
  ext x
  simp only [mem_coveredVertices_iff, List.mem_append, Set.mem_union]
  constructor
  · rintro ⟨e, he | he, hx⟩
    exacts [Or.inl ⟨e, he, hx⟩, Or.inr ⟨e, he, hx⟩]
  · rintro (⟨e, he, hx⟩ | ⟨e, he, hx⟩)
    exacts [⟨e, Or.inl he, hx⟩, ⟨e, Or.inr he, hx⟩]

/-- Moving the visited set across a first step, forwards: a vertex the walk visits is either
the vertex it departs from or a vertex the rest of it visits. This is where the step lemma is
used — the edge `e` has only the two ends `u` and `w`, so a vertex on `e` is one of them. -/
theorem mem_walkVertices_cons (hl : G.IsLink e u w) (hx : x ∈ G.walkVertices u (e :: W)) :
    x = u ∨ x ∈ G.walkVertices w W := by
  rcases mem_walkVertices_iff.1 hx with rfl | ⟨f, hf, hxf⟩
  · exact Or.inl rfl
  rcases List.mem_cons.1 hf with rfl | hf
  · rcases hxf.eq_or_eq_of_isLink hl with rfl | rfl
    exacts [Or.inl rfl, Or.inr mem_walkVertices_self]
  · exact Or.inr (mem_walkVertices_of_mem_covered ⟨f, hf, hxf⟩)

/-- Moving the visited set across a first step, backwards. -/
theorem mem_walkVertices_cons_of_mem (hl : G.IsLink e u w) (hx : x ∈ G.walkVertices w W) :
    x ∈ G.walkVertices u (e :: W) := by
  rcases mem_walkVertices_iff.1 hx with rfl | hx
  · exact mem_walkVertices_of_mem_covered ⟨e, List.mem_cons_self, hl.inc_right⟩
  · exact mem_walkVertices_of_mem_covered (coveredVertices_mono (List.subset_cons_self _ _) hx)

/-! ### Walks -/

/-- `G.IsWalk u W v` : the edges of `W`, in order, walk from `u` to `v` in `G`. Each edge is
taken from the vertex the previous one arrived at; the list is read at its head, so the
relation is built at the source end. -/
inductive IsWalk (G : Graph α β) : α → List β → α → Prop
  /-- Standing still at a vertex of the graph is a walk. -/
  | nil {x : α} (hx : x ∈ V(G)) : G.IsWalk x [] x
  /-- Taking an edge from the source of a walk prepends it. -/
  | cons {u w v : α} {e : β} {W : List β} (hl : G.IsLink e u w) (hW : G.IsWalk w W v) :
      G.IsWalk u (e :: W) v

theorem IsWalk.single (hl : G.IsLink e u v) : G.IsWalk u [e] v :=
  .cons hl (.nil hl.right_mem)

theorem IsWalk.left_mem (h : G.IsWalk u W v) : u ∈ V(G) := by
  cases h with
  | nil hx => exact hx
  | cons hl _ => exact hl.left_mem

/-- The edges of a walk are edges of the graph. -/
theorem IsWalk.edge_mem (h : G.IsWalk u W v) (he : e ∈ W) : e ∈ E(G) := by
  induction h with
  | nil => simp at he
  | cons hl _ ih =>
    rcases List.mem_cons.1 he with rfl | he
    exacts [hl.edge_mem, ih he]

theorem IsWalk.target_mem_walkVertices (h : G.IsWalk u W v) : v ∈ G.walkVertices u W := by
  induction h with
  | nil => exact mem_walkVertices_self
  | cons hl _ ih => exact mem_walkVertices_cons_of_mem hl ih

@[simp]
theorem isWalk_nil_iff : G.IsWalk u [] v ↔ u = v ∧ u ∈ V(G) := by
  constructor
  · rintro ⟨hx⟩; exact ⟨rfl, hx⟩
  · rintro ⟨rfl, hx⟩; exact .nil hx

theorem IsWalk.eq_of_nil (h : G.IsWalk u [] v) : u = v := (isWalk_nil_iff.1 h).1

/-- Walks concatenate, with no side condition. -/
theorem IsWalk.append (h₁ : G.IsWalk u W₁ w) (h₂ : G.IsWalk w W₂ v) :
    G.IsWalk u (W₁ ++ W₂) v := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hl _ ih => exact .cons hl (ih h₂)

/-- A walk runs backwards along the reverse of its edge list, with no side condition. -/
theorem IsWalk.reverse (h : G.IsWalk u W v) : G.IsWalk v W.reverse u := by
  induction h with
  | nil hx => simpa using IsWalk.nil hx
  | @cons u w v e W hl _ ih =>
    rw [List.reverse_cons]
    exact ih.append (IsWalk.single hl.symm)

/-- A walk in a subgraph is a walk in the graph. -/
theorem IsWalk.mono (hHG : H ≤ G) (h : H.IsWalk u W v) : G.IsWalk u W v := by
  induction h with
  | nil hx => exact .nil (hHG.vertexSet_mono hx)
  | cons hl _ ih => exact .cons (hl.mono hHG) ih

/-- A walk of a graph whose edges all survive into a subgraph is a walk of that subgraph.
This is the direction a deletion argument needs: an edge is removed, and a walk that never
used it is still there. -/
theorem IsWalk.anti (hHG : H ≤ G) (h : G.IsWalk u W v) (hu : u ∈ V(H))
    (hE : ∀ e ∈ W, e ∈ E(H)) : H.IsWalk u W v := by
  induction h with
  | nil => exact .nil hu
  | @cons u w v e W hl _ ih =>
    have he : e ∈ E(H) := hE e List.mem_cons_self
    have hl' : H.IsLink e u w := (hHG.isLink_iff he).2 hl
    exact .cons hl' (ih hl'.right_mem fun f hf ↦ hE f (List.mem_cons_of_mem _ hf))

/-! ### Paths -/

/-- `G.IsPath u W v` : a walk from `u` to `v` that never returns to a vertex it has left.
The condition is carried step by step — the vertex a step departs from is not among those the
rest of the path visits — rather than imposed afterwards on a computed vertex list. -/
inductive IsPath (G : Graph α β) : α → List β → α → Prop
  /-- Standing still at a vertex of the graph is a path. -/
  | nil {x : α} (hx : x ∈ V(G)) : G.IsPath x [] x
  /-- A step onto a path is allowed when the vertex it departs from is fresh. -/
  | cons {u w v : α} {e : β} {W : List β} (hl : G.IsLink e u w) (hW : G.IsPath w W v)
      (hfresh : u ∉ G.walkVertices w W) : G.IsPath u (e :: W) v

theorem IsPath.isWalk (h : G.IsPath u W v) : G.IsWalk u W v := by
  induction h with
  | nil hx => exact .nil hx
  | cons hl _ _ ih => exact .cons hl ih

theorem IsPath.edge_mem (h : G.IsPath u W v) (he : e ∈ W) : e ∈ E(G) := h.isWalk.edge_mem he

/-- One edge between two distinct vertices is a path. -/
theorem IsPath.single (hl : G.IsLink e u v) (huv : u ≠ v) : G.IsPath u [e] v :=
  .cons hl (.nil hl.right_mem) (by simpa using huv)

/-- A path in a subgraph is a path in the graph: the freshness clause reads only which
vertices the remaining edges touch, and a subgraph's edges have the same ends there. -/
theorem IsPath.mono (hHG : H ≤ G) (h : H.IsPath u W v) : G.IsPath u W v := by
  induction h with
  | nil hx => exact .nil (hHG.vertexSet_mono hx)
  | @cons u w v e W hl hW hfresh ih =>
    refine .cons (hl.mono hHG) ih fun hmem ↦ hfresh ?_
    -- Freshness travels because `H`'s edges link the same pairs in `G`.
    rcases mem_walkVertices_iff.1 hmem with rfl | ⟨f, hf, hinc⟩
    · exact mem_walkVertices_self
    · obtain ⟨y, hy⟩ := hinc
      exact mem_walkVertices_of_mem_covered
        ⟨f, hf, ((hHG.isLink_iff (hW.isWalk.edge_mem hf)).2 hy).inc_left⟩

theorem IsPath.target_mem_walkVertices (h : G.IsPath u W v) : v ∈ G.walkVertices u W :=
  h.isWalk.target_mem_walkVertices

/-- **Cutting a path at a vertex it passes through.** A path through `x` has a piece of itself
running from `x` to its target, and that piece uses only the path's own edges. This is the
engine of `Graph.IsWalk.contains_path`: when the next vertex is already on the path built so
far, the path is cut there instead of extended, so nothing ever gets longer. -/
theorem IsPath.from_visited (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ T, G.IsPath x T v ∧ T ⊆ W := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], .nil hx', List.nil_subset _⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨e :: W, .cons hl hW hfresh, List.Subset.refl _⟩
    · obtain ⟨T, hT, hTW⟩ := ih hx'
      exact ⟨T, hT, List.Subset.trans hTW (List.subset_cons_self _ _)⟩

/-- **Every walk contains a path** between the same two vertices, using only the walk's own
edges. This is the blueprint's "shorten an arbitrary walk at repeated vertices"; the
induction never lengthens anything, because the only alternative to prepending an edge is to
cut the path already built (`Graph.IsPath.from_visited`). -/
theorem IsWalk.contains_path (h : G.IsWalk u W v) : ∃ P, G.IsPath u P v ∧ P ⊆ W := by
  induction h with
  | nil hx => exact ⟨[], .nil hx, List.Subset.refl _⟩
  | @cons u w v e W hl hW ih =>
    obtain ⟨P, hP, hPW⟩ := ih
    by_cases hu : u ∈ G.walkVertices w P
    · -- The step lands on the path already built: cut it there rather than extend it.
      obtain ⟨T, hT, hTP⟩ := hP.from_visited hu
      exact ⟨T, hT, List.Subset.trans (List.Subset.trans hTP hPW) (List.subset_cons_self _ _)⟩
    · exact ⟨e :: P, .cons hl hP hu, List.cons_subset_cons _ hPW⟩

/-! ### Reachability -/

/-- `G.Reaches u v` : some walk of `G` runs from `u` to `v`. Stated with a walk rather than a
path because walks are what arguments build — they concatenate and reverse with no side
condition — and a path is recovered on demand (`Graph.Reaches.exists_isPath`). -/
def Reaches (G : Graph α β) (u v : α) : Prop := ∃ W, G.IsWalk u W v

@[refl]
theorem Reaches.refl (hu : u ∈ V(G)) : G.Reaches u u := ⟨[], .nil hu⟩

theorem Reaches.symm (h : G.Reaches u v) : G.Reaches v u :=
  let ⟨W, hW⟩ := h; ⟨W.reverse, hW.reverse⟩

theorem Reaches.trans (h₁ : G.Reaches u v) (h₂ : G.Reaches v w) : G.Reaches u w :=
  let ⟨W₁, hW₁⟩ := h₁; let ⟨W₂, hW₂⟩ := h₂; ⟨W₁ ++ W₂, hW₁.append hW₂⟩

/-- Whatever a walk reaches, a path reaches. -/
theorem Reaches.exists_isPath (h : G.Reaches u v) : ∃ P, G.IsPath u P v :=
  let ⟨_, hW⟩ := h; let ⟨P, hP, _⟩ := hW.contains_path; ⟨P, hP⟩

theorem Reaches.mono (hHG : H ≤ G) (h : H.Reaches u v) : G.Reaches u v :=
  let ⟨W, hW⟩ := h; ⟨W, hW.mono hHG⟩

/-! ### Connectedness -/

/-- A graph is connected when it has a vertex and every vertex reaches every other. The
nonemptiness clause is not bureaucracy: it is what makes the counting statements about trees
true as stated. -/
def Connected (G : Graph α β) : Prop :=
  V(G).Nonempty ∧ ∀ ⦃u⦄, u ∈ V(G) → ∀ ⦃v⦄, v ∈ V(G) → G.Reaches u v

theorem Connected.nonempty (h : G.Connected) : V(G).Nonempty := h.1

theorem Connected.reaches (h : G.Connected) (hu : u ∈ V(G)) (hv : v ∈ V(G)) : G.Reaches u v :=
  h.2 hu hv

/-- A graph is connected as soon as one vertex reaches all the others: reachability is
symmetric and transitive, so a common hub joins every pair. -/
theorem Connected.of_hub (hu : u ∈ V(G)) (h : ∀ v ∈ V(G), G.Reaches u v) : G.Connected :=
  ⟨⟨u, hu⟩, fun _ hx _ hy ↦ ((h _ hx).symm).trans (h _ hy)⟩

/-- In a connected graph any two vertices are joined by a path — the blueprint's imported
fact about finite graphs, with the finiteness it does not actually need dropped. -/
theorem Connected.exists_isPath (h : G.Connected) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    ∃ P, G.IsPath u P v :=
  (h.reaches hu hv).exists_isPath

/-! ### Transferring walks and paths along an inclusion or a deletion

`IsWalk.anti` above pulls a walk down an inclusion. These are its companions, factored here
because both the cycle module and the two-connectivity module reached for them independently.
-/

theorem mem_edgeSet_deleteEdges_iff {F : Set β} {f : β} :
    f ∈ E(G.deleteEdges F) ↔ f ∈ E(G) ∧ f ∉ F := by
  simp

/-- A walk that avoids the deleted names survives the deletion. -/
theorem IsWalk.deleteEdges {F : Set β} (h : G.IsWalk u W v) (hW : ∀ f ∈ W, f ∉ F) :
    (G.deleteEdges F).IsWalk u W v :=
  h.anti deleteEdges_le (by simpa using h.left_mem)
    fun f hf ↦ mem_edgeSet_deleteEdges_iff.2 ⟨h.edge_mem hf, hW f hf⟩

end Graph
end

section
-- module Solutions.Q146_CD.Graph_TwoConnected
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Vertex deletion and 2-connectivity

Deleting a vertex from Mathlib's multigraph `Graph α β`, and the blueprint's notion of a
2-connected graph.

## Vertex deletion is Mathlib's

Mathlib already has it: `Graph.deleteVerts G X = G.induce (V(G) \ X)`, in
`Mathlib/Combinatorics/Graph/Delete.lean`, with `V(G.deleteVerts X) = V(G) \ X` and
`E(G.deleteVerts X) = {e | ∃ x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X}` — an edge with an end in
`X` is gone, which is exactly what is wanted. Nothing here redefines it; `G.deleteVerts {x}`
is the deletion of one vertex, and what this file adds is the transfer of *walks* across it,
which Mathlib has no notion of.

Two of those transfers are the whole story, and both are corollaries of `Graph.IsWalk.anti`:

* `Graph.IsWalk.deleteVerts_singleton` — a walk that never visits `x` is a walk of `G - x`.
  The edges of such a walk automatically survive, because the ends of an edge of a walk are
  vertices the walk visits.
* `Graph.IsWalk.notMem_of_inc_of_deleteVerts` — a walk **in** `G - x` cannot have used an
  edge at `x`; there are none left to use. This is how an argument that routes around a
  vertex ends up avoiding a named edge, and it is what makes `Graph.IsTwoConnected.no_bridge`
  short.

Deleting a vertex the graph does not have changes nothing — `G.deleteVerts {x} = G` on the
nose (`Graph.deleteVerts_singleton_eq_self`), since `V(G) \ {x} = V(G)`. That equation is
what makes the union lemma's hard case disappear.

## At least three vertices

The counting clause of 2-connectivity is carried by `Graph.HasThreeVertices`, "three pairwise
distinct vertices", rather than by `3 ≤ V(G).ncard`. The two agree on a finite graph, but the
existential form is **monotone with no finiteness hypothesis** (`Graph.HasThreeVertices.mono`),
and monotonicity is precisely what `Graph.IsTwoConnected.union` needs: the union of two graphs
is not known to be finite at the point where its third vertex is produced. `Set.ncard` is `0`
on an infinite set, so `3 ≤ V(G).ncard` would additionally make every infinite graph fail to
be 2-connected, which is not the intent of the convention.

What consumers actually use is never the clause itself but `Graph.HasThreeVertices.exists_ne_ne`
— any two vertices leave a third over. `Graph.hasThreeVertices_iff_ncard` is the bridge back to
the count, for a consumer that has one.

## The convention, verbatim, and what it costs

`Graph.IsTwoConnected` is the blueprint's definition word for word (§"Plane graphs and the
utility graph"): at least three vertices, connected, and still connected after any one vertex
is deleted. Two consequences the blueprint calls out are recorded here as theorems rather
than as prose:

* the one-edge graph is **not** 2-connected, and
* a two-vertex cycle — two parallel edges — is a cycle without being 2-connected.

Both are instances of `Graph.not_isTwoConnected_banana`: `Graph.banana u v F` has only the two
vertices `u` and `v` whatever `F` is, so it fails the counting clause. Two-vertex cycles do
occur in the development, as face boundaries inside a larger 2-connected graph, and this is
the theorem that says they are not themselves 2-connected. (No cycle is *named* here: this
file must not depend on the cycle module.)

## Union

Mathlib's `Mathlib/Combinatorics/Graph/Lattice.lean` provides only the *infimum* of two
graphs — there is no union in this version of Mathlib — so `Graph.union` is defined here. On
an edge belonging to both graphs, `G`'s ends win:

```
(G.union H).IsLink e x y ↔ G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y)
```

which makes the definition total. It has to be resolved somehow: two graphs may disagree
about the ends of a shared edge name, and then no graph has both as subgraphs. When the two
graphs are `Graph.Compatible` — in particular when both are subgraphs of one graph, via
`Graph.Compatible.of_le_le`, which is the only way the plane layer forms unions — the
disjunction collapses to the naive one (`Graph.Compatible.union_isLink`) and both graphs are
subgraphs of the union.

## Blueprint

* `Graph.IsTwoConnected` — the definition in §"Plane graphs and the utility graph": "a finite
  graph is *2-connected* if it has at least three vertices, is connected, and remains
  connected after deletion of any one vertex".
* `Graph.IsTwoConnected.no_cut_vertex` — "with this convention a 2-connected graph has no cut
  vertex".
* `Graph.not_isTwoConnected_banana` — "the one-edge graph is not 2-connected", and the same
  computation for the two-vertex cycle of the next paragraph.
* `Graph.IsTwoConnected.no_bridge` — "A 2-connected graph has no bridge", the step of
  `lem:subdivision-ear-preserve` (a) that the ear decomposition runs on. Stated as "deleting
  the edge leaves its ends connected", which is the form `lem:cycle-criterion` consumes; the
  cycle itself is built elsewhere.
* `Graph.IsTwoConnected.union` — `lem:union-two-connected`, "if two finite 2-connected graphs
  have at least two vertices in common, their union is 2-connected".
-/

open Set

variable {α β : Type*} {G H K G₁ G₂ : Graph α β} {a b s t u v w x y z : α} {e f : β}
  {W : List β} {X : Set α} {F : Set β}

namespace Graph

/-! ### Deleting one vertex -/

/-- Deleting a vertex the graph does not have leaves the graph alone — on the nose, not merely
up to isomorphism, because `V(G) \ {x}` is literally `V(G)`. -/
theorem deleteVerts_singleton_eq_self (hx : x ∉ V(G)) : G.deleteVerts {x} = G := by
  rw [deleteVerts, sdiff_singleton_eq_self hx, induce_vertexSet]

/-! ### Walks across a vertex deletion -/

/-- Connectedness is unharmed by deleting a vertex the graph does not have. -/
theorem Connected.deleteVerts_singleton_of_notMem (h : G.Connected) (hx : x ∉ V(G)) :
    (G.deleteVerts {x}).Connected := by
  rwa [deleteVerts_singleton_eq_self hx]

/-! ### Cut vertices -/

/-! ### At least three vertices -/

/-- The graph has three pairwise distinct vertices. Stated existentially rather than as
`3 ≤ V(G).ncard` so that it is monotone with no finiteness hypothesis. -/
def HasThreeVertices (G : Graph α β) : Prop :=
  ∃ a ∈ V(G), ∃ b ∈ V(G), ∃ c ∈ V(G), a ≠ b ∧ a ≠ c ∧ b ≠ c

theorem HasThreeVertices.mono (h : G.HasThreeVertices) (hV : V(G) ⊆ V(H)) :
    H.HasThreeVertices := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := h
  exact ⟨p, hV hp, q, hV hq, r, hV hr, hpq, hpr, hqr⟩

/-- **Any two vertices leave a third over.** This, and not the counting clause itself, is what
every consumer of 2-connectivity uses; the two named vertices need not even be vertices of the
graph. -/
theorem HasThreeVertices.exists_ne_ne (h : G.HasThreeVertices) (u v : α) :
    ∃ w ∈ V(G), w ≠ u ∧ w ≠ v := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := h
  by_contra hcon
  push Not at hcon
  -- Every vertex is `u` or `v`, so the three distinct ones cannot all fit.
  have key : ∀ z ∈ V(G), z = u ∨ z = v := fun z hz ↦ (em (z = u)).imp id (hcon z hz)
  rcases key p hp with rfl | rfl <;> rcases key q hq with rfl | rfl <;>
    rcases key r hr with rfl | rfl <;> simp_all

/-! ### Two-connectivity -/

/-! ### The union of two graphs -/

/-- The union of two graphs. On an edge belonging to both, `G`'s ends win — a resolution is
needed, since two graphs may disagree about the ends of a shared edge name; for
`Graph.Compatible` graphs, which is the only case the development forms, the disjunction
collapses to the naive one. -/
protected def union (G H : Graph α β) : Graph α β where
  vertexSet := V(G) ∪ V(H)
  edgeSet := E(G) ∪ E(H)
  IsLink e x y := G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y)
  isLink_symm e _ :=
    { symm := by
        rintro x y (hxy | ⟨he, hxy⟩)
        exacts [Or.inl hxy.symm, Or.inr ⟨he, hxy.symm⟩] }
  eq_or_eq_of_isLink_of_isLink := by
    rintro g x y c d (hxy | ⟨hg, hxy⟩) (hcd | ⟨hg', hcd⟩)
    · exact hxy.left_eq_or_eq hcd
    · exact absurd hxy.edge_mem hg'
    · exact absurd hcd.edge_mem hg
    · exact hxy.left_eq_or_eq hcd
  edge_mem_iff_exists_isLink g := by
    constructor
    · rintro (hg | hg)
      · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hg
        exact ⟨x, y, Or.inl hxy⟩
      · by_cases hgG : g ∈ E(G)
        · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hgG
          exact ⟨x, y, Or.inl hxy⟩
        · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hg
          exact ⟨x, y, Or.inr ⟨hgG, hxy⟩⟩
    · rintro ⟨x, y, (hxy | ⟨-, hxy⟩)⟩
      exacts [Or.inl hxy.edge_mem, Or.inr hxy.edge_mem]
  left_mem_of_isLink := by
    rintro g x y (hxy | ⟨-, hxy⟩)
    exacts [Or.inl hxy.left_mem, Or.inr hxy.left_mem]

@[simp]
theorem vertexSet_union (G H : Graph α β) : V(G.union H) = V(G) ∪ V(H) := rfl

@[simp]
theorem edgeSet_union (G H : Graph α β) : E(G.union H) = E(G) ∪ E(H) := rfl

theorem left_le_union (G H : Graph α β) : G ≤ G.union H where
  vertexSet_mono := subset_union_left
  isLink_mono _ _ _ h := Or.inl h

/-- The right-hand graph is a subgraph of the union only when the two agree about their shared
edges — without that, no graph has both as subgraphs. -/
theorem Compatible.right_le_union (h : G.Compatible H) : H ≤ G.union H where
  vertexSet_mono := subset_union_right
  isLink_mono e x y hxy := by
    by_cases hg : e ∈ E(G)
    · exact Or.inl ((h.isLink_congr hg hxy.edge_mem).2 hxy)
    · exact Or.inr ⟨hg, hxy⟩

/-- For compatible graphs the union is the naive one. -/
theorem Compatible.union_isLink (h : G.Compatible H) :
    (G.union H).IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y := by
  refine ⟨fun hxy ↦ hxy.imp id (·.2), fun hxy ↦ ?_⟩
  rcases hxy with hxy | hxy
  · exact Or.inl hxy
  · exact h.right_le_union.isLink_mono hxy

/-- **Two connected parts covering a graph and sharing a vertex make it connected.** Used
twice below — once for the union itself, once for the union with a vertex deleted — and both
times the two parts are `G` and `H` while the whole is not their union on the nose. -/
theorem Connected.of_two_subgraphs (h₁ : G₁ ≤ K) (h₂ : G₂ ≤ K) (hV : V(K) ⊆ V(G₁) ∪ V(G₂))
    (hc₁ : G₁.Connected) (hc₂ : G₂.Connected) (hs₁ : s ∈ V(G₁)) (hs₂ : s ∈ V(G₂)) :
    K.Connected := by
  refine Connected.of_hub (h₁.vertexSet_mono hs₁) fun z hz ↦ ?_
  rcases hV hz with hz' | hz'
  · exact (hc₁.reaches hs₁ hz').mono h₁
  · exact (hc₂.reaches hs₂ hz').mono h₂

theorem Compatible.union_connected (h : G.Compatible H) (hG : G.Connected) (hH : H.Connected)
    (hs : s ∈ V(G)) (hs' : s ∈ V(H)) : (G.union H).Connected :=
  Connected.of_two_subgraphs (left_le_union G H) h.right_le_union subset_rfl hG hH hs hs'

end Graph
end

section
-- module Solutions.Q146_CD.CombinatorialInvariance
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Combinatorial invariance

The first module of Part II. It introduces the abstract record of a matched cellulation, the
notion of a geometric realization of that record, and proves that everything a realization
inherits from the record is the same for two realizations of one record —
`lem:combinatorial-invariance`.

Per the blueprint's citation index this lemma has no internal prerequisites: the whole point of
the design is that the combinatorial content of the cellulation machinery is separated from all
of the geometry, so this can be built while the Jordan curve theorem is still unproved.

## What is defined here, and how faithful it is

`CellStructure` is the *abstract* record of `def:matched-cellulation`: the finite cell sets in
each dimension, the endpoint maps, the outer subcomplex, the boundary walks, and the subcell
relation. Cells of all three dimensions are names drawn from one type `γ`; the 0- and 1-cells
are the vertices and the edges of an abstract multigraph `skel : Graph γ γ`, the 2-cells are a
set `faces`, and the three collections are disjoint. What is deliberately **not** in the record:
the parent maps (they belong to a refinement — a pair of stages — not to a stage), and any
compatibility between `sub` and the realizations (that is assertion (ix) of
`lem:cellulation-invariants`, and the blueprint is explicit that `≼_abs` "enters as a raw
datum"). No reflexivity or transitivity of `sub` is assumed; the one lemma that needs
transitivity takes it as a hypothesis.

`CellStructure.Realization` is one of the two geometric realizations. The repository's plane
graphs have `V(G) : Set Plane` — vertices *are* points — so the drawn skeleton cannot literally
be the abstract graph. It is instead the pushforward `S.skel.map pos` along the positions of
the 0-cells, with `pos` injective on `V(S.skel)`. This is the representation choice of the
module, and the alternative — carrying an abstract graph isomorphism as data — was rejected
because with the pushforward "the two skeleta realize the *same* abstract graph" is a
definitional identity rather than a theorem, which is exactly what the blueprint's proof of
part (a) asserts.

The price of the choice is paid here, once: `Graph.isTwoConnected_map_iff` and
`Graph.connected_map_iff` transport connectivity along an injective relabelling of the
vertices, so that 2-connectivity of the *drawn* graph — which is what
`def:admissible-graph` requires — transfers between the realizations. Those two, and the walk
and vertex-deletion lemmas they rest on, are general facts about `Graph.map` in the root
`Graph` namespace and belong in `Schoenflies/Graph/` if a second consumer appears.

`SkeletonHomeo` is `g : |Γ| → |Γ'|` of `def:matched-pair`, as a set-level homeomorphism with
its inverse supplied as data (so that no finiteness hypothesis is needed to invert it).
Clause 3 of `def:matched-pair` is recorded in the weaker form "`g` carries each drawn edge onto
the corresponding drawn edge", which is all that is used and which the full clause implies.

## The three parts of the lemma

Only part (b) has topological content. Parts (a) and (c) are, under this representation, either
definitional identities or one-line consequences of the fact that the index sets involved are
fields of the single structure both realizations realize; that is precisely the blueprint's
argument ("all the data in (c) belong to the common abstract cell structure"), and the
statements below are shaped so that a consumer gets the geometric conclusion on *both* sides
from one combinatorial hypothesis.

## Blueprint

* `Schoenflies.CellStructure` — the abstract record of `def:matched-cellulation`.
* `Schoenflies.CellStructure.Realization` — one of its two geometric realizations.
* `Schoenflies.CellStructure.Realization.nonboundary` — the open nonboundary part
  `|Γ| \ C` of `def:admissible-graph`.
* `Schoenflies.CellStructure.Realization.star` — the closed star `St(σ) = ⋃_{σ ≼ τ} closure τ`.
* `Schoenflies.CellStructure.SkeletonHomeo` — the skeleton homeomorphism of
  `def:matched-pair`.
* `Schoenflies.CellStructure.combinatorial_invariance` — `lem:combinatorial-invariance`,
  assembled from:
  * (a) `Realization.graph_eq_map`, `Realization.edgeSet_graph_congr`,
    `Realization.isTwoConnected_congr`, `SkeletonHomeo.image_outerSet`;
  * (b) `SkeletonHomeo.image_nonboundary`, `SkeletonHomeo.isConnected_nonboundary_iff`;
  * (c) `Realization.star_mono`, `Realization.star_transfer`,
    `Realization.star_subset_of_sub`, `outerEdge_face_corresponds`.
* `Graph.isTwoConnected_map_iff`, `Graph.connected_map_iff` — connectivity is invariant under
  an injective relabelling of the vertices; the transport that the pushforward representation
  of a realization needs.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Graph

variable {α α' β : Type*} {G : Graph α β} {f : α → α'} {u v x : α} {W : List β}

theorem IsWalk.map (f : α → α') (h : G.IsWalk u W v) : (G.map f).IsWalk (f u) W (f v) := by
  induction h with
  | nil hx => exact .nil (by simpa using Set.mem_image_of_mem f hx)
  | cons hl _ ih => exact .cons (hl.map f) ih

theorem Reaches.map (f : α → α') (h : G.Reaches u v) : (G.map f).Reaches (f u) (f v) :=
  ⟨h.choose, h.choose_spec.map f⟩

theorem Connected.map (f : α → α') (h : G.Connected) : (G.map f).Connected := by
  obtain ⟨⟨u, hu⟩, hreach⟩ := h
  refine ⟨⟨f u, by simpa using Set.mem_image_of_mem f hu⟩, ?_⟩
  rintro a ha b hb
  simp only [vertexSet_map, Set.mem_image] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  exact (hreach ha' hb').map f

theorem HasThreeVertices.map (hf : InjOn f V(G)) (h : G.HasThreeVertices) :
    (G.map f).HasThreeVertices := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := h
  have hmem : ∀ {z}, z ∈ V(G) → f z ∈ V(G.map f) := fun hz => by
    simpa using Set.mem_image_of_mem f hz
  exact ⟨f p, hmem hp, f q, hmem hq, f r, hmem hr, fun hcon => hpq (hf hp hq hcon),
    fun hcon => hpr (hf hp hr hcon), fun hcon => hqr (hf hq hr hcon)⟩

/-! ### The point set of a subgraph -/

end Graph

namespace Schoenflies

open _root_.Graph

variable {γ : Type*}

/-- The abstract record of a matched cellulation (def:matched-cellulation), stripped to the
data every consumer of combinatorial invariance reads.

The cells of all three dimensions are names drawn from one type `γ`: the 0-cells are the
vertices of the skeleton, the 1-cells are its edges, and the 2-cells are `faces`. The three
collections are required to be disjoint, so "the dimension of a cell" is well defined without
being a field.

`sub` is the abstract subcell relation `≼_abs`. The blueprint is explicit that it "enters as a
raw datum" and imposes no compatibility with the realizations: that compatibility is assertion
(ix) of lem:cellulation-invariants, proved elsewhere and for generated structures only. No
reflexivity or transitivity is assumed here either; the two lemmas below that need
transitivity take it as a hypothesis. -/
structure CellStructure (γ : Type*) where
  /-- The abstract 1-skeleton: its vertices are the 0-cells, its edges the 1-cells. -/
  skel : Graph γ γ
  /-- The 2-cells. -/
  faces : Set γ
  /-- The distinguished outer cycle, as a subgraph of the skeleton. -/
  outerGraph : Graph γ γ
  /-- The outer cycle is part of the skeleton. -/
  outerGraph_le : outerGraph ≤ skel
  /-- The cyclic boundary walk of each 2-cell, as a list of edge names. Raw datum: the
  blueprint lists it in the record of a matched cellulation and updates it explicitly under
  the two constructors. -/
  boundary : γ → List γ
  /-- The abstract subcell relation `≼_abs`. -/
  sub : γ → γ → Prop
  /-- Finitely many 0-cells. -/
  finite_vertexSet : V(skel).Finite
  /-- Finitely many 1-cells. -/
  finite_edgeSet : E(skel).Finite
  /-- Finitely many 2-cells. -/
  finite_faces : faces.Finite
  /-- A name is not both a 0-cell and a 1-cell. -/
  disjoint_vertexSet_edgeSet : Disjoint V(skel) E(skel)
  /-- A name is not both a 2-cell and a 0-cell. -/
  disjoint_faces_vertexSet : Disjoint faces V(skel)
  /-- A name is not both a 2-cell and a 1-cell. -/
  disjoint_faces_edgeSet : Disjoint faces E(skel)

namespace CellStructure

variable (S : CellStructure γ)

/-! ### Realizations -/

/-- A geometric realization of the abstract structure: a position for each 0-cell, a
parametrization for each 1-cell, and a point set for every open cell.

The drawn graph is `S.skel.map pos` — literally the pushforward of the *one* abstract
skeleton. That is what makes "two realizations of the same abstract graph" a matter of
definition rather than of a transported isomorphism.

Nothing is required of `cell` on a 2-cell. What it would have to satisfy — that the open
2-cell is the bounded complementary region of the Jordan curve of its boundary walk — is
assertion (vii) of lem:cellulation-invariants, which is not available at this point in the
development and which combinatorial invariance does not use. -/
structure Realization (S : CellStructure γ) where
  /-- Where each 0-cell sits. -/
  pos : γ → Plane
  /-- How each 1-cell runs. -/
  drawing : γ → ℝ → Plane
  /-- Distinct 0-cells sit at distinct points. -/
  injOn_pos : InjOn pos V(S.skel)
  /-- The positions and parametrizations draw the skeleton in the plane. -/
  isDrawing : IsDrawing (S.skel.map pos) drawing
  /-- The point set of each open cell. -/
  cell : γ → Set Plane
  /-- A 0-cell is realized by its point. -/
  cell_vertex : ∀ ⦃v⦄, v ∈ V(S.skel) → cell v = {pos v}
  /-- A 1-cell is realized by its open arc: the drawn arc minus its two endpoints. -/
  cell_edge : ∀ ⦃e x y⦄, S.skel.IsLink e x y → cell e = edgeArc drawing e \ {pos x, pos y}

namespace Realization

variable {S}
variable (R : S.Realization)

/-- The drawn skeleton: the pushforward of the abstract skeleton along the positions. -/
def graph : Graph Plane γ := S.skel.map R.pos

@[simp] theorem vertexSet_graph : V(R.graph) = R.pos '' V(S.skel) := vertexSet_map _ _

@[simp] theorem edgeSet_graph : E(R.graph) = E(S.skel) := edgeSet_map _ _

/-- The realized 1-skeleton `|Γ|`. -/
def skeletonSet : Set Plane := pointSet R.graph R.drawing

end Realization

/-! ### The skeleton homeomorphism -/

/-- The skeleton homeomorphism `g : |Γ| → |Γ'|` of def:matched-pair, between two realizations
of one abstract cell structure.

Clause 3 of def:matched-pair — "on each corresponding pair of edges, `g` restricts to a fixed
chosen homeomorphism between them, matching endpoints" — is recorded here in the weaker form
`edgeArc_image`, which says only that `g` carries each drawn edge onto the corresponding drawn
edge. That is all combinatorial invariance uses, and it is implied by the stronger clause.

Clause 2 of def:matched-pair, `g = u` on `C`, is *not* recorded: the boundary homeomorphism
`u` is not part of a cell structure. A consumer that needs the identification carries it
alongside; nothing here depends on it.

The inverse is supplied as data rather than produced from compactness, so that no finiteness
hypothesis is needed to speak of a homeomorphism; a producer holding `u⁻¹` has it anyway. -/
structure SkeletonHomeo {S : CellStructure γ} (R₁ R₂ : S.Realization) where
  /-- The map. -/
  toFun : Plane → Plane
  /-- Its inverse. -/
  invFun : Plane → Plane
  /-- The map is continuous on the skeleton. -/
  continuousOn_toFun : ContinuousOn toFun R₁.skeletonSet
  /-- The inverse is continuous on the other skeleton. -/
  continuousOn_invFun : ContinuousOn invFun R₂.skeletonSet
  /-- The inverse undoes the map. -/
  leftInvOn : LeftInvOn invFun toFun R₁.skeletonSet
  /-- The map undoes the inverse. -/
  rightInvOn : RightInvOn invFun toFun R₂.skeletonSet
  /-- Corresponding 0-cells correspond. -/
  pos_apply : ∀ ⦃v⦄, v ∈ V(S.skel) → toFun (R₁.pos v) = R₂.pos v
  /-- Corresponding 1-cells correspond. -/
  edgeArc_image : ∀ ⦃e⦄, e ∈ E(S.skel) → toFun '' edgeArc R₁.drawing e = edgeArc R₂.drawing e

namespace SkeletonHomeo

variable {S} {R₁ R₂ : S.Realization} (g : SkeletonHomeo R₁ R₂)

/-- The homeomorphism run backwards. -/
def symm : SkeletonHomeo R₂ R₁ where
  toFun := g.invFun
  invFun := g.toFun
  continuousOn_toFun := g.continuousOn_invFun
  continuousOn_invFun := g.continuousOn_toFun
  leftInvOn := g.rightInvOn
  rightInvOn := g.leftInvOn
  pos_apply := by
    intro v hv
    have hmem : R₁.pos v ∈ R₁.skeletonSet :=
      vertexSet_subset_pointSet (by rw [Realization.vertexSet_graph]; exact ⟨v, hv, rfl⟩)
    rw [← g.pos_apply hv, g.leftInvOn hmem]
  edgeArc_image := by
    intro e he
    have hsub : edgeArc R₁.drawing e ⊆ R₁.skeletonSet :=
      edgeArc_subset_pointSet (by rwa [Realization.edgeSet_graph])
    rw [← g.edgeArc_image he]
    exact g.leftInvOn.image_image' hsub

@[simp] theorem symm_toFun : g.symm.toFun = g.invFun := rfl

end SkeletonHomeo

/-! ### Combinatorial invariance -/

end CellStructure

end Schoenflies
end

section
-- module Solutions.Q146_CD.Concatenate
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Gluing arcs

Two arcs meeting only at the endpoint they share glue to one arc; two arcs meeting at *both*
of their ends glue to a Jordan curve. The glued parametrisation runs the first arc over the
lower half of the parameter interval and the second over the upper half, each at double
speed: `t ↦ f (2 * t)` below the midpoint and `t ↦ g (2 * t - 1)` above it. Since the
parameter here is an honest real number, that is literally what the definition says.

The halves are `[0, 1/2]` and `[1/2, 1]`. They cover the interval, and each is closed, so
continuity is Mathlib's pasting lemma `ContinuousOn.union_of_isClosed`. Injectivity splits
four ways — both parameters below the midpoint, both above, and the two mixed orders — and
only the mixed cases use the hypothesis that the two arcs meet nowhere else: there the common
value lies on both arcs, hence is the shared endpoint, and each arc's own injectivity pins
its parameter to the midpoint.

At the midpoint itself both branches of the `if` are meaningful and they agree, precisely
because the first arc finishes where the second starts. That is what makes the glued map well
defined rather than merely continuous, and it is why `concatenate_upperHalf` — the statement
that the glued map *is* the retimed second arc on the whole closed upper half, midpoint
included — carries the shared-endpoint hypothesis.

For the loop the seam analysis gains a second legitimate meeting point: besides the middle,
where the arcs are glued, there are the outer ends, where the loop is allowed to repeat
itself. Pinning those needs the start/finish counterparts of the midpoint lemmas.

## Blueprint

* `concatenate` — §1, the glued parametrisation.
* `IsArc.concatenate`, `IsArcBetween.concatenate` — two arcs meeting only at the endpoint they
  share glue to an arc.
* `IsLoop.concatenate` — two arcs glued along both of their ends make a loop.
* `IsJordanCurve.of_two_arcs` — two arcs meeting exactly at their two shared endpoints make a
  Jordan curve; the converse of the two-arcs decomposition, and the form every *construction*
  of a curve takes.
-/

open Set unitInterval

namespace Schoenflies

/-! ### The two halves of the parameter interval -/

/-- The lower half of the parameter interval, where the first arc runs. -/
def lowerHalf : Set ℝ := Icc 0 (1 / 2)

/-- The upper half of the parameter interval, where the second arc runs. The two halves
overlap in the midpoint: that is the seam. -/
def upperHalf : Set ℝ := Icc (1 / 2) 1

theorem halves_union : lowerHalf ∪ upperHalf = I :=
  Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)

theorem isClosed_lowerHalf : IsClosed lowerHalf := isClosed_Icc

theorem isClosed_upperHalf : IsClosed upperHalf := isClosed_Icc

/-- Doubling a parameter below the midpoint reaches at most one. -/
theorem double_mem_I {t : ℝ} (ht : t ∈ lowerHalf) : 2 * t ∈ I :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Doubling a parameter above the midpoint and stepping back reaches at least zero. -/
theorem doubleBack_mem_I {t : ℝ} (ht : t ∈ upperHalf) : 2 * t - 1 ∈ I :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-! ### The glued parametrisation -/

/-- Run `f` over the lower half of the interval and `g` over the upper half, each at double
speed. -/
noncomputable def concatenate (f g : ℝ → Plane) : ℝ → Plane :=
  fun t => if t ≤ 1 / 2 then f (2 * t) else g (2 * t - 1)

variable {f g : ℝ → Plane}

theorem concatenate_of_le {t : ℝ} (ht : t ≤ 1 / 2) : concatenate f g t = f (2 * t) :=
  if_pos ht

theorem concatenate_of_not_le {t : ℝ} (ht : ¬t ≤ 1 / 2) :
    concatenate f g t = g (2 * t - 1) :=
  if_neg ht

theorem concatenate_zero : concatenate f g 0 = f 0 := by
  rw [concatenate_of_le (by norm_num)]
  norm_num

theorem concatenate_one : concatenate f g 1 = g 1 := by
  rw [concatenate_of_not_le (by norm_num)]
  norm_num

/-- On the *closed* upper half the glued map is the retimed second arc — at the midpoint
included, where the `if` still takes the first branch. The two branches agree there only
because the first arc finishes where the second starts, which is what makes the glued map
well defined. -/
theorem concatenate_upperHalf (hmid : f 1 = g 0) {t : ℝ} (ht : t ∈ upperHalf) :
    concatenate f g t = g (2 * t - 1) := by
  by_cases h : t ≤ 1 / 2
  · -- The only parameter of the upper half below the midpoint is the midpoint.
    have : t = 1 / 2 := le_antisymm h ht.1
    subst this
    rw [concatenate_of_le h]
    norm_num
    exact hmid
  · exact concatenate_of_not_le h

/-! ### Continuity -/

/-- Continuity of the glued map: each half carries a composition, and the halves are closed
and cover. -/
theorem continuousOn_concatenate (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (hmid : f 1 = g 0) : ContinuousOn (concatenate f g) I := by
  rw [← halves_union]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_lowerHalf isClosed_upperHalf
  · -- On the lower half the glued map is `f` doubled.
    have h : ContinuousOn (fun t : ℝ => f (2 * t)) lowerHalf :=
      hf.comp (by fun_prop) fun t ht => double_mem_I ht
    exact h.congr fun t ht => concatenate_of_le ht.2
  · -- On the upper half it is `g`, doubled and stepped back.
    have h : ContinuousOn (fun t : ℝ => g (2 * t - 1)) upperHalf :=
      hg.comp (by fun_prop) fun t ht => doubleBack_mem_I ht
    exact h.congr fun t ht => concatenate_upperHalf hmid ht

/-! ### Pinning a parameter at the seam

At a point where two of the pieces meet, the value is one of the shared points, and the
injectivity of the arc it belongs to pins the parameter. Each half needs its own statement,
since they retime differently; the loop needs the outer ends as well as the middle. -/

theorem lowerHalf_at_finish (hfi : InjOn f I) {t : ℝ} (ht : t ∈ lowerHalf)
    (h : f (2 * t) = f 1) : t = 1 / 2 := by
  have := hfi (double_mem_I ht) one_mem_I h
  linarith

theorem upperHalf_at_start (hgi : InjOn g I) {t : ℝ} (ht : t ∈ upperHalf)
    (h : g (2 * t - 1) = g 0) : t = 1 / 2 := by
  have := hgi (doubleBack_mem_I ht) zero_mem_I h
  linarith

theorem upperHalf_at_finish (hgi : InjOn g I) {t : ℝ} (ht : t ∈ upperHalf)
    (h : g (2 * t - 1) = g 1) : t = 1 := by
  have := hgi (doubleBack_mem_I ht) one_mem_I h
  linarith

/-! ### Injectivity -/

/-- Across the seam: the common value lies on both arcs, so it is the shared endpoint, and
each half's injectivity pins its own parameter to the midpoint. Stated for a parameter of
each half rather than for `x` and `y`, so that the two orderings of the case split are the
same theorem. -/
theorem concatenate_seam (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1) {x y : ℝ}
    (hx : x ∈ lowerHalf) (hy : y ∈ upperHalf)
    (h : concatenate f g x = concatenate f g y) : x = y := by
  rw [concatenate_of_le hx.2, concatenate_upperHalf hmid hy] at h
  have hz : f (2 * x) = f 1 :=
    hmeet _ ⟨2 * x, double_mem_I hx, rfl⟩ ⟨2 * y - 1, doubleBack_mem_I hy, h.symm⟩
  have hy' : g (2 * y - 1) = g 0 := by rw [← h, hz]; exact hmid
  rw [lowerHalf_at_finish hfi hx hz, upperHalf_at_start hgi hy hy']

/-- Two arcs meeting only at the endpoint they share glue to an injective map. -/
theorem injOn_concatenate (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1) : InjOn (concatenate f g) I := by
  intro x hx y hy h
  rcases le_or_gt x (1 / 2) with hxl | hxg
  · rcases le_or_gt y (1 / 2) with hyl | hyg
    · -- Both parameters run the first arc: its own injectivity, doubled.
      rw [concatenate_of_le hxl, concatenate_of_le hyl] at h
      have := hfi (double_mem_I ⟨hx.1, hxl⟩) (double_mem_I ⟨hy.1, hyl⟩) h
      linarith
    · exact concatenate_seam hfi hgi hmid hmeet ⟨hx.1, hxl⟩ ⟨hyg.le, hy.2⟩ h
  · rcases le_or_gt y (1 / 2) with hyl | hyg
    · exact (concatenate_seam hfi hgi hmid hmeet ⟨hy.1, hyl⟩ ⟨hxg.le, hx.2⟩ h.symm).symm
    · -- Both run the second arc.
      rw [concatenate_of_not_le (not_le.2 hxg), concatenate_of_not_le (not_le.2 hyg)] at h
      have := hgi (doubleBack_mem_I ⟨hxg.le, hx.2⟩) (doubleBack_mem_I ⟨hyg.le, hy.2⟩) h
      linarith

/-! ### What the glued map covers -/

/-- Each half retimes *onto* the whole interval, so the glued map's image is exactly the two
arcs together. -/
theorem image_concatenate (hmid : f 1 = g 0) : concatenate f g '' I = f '' I ∪ g '' I := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases le_or_gt t (1 / 2) with h | h
    · exact Or.inl ⟨2 * t, double_mem_I ⟨ht.1, h⟩, (concatenate_of_le h).symm⟩
    · exact Or.inr ⟨2 * t - 1, doubleBack_mem_I ⟨h.le, ht.2⟩,
        (concatenate_of_not_le (not_le.2 h)).symm⟩
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · -- Half a parameter is the one that doubles to it.
      refine ⟨u / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      rw [concatenate_of_le (by linarith [hu.2])]
      congr 1
      ring
    · refine ⟨(u + 1) / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      rw [concatenate_upperHalf hmid ⟨by linarith [hu.1], by linarith [hu.2]⟩]
      congr 1
      ring

/-! ### The set-level gluing theorems

This is the form the rest of the development speaks: a piece is an arc between two named
points, the parametrisations are chosen inside the proofs and never seen again. -/

/-- Two pieces meeting only at the point where they are joined make one piece. -/
theorem IsArcBetween.concatenate {A B : Set Plane} {a b c : Plane} (hA : IsArcBetween A a b)
    (hB : IsArcBetween B b c) (hmeet : ∀ z ∈ A, z ∈ B → z = b) :
    IsArcBetween (A ∪ B) a c := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  have hmid : f 1 = g 0 := by rw [hf1, hg0]
  have hmeet' : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1 := by
    intro z hz hz'
    rw [hfim] at hz
    rw [hgim] at hz'
    rw [hf1]
    exact hmeet z hz hz'
  refine ⟨_, continuousOn_concatenate hfc hgc hmid, injOn_concatenate hfi hgi hmid hmeet',
    ?_, ?_, ?_⟩
  · rw [image_concatenate hmid, hfim, hgim]
  · rw [concatenate_zero]; exact hf0
  · rw [concatenate_one]; exact hg1

/-! ### Closing the loop

Two arcs that share *both* of their ends — the second runs back from where the first arrived
to where it set out — glue to a loop rather than to an arc. Everything above carries over
except the seam analysis: a common value now has two ways to be legitimate, at the middle
where the arcs are glued and at the outer ends where the loop closes, and the second of those
is exactly the repetition `IsLoop` allows itself at the finish. -/

/-- Across the seam, when the two arcs also share their outer ends. At the middle the
argument is the one for arcs; at the outer ends the second arc is at its finish, so its
parameter is `1` — which the hypothesis has excluded. -/
theorem concatenate_seam_loop (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hclose : g 1 = f 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1) {x y : ℝ}
    (hx : x ∈ lowerHalf) (hy : y ∈ upperHalf) (hy1 : y ≠ 1)
    (h : concatenate f g x = concatenate f g y) : x = y := by
  rw [concatenate_of_le hx.2, concatenate_upperHalf hmid hy] at h
  rcases hmeet _ ⟨2 * x, double_mem_I hx, rfl⟩ ⟨2 * y - 1, doubleBack_mem_I hy, h.symm⟩ with
    hz | hz
  · -- The value is where the loop closes: the second arc is at its finish, so `y = 1`.
    exact absurd (upperHalf_at_finish hgi hy (by rw [← h, hz]; exact hclose.symm)) hy1
  · have hy' : g (2 * y - 1) = g 0 := by rw [← h, hz]; exact hmid
    rw [lowerHalf_at_finish hfi hx hz, upperHalf_at_start hgi hy hy']

/-- Two arcs glued along both of their ends make a loop. -/
theorem IsLoop.concatenate (hfc : ContinuousOn f I) (hfi : InjOn f I) (hgc : ContinuousOn g I)
    (hgi : InjOn g I) (hmid : f 1 = g 0) (hclose : g 1 = f 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1) :
    IsLoop (Schoenflies.concatenate f g) where
  continuousOn := continuousOn_concatenate hfc hgc hmid
  closes := by rw [concatenate_zero, concatenate_one]; exact hclose.symm
  injOn := by
    intro x hx y hy h
    have hy1 : y ≠ 1 := ne_of_lt hy.2
    have hx1 : x ≠ 1 := ne_of_lt hx.2
    rcases le_or_gt x (1 / 2) with hxl | hxg
    · rcases le_or_gt y (1 / 2) with hyl | hyg
      · rw [concatenate_of_le hxl, concatenate_of_le hyl] at h
        have := hfi (double_mem_I ⟨hx.1, hxl⟩) (double_mem_I ⟨hy.1, hyl⟩) h
        linarith
      · exact concatenate_seam_loop hfi hgi hmid hclose hmeet ⟨hx.1, hxl⟩
          ⟨hyg.le, hy.2.le⟩ hy1 h
    · rcases le_or_gt y (1 / 2) with hyl | hyg
      · exact (concatenate_seam_loop hfi hgi hmid hclose hmeet ⟨hy.1, hyl⟩
          ⟨hxg.le, hx.2.le⟩ hx1 h.symm).symm
      · rw [concatenate_of_not_le (not_le.2 hxg), concatenate_of_not_le (not_le.2 hyg)] at h
        have := hgi (doubleBack_mem_I ⟨hxg.le, hx.2.le⟩)
          (doubleBack_mem_I ⟨hyg.le, hy.2.le⟩) h
        linarith

/-- Two pieces meeting exactly at their two shared endpoints make a Jordan curve. This is the
converse of the two-arcs decomposition, and the form every construction of a curve takes: a
cycle of a plane graph arrives as a path and one more edge back to where it started. -/
theorem IsJordanCurve.of_two_arcs {A B : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
    (hB : IsArcBetween B b a) (hmeet : ∀ z ∈ A, z ∈ B → z = a ∨ z = b) :
    IsJordanCurve (A ∪ B) := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  have hmid : f 1 = g 0 := by rw [hf1, hg0]
  have hclose : g 1 = f 0 := by rw [hg1, hf0]
  have hmeet' : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1 := by
    intro z hz hz'
    rw [hfim] at hz
    rw [hgim] at hz'
    rw [hf0, hf1]
    exact hmeet z hz hz'
  refine ⟨_, IsLoop.concatenate hfc hfi hgc hgi hmid hclose hmeet', ?_⟩
  rw [image_concatenate hmid, hfim, hgim]

end Schoenflies
end

section
-- module Solutions.Q146_CD.CrosscutCells
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Separating curves, absorption, and the two cells of a crosscut

Definition 2.4 calls a Jordan curve *separating* when its complement has exactly two regions,
one bounded and one unbounded, each with the curve as its boundary. Everything Part I proves
about a polygonal curve and Part II proves about a general one is packaged in that single
predicate, and the two lemmas below are the ones needed on both sides of the divide: they are
proved from the definition alone.

## The interface: `inside` and `outside` are total functions

The blueprint writes `Int(C)` and `Ext(C)` for the two regions and its consumers — the two
crosscut theorems — name them in their *statements*. So the two regions must be functions of
`C`, not sets produced by an existential inside the definition of separation. They are defined
here for an arbitrary set: `inside C` is the union of the bounded components of the complement
and `outside C` the union of the unbounded ones; together they partition `Cᶜ`.
Separation is then the assertion that each of the two halves is *one* region with boundary `C`
(Definition 2.4); that one is bounded and the other unbounded is then automatic, and so is
"exactly two regions", since a connected clopen piece of `Cᶜ` is a component of it.

`IsRegionOf C Ω` says `Ω` is one of the two, and `IsRegionPair C Ω Ω'` that `Ω, Ω'` are the two
in one order or the other. That is what lets Lemma 2.6 be stated once instead of twice: the
blueprint's `Ω` is sometimes `Int(C)` and sometimes `Ext(C)`, and every step of its proof is
symmetric in that choice.

## What the crosscut lemma actually needs

Lemma 2.6 is stated for a crosscut `P` of a separating curve `C` with arcs `A₁, A₂`, but its
proof never uses that `P` and the `Aᵢ` are arcs, nor the endpoints `p, q`, nor even that
`C = A₁ ∪ A₂`. What it uses is: `Aᵢ ⊆ C`, `P ∩ C ⊆ Aᵢ` (the crosscut meets the curve only in
the shared endpoints, which lie on both arcs), `Jᵢ = Aᵢ ∪ P` separating, and `A₁ ≠ A₂`. The
lemmas below are therefore stated at that level of generality, with `arcs_ne` supplying
`A₁ ≠ A₂` from the arc picture and `isJordanCurve_union` supplying the sentence "these are
Jordan curves" from `IsJordanCurve.of_two_arcs`.

One further hypothesis of the blueprint is dropped: `Ω` is described there as the region
containing `P ∖ {p, q}`, but what actually pins the roles of `Ω`, `Ω†`, `Wᵢ` and `Vᵢ` is the
inclusion `Ω† ⊆ Wᵢ`, which is a hypothesis here. A consumer supplies it by
`IsSeparating.exists_isRegionPair_subset`, which is the formal content of the blueprint's
"being connected it lies in one region of `ℝ² ∖ Jᵢ`, so `Wᵢ` and `Vᵢ` are well defined".

## Blueprint

* `inside`, `outside`, `IsSeparating` — Definition 2.4 (separating Jordan curve).
* `IsSeparating.absorption` — Lemma 2.5 (absorption).
* `crosscut_cells` — Lemma 2.6 (crosscut cells), all three parts, with the per-part lemmas
  `cell_subset_region_diff`, `cell_isComponent`, `closure_cell_inter_curve` stated separately
  because the bundled form carries the hypotheses of both indices at once.
-/

open Bornology Set

namespace Schoenflies

variable {C J P A A₁ A₂ Ω Ω' W V : Set Plane} {x p q : Plane}

/-! ### The inside and the outside of a set

Both are defined for an arbitrary set, without any separation hypothesis: `inside C` collects
the points whose component in the complement is bounded, `outside C` the rest of the
complement. -/

/-- The union of the bounded components of the complement — the blueprint's `Int(C)` once `C`
is known to be separating. -/
def inside (C : Set Plane) : Set Plane :=
  {x | x ∉ C ∧ IsBounded (connectedComponentIn Cᶜ x)}

/-- The union of the unbounded components of the complement — the blueprint's `Ext(C)` once `C`
is known to be separating. -/
def outside (C : Set Plane) : Set Plane :=
  {x | x ∉ C ∧ ¬ IsBounded (connectedComponentIn Cᶜ x)}

theorem inside_subset_compl : inside C ⊆ Cᶜ := fun _ hx => hx.1

theorem outside_subset_compl : outside C ⊆ Cᶜ := fun _ hx => hx.1

theorem inside_union_outside (C : Set Plane) : inside C ∪ outside C = Cᶜ := by
  ext z
  constructor
  · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
  · intro hz
    by_cases hb : IsBounded (connectedComponentIn Cᶜ z)
    · exact Or.inl ⟨hz, hb⟩
    · exact Or.inr ⟨hz, hb⟩

theorem disjoint_inside_outside : Disjoint (inside C) (outside C) := by
  rw [Set.disjoint_left]
  rintro z ⟨-, hb⟩ ⟨-, hb'⟩
  exact hb' hb

/-- Boundedness of the component is constant along a component, so the inside is a union of
whole components. -/
theorem connectedComponentIn_subset_inside (hx : x ∈ inside C) :
    connectedComponentIn Cᶜ x ⊆ inside C := by
  intro z hz
  refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
  rw [← connectedComponentIn_eq hz]
  exact hx.2

theorem connectedComponentIn_subset_outside (hx : x ∈ outside C) :
    connectedComponentIn Cᶜ x ⊆ outside C := by
  intro z hz
  refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
  rw [← connectedComponentIn_eq hz]
  exact hx.2

/-- A union of components of an open set is open. -/
theorem isOpen_inside (hC : IsClosed C) : IsOpen (inside C) := by
  rw [isOpen_iff_forall_mem_open]
  exact fun z hz => ⟨connectedComponentIn Cᶜ z, connectedComponentIn_subset_inside hz,
    Plane.isOpen_connectedComponentIn hC.isOpen_compl, mem_connectedComponentIn hz.1⟩

theorem isOpen_outside (hC : IsClosed C) : IsOpen (outside C) := by
  rw [isOpen_iff_forall_mem_open]
  exact fun z hz => ⟨connectedComponentIn Cᶜ z, connectedComponentIn_subset_outside hz,
    Plane.isOpen_connectedComponentIn hC.isOpen_compl, mem_connectedComponentIn hz.1⟩

/-! ### Definition 2.4: a separating Jordan curve -/

/-- Definition 2.4. A Jordan curve is *separating* when its complement has exactly two regions,
one bounded and one unbounded, each with boundary `C`.

Since `inside C` and `outside C` always partition the complement into the bounded-component
part and the unbounded-component part, "exactly two regions, one bounded and one unbounded"
says precisely that each part is a single region; and the boundedness of one and unboundedness
of the other are then consequences rather than hypotheses (`IsSeparating.isBounded_inside`,
`IsSeparating.not_isBounded_outside`). -/
structure IsSeparating (C : Set Plane) : Prop where
  /-- The set is a Jordan curve. -/
  isJordanCurve : IsJordanCurve C
  /-- The bounded part of the complement is a single region. -/
  isConnected_inside : IsConnected (inside C)
  /-- The unbounded part of the complement is a single region. -/
  isConnected_outside : IsConnected (outside C)
  /-- The inside has the curve as its boundary. -/
  frontier_inside : frontier (inside C) = C
  /-- The outside has the curve as its boundary. -/
  frontier_outside : frontier (outside C) = C

namespace IsSeparating

theorem isClosed (h : IsSeparating C) : IsClosed C := h.isJordanCurve.isClosed

theorem isOpen_inside (h : IsSeparating C) : IsOpen (Schoenflies.inside C) :=
  Schoenflies.isOpen_inside h.isClosed

theorem isOpen_outside (h : IsSeparating C) : IsOpen (Schoenflies.outside C) :=
  Schoenflies.isOpen_outside h.isClosed

/-- The inside really is one *region* of the complement, that is, a connected component of it:
it is a union of components which is itself connected. Together with its twin below this is
the "exactly two regions" clause of Definition 2.4. -/
theorem connectedComponentIn_eq_inside (h : IsSeparating C) (hx : x ∈ Schoenflies.inside C) :
    connectedComponentIn Cᶜ x = Schoenflies.inside C :=
  Set.Subset.antisymm (connectedComponentIn_subset_inside hx)
    (h.isConnected_inside.isPreconnected.subset_connectedComponentIn hx inside_subset_compl)

/-- The outside is a connected component of the complement. -/
theorem connectedComponentIn_eq_outside (h : IsSeparating C) (hx : x ∈ Schoenflies.outside C) :
    connectedComponentIn Cᶜ x = Schoenflies.outside C :=
  Set.Subset.antisymm (connectedComponentIn_subset_outside hx)
    (h.isConnected_outside.isPreconnected.subset_connectedComponentIn hx outside_subset_compl)

end IsSeparating

/-! ### The two regions, named

`IsRegionOf C Ω` is "`Ω` is a region of `ℝ² ∖ C`" and `IsRegionPair C Ω Ω'` is "`Ω` and `Ω'`
are *the* two regions". Both are stated without a separation hypothesis; the facts that make
them useful carry one. -/

/-- `Ω` is a region of the complement of `C`. -/
def IsRegionOf (C Ω : Set Plane) : Prop := Ω = inside C ∨ Ω = outside C

/-- `Ω` and `Ω'` are the two regions of the complement of `C`, in one order or the other. -/
def IsRegionPair (C Ω Ω' : Set Plane) : Prop :=
  (Ω = inside C ∧ Ω' = outside C) ∨ (Ω = outside C ∧ Ω' = inside C)

/-- Every component of the complement is one of the two regions: there are no others. This is
the last clause of "exactly two regions". -/
theorem IsSeparating.isRegionOf_connectedComponentIn (h : IsSeparating C) (hx : x ∉ C) :
    IsRegionOf C (connectedComponentIn Cᶜ x) := by
  have hx' : x ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hx
  rcases hx' with hx' | hx'
  · exact Or.inl (h.connectedComponentIn_eq_inside hx')
  · exact Or.inr (h.connectedComponentIn_eq_outside hx')

namespace IsRegionOf

theorem inside (C : Set Plane) : IsRegionOf C (Schoenflies.inside C) := Or.inl rfl

theorem outside (C : Set Plane) : IsRegionOf C (Schoenflies.outside C) := Or.inr rfl

theorem subset_compl (h : IsRegionOf C Ω) : Ω ⊆ Cᶜ := by
  rcases h with rfl | rfl
  · exact inside_subset_compl
  · exact outside_subset_compl

theorem isOpen (h : IsRegionOf C Ω) (hC : IsSeparating C) : IsOpen Ω := by
  rcases h with rfl | rfl
  · exact hC.isOpen_inside
  · exact hC.isOpen_outside

theorem isConnected (h : IsRegionOf C Ω) (hC : IsSeparating C) : IsConnected Ω := by
  rcases h with rfl | rfl
  · exact hC.isConnected_inside
  · exact hC.isConnected_outside

/-- A region is a connected component of the complement. -/
theorem connectedComponentIn_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) (hx : x ∈ Ω) :
    connectedComponentIn Cᶜ x = Ω := by
  rcases h with rfl | rfl
  · exact hC.connectedComponentIn_eq_inside hx
  · exact hC.connectedComponentIn_eq_outside hx

theorem frontier_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) : frontier Ω = C := by
  rcases h with rfl | rfl
  · exact hC.frontier_inside
  · exact hC.frontier_outside

/-- Every point of the curve is a limit of points of the region: this is the half of
`frontier Ω = C` that absorption uses. -/
theorem subset_closure (h : IsRegionOf C Ω) (hC : IsSeparating C) : C ⊆ closure Ω := by
  rw [← h.frontier_eq hC]
  exact frontier_subset_closure

/-- The closure of a region is the region together with the curve. -/
theorem closure_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) : closure Ω = Ω ∪ C := by
  have hfr := h.frontier_eq hC
  rw [(h.isOpen hC).frontier_eq] at hfr
  rw [← hfr, Set.union_sdiff_cancel _root_.subset_closure]

end IsRegionOf

namespace IsRegionPair

theorem left (h : IsRegionPair C Ω Ω') : IsRegionOf C Ω := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem right (h : IsRegionPair C Ω Ω') : IsRegionOf C Ω' := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem symm (h : IsRegionPair C Ω Ω') : IsRegionPair C Ω' Ω := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

theorem union_eq (h : IsRegionPair C Ω Ω') : Ω ∪ Ω' = Cᶜ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact inside_union_outside C
  · rw [Set.union_comm]
    exact inside_union_outside C

theorem disjoint (h : IsRegionPair C Ω Ω') : Disjoint Ω Ω' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact disjoint_inside_outside
  · exact disjoint_inside_outside.symm

/-- A connected set off the curve and off one region lies in the other. This is the only place
where "exactly two regions" is used, and it is used in exactly that form. -/
theorem subset_left_of_isPreconnected (h : IsRegionPair C Ω Ω') (hC : IsSeparating C)
    {S : Set Plane} (hS : IsPreconnected S) (hne : S.Nonempty) (hSC : S ⊆ Cᶜ)
    (hSΩ' : Disjoint S Ω') : S ⊆ Ω := by
  obtain ⟨z, hz⟩ := hne
  have hcover : S ⊆ Ω ∪ Ω' := by rw [h.union_eq]; exact hSC
  have hzΩ : z ∈ Ω := (hcover hz).resolve_right fun hz' => Set.disjoint_left.1 hSΩ' hz hz'
  exact hS.subset_left_of_subset_union (h.left.isOpen hC) (h.right.isOpen hC) h.disjoint hcover
    ⟨z, hz, hzΩ⟩

end IsRegionPair

/-! ### Lemma 2.5: absorption -/

/-- Lemma 2.5 (absorption), set-theoretic core. If every point of `C` is a limit of points of
`Ω`, and `Ω` sits inside an open `V` whose frontier lies in `J`, then `C` misses `V` only where
`J` does. -/
theorem absorption_of_subset_closure (hCΩ : C ⊆ closure Ω) (hV : IsOpen V)
    (hfr : frontier V ⊆ J) (hsub : Ω ⊆ V) : C \ J ⊆ V := by
  rintro z ⟨hzC, hzJ⟩
  by_contra hzV
  -- `z` lies in the closure of `V` but not in `V`, so it lies on the frontier, hence in `J`.
  exact hzJ (hfr (by rw [hV.frontier_eq]; exact ⟨closure_mono hsub (hCΩ hzC), hzV⟩))

/-- Lemma 2.5 (absorption). If a region `Ω` of the complement of a separating curve `C` is
contained in a region `V` of the complement of a separating curve `J`, then all of `C` off `J`
lies in `V`. -/
theorem IsSeparating.absorption (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionOf C Ω) (hV : IsRegionOf J V) (hsub : Ω ⊆ V) : C \ J ⊆ V :=
  absorption_of_subset_closure (hΩ.subset_closure hC) (hV.isOpen hJ)
    (hV.frontier_eq hJ).subset hsub

/-! ### Lemma 2.6: the two cells of a crosscut

The setting: `C` is a separating curve, `Ω` and `Ω'` its two regions, `J` a separating curve
with `P ⊆ J ⊆ C ∪ P`, and `W, V` the two regions of `ℝ² ∖ J`, with `Ω' ⊆ W`. The blueprint's
`J` is `Aᵢ ∪ P` for one of the two arcs `Aᵢ`; the proof only needs the two inclusions. -/

/-- The far region `Ω'` absorbs all of `C` off `J`, so the near cell `V` misses `C` entirely:
the part of `C` off `J` is in `W`, and the part on `J` is off `V` because `V` misses `J`. -/
theorem disjoint_cell_curve (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ' : IsRegionOf C Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) : Disjoint V C := by
  have hCW : C \ J ⊆ W := hC.absorption hJ hΩ' hWV.left hΩW
  rw [Set.disjoint_left]
  intro z hzV hzC
  by_cases hzJ : z ∈ J
  · exact hWV.right.subset_compl hzV hzJ
  · exact Set.disjoint_left.1 hWV.symm.disjoint hzV (hCW ⟨hzC, hzJ⟩)

/-- Lemma 2.6, first half of (a): the cell `V` is contained in `Ω ∖ P`. It misses `C`, it is
connected, and it misses `Ω'` because `Ω' ⊆ W`; so it lies in `Ω`. It misses `P` because it
misses `J ⊇ P`. -/
theorem cell_subset_region_diff (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionPair C Ω Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) (hPJ : P ⊆ J) : V ⊆ Ω \ P := by
  have hVC : Disjoint V C := disjoint_cell_curve hC hJ hΩ.right hWV hΩW
  have hVJ : V ⊆ Jᶜ := hWV.right.subset_compl
  -- `V` and `W` are the two regions of `ℝ² ∖ J`, and `Ω'` sits inside `W`.
  have hVΩ' : Disjoint V Ω' := hWV.symm.disjoint.mono_right hΩW
  have hVΩ : V ⊆ Ω :=
    hΩ.subset_left_of_isPreconnected hC (hWV.right.isConnected hJ).isPreconnected
      (hWV.right.isConnected hJ).nonempty (fun z hz => Set.disjoint_left.1 hVC hz) hVΩ'
  exact fun z hz => ⟨hVΩ hz, fun hzP => hVJ hz (hPJ hzP)⟩

/-- Lemma 2.6 (a): the cell `V` is a connected component of `Ω ∖ P`. Its frontier is `J`, which
lies in `C ∪ P` and so misses the open set `Ω ∖ P`; Lemma 1.7 does the rest. -/
theorem cell_isComponent (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionPair C Ω Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) (hPJ : P ⊆ J) (hJCP : J ⊆ C ∪ P) :
    ∀ z ∈ V, connectedComponentIn (Ω \ P) z = V := by
  intro z hz
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint (hWV.right.isOpen hJ)
    (hWV.right.isConnected hJ).isPreconnected
    (cell_subset_region_diff hC hJ hΩ hWV hΩW hPJ) ?_ hz
  rw [hWV.right.frontier_eq hJ]
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro w ⟨hwJ, hwΩ, hwP⟩
  rcases hJCP hwJ with hwC | hwP'
  · exact hΩ.left.subset_compl hwΩ hwC
  · exact hwP hwP'

/-- Lemma 2.6 (c): the closure of the cell meets `C` exactly in `J ∩ C`. The closure is
`V ∪ J`, and `V` misses `C`. -/
theorem closure_cell_inter_curve (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ' : IsRegionOf C Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) : closure V ∩ C = J ∩ C := by
  have hVC : Disjoint V C := disjoint_cell_curve hC hJ hΩ' hWV hΩW
  rw [hWV.right.closure_eq hJ, Set.union_inter_distrib_right, hVC.inter_eq, Set.empty_union]

/-! ### The arc-level side conditions

Two small facts turn the blueprint's arc picture into the hypotheses the lemmas above take. -/

/-! ### Lemma 2.6, bundled -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_Cycle
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cycles, acyclicity and bridges

This file sits directly on `Schoenflies/Graph/Walk.lean` and answers one question: which
edges of a multigraph lie on a cycle. Its main theorem is the blueprint's cycle criterion —
an edge lies on a cycle exactly when deleting it leaves its two ends joined — and a bridge is
read off it.

## A cycle is presented through one of its edges

`G.IsCycleThrough e u v D` is an edge `e` linking `u` to `v`, together with a **path** `D`
from `u` to `v` that does not use `e`. The closed walk is never assembled.

This is not a weakening. Every question the blueprint asks about a cycle is asked *at an
edge* — is this edge on a cycle, does deleting it disconnect its ends, is it a bridge, can it
be deleted from a spanning subgraph — so the edge is always available to present the cycle
through. And presenting it this way is what makes the definition short: the blueprint's
"connected subgraph in which every vertex has degree exactly two" would have to rule out, by
hand, every repetition that a closed walk can contain, whereas `Graph.IsPath` already forbids
them. The blueprint's own proof of the criterion runs in exactly this shape ("take a shortest
walk from `x` to `y` avoiding `e`; a shortest walk repeats no vertex, so it is a simple
path").

**Length two is included, and is why edges are names.** Two parallel edges — the same pair of
ends, two different names — are a cycle: one of them is `e`, the other is the one-edge path
`D`. The blueprint needs those ("two-vertex cycles do occur below, as boundaries of faces
created by overlays and by ears parallel to an existing edge"), and a walk that named
vertices could not tell the two apart.

## Loops

Mathlib's `Graph` allows an edge with both ends equal. **A loop is taken to be a cycle of
length one**, which is the usual convention and also what the blueprint's own definition
gives (a loop contributes two to the degree of its vertex, so the subgraph consisting of a
loop and its vertex is connected with every vertex of degree two). It comes out of the
definition here for free: `G.IsLink e x x` together with the empty path at `x`, which does
not use `e`, is a cycle through `e`. So `Graph.liesOnCycle_of_isLoopAt` needs no proof, no
graph is acyclic while carrying a loop, and no bridge is a loop. Nothing in this file
hypothesises looplessness.

## Deletion

Edge deletion is Mathlib's `Graph.deleteEdges`, not a new definition; `G.deleteEdges {e}` is
the graph with the single name `e` removed. What this file adds is the transfer interface —
a walk or a path survives a deletion exactly when it never took a deleted edge — which is the
whole content of a deletion argument, since which vertices an edge joins is not a question a
subgraph can answer differently. `Graph.IsWalk.anti` from `Walk.lean` is the engine;
`Graph.IsPath.anti` is proved here, since freshness has to be carried down too.

## Blueprint

* `Graph.liesOnCycle_iff_deleteEdges_reaches` — `lem:cycle-criterion`, "in a finite graph, an
  edge lies on a cycle if and only if deleting it does not disconnect its endpoints", both
  directions, with the finiteness the proof does not use dropped. The two halves are
  `Graph.LiesOnCycle.deleteEdges_reaches` and `Graph.LiesOnCycle.of_deleteEdges_reaches`.
* `Graph.IsBridge`, `Graph.isBridge_iff_not_reaches` — the bridges of
  `lem:subdivision-ear-preserve` ("a 2-connected graph has no bridge. Indeed, if `uv` were a
  bridge, the two components of `G - uv` …"), stated as the separation of the two ends.
* `Graph.IsAcyclic`, `Graph.Connected.deleteEdges_singleton` — the acyclicity underneath
  `lem:three-leaf-tree`, and the minimal spanning subgraph of the H5 construction ("take a
  minimal connected subgraph `T_i` spanning the three terminals. It is a tree: an edge of a
  cycle could be deleted"), which is exactly the statement that deleting an edge on a cycle
  keeps the graph connected.
* `Graph.IsPath.chord_liesOnCycle`, `Graph.IsAcyclic.mem_of_isLink_of_mem_walkVertices` — the
  step of `lem:three-leaf-tree`'s proof that says "a second neighbor on the path would close
  a cycle"; the form the tree module's longest-path argument consumes.
-/

open Set

variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f : β} {F : Set β} {W P D : List β}

namespace Graph

/-! ### Visited vertices along an inclusion

`Walk.lean` proves `walkVertices` monotone in the edge list. It is also monotone in the
graph, which is what pulling a path *down* into a subgraph needs: the freshness clause of a
path speaks about the subgraph's visited set, and that is the smaller one. -/

/-! ### Edge deletion

`Graph.deleteEdges` is Mathlib's. These are the four transfer lemmas every deletion argument
below reduces to. -/

theorem IsWalk.reaches_deleteEdges (h : G.IsWalk u W v) (hW : ∀ f ∈ W, f ∉ F) :
    (G.deleteEdges F).Reaches u v :=
  ⟨W, h.deleteEdges hW⟩

/-! ### Cycles -/

/-- `G.IsCycleThrough e u v D` : the edge `e` links `u` to `v`, and `D` is a path from `u`
back to `v` that does not use `e`. The cycle is `e` together with `D`; it is presented
through `e` because that is the edge every question is asked about. -/
def IsCycleThrough (G : Graph α β) (e : β) (u v : α) (D : List β) : Prop :=
  G.IsLink e u v ∧ G.IsPath u D v ∧ e ∉ D

/-- `G.LiesOnCycle e` : the edge `e` lies on a cycle of `G`. -/
def LiesOnCycle (G : Graph α β) (e : β) : Prop := ∃ u v D, G.IsCycleThrough e u v D

theorem IsCycleThrough.isLink (h : G.IsCycleThrough e u v D) : G.IsLink e u v := h.1

theorem IsCycleThrough.isPath (h : G.IsCycleThrough e u v D) : G.IsPath u D v := h.2.1

theorem IsCycleThrough.notMem (h : G.IsCycleThrough e u v D) : e ∉ D := h.2.2

/-! ### The cycle criterion

The blueprint's `lem:cycle-criterion`. Both directions are one step each, once the deletion
interface above is in place: forwards, the detour of the cycle is a walk that avoided `e`;
backwards, a path in the deletion cannot have used `e` because `e` is not there. -/

/-- **An edge on a cycle is not needed to join its ends**: the rest of the cycle still does.

The ends are given as an arbitrary pair `u, v` that `e` links, not as the pair the cycle was
presented with — an edge has only two ends, so the two presentations agree up to a swap, and
reachability is symmetric. -/
theorem LiesOnCycle.deleteEdges_reaches (hl : G.IsLink e u v) (h : G.LiesOnCycle e) :
    (G.deleteEdges {e}).Reaches u v := by
  obtain ⟨u', v', D, hl', hP, hD⟩ := h
  -- The detour avoids `e` by definition, so it is still there after `e` goes.
  have hR : (G.deleteEdges {e}).Reaches u' v' :=
    hP.isWalk.reaches_deleteEdges fun f hf hmem ↦ hD (Set.mem_singleton_iff.1 hmem ▸ hf)
  rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [hR, hR.symm]

/-- **A walk reroutes around an edge that lies on a cycle**: wherever it took `e`, it can go
the long way round instead. Proved by induction along the walk rather than by splicing the
detour into the edge list, so nothing has to be said about what the spliced list looks
like. -/
theorem IsWalk.reaches_deleteEdges_of_liesOnCycle (h : G.LiesOnCycle e) (hW : G.IsWalk u W v) :
    (G.deleteEdges {e}).Reaches u v := by
  induction hW with
  | nil hx => exact .refl (by simpa using hx)
  | @cons u w v f W hl _ ih =>
    refine Reaches.trans ?_ ih
    by_cases hfe : f = e
    · subst hfe
      exact h.deleteEdges_reaches hl
    · refine (IsWalk.single hl).reaches_deleteEdges fun g hg ↦ ?_
      obtain rfl : g = f := by simpa using hg
      simpa using hfe

/-- **Deleting an edge that lies on a cycle keeps the graph connected** — the blueprint's "it
is a tree: an edge of a cycle could be deleted", which is what makes a minimal connected
spanning subgraph acyclic. -/
theorem Connected.deleteEdges_singleton (hG : G.Connected) (h : G.LiesOnCycle e) :
    (G.deleteEdges {e}).Connected := by
  refine ⟨by simpa using hG.nonempty, fun u hu v hv ↦ ?_⟩
  rw [vertexSet_deleteEdges] at hu hv
  exact (hG.reaches hu hv).choose_spec.reaches_deleteEdges_of_liesOnCycle h

/-! ### Chords

An edge from the source of a path to a vertex the path already visits closes a cycle. This
is the shape in which acyclicity is used: it says a path cannot be extended backwards onto
itself. -/

/-! ### Acyclicity -/

/-! ### Bridges -/

end Graph
end

section
-- module Solutions.Q146_CD.PolyPath
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Polygonal paths

A polygonal path is carried by a list of vertices; its `poly` carrier is the union of the
segments joining consecutive entries. This is the combinatorial representation the whole
of Part I works with — by the blueprint's polygonal overlay convention only finite
polygonal objects are ever overlaid, so vertex lists, not parametrizations, are the
primitive.

## Blueprint

* `poly` — the carrier of a polygonal path.
* `exists_poly_of_isPreconnected` — Lemma 1.1 (polygonal connectedness), less the passage
  to a *simple* arc, which needs the finite-graph machinery and is proved with Lemma 1.2.
-/

open Metric Set

namespace Schoenflies

variable {Ω : Set Plane} {x y z : Plane}

/-! ### Segments -/

theorem isCompact_segment (x y : Plane) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image' ℝ x y]
  exact isCompact_Icc.image (by fun_prop)

/-! ### The carrier of a vertex list -/

/-- The carrier of a polygonal path: the union of the segments joining consecutive vertices.
A single vertex carries itself, so that a path may be constant. -/
def poly : List Plane → Set Plane
  | [] => ∅
  | [v] => {v}
  | u :: v :: rest => segment ℝ u v ∪ poly (v :: rest)

@[simp] theorem poly_nil : poly [] = ∅ := rfl

@[simp] theorem poly_singleton (v : Plane) : poly [v] = {v} := rfl

@[simp] theorem poly_cons_cons (u v : Plane) (rest : List Plane) :
    poly (u :: v :: rest) = segment ℝ u v ∪ poly (v :: rest) := rfl

/-- Every vertex lies on the carrier. -/
theorem mem_poly_of_mem : ∀ {vs : List Plane} {v : Plane}, v ∈ vs → v ∈ poly vs
  | [], _, h => absurd h (by simp)
  | [_], _, h => by simpa using h
  | u :: w :: rest, v, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr (mem_poly_of_mem h)

/-! ### Polygonal connectedness -/

/-- Concatenating two vertex lists that agree at the join concatenates their carriers. The
hypothesis is what makes this true: without it `poly [a] ∪ poly [b] = {a, b}` misses the segment
that `poly [a, b]` carries. -/
theorem poly_append : ∀ {vs : List Plane} (h : vs ≠ []) (w : Plane) (rest : List Plane),
    vs.getLast h = w → poly (vs ++ w :: rest) = poly vs ∪ poly (w :: rest)
  | [], h, _, _, _ => absurd rfl h
  | [v], _, w, rest, hvw => by
    simp only [List.getLast_singleton] at hvw
    subst hvw
    simp [segment_same]
  | u :: v :: tl, _, w, rest, hvw => by
    have h' : (v :: tl).getLast (List.cons_ne_nil v tl) = w := by
      rw [← List.getLast_cons (a := u) (List.cons_ne_nil v tl)]; exact hvw
    simp only [List.cons_append, poly_cons_cons]
    rw [← List.cons_append, poly_append (List.cons_ne_nil v tl) w rest h']
    exact (union_assoc _ _ _).symm

end Schoenflies
end

section
-- module Solutions.Q146_CD.Polygonal
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Polygonal sets, and segments as arcs

`IsPolygonal` is the blueprint's set-level predicate: a finite union of line segments, which
here is exactly the carrier of some vertex list.

The theorem the plane-graph layer needs from this module is `isArcBetween_segment`: a
*nondegenerate* segment is an arc between its endpoints. It is what makes the drawing
condition free for a polygonal plane graph — an edge's arc obligation is discharged by the
segment itself, and the distinctness of its ends is already part of well-formedness.

## Blueprint

* `IsPolygonal` — §1, "an arc or curve is polygonal if it is a finite union of line segments".
* `isArcBetween_segment` — a nondegenerate segment is an arc between its endpoints.
-/

open Metric Set

namespace Schoenflies

/-- A set is polygonal when it is the carrier of a finite vertex list, that is, a finite union
of line segments. -/
def IsPolygonal (A : Set Plane) : Prop := ∃ vs : List Plane, A = poly vs

@[simp] theorem poly_pair (a b : Plane) : poly [a, b] = segment ℝ a b := by
  rw [poly_cons_cons, poly_singleton]
  exact union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ a b))

/-- `lineMap a b` is injective on the unit interval exactly when the segment is
nondegenerate: two parameters differ by a multiple of `b - a`. Exposed separately because the
plane-graph drawing condition asks for the parametrization, not just its image. -/
theorem injOn_lineMap {a b : Plane} (hab : a ≠ b) :
    Set.InjOn (AffineMap.lineMap a b : ℝ → Plane) I := by
  intro s _ t _ hst
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have key : (s - t) • (b - a) = 0 := by
    simp only [AffineMap.lineMap_apply_module] at hst
    linear_combination (norm := module) hst
  rcases smul_eq_zero.1 key with h | h
  · linarith
  · exact absurd h hba

/-- A nondegenerate segment is an arc between its endpoints, parametrized by
`AffineMap.lineMap a b`. -/
theorem isArcBetween_segment {a b : Plane} (hab : a ≠ b) :
    IsArcBetween (segment ℝ a b) a b := by
  refine ⟨AffineMap.lineMap a b, AffineMap.lineMap_continuous.continuousOn, ?_, ?_, ?_, ?_⟩
  · exact injOn_lineMap hab
  · rw [segment_eq_image_lineMap]
  · simp
  · simp

/-- **A polygonal set is carried by a vertex list running from any of its points to any other.**
The list is written with its two ends displayed, so no `List.head`/`List.getLast` obligations
appear. -/
theorem exists_poly_anchored : ∀ (vs : List Plane), vs ≠ [] → ∀ z w : Plane,
    z ∈ poly vs → w ∈ poly vs → ∃ mid : List Plane, poly (z :: (mid ++ [w])) = poly vs := by
  intro vs
  induction vs with
  | nil => exact fun h => absurd rfl h
  | cons u tl ih =>
    rcases tl with _ | ⟨v, rest⟩
    · -- A one-point carrier: both ends are that point.
      intro _ z w hz hw
      rw [poly_singleton, Set.mem_singleton_iff] at hz hw
      subst hz; subst hw
      exact ⟨[], by simp [segment_same]⟩
    · intro _ z w hz hw
      have hne : (v :: rest) ≠ [] := List.cons_ne_nil v rest
      have hv : v ∈ poly (v :: rest) := mem_poly_of_mem (List.mem_cons_self ..)
      rw [poly_cons_cons] at hz hw
      -- `segment z u ⊆ segment u v` for `z` on the first edge, and likewise for `w`.
      have hsub : ∀ p ∈ segment ℝ u v, segment ℝ p u ⊆ segment ℝ u v := fun p hp =>
        (convex_segment u v).segment_subset hp (left_mem_segment ℝ u v)
      have hsub' : ∀ p ∈ segment ℝ u v, segment ℝ u p ⊆ segment ℝ u v := fun p hp =>
        (convex_segment u v).segment_subset (left_mem_segment ℝ u v) hp
      rcases hz with hz | hz
      · rcases hw with hw | hw
        · -- Both ends on the first edge: run out along the rest of the list and back.
          obtain ⟨Z, hZ⟩ := ih hne v v hv hv
          refine ⟨u :: v :: (Z ++ [v, v, u]), ?_⟩
          have hlast : (z :: u :: (v :: (Z ++ [v]))).getLast (by simp) = v := by
            simp
          have hsplit : z :: ((u :: v :: (Z ++ [v, v, u])) ++ [w])
              = (z :: u :: (v :: (Z ++ [v]))) ++ (v :: u :: [w]) := by
            simp
          have h1 : poly (z :: u :: (v :: (Z ++ [v])))
              = segment ℝ z u ∪ (segment ℝ u v ∪ poly (v :: rest)) := by
            rw [poly_cons_cons, poly_cons_cons, hZ]
          have h2 : poly (v :: u :: [w]) = segment ℝ u v ∪ segment ℝ u w := by
            rw [poly_cons_cons, poly_pair, segment_symm ℝ v u]
          have hd1 : segment ℝ z u ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            (hsub z hz).trans Set.subset_union_left
          have hd2 : segment ℝ u v ∪ segment ℝ u w ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            Set.union_subset Set.subset_union_left ((hsub' w hw).trans Set.subset_union_left)
          rw [hsplit, poly_append (by simp) v (u :: [w]) hlast, h1, h2, poly_cons_cons,
            Set.union_eq_self_of_subset_left hd1, Set.union_eq_self_of_subset_right hd2]
        · -- The far end is on the rest: append its list to the first edge.
          obtain ⟨Y, hY⟩ := ih hne v w hv hw
          refine ⟨u :: v :: Y, ?_⟩
          have hsplit : z :: ((u :: v :: Y) ++ [w]) = z :: u :: (v :: (Y ++ [w])) := by simp
          have hd1 : segment ℝ z u ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            (hsub z hz).trans Set.subset_union_left
          rw [hsplit, poly_cons_cons, poly_cons_cons, hY, poly_cons_cons,
            Set.union_eq_self_of_subset_left hd1]
      · rcases hw with hw | hw
        · -- The near end is on the rest: run to `v`, then out along the first edge.
          obtain ⟨X, hX⟩ := ih hne z v hz hv
          refine ⟨X ++ [v, v, u], ?_⟩
          have hlast : (z :: (X ++ [v])).getLast (by simp) = v := by simp
          have hsplit : z :: ((X ++ [v, v, u]) ++ [w]) = (z :: (X ++ [v])) ++ (v :: u :: [w]) := by
            simp
          have h2 : poly (v :: u :: [w]) = segment ℝ u v ∪ segment ℝ u w := by
            rw [poly_cons_cons, poly_pair, segment_symm ℝ v u]
          rw [hsplit, poly_append (by simp) v (u :: [w]) hlast, hX, h2, poly_cons_cons,
            Set.union_eq_self_of_subset_right (hsub' w hw), Set.union_comm]
        · -- Both ends on the rest: run from one to `v`, out and back along the first edge, on.
          obtain ⟨X, hX⟩ := ih hne z v hz hv
          obtain ⟨Y, hY⟩ := ih hne v w hv hw
          refine ⟨X ++ [v, v, u] ++ (v :: Y), ?_⟩
          have hlast : (z :: (X ++ [v])).getLast (by simp) = v := by simp
          have hsplit : z :: ((X ++ [v, v, u] ++ (v :: Y)) ++ [w])
              = (z :: (X ++ [v])) ++ (v :: u :: (v :: (Y ++ [w]))) := by simp
          have h2 : poly (v :: u :: (v :: (Y ++ [w])))
              = segment ℝ u v ∪ (segment ℝ u v ∪ poly (v :: rest)) := by
            rw [poly_cons_cons, poly_cons_cons, hY, segment_symm ℝ v u]
          have hd1 : segment ℝ u v ⊆ segment ℝ u v ∪ poly (v :: rest) := Set.subset_union_left
          have hd2 : poly (v :: rest) ⊆ segment ℝ u v ∪ poly (v :: rest) := Set.subset_union_right
          rw [hsplit, poly_append (by simp) v (u :: (v :: (Y ++ [w]))) hlast, hX, h2,
            poly_cons_cons, Set.union_eq_self_of_subset_left hd1,
            Set.union_eq_self_of_subset_left hd2]

/-- **Two polygonal sets that meet have a polygonal union.** Anchor both lists at a common
point and concatenate. -/
theorem IsPolygonal.union {A B : Set Plane} (hA : IsPolygonal A) (hB : IsPolygonal B)
    (hmeet : (A ∩ B).Nonempty) : IsPolygonal (A ∪ B) := by
  obtain ⟨vs, rfl⟩ := hA
  obtain ⟨ws, rfl⟩ := hB
  obtain ⟨z, hzA, hzB⟩ := hmeet
  have hvs : vs ≠ [] := by rintro rfl; exact hzA
  have hws : ws ≠ [] := by rintro rfl; exact hzB
  obtain ⟨X, hX⟩ := exists_poly_anchored vs hvs z z hzA hzA
  obtain ⟨Y, hY⟩ := exists_poly_anchored ws hws z z hzB hzB
  refine ⟨(z :: (X ++ [z])) ++ (z :: (Y ++ [z])), ?_⟩
  have hlast : (z :: (X ++ [z])).getLast (by simp) = z := by simp
  rw [poly_append (by simp) z (Y ++ [z]) hlast, hX, hY]

end Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_CycleJordan
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The realisation of a cycle is a Jordan curve

A cycle of a plane graph arrives as `Schoenflies/Graph/Cycle.lean` presents it: an edge, and a
path between that edge's two ends which does not use it. Its realisation is the set of points
the arcs of those edges occupy, and the claim is that this set is a Jordan curve.

## The argument is set-level; no parametrisation of a walk is built

The obvious approach — a `walkArc` definition folding `Schoenflies.concatenate` along the edge
list — is the wrong shape twice over. The empty-list base case is a *constant* map, which is
not an arc, so the fold cannot be shown injective at the last step; and threading a
parametrisation through the induction buys nothing, since every consumer wants the point set.

Instead **the existence of the arc is what the induction carries**, in
`Schoenflies.IsArcBetween`. The arcs are chosen inside the induction and the concatenation of
them is chosen by the gluing theorem; no parametrisation is ever named.

## Where the geometry enters

Exactly once, in `Graph.IsDrawing.first_edge_meets_rest`: a common point of the first edge's
arc and the rest of the path is a vertex incident with both edges
(`Graph.IsDrawing.arcs_meet_at_vertex`), hence one of the two ends of the first edge, and the
path's own freshness clause — the vertex a step departs from is not one the rest visits —
forbids it being the source. Taking the same edge again is refused by the *same* clause, so a
separate "the edges of a path are distinct" lemma is not needed.

## Loops

Nothing here hypothesises looplessness, and nothing needs to: `Graph.IsDrawing.ne_of_isLink`
derives it. An edge with equal ends would be drawn by an arc whose parametrisation takes the
same value at `0` and at `1`, which its injectivity forbids. That is what rules out the
degenerate cycle `Graph.liesOnCycle_of_isLoopAt` — a loop with an empty detour — whose
realisation is a single arc and not a Jordan curve.

## Blueprint

* `Graph.edgesCover` — what a *list* of edges occupies. `Graph.pointSet` is the vertices
  together with this, taken over all the edges of the graph.
* `Graph.IsDrawing.path_isArcBetween` — the realisation of a path is an arc between its two
  ends.
* `Graph.IsDrawing.cycle_isJordanCurve` — §"Plane graphs and the utility graph": "in a plane
  graph the realization of a cycle is a Jordan curve: its edges are simple arcs with pairwise
  disjoint interiors, and consecutive edges meet exactly at their shared vertices, so the edge
  arcs concatenate injectively into a simple closed curve".
* `Graph.IsDrawing.cycle_inter` — the meeting condition in full: the detour and the edge meet
  in exactly the edge's two ends. `Schoenflies.IsJordanCurve.of_two_arcs` consumes only one
  inclusion of it, but the equality is what the blueprint asserts.
-/

open Set Schoenflies unitInterval
open scoped _root_.Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z : Plane} {W D : List β}

/-! ### What a list of edges occupies -/

/-- The point set of a list of edges: the union of their edge arcs. A walk is a list of edges,
so this is what a walk of a plane graph draws. -/
def edgesCover (drawing : β → ℝ → Plane) (W : List β) : Set Plane :=
  ⋃ e ∈ W, edgeArc drawing e

theorem mem_edgesCover_iff :
    z ∈ edgesCover drawing W ↔ ∃ e ∈ W, z ∈ edgeArc drawing e := by
  simp [edgesCover]

theorem mem_edgesCover (he : e ∈ W) (hz : z ∈ edgeArc drawing e) : z ∈ edgesCover drawing W :=
  mem_edgesCover_iff.2 ⟨e, he, hz⟩

@[simp]
theorem edgesCover_nil : edgesCover drawing ([] : List β) = ∅ := by
  simp [edgesCover]

@[simp]
theorem edgesCover_cons :
    edgesCover drawing (e :: W) = edgeArc drawing e ∪ edgesCover drawing W := by
  ext z
  simp [edgesCover]

/-! ### A plane graph has no loops

This is not a hypothesis anywhere in this file; it is a consequence of the drawing condition,
and it is what makes the degenerate cycle — a loop, with the empty path back — impossible. -/

/-- **An edge of a plane graph has two distinct ends.** An edge with equal ends would be drawn
by an arc whose parametrisation returns to its start, which its injectivity forbids. -/
theorem IsDrawing.ne_of_isLink (h : IsDrawing G drawing) (hl : G.IsLink e u v) : u ≠ v := by
  rintro rfl
  obtain ⟨g, -, hinj, -, hg0, hg1⟩ := h.edge_isArcBetween hl
  have : (0 : ℝ) = 1 := hinj zero_mem_I one_mem_I (hg0.trans hg1.symm)
  norm_num at this

/-! ### The realisation of a path

The induction carries the *existence* of an arc, not a parametrisation. Its one geometric
step is `Graph.IsDrawing.first_edge_meets_rest`. -/

/-- **The first edge's arc meets the rest of the path only at the waypoint.** Two cases, and
neither is geometric beyond the workhorse `Graph.IsDrawing.arcs_meet_at_vertex`: if the rest
takes the same edge again, the source is one of its ends; if it takes a different one, a
common point is a vertex incident with both, so it is the source or the waypoint. Either way a
point that was the source would put the source among the vertices the rest visits, which is
what the path's freshness clause forbids. -/
theorem IsDrawing.first_edge_meets_rest (h : IsDrawing G drawing) (hl : G.IsLink e u w)
    (hW : ∀ f ∈ W, f ∈ E(G)) (hfresh : u ∉ G.walkVertices w W)
    (hze : z ∈ edgeArc drawing e) (hzW : z ∈ edgesCover drawing W) : z = w := by
  obtain ⟨f, hf, hzf⟩ := mem_edgesCover_iff.1 hzW
  -- Taking the same edge again would put the source among the vertices the rest visits.
  have hef : e ≠ f := by
    rintro rfl
    exact hfresh (mem_walkVertices_of_mem_covered ⟨e, hf, hl.inc_left⟩)
  obtain ⟨-, hinc, hincf⟩ := h.edge_inter hl.edge_mem (hW f hf) hef hze hzf
  rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
  · exact absurd (mem_walkVertices_of_mem_covered ⟨f, hf, hincf⟩) hfresh
  · rfl

/-- **The realisation of a path is an arc between its two ends.** The path must go somewhere:
the empty path draws the empty set, which is not an arc.

The induction is on the path, at the source end, and what it carries is the existence of the
arc. At each step the first edge's arc and the rest's arc meet only at the waypoint
(`Graph.IsDrawing.first_edge_meets_rest`), so `Schoenflies.IsArcBetween.concatenate` glues
them. -/
theorem IsDrawing.path_isArcBetween (h : IsDrawing G drawing) (hP : G.IsPath u W v)
    (hne : W ≠ []) : IsArcBetween (edgesCover drawing W) u v := by
  induction hP with
  | nil => exact absurd rfl hne
  | @cons u w v e W hl hP hfresh ih =>
    rcases eq_or_ne W [] with rfl | hW
    · -- A single edge: the rest contributes nothing, and the path arrives where the edge does.
      obtain rfl : w = v := hP.isWalk.eq_of_nil
      simpa using h.edge_isArcBetween hl
    · refine edgesCover_cons ▸ (h.edge_isArcBetween hl).concatenate (ih hW) ?_
      exact fun z hze hzW ↦
        h.first_edge_meets_rest hl (fun f hf ↦ hP.edge_mem hf) hfresh hze hzW

/-! ### The realisation of a cycle -/

/-- The detour of a cycle is a path with at least one edge — an empty detour would return to
where it set out, and the edge it is a detour for has two distinct ends — so it is drawn by an
arc between those ends. -/
theorem IsDrawing.detour_isArcBetween (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D) :
    IsArcBetween (edgesCover drawing D) u v := by
  refine h.path_isArcBetween hc.isPath fun hD ↦ ?_
  exact h.ne_of_isLink hc.isLink (hD ▸ hc.isPath.isWalk).eq_of_nil

/-- **The detour of a cycle meets the edge only at the edge's two ends.** A common point lies
on the edge and on some edge of the detour, which the detour does not contain, so it is a
vertex incident with the edge — and an edge has only its two ends. -/
theorem IsDrawing.detour_meets_edge (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D)
    (hzD : z ∈ edgesCover drawing D) (hze : z ∈ edgeArc drawing e) : z = u ∨ z = v := by
  obtain ⟨f, hf, hzf⟩ := mem_edgesCover_iff.1 hzD
  have hef : e ≠ f := fun hEq ↦ hc.notMem (hEq ▸ hf)
  obtain ⟨-, hinc, -⟩ :=
    h.edge_inter hc.isLink.edge_mem (hc.isPath.edge_mem hf) hef hze hzf
  exact hinc.eq_or_eq_of_isLink hc.isLink

/-- **The realisation of a cycle is a Jordan curve.** The detour is drawn by an arc from one
end of the edge to the other, the edge is drawn by an arc back, and the two meet only at those
two ends, so `Schoenflies.IsJordanCurve.of_two_arcs` closes the loop. -/
theorem IsDrawing.cycle_isJordanCurve (h : IsDrawing G drawing)
    (hc : G.IsCycleThrough e u v D) : IsJordanCurve (edgesCover drawing (e :: D)) := by
  have hJ : IsJordanCurve (edgesCover drawing D ∪ edgeArc drawing e) :=
    IsJordanCurve.of_two_arcs (h.detour_isArcBetween hc)
      (h.edge_isArcBetween hc.isLink).reverse fun z hzD hze ↦ h.detour_meets_edge hc hzD hze
  rw [edgesCover_cons, Set.union_comm]
  exact hJ

/-- The source of a nonempty walk lies on what the walk draws. -/
theorem IsWalk.left_mem_edgesCover {u v : Plane} {W : List β} (hW : G.IsWalk u W v)
    (hd : IsDrawing G drawing) (hne : W ≠ []) : u ∈ edgesCover drawing W := by
  cases hW with
  | nil => exact absurd rfl hne
  | cons hl _ => exact mem_edgesCover (List.mem_cons_self ..) (hd.edge_isArcBetween hl).left_mem

/-- **A walk of a polygonal plane graph draws a polygonal set.** Consecutive edges share the
vertex between them, so the union stays a single vertex list. -/
theorem IsDrawing.isPolygonal_edgesCover (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), Schoenflies.IsPolygonal (edgeArc drawing f)) :
    ∀ {u v : Plane} {W : List β}, G.IsWalk u W v → W ≠ [] →
      Schoenflies.IsPolygonal (edgesCover drawing W) := by
  intro u v W hW
  induction hW with
  | nil => exact fun h => absurd rfl h
  | @cons u w v f W hl hW ih =>
    intro _
    rcases eq_or_ne W [] with rfl | hWne
    · simpa using hpoly f hl.edge_mem
    · rw [edgesCover_cons]
      exact ((hpoly f hl.edge_mem).union (ih hWne)
        ⟨w, (hd.edge_isArcBetween hl).right_mem, hW.left_mem_edgesCover hd hWne⟩)

end Graph
end

section
-- module Solutions.Q146_CD.Graph_PathGraph
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A path presented as a graph

`Schoenflies/Graph/Walk.lean` says what it means for an edge list to *run* through a graph.
This file says what it means for a graph to *be* a path, and — the point of the file —
constructs one.

## Why the object exists

An ear is a path that gets glued onto a graph, so it has to be a graph itself, not a walk
inside one. `Graph.IsPathGraph P u W v` says that `P`'s own edges, listed in the order `W`,
form a path from `u` to `v` and that `P`'s vertices are exactly the ones that path visits.
The list `W` is an index of the predicate rather than an existential: its **order** is part
of the claim, and it is what lets every later argument cut the path at a vertex without first
having to sort anything.

Mathlib's `Graph α β` carries a `Set β` of edges, not a list, so the correspondence between
the two is a clause of the definition (`Graph.IsPathGraph.edgeSet_eq`) rather than something
a list-based graph would give for free.

## Constructing one

`Graph.pathGraphOf G u W` is the subgraph of `G` spanned by the walk `W` from `u`: the
vertices the walk visits, and its own edges. Everything else in the file is a hypothesis of
the form `IsPathGraph`; this is where one is produced, and it is what an ear decomposition
runs on — a path found inside a big graph has to be turned into a graph before it can be
unioned back in.

## What the ear argument actually asks

Always the same thing: **whatever vertex is deleted, every remaining vertex of the path still
reaches one of the two ends** (`Graph.IsPathGraph.reaches_an_end`). The proof is uniform in
the deleted vertex `c`, with no case split on whether `c` is an end, an interior vertex or
off the path at all:

* if `c` is on the path, cut there (`Graph.IsPath.split`); each remaining vertex lies on one
  of the two halves, and a half runs to its far end without meeting the cut, because the
  split's last clause says the far half never returns to the source;
* if `c` is not on the path, cut at the vertex itself and reverse the near half.

Both branches go through the same two lemmas, `Graph.IsPath.reaches_target_of_ne_source` and
its mirror, so the interior case has no separate content.

## Blueprint

* `Graph.IsPathGraph` — the object called "a path `P`" in Lemma
  `lem:subdivision-ear-preserve` (b) ("if `P` is a path whose distinct endpoints lie in `G`
  … then `G ∪ P` is 2-connected") and "an ear" in Lemma `lem:relative-ear`.
* `Graph.IsPathGraph.reaches_an_end` — the blueprint's "every component of `P - x` is
  attached to `G - x` at one of the two endpoints of `P`; when `x` is an endpoint, the
  remainder of `P` is attached at the other endpoint", both sentences at once.
* `Graph.pathGraphOf` — the "shortest path through `L` between two such neighbors is an ear"
  of `lem:relative-ear`: a path of the ambient graph, presented as a graph.

Nothing here mentions 2-connectivity; the union of a 2-connected graph with an ear is a
later module.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`, so that `h.reaches_an_end` and
`G.pathGraphOf u W` resolve by dot notation.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H P : Graph α β} {u v w x y c : α} {e : β} {W W₁ W₂ : List β}

/-! ### Walks and vertex deletion

Mathlib's `Graph.deleteVerts` takes a set; a single deleted vertex is `{c}`. -/

/-! ### Reaching an end of a path after a deletion -/

/-! ### A graph that is a path -/

/-! ### Constructing a path graph -/

/-- **The subgraph of `G` spanned by the walk `W` from `u`**: the vertices that walk visits,
carrying exactly the walk's own edges.

This is the construction an ear decomposition needs — a path found inside a big graph, turned
into a graph of its own so that it can be unioned back in. It is built from Mathlib's
`Graph.restrict` and `Graph.induce`, so that `Graph.pathGraphOf_le` is almost free. -/
def pathGraphOf (G : Graph α β) (u : α) (W : List β) : Graph α β :=
  (G.restrict {e | e ∈ W}).induce (G.walkVertices u W)

@[simp]
theorem pathGraphOf_vertexSet : V(G.pathGraphOf u W) = G.walkVertices u W := rfl

@[simp]
theorem pathGraphOf_isLink :
    (G.pathGraphOf u W).IsLink e x y ↔
      e ∈ W ∧ G.IsLink e x y ∧ x ∈ G.walkVertices u W ∧ y ∈ G.walkVertices u W := by
  simp only [pathGraphOf, induce_isLink, restrict_isLink, mem_setOf_eq]
  tauto

/-! ### Finiteness

A walk visits finitely many vertices and takes finitely many edges, so the graph it spans is
finite with no hypothesis on the ambient graph. -/

end Graph
end

section
-- module Solutions.Q146_CD.Graph_RelativeEar
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The relative ear decomposition

`lem:relative-ear`: *if `H` is a 2-connected subgraph of a finite 2-connected graph `G`, then
`G` is obtained from `H` by repeatedly adding paths whose distinct endpoints are already
present and whose internal vertices are new.*

Two things are delivered, and they are different in kind.

* `Graph.IsTwoConnected.relative_ear_exists` — the **relative** ear: the blueprint's own
  construction, through a component of `G - V(K)`, which is what makes the internal vertices
  new. `Graph.IsTwoConnected.ear_exists` in `Schoenflies/Graph/Ear.lean` finds *an* ear by a
  crossing walk, but says nothing about where the ear's interior lies — its path may run back
  and forth through the subgraph. That is enough to make the subgraph grow; it is **not**
  enough for the consumers, which need "whose internal vertices are new" verbatim (the ear's
  interior must be disjoint from the current skeleton, so that it lies in one current face).
* `Graph.IsTwoConnected.ear_decomposition` — the **iterated** form, as an induction principle.
  `Graph.IsTwoConnected.grows_by_ear` is deliberately one step; the finiteness induction the
  blueprint hides behind "finiteness terminates the process" is done here.

## Why the relative form is a different theorem

The blueprint's proof does not walk out of the subgraph and hope. It looks at a component `L`
of `G - V(H₀)`: if `L` has a vertex it has two distinct neighbours in `H₀`, since otherwise
its unique neighbour would be a cut vertex of `G`, and a shortest path through `L` between two
such neighbours is an ear. That path meets `V(H₀)` only at its two ends **by construction**,
because its interior was built inside `G - V(H₀)`.

All of that is already proved: `Graph.IsTwoConnected.exists_path_through_component` in
`Schoenflies/Graph/Component.lean` packages the component argument and the path through it.
What is left here is to feed it `S = V(K)` — the two distinct vertices of `S` it asks for are
two of the three that a 2-connected `K` has — and to read its "every edge has an end outside
`S`" as "no edge of the ear is an edge of `K`".

The degenerate branch is the blueprint's second sentence: if every vertex of `G` is already
present, a missing edge is an ear of length one, and it has no internal vertex at all. As in
`Graph.IsTwoConnected.ear_exists`, that branch — and only that branch — needs `G` to be
loopless: a loop added to a 2-connected graph leaves it 2-connected, and no ear between
*distinct* endpoints can supply it.

## The termination measure

Edges, not vertices: `(E(G) \ E(B)).ncard`, which is finite because `G` is. Every ear
contributes at least one edge that `B` did not have — in the relative form *every* edge of the
ear is new, since each has an end outside `V(B)` — so the measure strictly drops, and the
process stops exactly when `B = G`. The stopping step is `Graph.eq_of_le_of_subset_subset`: a
subgraph with all the vertices and all the edges is the graph.

Note that the measure never needs to see a vertex. It is tempting to stop when `E(B) = E(G)`
and argue that a connected `G` has no isolated vertex; that is true but needs the degree
theory, and is unnecessary: if `V(B) ≠ V(G)` the ear that the first branch produces has an
edge outside `E(B)`, so the measure was not zero after all.

## One import that looks wrong

`Schoenflies/Graph/Tree.lean` is imported for a single two-line fact, `Graph.IsPath.ne_nil` —
a path between distinct vertices has an edge — which happens to live there. Nothing else in
this file has anything to do with trees. The honest fix is for the integrator to hoist
`Graph.IsPath.ne_nil` into `Schoenflies/Graph/Walk.lean`, where it belongs, and drop the
import; it is not restated here.

## What the induction principle gives a consumer

`motive G`, from `motive K` and one step. The step is handed the ear in full — the path `D` of
`G`, its distinct ends in `V(B)`, and the freshness of its interior — together with
`B.IsTwoConnected`, `K ≤ B` and `B ≤ G`, and must produce `motive (B.union (G.pathGraphOf a D))`.
That is exactly the shape of the induction in `lem:face-cycles` ("suppose it holds for the
current graph and add the next geometric ear") and of the finite transfer of Part II.

## Blueprint

* `Graph.IsTwoConnected.relative_ear_exists` — `lem:relative-ear`, the ear itself: "a shortest
  path through `L` between two such neighbours is an ear", plus "if all vertices are already
  present, add a missing edge as an ear of length one".
* `Graph.IsTwoConnected.relative_grows_by_ear` — the same, glued on: one step of "`G` is
  obtained from `H` by repeatedly adding paths".
* `Graph.IsTwoConnected.ear_decomposition` — `lem:relative-ear` in full, including
  "finiteness terminates the process", as an induction principle.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G K B : Graph α β} {a b x y : α} {e f : β} {D : List β}

/-! ### Two facts about a subgraph inclusion

Both are general and neither is in `Schoenflies/Graph/Walk.lean`; the integrator may want to
hoist them. -/

/-! ### The relative ear -/

/-! ### Reading the enlarged graph

Two unfoldings a consumer of the induction principle below needs immediately, since the step's
conclusion is about `B.union (G.pathGraphOf a D)`. Both are immediate from the simp lemmas of
`Schoenflies/Graph/TwoConnected.lean` and `Schoenflies/Graph/PathGraph.lean`; they are here
only so that no consumer has to rediscover which two to combine. -/

@[simp]
theorem vertexSet_union_pathGraphOf (B G : Graph α β) (a : α) (D : List β) :
    V(B.union (G.pathGraphOf a D)) = V(B) ∪ G.walkVertices a D := rfl

/-! ### Iterating: the decomposition itself -/

end Graph
end

section
-- module Solutions.Q146_CD.Subarc
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subarcs, open arcs, and the subarc basis

A subarc is the arc restricted to a subinterval of the parameter interval — but an arc is
carried by a map *on* `[0, 1]`, so the restriction has to be reparametrised back onto it.
That reparametrisation is `reparam a b : t ↦ a + t * (b - a)`: pure arithmetic, with no
inverse to construct and no choice to make. With it a subarc is a composition, and the two
things an arc must be — continuous and injective — are the two things a composition inherits.

Injectivity is required only on `uIcc a b`, the parameter interval actually traversed, not on
all of `[0, 1]`. That is what lets the two arcs of a Jordan curve be cut out of a loop, whose
parametrisation is injective on `[0, 1)` only.

The substance of the file is the last two sections. A parametrisation is an **open map onto
its arc**: the image of a relatively open piece of the parameter interval is relatively open
in the arc. This is where the continuity of the inverse earns its keep, and it is proved
without ever constructing that inverse — a continuous injection on a compact set is a closed
map onto its image, and a closed injective map is open onto its image, by complements.
Together with `basic_piece_inside_ball`, which puts such a piece inside any prescribed ball,
these images are a basis of the arc's subspace topology.

Relative openness is stated in the ambient form `∃ V, IsOpen V ∧ W = V ∩ A` rather than
through the subtype `↥A`, since every consumer here works with subsets of the plane.

## Blueprint

The blueprint uses subarcs throughout §1 without a numbered statement of their own; they are
the tool behind, among others, the model-curve parametrization (`lem:jordan-circle`), where
"the relatively open subarcs of `C`" are exactly the images produced by `image_isRelOpen`, and
the density arguments of `lem:accessible-dense`, which need `basic_piece_inside_ball`.

* `subarc`, `isArcBetween_subarc` — a piece of an arc is again an arc.
* `IsArc.exists_isArcBetween_subset` — the set-level reading: two points of an arc bound a
  subarc of it.
* `openArc` — the blueprint's `P°`, an arc without its two endpoints.
* `image_isRelOpen` — a parametrisation is an open map onto its arc; `openArc_isRelOpen` and
  `openArc_subarc_isRelOpen` are the "relatively open subarcs" of `lem:jordan-circle`.
* `basic_piece_inside_ball` — the subarc basis.
-/

open Set unitInterval

namespace Schoenflies

/-! ### Reparametrising `[0, 1]` onto a subinterval -/

/-- The affine map carrying `[0, 1]` onto the parameter interval between `a` and `b`,
running from `a` to `b`. -/
def reparam (a b : ℝ) : ℝ → ℝ := fun t => a + t * (b - a)

variable {a b : ℝ}

@[simp] theorem reparam_zero : reparam a b 0 = a := by simp [reparam]

@[simp] theorem reparam_one : reparam a b 1 = b := by simp [reparam]

/-! ### Subarcs -/

/-- The subarc of `f` between the parameters `a` and `b`: the arc traversed from `f a` to
`f b`, reparametrised so that it is again a map on `[0, 1]`. -/
def subarc (f : ℝ → Plane) (a b : ℝ) : ℝ → Plane := fun t => f (reparam a b t)

variable {f : ℝ → Plane}

@[simp] theorem subarc_zero : subarc f a b 0 = f a := by simp [subarc]

@[simp] theorem subarc_one : subarc f a b 1 = f b := by simp [subarc]

/-! ### The arc without its endpoints -/

/-- The open arc — the blueprint's `P°`: an arc with its two endpoints removed.

Taken on the parameter side, as the image of the open unit interval, because that is the form
the subarc basis argument needs: an open subarc is the image of an open subinterval.
Injectivity then says it is also the arc minus the two endpoint *values*, which is how the
blueprint reads it (`openArc_eq_diff`). -/
def openArc (f : ℝ → Plane) : Set Plane := f '' Ioo 0 1

theorem Ioo_subset_I : Ioo (0 : ℝ) 1 ⊆ I := Ioo_subset_Icc_self

/-- On an arc the two readings of "without its endpoints" agree: dropping the endpoints of the
parameter interval drops exactly the two endpoint values, since injectivity means no other
parameter shares them. -/
theorem openArc_eq_diff (hi : InjOn f I) : openArc f = f '' I \ {f 0, f 1} := by
  have hIoo : Ioo (0 : ℝ) 1 = I \ {0, 1} := by
    ext t
    simp only [mem_Ioo, mem_sdiff, mem_Icc, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨⟨h0.le, h1.le⟩, h0.ne', h1.ne⟩
    · rintro ⟨⟨h0, h1⟩, hne0, hne1⟩; exact ⟨h0.lt_of_ne' hne0, h1.lt_of_ne hne1⟩
  have hpair : f '' ({0, 1} : Set ℝ) = {f 0, f 1} := image_pair f 0 1
  rw [openArc, hIoo, hi.image_sdiff_subset (by
        rintro t (rfl | rfl); exacts [zero_mem_I, one_mem_I]), hpair]

/-! ### The interior of an arc, set-level

`openArc` is stated for a parametrisation. Three separate modules needed the same facts stated
for the *set* — `IsArcBetween A p q` gives `A ∖ {p, q}` connected, nonempty, and having both
endpoints in its closure — and each proved them again from scratch, one of them twice under two
names. Two of those copies were literally the same statement in modules that do not import each
other, so the build never noticed: alpha-equivalent `Prop`s are defeq under proof irrelevance,
and Lean's import checker accepts them. They live here now. -/

/-- **The interior of an arc is the image of the open parameter interval.** The bridge from
`IsArcBetween`, which is about the set, to `openArc`, which is about a parametrisation. -/
theorem IsArcBetween.diff_eq_openArc {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    ∃ f : ℝ → Plane, ContinuousOn f I ∧ A \ {p, q} = f '' Ioo 0 1 := by
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := h
  exact ⟨f, hc, by rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi, openArc]⟩

/-- **The interior of an arc is connected.** It is the continuous image of `Ioo 0 1`. -/
theorem IsArcBetween.isPreconnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsPreconnected (A \ {p, q}) := by
  obtain ⟨f, hc, hEq⟩ := h.diff_eq_openArc
  rw [hEq]
  exact isPreconnected_Ioo.image _ (hc.mono Ioo_subset_I)

/-- **An endpoint of an arc is a limit of its interior.** This is what turns "the closure of a
cell meets the curve in one arc only" into a statement about the *endpoints* of a crosscut, and
it is what says an ear's two ends lie on the boundary of the face its interior lies in. -/
theorem IsArcBetween.left_mem_closure_diff {A : Set Plane} {p q : Plane}
    (h : IsArcBetween A p q) : p ∈ closure (A \ {p, q}) := by
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := h
  have hEq : A \ {p, q} = f '' Ioo 0 1 := by
    rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi, openArc]
  -- The endpoint is the limit of the interior as the parameter tends to `0`.
  rw [hEq, ← h0]
  refine ((hc 0 zero_mem_I).mono Ioo_subset_I).mem_closure_image ?_
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  exact zero_mem_I

theorem IsArcBetween.right_mem_closure_diff {A : Set Plane} {p q : Plane}
    (h : IsArcBetween A p q) : q ∈ closure (A \ {p, q}) := by
  rw [Set.pair_comm]
  exact h.reverse.left_mem_closure_diff

/-! ### A parametrisation is an open map onto its arc -/

/-! ### The subarc basis -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.FaceCycles
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun
/-!
# Face cycles: the base cycle, and the faces of a plane graph that grows by ears

`lem:face-cycles` — *every face of a finite 2-connected polygonal plane graph has a cycle as
its boundary and is one of the two complementary regions of that cycle* — is proved by growing
the graph from a cycle by ears (`Graph.IsTwoConnected.ear_decomposition`) and applying
`thm:polygonal-crosscut` at each step. This file supplies everything in that proof that is not
the crosscut application itself. **The lemma is not proved here**; see "What is missing" below,
which says exactly what is in the way.

## The base cycle

The blueprint's first paragraph, in full. *"First choose a cycle of length at least three.
Such a cycle exists: under our convention the graph has at least three vertices, and every
vertex has at least two distinct neighbors. Indeed, if a vertex `v` had only one distinct
neighbor `w`, then deleting `w` would isolate `v` from some third vertex, contrary to
2-connectivity. Now take a maximal simple path. An endpoint has a neighbor on the path other
than its predecessor, and the resulting closed subpath is a cycle of length at least three."*

`Graph.IsTwoConnected.exists_adj_ne` is the two-neighbours sentence; "take a maximal simple
path" is `Graph.exists_longest_path`, already in `Schoenflies/Graph/Tree.lean` and not rebuilt
here; and `Graph.IsTwoConnected.exists_long_cycle` is the conclusion, packaged as
`Graph.IsLongCycle`, a cycle together with a *named* third vertex. Naming the third vertex
rather than counting is what both consumers want: the counting clause of
`Graph.IsTwoConnected`, and — later — the non-degeneracy of the polygon the cycle draws.

`Graph.cycleGraph` is that cycle as a subgraph, and `Graph.IsLongCycle.isTwoConnected` is
*"the cycle `C` is 2-connected, so Lemma `lem:relative-ear` builds the graph from `C`"*. This
is the one place "length at least three" is used: a two-vertex cycle is a `Graph.banana`, and
`Graph.not_isTwoConnected_banana` says it is not 2-connected.

## One step of the induction

Adding an ear removes the ear's own point set from the exterior and changes nothing else:
`Graph.pointSet_union`, `Graph.exterior_union` and `Graph.face_union_eq_of_disjoint` are
*"all other faces are unchanged"*.

`Graph.IsDrawing.exists_face_of_ear` is *"its interior is connected and disjoint from the
current graph, so it lies in one current face `F`"*: the ear's realisation without its two ends
is the interior of an arc, hence connected
(`Schoenflies.IsArcBetween.isConnected_diff`), and it misses the drawing of the current
subgraph altogether (`Graph.IsDrawing.edgesCover_inter_pointSet`).
`Graph.IsDrawing.ends_mem_frontier_face` is the next sentence, *"the ear's two endpoints are
limits of its interior, which lies in `F`, so they lie on `∂F`"* — which is what makes the ear
a crosscut of that face.

`Graph.IsDrawing.mono` — a subgraph of a plane graph is a plane graph, with the same drawing —
is what lets the induction talk about the faces of the current subgraph at all.

## An interface repair

`Graph.IsTwoConnected.ear_decomposition` hands its step the ear's path but **not** the clause
`∀ g ∈ D, g ∉ E(B)`, which `Graph.IsTwoConnected.relative_ear_exists` proves and which
`Graph.IsTwoConnected.relative_grows_by_ear` drops on the way. A geometric consumer needs it:
without it the ear may be drawn right on top of the current subgraph, and
`Graph.IsDrawing.edgesCover_inter_pointSet` is false. `Graph.ear_edges_notMem_or_union_eq`
recovers it in the only form available from the outside — either every edge of the ear is new,
or the ear is a single edge the subgraph already had and the enlarged graph *is* the old graph,
so the step has nothing to prove. The better fix is for the integrator to add the clause to
`relative_grows_by_ear` and to `ear_decomposition`; that would make this lemma unnecessary.

## What is missing

The crosscut application, and therefore `lem:face-cycles` itself. `thm:polygonal-crosscut` is
available as `Schoenflies.IsPolygonalCrosscut` and `Schoenflies.polygonal_crosscut`, whose
hypotheses are stated for `Schoenflies.ClosedPolygon`s: an explicit cyclic vertex list with
`vertex_inj`, `edges_meet` and `corner` (no two consecutive edges collinear). The realisation
of a graph cycle arrives here as a **set** — `Graph.edgesCover drawing (e :: D)` — which
`Graph.IsDrawing.cycle_isJordanCurve` knows to be a Jordan curve and `Graph.polygonal_redrawing`
knows to be polygonal. Turning such a set into a `ClosedPolygon` (enumerate its vertices
cyclically, delete the redundant collinear ones, and derive `vertex_inj` and `edges_meet` from
simplicity) is a construction `main` does not have, and the same construction is needed again
for the two curves `Aᵢ ∪ P` that the crosscut produces. Nothing below pretends to it, and no
statement below is weaker than its blueprint counterpart.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`. The two arc lemmas are stated in
`Schoenflies`, where the rest of the arc theory lives.

## Blueprint

* `Graph.IsTwoConnected.exists_adj_ne` — "every vertex has at least two distinct neighbors".
* `Graph.IsLongCycle`, `Graph.IsTwoConnected.exists_long_cycle` — "the resulting closed subpath
  is a cycle of length at least three".
* `Graph.cycleGraph`, `Graph.IsLongCycle.isTwoConnected` — "the cycle `C` is 2-connected, so
  Lemma `lem:relative-ear` builds the graph from `C`".
* `Graph.ear_edges_notMem_or_union_eq` — the ear's edges are new, or the ear is not an ear.
* `Graph.pointSet_union`, `Graph.exterior_union`, `Graph.face_union_subset`,
  `Graph.face_union_eq_of_disjoint` — "all other faces are unchanged".
* `Graph.IsDrawing.mono` — the current subgraph is itself a plane graph.
* `Schoenflies.IsArcBetween.isConnected_diff`,
  `Schoenflies.IsArcBetween.left_mem_closure_diff`, `…right_mem_closure_diff`,
  `Graph.IsDrawing.edgesCover_inter_pointSet`, `Graph.IsDrawing.exists_face_of_ear`,
  `Graph.IsDrawing.ends_mem_frontier_face` — "its interior is connected and disjoint from the
  current graph, so it lies in one current face `F` … the ear's two endpoints are limits of its
  interior, which lies in `F`, so they lie on `∂F`; the ear is therefore a crosscut of that
  side".
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H K B : Graph α β} {u v w x y z c : α} {e f g : β} {D W : List β}

/-! ## Two distinct neighbours -/

/-! ## The base cycle

"Take a maximal simple path" is `Graph.exists_longest_path`, already in
`Schoenflies/Graph/Tree.lean` — it is what the three-leaf lemma runs on — so nothing here
rebuilds it. -/

/-! ## The cycle as a subgraph, and its 2-connectivity

`Graph.IsTwoConnected.ear_decomposition` starts from a 2-connected subgraph. The subgraph the
blueprint starts from is the base cycle, and this section builds it and proves it 2-connected.
This is the one place where "length at least three" is used: a two-vertex cycle is a
`Graph.banana`, and `Graph.not_isTwoConnected_banana` says it is not 2-connected. -/

/-- The subgraph of `G` drawn by a cycle: the detour followed by the edge, as a closed walk.
Exported as the object rather than hidden behind an existential — the consumer of
`lem:face-cycles` needs the graph itself, to feed it to the ear decomposition. -/
def cycleGraph (G : Graph α β) (u : α) (e : β) (D : List β) : Graph α β :=
  G.pathGraphOf u (D ++ [e])

namespace IsCycleThrough

variable (hc : G.IsCycleThrough e u v D)
include hc

/-- Closing the cycle adds no vertex: both ends of the edge are already on the detour. -/
theorem walkVertices_round : G.walkVertices u (D ++ [e]) = G.walkVertices u D := by
  refine Set.Subset.antisymm (fun y hy ↦ ?_) (walkVertices_mono (List.subset_append_left _ _))
  rcases mem_walkVertices_iff.1 hy with rfl | hcov
  · exact mem_walkVertices_self
  rw [coveredVertices_append] at hcov
  rcases hcov with hcov | ⟨g, hg, hinc⟩
  · exact mem_walkVertices_of_mem_covered hcov
  obtain rfl : g = e := by simpa using hg
  rcases hinc.eq_or_eq_of_isLink hc.isLink with rfl | rfl
  · exact mem_walkVertices_self
  · exact hc.isPath.target_mem_walkVertices

@[simp]
theorem cycleGraph_vertexSet : V(G.cycleGraph u e D) = G.walkVertices u D := by
  rw [cycleGraph, pathGraphOf_vertexSet, hc.walkVertices_round]

end IsCycleThrough

/-! ## An ear that is not new

`Graph.IsTwoConnected.ear_decomposition` hands its step the ear's path but **not** the clause
`∀ g ∈ D, g ∉ E(B)` that `Graph.IsTwoConnected.relative_ear_exists` proves and that
`Graph.IsTwoConnected.relative_grows_by_ear` drops. A *geometric* consumer needs it: the ear's
drawing has to miss the drawing of the current subgraph, and an edge shared with `B` would sit
right on it.

It is recoverable, and this section recovers it. An edge of the ear that `B` already has must
join the ear's two ends; the ear is then that single edge, and the enlarged graph is the old
one, so the step has nothing to prove. The integrator may prefer to add the clause to
`relative_grows_by_ear` and to `ear_decomposition` instead — that is the better fix, and it
makes this section unnecessary. -/

/-! ## The faces of a graph that grows

Adding an ear removes the ear's own point set from the exterior and changes nothing else. That
is the whole of "all other faces are unchanged", and the half of "its interior is connected and
disjoint from the current graph, so it lies in one current face `F`" that is pure topology. -/

section Plane

open Schoenflies

variable {β : Type*} {G B P : Graph Plane β} {drawing : β → ℝ → Plane} {z a b : Plane}
  {S : Set Plane} {D : List β}

/-- What a union of two plane graphs occupies is what the two of them occupy. -/
@[simp]
theorem pointSet_union (B P : Graph Plane β) (drawing : β → ℝ → Plane) :
    pointSet (B.union P) drawing = pointSet B drawing ∪ pointSet P drawing := by
  simp only [pointSet, vertexSet_union, edgeSet_union, Set.biUnion_union]
  ext w
  simp only [Set.mem_union]
  tauto

/-! ### The ear lies in one face

The blueprint's *"its interior is connected and disjoint from the current graph, so it lies in
one current face `F`"*, in full. -/

/- "An arc without its two endpoints is connected" is
`Schoenflies.IsArcBetween.isConnected_diff`, now in `Schoenflies/Subarc.lean`. -/

/-! ### A subgraph of a plane graph is a plane graph

The induction speaks of the faces of the *current* subgraph, so every step needs the current
subgraph to be a plane graph in its own right. Nothing has to be redrawn: the same drawing
serves. General, and not in `Schoenflies/Graph/Drawing.lean`; the integrator may want to hoist
it. -/

/-! ### The ear's ends lie on the boundary of the face its interior lies in -/

/- "An endpoint of an arc is a limit of the arc's interior" is
`Schoenflies.IsArcBetween.left_mem_closure_diff` / `…right_mem_closure_diff`, hoisted into
`Schoenflies/Subarc.lean` alongside `…isConnected_diff`. This module had its own copy, with the
same statement as the one in `Schoenflies/AlternatingCrosscuts.lean`; the two modules do not
import each other, so the build accepted both. -/

set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

end Plane

end Graph
end

section
-- module Solutions.Q146_CD.SegmentCut
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cutting a segment

Mathlib has no lemma splitting a segment at an interior point, and the polygonal subdivision
of Layer 6 is built entirely out of one: cutting loses nothing (`segment_split`) and cutting
is permanent (`openSegment_left_subset`, `openSegment_right_subset` — each half's interior
stays inside the whole's, so nothing later can put a removed point back into an interior).

Everything here is an identity between convex combinations. The `⊇` half of the split is
convexity; the `⊆` half rescales the parameter, and the only case analysis is on whether the
far coefficient vanishes.

## Blueprint

* `segment_split` — cutting at a point of the segment loses nothing; underneath
  `subdivide_covers`.
* `openSegment_left_subset`, `openSegment_right_subset` — a cut is permanent; underneath
  `subdivide_inside`.
-/

open Set

namespace Schoenflies

variable {a b p : Plane}

/-- Cutting a segment at one of its points loses nothing: the two halves cover it. -/
theorem segment_split (hp : p ∈ segment ℝ a b) :
    segment ℝ a b = segment ℝ a p ∪ segment ℝ p b := by
  refine subset_antisymm ?_ (union_subset
    ((convex_segment a b).segment_subset (left_mem_segment ℝ a b) hp)
    ((convex_segment a b).segment_subset hp (right_mem_segment ℝ a b)))
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨u, v, hu, hv, huv, rfl⟩
  rcases le_or_gt v β with hvβ | hvβ
  · -- `x` lies on the near half. Rescale `v` by `β`, unless `β = 0`, when the cut is at `a`.
    left
    rcases eq_or_lt_of_le hβ with rfl | hβpos
    · have hv0 : v = 0 := le_antisymm hvβ hv
      have hu1 : u = 1 := by linarith
      subst hv0; subst hu1
      simp only [zero_smul, add_zero, one_smul]
      exact left_mem_segment ℝ a _
    · refine ⟨1 - v / β, v / β, by
        rw [sub_nonneg]
        exact div_le_one_of_le₀ hvβ hβpos.le, by positivity, by ring, ?_⟩
      have hβne : β ≠ 0 := ne_of_gt hβpos
      have hvβ' : v / β * β = v := div_mul_cancel₀ v hβne
      have hcoef : (1 - v / β) + (v / β) * α = u := by
        have hα' : α = 1 - β := by linarith
        calc (1 - v / β) + (v / β) * α
            = (1 - v / β) + (v / β) * (1 - β) := by rw [hα']
          _ = 1 - v / β * β := by ring
          _ = 1 - v := by rw [hvβ']
          _ = u := by linarith
      rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul, hcoef, hvβ']
  · -- `x` lies on the far half. Rescale `u` by `α`, which is positive because `v > β`.
    right
    have hαpos : 0 < α := by linarith
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have huα : u ≤ α := by linarith
    refine ⟨u / α, 1 - u / α, by positivity, by
      rw [sub_nonneg]
      exact div_le_one_of_le₀ huα hαpos.le, by ring, ?_⟩
    have huα' : u / α * α = u := div_mul_cancel₀ u hαne
    have hcoef : (u / α) * β + (1 - u / α) = v := by
      have hβ' : β = 1 - α := by linarith
      calc (u / α) * β + (1 - u / α)
          = (u / α) * (1 - α) + (1 - u / α) := by rw [hβ']
        _ = 1 - u / α * α := by ring
        _ = 1 - u := by rw [huα']
        _ = v := by linarith
    rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul, hcoef, huα']

end Schoenflies
end

section
-- module Solutions.Q146_CD.SegmentOrder
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Along one segment: the distance from an end as a coordinate

Everything the polygonal overlay has to say about several collinear segments — which piece
lies inside which, where a piece may end, when two pieces have to coincide — is
one-dimensional: it happens along a single straight segment. This module supplies the
coordinate that makes it ordinary arithmetic. Along a nondegenerate `segment ℝ a b` the
distance from `a` determines the point, and it reads betweenness off as a pair of
inequalities, so a claim about four collinear points becomes a claim about four reals.

No new geometry is needed. `dist_left_lineMap` already says the distance from `a` *is* the
parameter of `AffineMap.lineMap a b`, scaled by the segment's length, and `image_segment`
already says that parametrization carries segments of `ℝ` to segments of the plane. What is
added here is the translation, stated once so that the arithmetic does not have to be redone
at every use.

The two results the module exists for come last, and they are what makes cutting at every
meet enough:

* a piece that meets an overlap and keeps the overlap's ends out of its interior lies inside
  the overlap (`segment_inside_of_ends_outside`);
* two pieces whose interiors meet, each keeping the other's ends out of its interior, are the
  same pair of points (`same_ends_of_meeting_interiors`).

Both are stated **inside one ambient segment**. Collinearity is not optional: a piece crossing
the overlap transversally would meet it and avoid both its ends without lying inside it, so
every point named is a point of one ambient `segment ℝ a b`.

Both are also stated with no orientation asked of the caller. The `_oriented` forms they wrap
are near-end-first, which is what the arithmetic wants; the unoriented forms decide the
orientation themselves, and they are what the overlay uses.

## A note on degenerate pieces

Mathlib's `openSegment ℝ u u` is `{u}`, not `∅`. A degenerate piece therefore has a nonempty
interior, and the strict translation `dist_lt_of_mem_openSegment` genuinely needs `u ≠ v`.
The two headline theorems do *not* ask for it: in each of them a degenerate piece is either
excluded by the hypotheses or settled outright, and that case split lives inside the proof.

## Blueprint

* `segment_inside_of_ends_outside`, `same_ends_of_meeting_interiors` — the separation behind
  the deduplication clause of the polygonal overlay (`lem:polygonal-overlay`, "represent every
  duplicate geometric subsegment only once") and of the subdivision in
  `lem:polygonal-connected` ("delete duplicate subsegments"): once every piece's ends are cut
  points, and so interior to nothing, two pieces that share an interior point coincide instead
  of merely overlapping.
-/

open Set

namespace Schoenflies

variable {a b : Plane}

/-! ### The parametrization of a segment

`AffineMap.lineMap a b` walks from `a` to `b`. It carries a segment of `ℝ` onto the
corresponding piece of `[a, b]`, and it turns the distance from `a` into multiplication by
the segment's length. Those two facts are the whole content of the module; the rest is
arithmetic. -/

/-- The distance from the left endpoint to the point at parameter `t` is `t` times the
segment's length. This is `dist_left_lineMap` with the absolute value discharged. -/
theorem dist_left_lineMap_of_nonneg (a b : Plane) {t : ℝ} (ht : 0 ≤ t) :
    dist a (AffineMap.lineMap a b t) = t * dist a b := by
  rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ht]

/-- The piece of `[a, b]` spanned by two parameters is the image of the segment they span. -/
theorem segment_lineMap_image (a b : Plane) (p q : ℝ) :
    segment ℝ (AffineMap.lineMap a b p) (AffineMap.lineMap a b q)
      = (AffineMap.lineMap a b : ℝ →ᵃ[ℝ] Plane) '' segment ℝ p q := by
  simp

/-- Every point of `[a, b]` carries a parameter: a number `t ∈ [0, 1]` placing it on the
segment, whose distance from `a` is `t` times the segment's length. This is the only way the
rest of the module looks at a point of the segment. -/
theorem exists_param_of_mem_segment {x : Plane} (hx : x ∈ segment ℝ a b) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ AffineMap.lineMap a b t = x ∧ dist a x = t * dist a b := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  exact ⟨t, ht0, ht1, rfl, dist_left_lineMap_of_nonneg a b ht0⟩

/-! ### The coordinate -/

/-- Along a nondegenerate segment, the distance from the left endpoint **orders the
parameters**: a nonzero length cancels from `s * ‖b - a‖ ≤ t * ‖b - a‖`. -/
theorem parameter_le_of_distance (hab : a ≠ b) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : dist a (AffineMap.lineMap a b s) ≤ dist a (AffineMap.lineMap a b t)) : s ≤ t := by
  have hd : 0 < dist a b := dist_pos.2 hab
  rw [dist_left_lineMap_of_nonneg a b hs, dist_left_lineMap_of_nonneg a b ht] at h
  exact le_of_mul_le_mul_right (by linarith) hd

/-- The distance from `a` determines the point: two points of a nondegenerate `[a, b]` at
equal distance from `a` are equal. -/
theorem eq_of_dist_left_eq (hab : a ≠ b) {x y : Plane} (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) (h : dist a x = dist a y) : x = y := by
  have hd : 0 < dist a b := dist_pos.2 hab
  obtain ⟨s, -, -, rfl, hsd⟩ := exists_param_of_mem_segment hx
  obtain ⟨t, -, -, rfl, htd⟩ := exists_param_of_mem_segment hy
  rw [hsd, htd] at h
  rw [mul_right_cancel₀ (ne_of_gt hd) h]

/-! ### Betweenness as a pair of inequalities -/

/-- A point between two points of the segment is between them in distance from `a` as well:
measured from `a`, the nearer end comes first. -/
theorem dist_le_of_mem_segment (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (huv : dist a u ≤ dist a v) (hx : x ∈ segment ℝ u v) :
    dist a u ≤ dist a x ∧ dist a x ≤ dist a v := by
  have hd : (0 : ℝ) ≤ dist a b := dist_nonneg
  obtain ⟨p, hp0, -, rfl, hpd⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, hq0, -, rfl, hqd⟩ := exists_param_of_mem_segment hv
  have hpq : p ≤ q := parameter_le_of_distance hab hp0 hq0 huv
  -- The parametrization carries `[p, q]` onto the piece, so `x` has a parameter in `[p, q]`.
  rw [segment_lineMap_image, segment_eq_Icc hpq] at hx
  obtain ⟨t, ⟨hpt, htq⟩, rfl⟩ := hx
  rw [hpd, hqd, dist_left_lineMap_of_nonneg a b (hp0.trans hpt)]
  exact ⟨by nlinarith, by nlinarith⟩

/-! ### The same translation for interiors

`openSegment ℝ u u = {u}` in Mathlib, so the strict form asks for a nondegenerate piece; its
converse does not, since strict inequalities force nondegeneracy on their own. -/

/-! ### Where a point that is not interior to a piece must sit

These two carry the whole one-dimensional argument. A point of the ambient segment kept out
of a piece's interior has to be outside on one side or the other, and knowing which side it
is not settles it. -/

/-! ### What the overlay is after -/

/-! ### The same two, asking the caller nothing about orientation

A piece is a pair of ends, and which of them is nearer `a` is none of the caller's business —
`segment` and `openSegment` do not care. The oriented forms above are near-end-first because
that is what the arithmetic wants; these decide the orientation themselves. Every hypothesis
is restated in both spellings first, so each of the four cases is just "which way round, then
cite". -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.Subdivide
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subdividing a list of segments

A polygonal edge **is** its pair of endpoints: a straight segment is determined by its ends,
so naming one by anything else names a distinction that does not exist. `Piece := Plane ×
Plane`, and the blueprint's "represent every duplicate geometric subsegment only once"
becomes deduplication of a list of *names*, with no geometry in it.

**The subdivision recurses on the POINT list, not on the segment.** `subdivide pieces points`
cuts every current piece at the head point and recurses with the rest. Read literally the
blueprint wants the cut points as data, which would need a choice operator (the meets are
existential) and then a sort (to order them along each segment). Neither is required: order
does not matter, because cutting at a point that has already become an endpoint is a no-op.

Three facts about one cut, each lifted across the piece list and then across the point list:

* `subdivide_cover` — cutting loses nothing, so a subdivision occupies what it came from;
* `subdivide_ne` — no piece degenerates, so the drawing condition's invariant survives;
* `subdivide_interior_subset` — every piece's interior lies inside the interior of a piece
  it came from. This is what makes a cut **permanent**: nothing later can put a removed point
  back into an interior.

## Blueprint

* `Piece`, `cover` — the segment representation and what a list of them occupies.
* `subdivide` and its three properties — the cutting half of Lemma 3.7 (polygonal overlay).
-/

open Metric Set

namespace Schoenflies

/-- A polygonal edge is its pair of endpoints. -/
abbrev Piece := Plane × Plane

namespace Piece

/-- The closed segment a piece occupies. -/
def seg (P : Piece) : Set Plane := segment ℝ P.1 P.2

/-- The interior of a piece. -/
def interior (P : Piece) : Set Plane := openSegment ℝ P.1 P.2

/-- A piece is nondegenerate when its two ends differ. -/
def Nondeg (P : Piece) : Prop := P.1 ≠ P.2

end Piece

/-- What a list of pieces occupies. -/
def cover (pieces : List Piece) : Set Plane := ⋃ P ∈ pieces, P.seg

@[simp] theorem cover_nil : cover [] = ∅ := by simp [cover]

@[simp] theorem cover_cons (P : Piece) (ps : List Piece) :
    cover (P :: ps) = P.seg ∪ cover ps := by
  simp [cover]

theorem cover_append (ps qs : List Piece) : cover (ps ++ qs) = cover ps ∪ cover qs := by
  induction ps with
  | nil => simp
  | cons P ps ih => rw [List.cons_append, cover_cons, cover_cons, ih, union_assoc]

/-! ### One cut -/

open scoped Classical in
/-- Cut one piece at one point: two pieces if the point is interior to it, and the piece
unchanged otherwise. Cutting at a point that is already an endpoint is a no-op. -/
noncomputable def splitAt (p : Plane) (P : Piece) : List Piece :=
  if p ∈ P.interior then [(P.1, p), (p, P.2)] else [P]

/-! ### One cut, across the whole list -/

/-- Cut every piece of the list at one point. -/
noncomputable def splitAllAt (p : Plane) (pieces : List Piece) : List Piece :=
  pieces.flatMap (splitAt p)

/-! ### The subdivision -/

/-- Subdivide a list of pieces at a list of points, recursing on the POINT list: cut every
current piece at the head, then carry on with the tail. -/
noncomputable def subdivide (pieces : List Piece) : List Plane → List Piece
  | [] => pieces
  | p :: ps => subdivide (splitAllAt p pieces) ps

@[simp] theorem subdivide_nil (pieces : List Piece) : subdivide pieces [] = pieces := rfl

@[simp] theorem subdivide_cons (pieces : List Piece) (p : Plane) (ps : List Plane) :
    subdivide pieces (p :: ps) = subdivide (splitAllAt p pieces) ps := rfl

end Schoenflies
end

section
-- module Solutions.Q146_CD.Overlay
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The polygonal overlay

Finitely many segments become a plane graph once they are subdivided at their meets and each
duplicated subsegment is named once (`lem:polygonal-overlay`).

## Blueprint

* `polygonal_overlay` — Lemma 3.7 (polygonal overlay).
-/

open Metric Set

namespace Schoenflies

/-! ### Two more properties of `subdivide`

Both belong in `Schoenflies/Subdivide.lean` beside the other four; they are here because that
module is on `main`.

`subdivide_subset` is `subdivide_interior_subset` with the **closed** inclusion carried
alongside the open one, in one existential: separation reads a piece's ends off its source
segment and its interior off the source's interior, and it needs both at the same source.

`subdivide_ends` is the endpoint criterion — an end of a piece that is not a cut point was an
end all along. Without it the case of two pieces from different sources does not close: two
different subpieces can both sit inside one long overlap. -/

/-! ### What the cut points have to cover

Two conditions, and between them they are the blueprint's "subdivide at all old endpoints,
isolated intersections, and endpoints of overlapping intervals". The second asks for **some**
pair of ends of each meet rather than every pair, because that is what a construction can
supply: a meet is `segment ℝ u v` and `segment ℝ v u` alike, and that a nondegenerate
segment's ends are determined by its point set is a theorem this development does not have and
does not need. -/

/-- Where two pieces meet. -/
def meetOf (P Q : Piece) : Set Plane := P.seg ∩ Q.seg

theorem meetOf_comm (P Q : Piece) : meetOf P Q = meetOf Q P := inter_comm _ _

/-- Every end of every source piece is a cut point. -/
def EndsAreCut (pieces : List Piece) (points : List Plane) : Prop :=
  ∀ P ∈ pieces, ∀ z, (z = P.1 ∨ z = P.2) → z ∈ points

/-! ### Producing the cut points

Nothing computes them. The overlay is stated existentially, so the list is built by the
induction that proves it exists, and `segment_inter_segment` hands over the ends of a meet the
moment the meet is known to be nonempty. That is what keeps the choice operator out: the
witnesses of `segment_inter_segment` are not unique, so there is nothing to name. -/

/-! ### Separation

Cut at every end of every source piece and at both ends of every meet, and two pieces of the
subdivision that share an interior point are the **same** segment — equal, not disjoint.
Overlapping collinear pieces cannot be pulled apart by cutting; after enough cuts they
coincide, which is what the blueprint's deduplication clause is for. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.OverlayGraph
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The polygonal overlay, assembled into a plane graph

`Schoenflies/Overlay.lean` does the separating half of `lem:polygonal-overlay`: after cutting
at the right points, two pieces of the subdivision whose interiors meet are the **same
segment**, in one order or the other. This module turns that into a plane graph.

The only thing standing between "the same segment" and "the same edge" is that a segment has
two names, `(a, b)` and `(b, a)`. `orientPiece` removes the choice by fixing a total order on
plane points — `Precedes`, lexicographic in the coordinates — and putting the smaller end
first. Two names for one segment then orient to the *same* name, so "represent each duplicated
subsegment once" stops being deduplication up to reversal and becomes deduplication up to
equality, which `List.dedup` does without knowing any geometry. Nothing geometric rests on
which order it is: only `precedes_total` and `eq_of_precedes_of_precedes` are ever used.

The graph is `overlayGraph`, a `Graph Plane Piece`: its edges are the oriented, deduplicated
pieces, and its vertices are their ends. `IsLink P x y` says that `P` is an edge and that `x`
and `y` are its two ends in one order or the other — which is why
`eq_or_eq_of_isLink_of_isLink` is a two-line case split rather than an argument.

The three clauses of `Graph.IsDrawing` come out as follows.

* *Each edge is drawn by an arc between its ends* — `isArcBetween_segment`, given
  nondegeneracy, which `subdivide_ne` preserves and orienting does not disturb.
* *An edge's arc meets the vertex set only at its own ends* — a vertex is an end of some
  edge, hence a cut point, and `subdivide_avoids` says a cut point is interior to nothing.
* *Distinct edges meet only at shared vertices* — a common point that is an end of neither
  would be interior to both, and `subdivide_separated` would make the two pieces the same
  segment, hence (after orienting) the same name. Once it is an end of one it is a cut point,
  so it cannot be interior to the other either, and it is an end of both.

## Blueprint

* `Precedes`, `orientPiece` — the canonical orientation of a segment.
* `overlayPieces`, `overlayGraph`, `segmentDrawing` — the graph of Lemma 3.7.
* `polygonal_overlay` — Lemma 3.7 (polygonal overlay), the whole statement.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### A total order on plane points

It exists to pick one of two points canonically. Only two facts about it are used: that it
compares any two points, and that it cannot rank two distinct points both ways round. -/

/-- The lexicographic order on plane points: first coordinate, then second. -/
def Precedes (p q : Plane) : Prop := p 0 < q 0 ∨ (p 0 = q 0 ∧ p 1 ≤ q 1)

theorem precedes_total (p q : Plane) : Precedes p q ∨ Precedes q p := by
  rcases lt_trichotomy (p 0) (q 0) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total (p 1) (q 1) with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

theorem eq_of_precedes_of_precedes {p q : Plane} (h : Precedes p q) (h' : Precedes q p) :
    p = q := by
  -- Both coordinates are pinned: the first by trichotomy, the second by antisymmetry of `≤`.
  have key : p 0 = q 0 ∧ p 1 = q 1 := by
    rcases h with h | ⟨ha, hb⟩ <;> rcases h' with h' | ⟨ha', hb'⟩
    · exact absurd h (asymm h')
    · exact absurd h (by rw [ha']; exact lt_irrefl _)
    · exact absurd h' (by rw [ha]; exact lt_irrefl _)
    · exact ⟨ha, le_antisymm hb hb'⟩
  ext i
  fin_cases i
  · exact key.1
  · exact key.2

/-! ### The canonical orientation of a piece -/

open scoped Classical in
/-- A piece with its ends in lexicographic order. Two names for one segment orient to the
same name; that is the whole purpose. -/
noncomputable def orientPiece (P : Piece) : Piece :=
  if Precedes P.1 P.2 then P else (P.2, P.1)

theorem orientPiece_of_precedes {P : Piece} (h : Precedes P.1 P.2) : orientPiece P = P := by
  classical
  exact if_pos h

theorem orientPiece_of_not_precedes {P : Piece} (h : ¬ Precedes P.1 P.2) :
    orientPiece P = (P.2, P.1) := by
  classical
  exact if_neg h

/-- Orienting does not move the segment. -/
@[simp] theorem orientPiece_seg (P : Piece) : (orientPiece P).seg = P.seg := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact segment_symm ℝ _ _

/-- Nor the interior. -/
@[simp] theorem orientPiece_interior (P : Piece) : (orientPiece P).interior = P.interior := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact openSegment_symm ℝ _ _

theorem orientPiece_nondeg {P : Piece} (h : P.Nondeg) : (orientPiece P).Nondeg := by
  by_cases hp : Precedes P.1 P.2
  · rw [orientPiece_of_precedes hp]; exact h
  · rw [orientPiece_of_not_precedes hp]; exact fun e => h e.symm

/-- **Orienting forgets the name it was given.** This is the fact that makes deduplication
carry no geometry. -/
@[simp] theorem orientPiece_swap (P : Piece) : orientPiece (P.2, P.1) = orientPiece P := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
    by_cases h' : Precedes P.2 P.1
    · -- Each end precedes the other, so they are the same point and the pair is its own
      -- reversal.
      have he : P.1 = P.2 := eq_of_precedes_of_precedes h h'
      rw [orientPiece_of_precedes (P := (P.2, P.1)) h']
      exact Prod.ext he.symm he
    · rw [orientPiece_of_not_precedes (P := (P.2, P.1)) h']
  · rw [orientPiece_of_not_precedes h,
      orientPiece_of_precedes (P := (P.2, P.1)) ((precedes_total P.1 P.2).resolve_left h)]

/-! ### Deduplication

`cover` only sees which pieces are in the list, so both steps of the assembly — orienting and
deduplicating — leave it alone. -/

theorem cover_map_orientPiece (l : List Piece) : cover (l.map orientPiece) = cover l := by
  ext x
  simp only [cover, mem_iUnion, exists_prop, List.mem_map]
  constructor
  · rintro ⟨P, ⟨Q, hQ, rfl⟩, hx⟩
    exact ⟨Q, hQ, by rwa [orientPiece_seg] at hx⟩
  · rintro ⟨Q, hQ, hx⟩
    exact ⟨orientPiece Q, ⟨Q, hQ, rfl⟩, by rwa [orientPiece_seg]⟩

open scoped Classical in
/-- The edges of the overlay: the pieces of the subdivision, oriented and then deduplicated.
Orienting is what makes the deduplication a plain list operation. -/
noncomputable def overlayPieces (pieces : List Piece) (points : List Plane) : List Piece :=
  ((subdivide pieces points).map orientPiece).dedup

/-! ### The graph -/

/-- The ends of a list of pieces. -/
def endSet (edges : List Piece) : Set Plane := {v | ∃ P ∈ edges, v = P.1 ∨ v = P.2}

/-- The overlay graph: the oriented deduplicated pieces as edges, their ends as vertices.

An edge links `x` and `y` exactly when they are its two ends in one order or the other, which
is what makes `eq_or_eq_of_isLink_of_isLink` a case split with no content. -/
noncomputable def overlayGraph (pieces : List Piece) (points : List Plane) :
    Graph Plane Piece where
  vertexSet := endSet (overlayPieces pieces points)
  IsLink P x y := P ∈ overlayPieces pieces points ∧
    ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1))
  edgeSet := {P | P ∈ overlayPieces pieces points}
  isLink_symm := fun _ _ => ⟨fun _ _ h => ⟨h.1, by tauto⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro P x y v w ⟨-, hxy⟩ ⟨-, hvw⟩
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink := by
    intro P
    simp only [mem_setOf_eq]
    exact ⟨fun hP => ⟨P.1, P.2, hP, Or.inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, hP, _⟩ => hP⟩
  left_mem_of_isLink := by
    rintro P x y ⟨hP, h⟩
    exact ⟨P, hP, by tauto⟩

variable {pieces : List Piece} {points : List Plane} {P : Piece} {x y v : Plane}

@[simp] theorem overlayGraph_vertexSet :
    V(overlayGraph pieces points) = endSet (overlayPieces pieces points) := rfl

@[simp] theorem overlayGraph_mem_edgeSet :
    P ∈ E(overlayGraph pieces points) ↔ P ∈ overlayPieces pieces points := Iff.rfl

@[simp] theorem overlayGraph_isLink :
    (overlayGraph pieces points).IsLink P x y ↔
      P ∈ overlayPieces pieces points ∧ ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1)) := Iff.rfl

/-! ### The drawing

A straight edge is drawn by the affine parametrization of its segment, so the arc clause of
`IsDrawing` is `isArcBetween_segment` and nothing else. -/

/-- Every piece is drawn by the affine parametrization of its segment. -/
noncomputable def segmentDrawing (P : Piece) : ℝ → Plane := AffineMap.lineMap P.1 P.2

@[simp] theorem edgeArc_segmentDrawing (P : Piece) :
    Graph.edgeArc segmentDrawing P = P.seg :=
  (segment_eq_image_lineMap ℝ P.1 P.2).symm

/-! ### Finiteness

Without this the whole face and outer-face machinery of `Schoenflies/Graph/Drawing.lean` and
`Schoenflies/Graph/OuterFace.lean` is inapplicable to the overlay, since every statement there
carries a `[G.Finite]` instance. Both sets come from one finite list, so it is immediate — but
it has to be said, and the instance has to be found by typeclass search at the call site. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.Direction
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Directions, and the two arcs cut out by a pair of rays

This module supplies the *direction facts* that the two-sided strip lemma runs on. Everything
here is stated through the sign of the orientation form `Plane.det`: no angle is named, no
inverse trigonometric function appears, and no case distinction on the sense of a turn is
ever made.

A *direction* is a unit vector (`Plane.IsDirection`). What actually matters about a direction
is its ray — the set of its positive multiples — because every predicate below is invariant
under positive scaling (`Plane.smul_mem_arcCCW`). So the arcs are defined on all nonzero
vectors and the unit-vector normalisation `Plane.dir` is only a convenience.

## The two arcs

Two directions `u` and `w` that are neither equal nor opposite are exactly two directions with
`det u w ≠ 0` (`Plane.det_ne_zero_iff`). They cut the circle of directions into two open arcs.
The arc traversed counterclockwise from `u` to `w` is `Plane.arcCCW u w`, defined by Sedgewick's
`ccw` predicate on the triple `(u, d, w)`: at least two of the three consecutive orientation
forms are positive. This definition is manifestly invariant under rotating the triple, and — this
is the point — it is correct for *both* arcs at once, the short one and the long one, with no
sign hypothesis in the definition itself.

`Plane.mem_ray_or_mem_arcCCW` and `Plane.arcCCW_disjoint` say that the two arcs and the two
bounding rays partition the nonzero vectors.

## The transfer fact

`Plane.same_arc_of_det_neg_of_det_pos` is Appendix C's transfer fact: *a direction with negative
`det` against the first ray lies on the same arc as a direction with positive `det` against the
second*. Note that no nearness hypothesis is needed for it — see the module note below.

## Blueprint

* `Plane.IsDirection`, `Plane.dir`, `Plane.arcCCW`, `Plane.det_ne_zero_iff`,
  `Plane.mem_ray_or_mem_arcCCW`, `Plane.arcCCW_disjoint` — Appendix C, item 1, "two distinct,
  non-opposite unit vectors bound two open arcs of directions".
* `Plane.same_arc_of_det_neg_of_det_pos` — Appendix C, item 1, the transfer fact.
* `Plane.exists_isDirection_det_ne_zero`, `Plane.exists_isDirection_det_and_inner_ne_zero` —
  Appendix C, item 1, "the existence of a unit vector avoiding any prescribed finite set of
  directions".
* `Plane.germs_split`, `Plane.exists_germ_threshold` — the vertex matching inside Lemma 1.8
  (Two-sided polygonal strips): the two left half-strip germs land on one arc and the two right
  ones on the other.

## A note on "near"

Appendix C states the transfer fact for directions *near* the two bounding rays. The nearness is
not needed: `Plane.mem_arcCCW_rev_iff` shows that the arc counterclockwise from `w` to `u` is cut
out by a *disjunction* of two sign conditions, so a single sign suffices to land on it. The
mirror statement — a direction with positive `det` against `u` and one with negative `det`
against `w` both lie on `arcCCW u w` — is *not* available from one sign each, because that arc is
cut out by the *conjunction* (`Plane.mem_arcCCW_iff`). Lemma 1.8 needs the mirror statement too,
for the two right germs, and there the missing second sign is exactly what "`s/t` small" buys:
`Plane.exists_germ_threshold` supplies it, with an explicit threshold.
-/

open Set

namespace Schoenflies

namespace Plane

variable {u w d d₁ d₂ r₁ r₂ v : Plane} {r t s : ℝ}

/-! ### Directions -/

/-- A *direction* is a unit vector. Only the ray a direction spans ever matters below, but
normalising to unit length gives a canonical representative of that ray. -/
def IsDirection (u : Plane) : Prop := ‖u‖ = 1

theorem IsDirection.norm (hu : IsDirection u) : ‖u‖ = 1 := hu

/-- The unit vector along a nonzero vector. -/
noncomputable def dir (u : Plane) : Plane := ‖u‖⁻¹ • u

theorem isDirection_dir (hu : u ≠ 0) : IsDirection (dir u) := by
  have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [IsDirection, dir, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos,
    inv_mul_cancel₀ hpos.ne']

/-- `dir u` is a positive multiple of `u`, which is why every sign-of-`det` predicate is blind
to the difference. -/
theorem dir_eq_smul (hu : u ≠ 0) : ∃ c : ℝ, 0 < c ∧ dir u = c • u :=
  ⟨‖u‖⁻¹, inv_pos.2 (norm_pos_iff.2 hu), rfl⟩

/-! ### Nonvanishing of `det` -/

theorem ne_zero_left_of_det_ne_zero (h : det u w ≠ 0) : u ≠ 0 := by
  rintro rfl
  exact h (by simp [det])

theorem ne_zero_right_of_det_ne_zero (h : det u w ≠ 0) : w ≠ 0 := by
  rintro rfl
  exact h (by simp [det])

/-! ### The two arcs -/

/-- The open arc of directions traversed counterclockwise from `u` to `w`.

A nonzero `d` lies on it when at least two of the three consecutive orientation forms of the
triple `(u, d, w)` are positive. The definition is a cyclic condition, so it is correct for the
short arc and for the long arc alike, with no hypothesis on the sign of `det u w`. -/
def arcCCW (u w : Plane) : Set Plane :=
  {d | (0 < det u d ∧ 0 < det d w) ∨ (0 < det d w ∧ 0 < det w u) ∨ (0 < det w u ∧ 0 < det u d)}

/-- Fix the orientation by `0 < det u w`, so that `w` is counterclockwise of `u` by less than a
half turn. Then the arc counterclockwise from `u` to `w` is the *short* one, and membership is
the conjunction of two sign conditions. -/
theorem mem_arcCCW_iff (h : 0 < det u w) : d ∈ arcCCW u w ↔ 0 < det u d ∧ 0 < det d w := by
  have hwu : det w u < 0 := by rw [det_comm w u]; linarith
  refine ⟨?_, Or.inl⟩
  rintro (h1 | ⟨_, h2⟩ | ⟨h2, _⟩)
  · exact h1
  · linarith
  · linarith

/-- With the same orientation `0 < det u w`, the arc counterclockwise from `w` back to `u` is the
*long* one — more than a half turn — and membership is a **disjunction**. This asymmetry is the
whole content of the transfer fact: one sign suffices here, two are needed on the short arc. -/
theorem mem_arcCCW_rev_iff (h : 0 < det u w) :
    d ∈ arcCCW w u ↔ det u d < 0 ∨ det d w < 0 := by
  have e1 : det w d = -det d w := det_comm w d
  have e2 : det d u = -det u d := det_comm d u
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h2, _⟩ | ⟨_, h1⟩)
    · exact Or.inl (by rw [e2] at h2; linarith)
    · exact Or.inl (by rw [e2] at h2; linarith)
    · exact Or.inr (by rw [e1] at h1; linarith)
  · rintro (h1 | h2)
    · exact Or.inr (Or.inl ⟨by rw [e2]; linarith, h⟩)
    · exact Or.inr (Or.inr ⟨h, by rw [e1]; linarith⟩)

/-- Every sign-of-`det` condition is blind to positive rescaling, so the arcs really are sets of
*rays*, not of vectors. -/
theorem smul_mem_arcCCW (hr : 0 < r) : r • d ∈ arcCCW u w ↔ d ∈ arcCCW u w := by
  have key : ∀ x : ℝ, 0 < r * x ↔ 0 < x := by
    intro x
    constructor <;> intro hx <;> nlinarith
  simp only [arcCCW, mem_setOf_eq, det_smul_left, det_smul_right, key]

/-- The two rays and the two arcs exhaust the nonzero vectors. Together with
`Plane.arcCCW_disjoint` this is the statement that two distinct, non-opposite directions bound
two arcs. -/
theorem mem_ray_or_mem_arcCCW (h : 0 < det u w) (hd : d ≠ 0) :
    (∃ c : ℝ, 0 < c ∧ d = c • u) ∨ (∃ c : ℝ, 0 < c ∧ d = c • w) ∨
      d ∈ arcCCW u w ∨ d ∈ arcCCW w u := by
  have hu : u ≠ 0 := ne_zero_left_of_det_ne_zero h.ne'
  have hw : w ≠ 0 := ne_zero_right_of_det_ne_zero h.ne'
  by_cases hneg : det u d < 0 ∨ det d w < 0
  · exact Or.inr (Or.inr (Or.inr ((mem_arcCCW_rev_iff h).2 hneg)))
  push Not at hneg
  obtain ⟨h1, h2⟩ := hneg
  rcases lt_or_eq_of_le h1 with h1' | h1'
  · rcases lt_or_eq_of_le h2 with h2' | h2'
    · exact Or.inr (Or.inr (Or.inl ((mem_arcCCW_iff h).2 ⟨h1', h2'⟩)))
    · -- `det d w = 0`: `d` lies along the line of `w`, and `det u d ≥ 0` fixes the sign.
      obtain ⟨c, rfl⟩ := (det_eq_zero_iff_smul w d hw).1 (by rw [det_comm w d, ← h2']; ring)
      refine Or.inr (Or.inl ⟨c, ?_, rfl⟩)
      rw [det_smul_right] at h1'
      nlinarith
  · -- `det u d = 0`: `d` lies along the line of `u`, and `det d w ≥ 0` fixes the sign.
    obtain ⟨c, rfl⟩ := (det_eq_zero_iff_smul u d hu).1 h1'.symm
    refine Or.inl ⟨c, ?_, rfl⟩
    rw [det_smul_left] at h2
    rcases lt_or_eq_of_le h2 with h2' | h2'
    · nlinarith
    · exfalso
      have : c = 0 := by
        rcases mul_eq_zero.1 h2'.symm with hc | hd'
        · exact hc
        · exact absurd hd' h.ne'
      exact hd (by rw [this, zero_smul])

/-! ### The transfer fact -/

/-- A direction with **negative** `det` against `u` lies on the arc counterclockwise from `w`
to `u`. No nearness hypothesis is needed. -/
theorem mem_arcCCW_rev_of_det_neg (h : 0 < det u w) (hd : det u d < 0) : d ∈ arcCCW w u :=
  (mem_arcCCW_rev_iff h).2 (Or.inl hd)

/-- A direction with **positive** `det` against `w` lies on the arc counterclockwise from `w`
to `u`. No nearness hypothesis is needed. -/
theorem mem_arcCCW_rev_of_det_pos (h : 0 < det u w) (hd : 0 < det w d) : d ∈ arcCCW w u :=
  (mem_arcCCW_rev_iff h).2 (Or.inr (by rw [det_comm d w]; linarith))

/-! ### Half-strip germs

Fix a vertex with incoming unit tangent `u` and outgoing unit tangent `w`, and let `r₁ = -u`,
`r₂ = w` be the two rays leaving the vertex, so that `perp r₁ = -u^⊥` and `perp r₂ = w^⊥`.
Then the four half-strip germs of Lemma 1.8 are, in the blueprint's own notation,

* incoming left, `-t u + s u^⊥ = t • r₁ - s • perp r₁`;
* outgoing left, `t w + s w^⊥ = t • r₂ + s • perp r₂`;
* incoming right, `-t u - s u^⊥ = t • r₁ + s • perp r₁`;
* outgoing right, `t w - s w^⊥ = t • r₂ - s • perp r₂`,

each with `t, s > 0`. The four computations below place them on the two arcs. -/

/-- The orientation form of a germ against its own tangent sees only the transverse
coefficient: this is the blueprint's `det(r₁, d) = -s` and `det(r₂, d) = s`. -/
theorem det_germ_self (r : Plane) (t s : ℝ) :
    det r (t • r + s • perp r) = s * ‖r‖ ^ 2 := by
  rw [det_add_right, det_smul_right, det_smul_right, det_self, det_perp_self]
  ring

theorem det_germ_self' (r : Plane) (t s : ℝ) :
    det (t • r + s • perp r) r = -(s * ‖r‖ ^ 2) := by
  rw [det_comm, det_germ_self]

/-- The orientation form of a germ at `r₁` against the *other* ray. The inner-product term is
what makes the transverse coefficient have to be small relative to the longitudinal one. -/
theorem det_germ (r₁ r₂ : Plane) (t s : ℝ) :
    det (t • r₁ + s • perp r₁) r₂ = t * det r₁ r₂ - s * inner ℝ r₁ r₂ := by
  rw [det_add_left, det_smul_left, det_smul_left, det_perp_left]
  ring

/-- The orientation form of a germ at `r₂` against the other ray. -/
theorem det_germ' (r₁ r₂ : Plane) (t s : ℝ) :
    det r₁ (t • r₂ + s • perp r₂) = t * det r₁ r₂ + s * inner ℝ r₁ r₂ := by
  rw [det_add_right, det_smul_right, det_smul_right, det_perp_right]

theorem sq_norm_pos_left (h : 0 < det r₁ r₂) : 0 < ‖r₁‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 (ne_zero_left_of_det_ne_zero h.ne')) 2

theorem sq_norm_pos_right (h : 0 < det r₁ r₂) : 0 < ‖r₂‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 (ne_zero_right_of_det_ne_zero h.ne')) 2

/-- The **incoming left** germ lands on the arc counterclockwise from `r₂` to `r₁`, for *every*
longitudinal coefficient `t`: this is the half of the vertex matching that costs nothing,
because that arc is cut out by a disjunction. -/
theorem germ_mem_arcCCW_rev_of_left (h : 0 < det r₁ r₂) (hs : 0 < s) (t : ℝ) :
    t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ := by
  refine mem_arcCCW_rev_of_det_neg h ?_
  have e : t • r₁ - s • perp r₁ = t • r₁ + (-s) • perp r₁ := by module
  rw [e, det_germ_self]
  nlinarith [sq_norm_pos_left h]

/-- The **outgoing left** germ lands on the same arc, again for every `t`. -/
theorem germ_mem_arcCCW_rev_of_right (h : 0 < det r₁ r₂) (hs : 0 < s) (t : ℝ) :
    t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁ := by
  refine mem_arcCCW_rev_of_det_pos h ?_
  rw [det_germ_self]
  exact mul_pos hs (sq_norm_pos_right h)

/-- The **incoming right** germ lands on the arc counterclockwise from `r₁` to `r₂` provided the
transverse coefficient is small enough against the longitudinal one. The inequality
`s ⟪r₁, r₂⟫ < t det(r₁, r₂)` is exactly "`s/t` small", written without a division. -/
theorem germ_mem_arcCCW_of_left (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ := by
  refine (mem_arcCCW_iff h).2 ⟨?_, ?_⟩
  · rw [det_germ_self]
    exact mul_pos hs (sq_norm_pos_left h)
  · rw [det_germ]
    linarith

/-- The **outgoing right** germ lands on the same arc, under the same smallness condition. -/
theorem germ_mem_arcCCW_of_right (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂ := by
  have e : t • r₂ - s • perp r₂ = t • r₂ + (-s) • perp r₂ := by module
  refine (mem_arcCCW_iff h).2 ⟨?_, ?_⟩
  · rw [e, det_germ']
    linarith
  · rw [e, det_germ_self']
    nlinarith [sq_norm_pos_right h]

/-- **The vertex matching of Lemma 1.8.** With the strips narrow enough — `s ⟪r₁, r₂⟫` under
`t det(r₁, r₂)` — the two left germs lie on one arc and the two right germs on the other. No
angle is named and no case distinction on the sense of the turn arises: the two cases of the
turn are the two orders in which `r₁` and `r₂` may be presented, and `det_comm` exchanges
them. -/
theorem germs_split (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    (t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ ∧ t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁) ∧
      (t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ ∧ t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂) :=
  ⟨⟨germ_mem_arcCCW_rev_of_left h hs t, germ_mem_arcCCW_rev_of_right h hs t⟩,
    ⟨germ_mem_arcCCW_of_left h hs hsmall, germ_mem_arcCCW_of_right h hs hsmall⟩⟩

/-! ### A direction avoiding finitely many others

The argument is a counting one, with no measure and no trigonometry: the one-parameter family
`a ↦ (1, a)` meets the line of any fixed nonzero vector at most once, so finitely many vectors
rule out only finitely many parameters, and `ℝ` has more than finitely many. -/

/-- The family used to dodge finitely many directions. -/
theorem mk_one_ne_zero (a : ℝ) : mk 1 a ≠ 0 := by
  intro h
  have h0 : mk 1 a 0 = (0 : Plane) 0 := by rw [h]
  simp at h0

theorem det_mk_one (a : ℝ) (v : Plane) : det (mk 1 a) v = v 1 - a * v 0 := by
  simp [det]

/-- **Appendix C.** There is a unit vector not parallel to any of a prescribed finite set of
nonzero vectors. This is what lets one rotate coordinates so that no edge of a finite polygonal
figure is horizontal. -/
theorem exists_isDirection_det_ne_zero {S : Set Plane} (hS : S.Finite) :
    ∃ u : Plane, IsDirection u ∧ ∀ v ∈ S, v ≠ 0 → det u v ≠ 0 := by
  -- The parameters ruled out by `S` are the slopes of its members, hence at most as many as `S`.
  have hbad : {a : ℝ | ∃ v ∈ S, v ≠ 0 ∧ det (mk 1 a) v = 0}.Finite := by
    refine Set.Finite.subset (hS.image fun v => v 1 / v 0) ?_
    rintro a ⟨v, hv, hv0, hdet⟩
    rw [det_mk_one] at hdet
    have h0 : v 0 ≠ 0 := by
      intro h
      refine hv0 ?_
      have h1 : v 1 = 0 := by rw [h] at hdet; linarith
      ext i
      fin_cases i <;> simp [h, h1]
    exact ⟨v, hv, by field_simp <;> linarith⟩
  obtain ⟨a, ha⟩ := hbad.infinite_compl.nonempty
  refine ⟨dir (mk 1 a), isDirection_dir (mk_one_ne_zero a),
    fun v hv hv0 hdet => ha ⟨v, hv, hv0, ?_⟩⟩
  -- `dir` only rescales, so it cannot create a vanishing orientation form.
  obtain ⟨c, hc, hcd⟩ := dir_eq_smul (mk_one_ne_zero a)
  rw [hcd, det_smul_left] at hdet
  rcases mul_eq_zero.1 hdet with h | h
  · exact absurd h hc.ne'
  · exact h

/-! ### The arcs are open

Not needed by Lemma 1.8, which uses only the partition, but it justifies the word "open" in
"two open arcs of directions". -/

theorem continuous_det_right (u : Plane) : Continuous fun d : Plane => det u d := by
  refine Continuous.sub (Continuous.mul continuous_const ?_) (Continuous.mul continuous_const ?_)
  · exact PiLp.continuous_apply _ _ 1
  · exact PiLp.continuous_apply _ _ 0

end Plane

end Schoenflies
end

section
-- module Solutions.Q146_CD.Parity
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.poly_pair _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The crossing count of a polygon, and its parity

This is the arithmetic half of the polygonal Jordan curve theorem. A closed polygon is a
list of edges; a point off it gets a number, the count of edges the ray leaving the point
meets; and the whole separation statement follows from the fact that this number changes by
one exactly when the ray's foot sweeps across an edge.

## The frame

The blueprint rotates the coordinate system so that no edge is horizontal. Rotating a curve
is a change of the curve, which would have to be transported back at the end, so instead the
*ray direction* is carried as a parameter. A direction `u` (a unit vector,
`Plane.IsDirection`) fixes an orthonormal frame through

* `fwd u z` — how far along `u` the point `z` lies,
* `hgt u z` — how far across `u` it lies, positive on the counterclockwise side.

"Horizontal" becomes "level for `u`", i.e. `hgt u a = hgt u b`, and
`exists_direction_hgt_ne` — a one-line consequence of `Plane.exists_isDirection_det_ne_zero`
— supplies a `u` for which no edge of a finite list is level. Nothing below needs the
direction to be produced that way: `hgt u P.1 ≠ hgt u P.2` for every piece is carried as a
hypothesis, so no curve is ever moved and nothing has to be transported back.

## The count

An edge is a `Piece`, i.e. its pair of ends, and a polygon is a `List Piece` — the same
representation the overlay uses, so a subdivision produced by `Schoenflies.subdivide` can be
fed straight in. `Crosses u P q` says that the level line through `q` meets `P` strictly
beyond `q`, with the blueprint's half-open convention at the lower end, which is what makes
the count well defined with no genericity assumption. `crossings` counts and `parity`
reduces mod `2`.

Closedness of the polygon enters through `IsClosedChain`: the boundary of the edge list
vanishes mod `2`, stated by duality as "every `ZMod 2`-valued function of the ends sums to
zero over the list". `edgesOf` builds a closed chain from a cyclic vertex list, and
`IsClosedChain` survives `subdivide`.

## Blueprint

* `crossings`, `parity` — the count `π_C` of the section "The polygonal Jordan and crosscut
  theorems".
* `exists_direction_hgt_ne` — the setup of that section: a ray direction level for no edge.
* `crossings_subdivide`, `parity_subdivide` — Lemma 2.1 (subdivision invariance). Proved for
  the *count*, not only its parity, and for the whole `subdivide` operation of
  `Schoenflies.Subdivide`, not only for a single cut.
* `parity_eq_of_mem_ball`, `parity_eq_of_isPreconnected`,
  `parity_eq_of_mem_connectedComponentIn` — the first half of Lemma 2.2 (crossing parity):
  `π_C` is locally constant off the polygon, hence constant on each component of the
  complement.
* `parity_flip` — the second half of Lemma 4.4: the two local sides of an edge have opposite
  parity.
* `parity_eq_zero_of_lt` — `π_C = 0` beyond the polygon in the ray direction; the value on
  the unbounded region.
* `IsClosedChain`, `edgesOf`, `isClosedChain_subdivide` — the closedness hypothesis, its
  supply from a cyclic vertex list, and its survival of subdivision.
-/

open Metric Set

namespace Schoenflies

variable {u a b c p q z w : Plane} {s t : ℝ} {L : List Piece}

/-! ### The frame attached to a direction -/

/-- How far across the direction `u` the point `z` lies. Edges on which this is constant are
the blueprint's horizontal edges. -/
def hgt (u z : Plane) : ℝ := Plane.det u z

/-- How far along the direction `u` the point `z` lies. The ray from `q` is the set of points
of the same `hgt` and larger `fwd`. -/
noncomputable def fwd (u z : Plane) : ℝ := inner ℝ z u

theorem hgt_eq (u z : Plane) : hgt u z = u 0 * z 1 - u 1 * z 0 := rfl

theorem fwd_eq (u z : Plane) : fwd u z = z 0 * u 0 + z 1 * u 1 := Plane.inner_eq z u

namespace Plane

theorem add_apply (x y : Plane) (i : Fin 2) : (x + y) i = x i + y i := rfl

theorem smul_apply (r : ℝ) (x : Plane) (i : Fin 2) : (r • x) i = r * x i := rfl

end Plane

/-- The coordinate rewriting used throughout: every claim about `hgt` and `fwd` of an affine
combination is a polynomial identity in the four coordinates. -/
theorem hgt_lin (u a b : Plane) (t : ℝ) :
    hgt u (a + t • (b - a)) = hgt u a + t * (hgt u b - hgt u a) := by
  simp only [hgt_eq, Plane.add_apply, Plane.smul_apply, Plane.sub_apply] <;> ring

theorem fwd_lin (u a b : Plane) (t : ℝ) :
    fwd u (a + t • (b - a)) = fwd u a + t * (fwd u b - fwd u a) := by
  simp only [fwd_eq, Plane.add_apply, Plane.smul_apply, Plane.sub_apply] <;> ring

theorem hgt_sub (u x y : Plane) : hgt u (x - y) = hgt u x - hgt u y := by
  simp only [hgt_eq, Plane.sub_apply] <;> ring

theorem fwd_sub (u x y : Plane) : fwd u (x - y) = fwd u x - fwd u y := by
  simp only [fwd_eq, Plane.sub_apply] <;> ring

theorem hgt_add_smul (u v x : Plane) (t : ℝ) :
    hgt u (x + t • v) = hgt u x + t * hgt u v := by
  simp only [hgt_eq, Plane.add_apply, Plane.smul_apply] <;> ring

theorem fwd_add_smul (u v x : Plane) (t : ℝ) :
    fwd u (x + t • v) = fwd u x + t * fwd u v := by
  simp only [fwd_eq, Plane.add_apply, Plane.smul_apply] <;> ring

section Direction

variable (hu : Plane.IsDirection u)
include hu

theorem norm_sq_one : u 0 ^ 2 + u 1 ^ 2 = 1 := by
  rw [← Plane.norm_sq_eq, hu, one_pow]

omit hu in
@[simp] theorem hgt_self : hgt u u = 0 := by simp only [hgt_eq] <;> ring

theorem fwd_self : fwd u u = 1 := by rw [fwd_eq, ← norm_sq_one hu]; ring

theorem hgt_perp : hgt u (Plane.perp u) = 1 := by
  rw [hgt_eq, ← norm_sq_one hu]; simp only [Plane.perp_zero, Plane.perp_one] <;> ring

omit hu in
theorem fwd_perp : fwd u (Plane.perp u) = 0 := by
  simp only [fwd_eq, Plane.perp_zero, Plane.perp_one] <;> ring

/-- The frame is a basis: every vector is its two coordinates. -/
theorem decomp (v : Plane) : v = fwd u v • u + hgt u v • Plane.perp u := by
  have h1 := norm_sq_one hu
  ext i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Plane.add_apply, Plane.smul_apply, Plane.perp_zero,
      Plane.perp_one, hgt_eq, fwd_eq]
  · linear_combination (-(v 0)) * h1
  · linear_combination (-(v 1)) * h1

/-- Two points with the same frame coordinates are equal. -/
theorem eq_of_coords (h1 : fwd u z = fwd u w) (h2 : hgt u z = hgt u w) : z = w := by
  have hz := decomp hu z
  have hw := decomp hu w
  rw [h1, h2] at hz
  exact hz.trans hw.symm

theorem abs_fwd_le_norm (v : Plane) : |fwd u v| ≤ ‖v‖ := by
  have h := abs_real_inner_le_norm v u
  rw [hu, mul_one] at h
  exact h

end Direction

/-! ### Where an edge meets a level line -/

/-- The point of the line through `a` and `b` at height `t`. Only used when the line is not
level, i.e. `hgt u a ≠ hgt u b`. -/
noncomputable def meet (u a b : Plane) (t : ℝ) : Plane :=
  a + ((t - hgt u a) / (hgt u b - hgt u a)) • (b - a)

theorem hgt_meet (h : hgt u a ≠ hgt u b) (t : ℝ) : hgt u (meet u a b t) = t := by
  have hne : hgt u b - hgt u a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  rw [meet, hgt_lin]
  field_simp
  ring

/-- Below the top and above the bottom, the meeting point is on the edge. -/
theorem meet_mem_segment (h : hgt u a < hgt u b) (h1 : hgt u a ≤ t) (h2 : t ≤ hgt u b) :
    meet u a b t ∈ segment ℝ a b := by
  have hne : (0:ℝ) < hgt u b - hgt u a := by linarith
  rw [segment_eq_image' ℝ a b]
  exact ⟨_, ⟨div_nonneg (by linarith) hne.le, (div_le_one hne).2 (by linarith)⟩, rfl⟩

/-- The meeting point is the only point of the edge at its height. -/
theorem eq_meet (h : hgt u a ≠ hgt u b) (hz : z ∈ segment ℝ a b) :
    z = meet u a b (hgt u z) := by
  have hne : hgt u b - hgt u a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  rw [segment_eq_image' ℝ a b] at hz
  obtain ⟨r, -, rfl⟩ := hz
  have : (hgt u (a + r • (b - a)) - hgt u a) / (hgt u b - hgt u a) = r := by
    rw [hgt_lin]; field_simp <;> ring
  rw [meet, this]

/-- Reversing an edge does not move its meeting point. -/
theorem meet_swap (h : hgt u a ≠ hgt u b) (t : ℝ) : meet u b a t = meet u a b t := by
  have hne : hgt u b - hgt u a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have h2 : (t - hgt u b) / (hgt u a - hgt u b)
      = 1 - (t - hgt u a) / (hgt u b - hgt u a) := by field_simp <;> ring
  rw [meet, meet, h2, sub_smul, one_smul, smul_sub, smul_sub]
  abel

/-! ### The crossing count -/

/-- The edge `P` meets the level line through `q` strictly beyond `q`.

The height test is half-open at the bottom: an edge whose lower end is exactly at the height
of `q` counts, one whose upper end is counts not. That convention is what makes the count
well defined at every `q` off the polygon, with no genericity assumption. -/
def Crosses (u : Plane) (P : Piece) (q : Plane) : Prop :=
  min (hgt u P.1) (hgt u P.2) ≤ hgt u q ∧ hgt u q < max (hgt u P.1) (hgt u P.2) ∧
    fwd u q < fwd u (meet u P.1 P.2 (hgt u q))

/-- Crossing is decided classically; the count is a `noncomputable` definition. -/
noncomputable instance decidableCrosses (u : Plane) (P : Piece) (q : Plane) :
    Decidable (Crosses u P q) := Classical.dec _

theorem crosses_swap (h : hgt u a ≠ hgt u b) (q : Plane) :
    Crosses u (b, a) q ↔ Crosses u (a, b) q := by
  simp only [Crosses, meet_swap h, min_comm (hgt u b) (hgt u a), max_comm (hgt u b) (hgt u a)]

/-- How many edges of `L` the ray from `q` crosses. -/
noncomputable def crossings (u : Plane) (L : List Piece) (q : Plane) : ℕ :=
  (L.map (fun P => if Crosses u P q then 1 else 0)).sum

/-- The contribution of one edge to the parity. -/
noncomputable def mark (u : Plane) (P : Piece) (q : Plane) : ZMod 2 :=
  if Crosses u P q then 1 else 0

/-- The crossing parity `π_C(q)`. -/
noncomputable def parity (u : Plane) (L : List Piece) (q : Plane) : ZMod 2 :=
  (L.map (fun P => mark u P q)).sum

@[simp] theorem crossings_nil (u q : Plane) : crossings u [] q = 0 := rfl

@[simp] theorem crossings_cons (u : Plane) (P : Piece) (L : List Piece) (q : Plane) :
    crossings u (P :: L) q = (if Crosses u P q then 1 else 0) + crossings u L q := by
  classical
  simp [crossings]

@[simp] theorem parity_nil (u q : Plane) : parity u [] q = 0 := rfl

@[simp] theorem parity_cons (u : Plane) (P : Piece) (L : List Piece) (q : Plane) :
    parity u (P :: L) q = mark u P q + parity u L q := by
  simp [parity]

theorem parity_append (u : Plane) (L₁ L₂ : List Piece) (q : Plane) :
    parity u (L₁ ++ L₂) q = parity u L₁ q + parity u L₂ q := by
  simp [parity, List.sum_append]

/-! ### Subdivision invariance -/

/-- An interior point of a non-level edge is strictly between its ends in height. -/
theorem hgt_lt_of_mem_openSegment (hab : hgt u a < hgt u b) (hc : c ∈ openSegment ℝ a b) :
    hgt u a < hgt u c ∧ hgt u c < hgt u b := by
  rw [openSegment_eq_image' ℝ a b] at hc
  obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := hc
  rw [hgt_lin]
  constructor
  · nlinarith
  · nlinarith

/-! ### Closed chains -/

theorem sum_map_add {α : Type*} (l : List α) (F G : α → ZMod 2) :
    (l.map (fun x => F x + G x)).sum = (l.map F).sum + (l.map G).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih] <;> ring

theorem add_self_zmod_two (x : ZMod 2) : x + x = 0 := by
  revert x; decide

/-- The edge list is a **closed chain**: its boundary vanishes mod `2`. Stated by duality —
every `ZMod 2`-valued function of the ends sums to zero over the list — which is exactly what
the parity argument consumes, and which `isClosedChain_edgesOf` supplies for a cyclic vertex
list. -/
def IsClosedChain (L : List Piece) : Prop :=
  ∀ f : Plane → ZMod 2, (L.map (fun P => f P.1 + f P.2)).sum = 0

/-! ### What a list of edges occupies -/

theorem mem_cover {P : Piece} (hP : P ∈ L) (hz : z ∈ P.seg) : z ∈ cover L :=
  Set.mem_biUnion hP hz

theorem isCompact_cover (L : List Piece) : IsCompact (cover L) := by
  induction L with
  | nil => rw [cover_nil]; exact isCompact_empty
  | cons P L ih => rw [cover_cons]; exact (isCompact_segment P.1 P.2).union ih

theorem isClosed_cover (L : List Piece) : IsClosed (cover L) := (isCompact_cover L).isClosed

/-- Where an edge meets the level line, when it does. -/
theorem meet_mem_seg {P : Piece} (h : hgt u P.1 ≠ hgt u P.2)
    (h1 : min (hgt u P.1) (hgt u P.2) ≤ t) (h2 : t ≤ max (hgt u P.1) (hgt u P.2)) :
    meet u P.1 P.2 t ∈ P.seg := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · rw [min_eq_left hlt.le] at h1
    rw [max_eq_right hlt.le] at h2
    exact meet_mem_segment hlt h1 h2
  · rw [min_eq_right hlt.le] at h1
    rw [max_eq_left hlt.le] at h2
    have hmem := meet_mem_segment hlt h1 h2
    rwa [meet_swap h, segment_symm] at hmem

/-! ### Moving the base point -/

section Moves

variable (hu : Plane.IsDirection u)
include hu

omit hu in
theorem hgt_along (q : Plane) (s : ℝ) : hgt u (q + s • u) = hgt u q := by
  rw [hgt_add_smul, hgt_self]; ring

theorem fwd_along (q : Plane) (s : ℝ) : fwd u (q + s • u) = fwd u q + s := by
  rw [fwd_add_smul, fwd_self hu]; ring

theorem hgt_across (q : Plane) (s : ℝ) : hgt u (q + s • Plane.perp u) = hgt u q + s := by
  rw [hgt_add_smul, hgt_perp hu]; ring

omit hu in
theorem fwd_across (q : Plane) (s : ℝ) : fwd u (q + s • Plane.perp u) = fwd u q := by
  rw [fwd_add_smul, fwd_perp]; ring

/-- The segment from `q` in the ray direction is exactly the points at the same height with
`fwd` in between. -/
theorem mem_segment_along {q y : Plane} {s : ℝ} (hs : 0 ≤ s) (h1 : hgt u y = hgt u q)
    (h2 : fwd u q ≤ fwd u y) (h3 : fwd u y ≤ fwd u q + s) :
    y ∈ segment ℝ q (q + s • u) := by
  rcases eq_or_lt_of_le hs with rfl | hspos
  · have hy : y = q := eq_of_coords hu (by linarith) h1
    rw [hy, zero_smul, add_zero]
    exact left_mem_segment ℝ q q
  · rw [segment_eq_image' ℝ q (q + s • u)]
    refine ⟨(fwd u y - fwd u q) / s,
      ⟨div_nonneg (by linarith) hs, (div_le_one hspos).2 (by linarith)⟩, ?_⟩
    simp only []
    have hsub : q + s • u - q = s • u := by abel
    rw [hsub, smul_smul, div_mul_cancel₀ _ (ne_of_gt hspos)]
    exact eq_of_coords hu (by rw [fwd_add_smul, fwd_self hu]; ring)
      (by rw [hgt_add_smul, hgt_self, h1]; ring)

/-- The segment from `q` across the ray direction is exactly the points with the same `fwd`
and height in between. -/
theorem mem_segment_across {q y : Plane} {s : ℝ} (hs : 0 ≤ s) (h1 : fwd u y = fwd u q)
    (h2 : hgt u q ≤ hgt u y) (h3 : hgt u y ≤ hgt u q + s) :
    y ∈ segment ℝ q (q + s • Plane.perp u) := by
  rcases eq_or_lt_of_le hs with rfl | hspos
  · have hy : y = q := eq_of_coords hu h1 (by linarith)
    rw [hy, zero_smul, add_zero]
    exact left_mem_segment ℝ q q
  · rw [segment_eq_image' ℝ q (q + s • Plane.perp u)]
    refine ⟨(hgt u y - hgt u q) / s,
      ⟨div_nonneg (by linarith) hs, (div_le_one hspos).2 (by linarith)⟩, ?_⟩
    simp only []
    have hsub : q + s • Plane.perp u - q = s • Plane.perp u := by abel
    rw [hsub, smul_smul, div_mul_cancel₀ _ (ne_of_gt hspos)]
    exact eq_of_coords hu (by rw [fwd_add_smul, fwd_perp, h1]; ring)
      (by rw [hgt_add_smul, hgt_perp hu]; ring)

omit hu in
/-- A connected piece of an edge that stays between two heights and never meets the level
line `fwd = ξ` stays on one side of it. -/
theorem side_const {lo hi ξ : ℝ}
    (hmiss : ∀ y ∈ segment ℝ a b, fwd u y = ξ → lo ≤ hgt u y → hgt u y ≤ hi → False)
    (hz : z ∈ segment ℝ a b) (hw : w ∈ segment ℝ a b)
    (hzl : lo ≤ hgt u z) (hzh : hgt u z ≤ hi) (hwl : lo ≤ hgt u w) (hwh : hgt u w ≤ hi) :
    (ξ < fwd u z ↔ ξ < fwd u w) := by
  have key : ∀ z w : Plane, z ∈ segment ℝ a b → w ∈ segment ℝ a b →
      lo ≤ hgt u z → hgt u z ≤ hi → lo ≤ hgt u w → hgt u w ≤ hi →
      ξ < fwd u z → ξ < fwd u w := by
    intro z w hz hw hzl hzh hwl hwh hlt
    by_contra hcon
    push Not at hcon
    have hpos : 0 < fwd u z - fwd u w := by linarith
    set r := (fwd u z - ξ) / (fwd u z - fwd u w) with hr
    have hr0 : 0 ≤ r := div_nonneg (by linarith) hpos.le
    have hr1 : r ≤ 1 := (div_le_one hpos).2 (by linarith)
    have hy : z + r • (w - z) ∈ segment ℝ a b :=
      (convex_segment a b).segment_subset hz hw
        (by rw [segment_eq_image' ℝ z w]; exact ⟨r, ⟨hr0, hr1⟩, rfl⟩)
    refine hmiss _ hy ?_ ?_ ?_
    · rw [fwd_lin, hr]; field_simp <;> ring
    · rw [hgt_lin]
      linarith [mul_nonneg hr0 (sub_nonneg.2 hwl), mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hzl)]
    · rw [hgt_lin]
      linarith [mul_nonneg hr0 (sub_nonneg.2 hwh), mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hzh)]
  exact ⟨fun h => key z w hz hw hzl hzh hwl hwh h, fun h => key w z hw hz hwl hwh hzl hzh h⟩

/-- Moving the base point along the ray direction, without meeting the polygon, changes no
crossing. -/
theorem parity_move_along (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) {q : Plane} {s : ℝ}
    (hs : 0 ≤ s) (hmiss : ∀ y ∈ segment ℝ q (q + s • u), y ∉ cover L) :
    parity u L (q + s • u) = parity u L q := by
  refine congrArg List.sum (List.map_congr_left ?_)
  intro P hP
  have hPne := hL P hP
  have hiff : Crosses u P (q + s • u) ↔ Crosses u P q := by
    simp only [Crosses, hgt_along, fwd_along hu]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      by_contra hcon
      push Not at hcon
      exact hmiss _ (mem_segment_along hu hs (hgt_meet hPne _) h3.le hcon)
        (mem_cover hP (meet_mem_seg hPne h1 h2.le))
  simp only [mark, hiff]

end Moves

/-! ### Sweeping across the ray direction -/

/-- The marker attached to a vertex when the base point is swept across by `s`: the vertex
counts when its height lies in the half-open band swept out and it lies beyond the base
point. Summed over both ends of every edge this vanishes, because the polygon is closed;
that is the whole content of crossing parity. -/
noncomputable def fmark (u q : Plane) (s : ℝ) (v : Plane) : ZMod 2 :=
  if hgt u q < hgt u v ∧ hgt u v ≤ hgt u q + s ∧ fwd u q < fwd u v then 1 else 0

theorem mark_swap (h : hgt u a ≠ hgt u b) (q : Plane) : mark u (b, a) q = mark u (a, b) q := by
  simp only [mark, crosses_swap h]

section Across

variable (hu : Plane.IsDirection u)
include hu

/-- One edge, swept across. The crossings gained or lost are exactly the ends whose heights
the sweep passes, on the far side of the base point. -/
theorem mark_step {q : Plane} {s : ℝ} (hs : 0 ≤ s) (hab : hgt u a < hgt u b)
    (hmiss : ∀ y ∈ segment ℝ a b, fwd u y = fwd u q → hgt u q ≤ hgt u y →
      hgt u y ≤ hgt u q + s → False) :
    mark u (a, b) q + mark u (a, b) (q + s • Plane.perp u)
      = fmark u q s a + fmark u q s b := by
  have hne : hgt u a ≠ hgt u b := ne_of_lt hab
  have hha : ∀ t : ℝ, hgt u (meet u a b t) = t := fun t => hgt_meet hne t
  have hma : ∀ t : ℝ, hgt u a ≤ t → t ≤ hgt u b → meet u a b t ∈ segment ℝ a b :=
    fun t h1 h2 => meet_mem_segment hab h1 h2
  have haseg : a ∈ segment ℝ a b := left_mem_segment ℝ a b
  have hbseg : b ∈ segment ℝ a b := right_mem_segment ℝ a b
  have hside : ∀ z, z ∈ segment ℝ a b → ∀ w, w ∈ segment ℝ a b →
      hgt u q ≤ hgt u z → hgt u z ≤ hgt u q + s →
      hgt u q ≤ hgt u w → hgt u w ≤ hgt u q + s →
      (fwd u q < fwd u z ↔ fwd u q < fwd u w) :=
    fun z hz w hw h1 h2 h3 h4 => side_const hmiss hz hw h1 h2 h3 h4
  simp only [mark, fmark, Crosses, min_eq_left hab.le, max_eq_right hab.le,
    hgt_across hu, fwd_across]
  rcases le_or_gt (hgt u a) (hgt u q) with hA | hA
  · rcases lt_or_ge (hgt u q + s) (hgt u b) with hB | hB
    · -- the sweep stays strictly below the upper end: no end is passed
      have e := hside (meet u a b (hgt u q)) (hma _ hA (by linarith))
        (meet u a b (hgt u q + s)) (hma _ (by linarith) hB.le)
        (hha _).ge (by rw [hha]; linarith) (by rw [hha]; linarith) (hha _).le
      by_cases hD : fwd u q < fwd u (meet u a b (hgt u q))
      · rw [if_pos ⟨hA, by linarith, hD⟩, if_pos ⟨by linarith, hB, e.1 hD⟩,
          if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith)]
        decide
      · rw [if_neg (by rintro ⟨-, -, g⟩; exact hD g),
          if_neg (by rintro ⟨-, -, g⟩; exact hD (e.2 g)),
          if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith)]
    · rcases lt_or_ge (hgt u q) (hgt u b) with hB2 | hB2
      · -- the sweep passes the upper end
        have e := hside (meet u a b (hgt u q)) (hma _ hA hB2.le) b hbseg
          (hha _).ge (by rw [hha]; linarith) (by linarith) hB
        by_cases hD : fwd u q < fwd u (meet u a b (hgt u q))
        · rw [if_pos ⟨hA, hB2, hD⟩, if_neg (by rintro ⟨-, g, -⟩; linarith),
            if_neg (by rintro ⟨g, -, -⟩; linarith), if_pos ⟨hB2, hB, e.1 hD⟩]
          decide
        · rw [if_neg (by rintro ⟨-, -, g⟩; exact hD g),
            if_neg (by rintro ⟨-, g, -⟩; linarith),
            if_neg (by rintro ⟨g, -, -⟩; linarith),
            if_neg (by rintro ⟨-, -, g⟩; exact hD (e.2 g))]
      · -- the edge is entirely below the sweep
        rw [if_neg (by rintro ⟨-, g, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith),
          if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨g, -, -⟩; linarith)]
  · rcases le_or_gt (hgt u a) (hgt u q + s) with hA2 | hA2
    · rcases lt_or_ge (hgt u q + s) (hgt u b) with hB | hB
      · -- the sweep passes the lower end only
        have e := hside (meet u a b (hgt u q + s)) (hma _ hA2 hB.le) a haseg
          (by rw [hha]; linarith) (hha _).le (by linarith) hA2
        by_cases hD : fwd u q < fwd u a
        · rw [if_neg (by rintro ⟨g, -, -⟩; linarith), if_pos ⟨hA2, hB, e.2 hD⟩,
            if_pos ⟨hA, hA2, hD⟩, if_neg (by rintro ⟨-, g, -⟩; linarith)]
          decide
        · rw [if_neg (by rintro ⟨g, -, -⟩; linarith),
            if_neg (by rintro ⟨-, -, g⟩; exact hD (e.1 g)),
            if_neg (by rintro ⟨-, -, g⟩; exact hD g),
            if_neg (by rintro ⟨-, g, -⟩; linarith)]
      · -- the sweep passes both ends
        have e := hside a haseg b hbseg (by linarith) hA2 (by linarith) hB
        by_cases hD : fwd u q < fwd u a
        · rw [if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith),
            if_pos ⟨hA, hA2, hD⟩, if_pos ⟨by linarith, hB, e.1 hD⟩]
          decide
        · rw [if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith),
            if_neg (by rintro ⟨-, -, g⟩; exact hD g),
            if_neg (by rintro ⟨-, -, g⟩; exact hD (e.2 g))]
    · -- the edge is entirely above the sweep
      rw [if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨g, -, -⟩; linarith),
        if_neg (by rintro ⟨-, g, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith)]

/-- Sweeping the base point across the ray direction, without meeting the polygon, does not
change the parity. This is where the polygon has to be closed. -/
theorem parity_move_across (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (hC : IsClosedChain L)
    {q : Plane} {s : ℝ} (hs : 0 ≤ s)
    (hmiss : ∀ y ∈ segment ℝ q (q + s • Plane.perp u), y ∉ cover L) :
    parity u L (q + s • Plane.perp u) = parity u L q := by
  have key : ∀ P ∈ L, mark u P q + mark u P (q + s • Plane.perp u)
      = fmark u q s P.1 + fmark u q s P.2 := by
    intro P hP
    obtain ⟨a, b⟩ := P
    have hne := hL (a, b) hP
    have hmiss' : ∀ y ∈ segment ℝ a b, fwd u y = fwd u q → hgt u q ≤ hgt u y →
        hgt u y ≤ hgt u q + s → False := fun y hy h1 h2 h3 =>
      hmiss y (mem_segment_across hu hs h1 h2 h3) (mem_cover hP hy)
    rcases lt_or_gt_of_ne hne with h | h
    · exact mark_step hu hs h hmiss'
    · have hmiss'' : ∀ y ∈ segment ℝ b a, fwd u y = fwd u q → hgt u q ≤ hgt u y →
          hgt u y ≤ hgt u q + s → False := by
        intro y hy
        exact hmiss' y (by rwa [segment_symm] at hy)
      have hstep := mark_step hu hs h hmiss''
      rw [mark_swap hne, mark_swap hne] at hstep
      rw [hstep]
      exact add_comm _ _
  have hzero : parity u L q + parity u L (q + s • Plane.perp u) = 0 := by
    rw [parity, parity, ← sum_map_add, List.map_congr_left key]
    exact hC (fun v => fmark u q s v)
  have harith : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
  exact harith _ _ hzero

/-- The two moves, for a shift of either sign. -/
theorem parity_move_along' (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) {q q' : Plane} (s : ℝ)
    (hq' : q' = q + s • u) (hmiss : ∀ y ∈ segment ℝ q q', y ∉ cover L) :
    parity u L q' = parity u L q := by
  rcases le_or_gt 0 s with hs | hs
  · subst hq'; exact parity_move_along hu hL hs hmiss
  · have hq : q = q' + (-s) • u := by rw [hq', neg_smul, add_neg_cancel_right]
    have hmiss' : ∀ y ∈ segment ℝ q' (q' + (-s) • u), y ∉ cover L := by
      intro y hy
      rw [← hq] at hy
      exact hmiss y (by rwa [segment_symm] at hy)
    have hmove := parity_move_along hu hL (by linarith : (0:ℝ) ≤ -s) hmiss'
    rw [← hq] at hmove
    exact hmove.symm

theorem parity_move_across' (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (hC : IsClosedChain L)
    {q q' : Plane} (s : ℝ) (hq' : q' = q + s • Plane.perp u)
    (hmiss : ∀ y ∈ segment ℝ q q', y ∉ cover L) :
    parity u L q' = parity u L q := by
  rcases le_or_gt 0 s with hs | hs
  · subst hq'; exact parity_move_across hu hL hC hs hmiss
  · have hq : q = q' + (-s) • Plane.perp u := by rw [hq', neg_smul, add_neg_cancel_right]
    have hmiss' : ∀ y ∈ segment ℝ q' (q' + (-s) • Plane.perp u), y ∉ cover L := by
      intro y hy
      rw [← hq] at hy
      exact hmiss y (by rwa [segment_symm] at hy)
    have hmove := parity_move_across hu hL hC (by linarith : (0:ℝ) ≤ -s) hmiss'
    rw [← hq] at hmove
    exact hmove.symm

end Across

/-! ### Crossing parity -/

theorem exists_ball_avoiding {z : Plane} (h : z ∉ cover L) :
    ∃ ε > 0, ∀ y ∈ ball z ε, y ∉ cover L := by
  have hopen := (isClosed_cover L).isOpen_compl
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε, hsub⟩ := hopen z h
  exact ⟨ε, hε, fun y hy => hsub hy⟩

section Constancy

variable (hu : Plane.IsDirection u)
include hu

/-- The parity is constant on a ball that misses the polygon: reach any nearby point by a
move along the ray direction followed by a move across it. -/
theorem parity_eq_of_mem_ball (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (hC : IsClosedChain L)
    {q q' : Plane} {ε : ℝ} (hq' : q' ∈ ball q ε) (hmiss : ∀ y ∈ ball q ε, y ∉ cover L) :
    parity u L q' = parity u L q := by
  have hεpos : 0 < ε := lt_of_le_of_lt dist_nonneg (mem_ball.1 hq')
  have hqb : q ∈ ball q ε := mem_ball_self hεpos
  obtain ⟨w, hw⟩ : ∃ w : Plane, w = q + (fwd u (q' - q)) • u := ⟨_, rfl⟩
  have hwball : w ∈ ball q ε := by
    have hsub : q + (fwd u (q' - q)) • u - q = (fwd u (q' - q)) • u := by abel
    rw [mem_ball, dist_eq_norm, hw, hsub, norm_smul, Real.norm_eq_abs, hu, mul_one]
    calc |fwd u (q' - q)| ≤ ‖q' - q‖ := abs_fwd_le_norm hu _
      _ = dist q' q := (dist_eq_norm q' q).symm
      _ < ε := mem_ball.1 hq'
  have hq'w : q' = w + (hgt u (q' - q)) • Plane.perp u := by
    have hd := decomp hu (q' - q)
    rw [hw, add_assoc, ← hd]
    abel
  have h1 : parity u L w = parity u L q :=
    parity_move_along' hu hL _ hw
      (fun y hy => hmiss y ((convex_ball q ε).segment_subset hqb hwball hy))
  have h2 : parity u L q' = parity u L w :=
    parity_move_across' hu hL hC _ hq'w
      (fun y hy => hmiss y ((convex_ball q ε).segment_subset hwball hq' hy))
  rw [h2, h1]

/-- **Crossing parity** (Lemma 2.2). `π_C` is constant on every preconnected subset of the
complement of the polygon — in particular on every component. -/
theorem parity_eq_of_isPreconnected (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2)
    (hC : IsClosedChain L) {S : Set Plane} (hS : IsPreconnected S)
    (hSC : ∀ z ∈ S, z ∉ cover L) {x y : Plane} (hx : x ∈ S) (hy : y ∈ S) :
    parity u L x = parity u L y := by
  by_contra hne
  have hopen : ∀ c : ZMod 2, IsOpen {z : Plane | z ∉ cover L ∧ parity u L z = c} := by
    intro c
    rw [Metric.isOpen_iff]
    rintro z ⟨hz1, hz2⟩
    obtain ⟨ε, hε, hball⟩ := exists_ball_avoiding hz1
    exact ⟨ε, hε, fun t ht => ⟨hball t ht,
      by rw [parity_eq_of_mem_ball hu hL hC ht hball, hz2]⟩⟩
  have htwo : ∀ e : ZMod 2, e = parity u L x ∨ e = parity u L y := by
    revert hne
    generalize parity u L x = c
    generalize parity u L y = d
    revert c d
    decide
  obtain ⟨z, -, hzA, hzB⟩ :=
    hS _ _ (hopen (parity u L x)) (hopen (parity u L y))
      (fun t ht => (htwo (parity u L t)).imp (fun h => ⟨hSC t ht, h⟩) (fun h => ⟨hSC t ht, h⟩))
      ⟨x, hx, hSC x hx, rfl⟩ ⟨y, hy, hSC y hy, rfl⟩
  exact hne (hzA.2 ▸ hzB.2)

/-- The parity is constant on the component of the complement containing a point. -/
theorem parity_eq_of_mem_connectedComponentIn (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2)
    (hC : IsClosedChain L) {x y : Plane} (hx : x ∉ cover L)
    (hy : y ∈ connectedComponentIn (cover L)ᶜ x) : parity u L y = parity u L x :=
  parity_eq_of_isPreconnected hu hL hC isPreconnected_connectedComponentIn
    (fun _ ht => connectedComponentIn_subset _ _ ht) hy (mem_connectedComponentIn hx)

end Constancy

/-! ### The value far along the ray, and the jump across an edge -/

/-- Beyond the polygon in the ray direction the count is zero. -/
theorem parity_eq_zero_of_lt (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) {q : Plane}
    (h : ∀ z ∈ cover L, fwd u z < fwd u q) : parity u L q = 0 := by
  refine List.sum_eq_zero ?_
  intro x hx
  obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
  refine if_neg ?_
  rintro ⟨h1, h2, h3⟩
  exact absurd (h _ (mem_cover hP (meet_mem_seg (hL P hP) h1 h2.le))) (not_lt.2 h3.le)

section Flip

variable (hu : Plane.IsDirection u)
include hu

/-- **Opposite sides of an edge** (Lemma 2.2, second half). At an interior point `p` of one
edge of the list which no other edge of the list passes through, the two points just before
and just after `p` in the ray direction lie off the polygon and have opposite parity: the
count changes by one as the base point sweeps across the edge. -/
theorem parity_flip {L₁ L₂ : List Piece} {a b p : Plane}
    (hL : ∀ P ∈ L₁ ++ (a, b) :: L₂, hgt u P.1 ≠ hgt u P.2)
    (hp : p ∈ openSegment ℝ a b) (h1 : p ∉ cover L₁) (h2 : p ∉ cover L₂) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      p - t • u ∉ cover (L₁ ++ (a, b) :: L₂) ∧
      p + t • u ∉ cover (L₁ ++ (a, b) :: L₂) ∧
      parity u (L₁ ++ (a, b) :: L₂) (p - t • u)
        = parity u (L₁ ++ (a, b) :: L₂) (p + t • u) + 1 := by
  have hab : hgt u a ≠ hgt u b := hL (a, b) (by simp)
  have hpK : p ∉ cover (L₁ ++ L₂) := by
    rw [cover_append]
    rintro (h | h)
    · exact h1 h
    · exact h2 h
  obtain ⟨ε, hε, hball⟩ := exists_ball_avoiding hpK
  refine ⟨ε, hε, fun t ht htε => ?_⟩
  -- the two test points and their frame coordinates
  have hneg : p - t • u = p + (-t) • u := by rw [neg_smul]; abel
  have hgm : hgt u (p - t • u) = hgt u p := by rw [hneg, hgt_along]
  have hgp : hgt u (p + t • u) = hgt u p := hgt_along p t
  have hfm : fwd u (p - t • u) = fwd u p - t := by rw [hneg, fwd_along hu]; ring
  have hfp : fwd u (p + t • u) = fwd u p + t := fwd_along hu p t
  have hdist : ∀ r : ℝ, |r| < ε → p + r • u ∈ ball p ε := by
    intro r hr
    have hsub : p + r • u - p = r • u := by abel
    rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, hu, mul_one]
    exact hr
  have habsm : |(-t)| < ε := by rw [abs_neg, abs_of_pos ht]; exact htε
  have habsp : |t| < ε := by rw [abs_of_pos ht]; exact htε
  -- the only point of the edge at the height of `p` is `p` itself
  have hpseg : p ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hp
  have hmeetp : meet u a b (hgt u p) = p := (eq_meet hab hpseg).symm
  have hnotseg : ∀ r : ℝ, r ≠ 0 → p + r • u ∉ segment ℝ a b := by
    intro r hr hmem
    have heq : p + r • u = p := by
      rw [eq_meet hab hmem, hgt_along, hmeetp]
    have hf : fwd u (p + r • u) = fwd u p + r := fwd_along hu p r
    rw [heq] at hf
    exact hr (by linarith)
  have hcov : ∀ r : ℝ, r ≠ 0 → |r| < ε → p + r • u ∉ cover (L₁ ++ (a, b) :: L₂) := by
    intro r hr hrε hmem
    rw [cover_append, cover_cons] at hmem
    rcases hmem with h | h | h
    · exact hball _ (hdist r hrε) (by rw [cover_append]; exact Or.inl h)
    · exact hnotseg r hr h
    · exact hball _ (hdist r hrε) (by rw [cover_append]; exact Or.inr h)
  -- an edge other than `(a, b)` meets the level line far from `p`, so it is not affected
  have hfar : ∀ P ∈ L₁ ++ L₂, hgt u P.1 ≠ hgt u P.2 →
      min (hgt u P.1) (hgt u P.2) ≤ hgt u p → hgt u p ≤ max (hgt u P.1) (hgt u P.2) →
      ε ≤ |fwd u (meet u P.1 P.2 (hgt u p)) - fwd u p| := by
    intro P hP hPne g1 g2
    have hmcov : meet u P.1 P.2 (hgt u p) ∈ cover (L₁ ++ L₂) :=
      mem_cover hP (meet_mem_seg hPne g1 g2)
    have hmnb : ¬ (dist (meet u P.1 P.2 (hgt u p)) p < ε) := fun h =>
      hball _ (mem_ball.2 h) hmcov
    push Not at hmnb
    rw [dist_eq_norm] at hmnb
    have hh : hgt u (meet u P.1 P.2 (hgt u p) - p) = 0 := by
      rw [hgt_sub, hgt_meet hPne]; ring
    have hd := decomp hu (meet u P.1 P.2 (hgt u p) - p)
    rw [hh, zero_smul, add_zero] at hd
    have hnorm : ‖meet u P.1 P.2 (hgt u p) - p‖
        = |fwd u (meet u P.1 P.2 (hgt u p) - p)| := by
      conv_lhs => rw [hd]
      rw [norm_smul, Real.norm_eq_abs, hu, mul_one]
    rw [hnorm, fwd_sub] at hmnb
    exact hmnb
  have hother : ∀ P ∈ L₁ ++ L₂, mark u P (p - t • u) + mark u P (p + t • u) = 0 := by
    intro P hP
    have hPne : hgt u P.1 ≠ hgt u P.2 := by
      rcases List.mem_append.1 hP with h | h
      · exact hL P (by simp [h])
      · exact hL P (by simp [h])
    have hiff : Crosses u P (p - t • u) ↔ Crosses u P (p + t • u) := by
      simp only [Crosses, hgm, hgp, hfm, hfp]
      constructor
      · rintro ⟨g1, g2, g3⟩
        refine ⟨g1, g2, ?_⟩
        rcases le_abs.1 (hfar P hP hPne g1 g2.le) with hcase | hcase
        · linarith
        · linarith
      · rintro ⟨g1, g2, g3⟩
        exact ⟨g1, g2, by linarith⟩
    simp only [mark, hiff]
    exact add_self_zmod_two _
  -- the edge `(a, b)` itself is crossed from exactly one of the two points
  have hbtw : min (hgt u a) (hgt u b) < hgt u p ∧ hgt u p < max (hgt u a) (hgt u b) := by
    rcases lt_or_gt_of_ne hab with h | h
    · obtain ⟨g1, g2⟩ := hgt_lt_of_mem_openSegment h hp
      rw [min_eq_left h.le, max_eq_right h.le]
      exact ⟨g1, g2⟩
    · obtain ⟨g1, g2⟩ := hgt_lt_of_mem_openSegment h (by rwa [openSegment_symm] at hp)
      rw [min_eq_right h.le, max_eq_left h.le]
      exact ⟨g1, g2⟩
  have hedge : mark u (a, b) (p - t • u) + mark u (a, b) (p + t • u) = 1 := by
    have hm1 : Crosses u (a, b) (p - t • u) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hgm]; exact hbtw.1.le
      · rw [hgm]; exact hbtw.2
      · rw [hgm, hfm, hmeetp]; linarith
    have hm2 : ¬ Crosses u (a, b) (p + t • u) := by
      rintro ⟨-, -, g⟩
      rw [hgp, hfp, hmeetp] at g
      linarith
    rw [mark, mark, if_pos hm1, if_neg hm2, add_zero]
  refine ⟨by rw [hneg]; exact hcov (-t) (by linarith) habsm, hcov t (ne_of_gt ht) habsp, ?_⟩
  have hz1 : (L₁.map (fun P => mark u P (p - t • u) + mark u P (p + t • u))).sum = 0 := by
    refine List.sum_eq_zero ?_
    intro x hx
    obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
    exact hother P (List.mem_append_left _ hP)
  have hz2 : (L₂.map (fun P => mark u P (p - t • u) + mark u P (p + t • u))).sum = 0 := by
    refine List.sum_eq_zero ?_
    intro x hx
    obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
    exact hother P (List.mem_append_right _ hP)
  have hsum : parity u (L₁ ++ (a, b) :: L₂) (p - t • u)
      + parity u (L₁ ++ (a, b) :: L₂) (p + t • u) = 1 := by
    rw [parity, parity, ← sum_map_add, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, hz1, hz2, hedge]
    ring
  have harith : ∀ x y : ZMod 2, x + y = 1 → x = y + 1 := by decide
  exact harith _ _ hsum

end Flip

/-! ### Choosing the ray direction -/

/-- The blueprint's opening move — "rotate so that no edge is horizontal" — without rotating
anything: finitely many edge directions rule out only finitely many rays, so some direction
is level for none of them. -/
theorem exists_direction_hgt_ne (L : List Piece) (hnd : ∀ P ∈ L, P.Nondeg) :
    ∃ u : Plane, Plane.IsDirection u ∧ ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2 := by
  obtain ⟨u, hu, hdet⟩ :=
    Plane.exists_isDirection_det_ne_zero (L.finite_toSet.image (fun P : Piece => P.2 - P.1))
  refine ⟨u, hu, fun P hP heq => ?_⟩
  have hne : P.2 - P.1 ≠ 0 := sub_ne_zero.2 fun h => hnd P hP h.symm
  have hzero : hgt u (P.2 - P.1) = 0 := by rw [hgt_sub, heq]; ring
  exact hdet _ ⟨P, hP, rfl⟩ hne hzero

end Schoenflies
end

section
-- module Solutions.Q146_CD.UniformBound
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# One positive bound for finitely many

Every "choose `ε` small enough for all of them" step in the development is this lemma: a
finite family of positive bounds has a single positive bound below all of them. The
polygonal-redrawing argument alone uses it three times, and the two-sided strip lemma chooses
its vertex disks and edge blocks the same way.

It is stated for a *predicate that is monotone downward in the bound* rather than as a `min`
fold, because no consumer wants the value — only that some positive value works for every
member at once.

## Blueprint

* `exists_pos_le_of_finite` — the numerical form.
* `exists_pos_forall_of_finite` — the form consumers use: a downward-monotone predicate
  holding at some positive bound for each member holds at one common positive bound.
-/

open Set

namespace Schoenflies

variable {ι : Type*}

/-- A finite family of positive reals is bounded below by a positive real. -/
theorem exists_pos_le_of_finite {S : Set ι} (hS : S.Finite) {f : ι → ℝ}
    (hf : ∀ i ∈ S, 0 < f i) : ∃ ε > 0, ∀ i ∈ S, ε ≤ f i := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a S ha hS ih =>
    obtain ⟨ε, hε, hbound⟩ := ih fun i hi => hf i (mem_insert_of_mem _ hi)
    refine ⟨min ε (f a), lt_min hε (hf a (mem_insert _ _)), fun i hi => ?_⟩
    rcases mem_insert_iff.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (hbound i hi)

/-- The form the geometry uses: if a property that only gets easier as the bound shrinks holds
at *some* positive bound for each member of a finite family, then it holds at *one* positive
bound for all of them at once. -/
theorem exists_pos_forall_of_finite {S : Set ι} (hS : S.Finite) {P : ι → ℝ → Prop}
    (hmono : ∀ i, ∀ ⦃δ ε : ℝ⦄, 0 < δ → δ ≤ ε → P i ε → P i δ)
    (hex : ∀ i ∈ S, ∃ ε > 0, P i ε) :
    ∃ ε > 0, ∀ i ∈ S, P i ε := by
  classical
  -- Pick a witness for each member, then take a positive bound below all the witnesses.
  choose! f hfpos hfP using hex
  obtain ⟨ε, hε, hbound⟩ := exists_pos_le_of_finite hS (f := f) hfpos
  exact ⟨ε, hε, fun i hi => hmono i hε (hbound i hi) (hfP i hi)⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.Strip
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.poly_cons_cons _root_.Schoenflies.poly_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.poly_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Two-sided polygonal strips

This module builds the *collar* of Lemma 1.8: an open neighbourhood `N` of a simple closed
polygon `P` whose complement in `N` splits into two connected open sets, the two local sides.

The blueprint's construction is "a small closed disk about every vertex, a thin rectangular
block about every edge, chosen so that consecutive blocks overlap and nonadjacent closures are
disjoint". The blocks here are

* `Plane.cone v A R` — the open sector of radius `R` about a vertex `v` cut out by an arc `A`
  of directions, and
* `Plane.strip a u t₁ t₂ s₁ s₂` — the open rectangle around a directed edge, written in the
  edge's own coordinates `t = ⟪u, x - a⟫` (along) and `s = det u (x - a)` (across).

Everything about the *side matching at a vertex* comes from `Schoenflies/Direction.lean`
through the orientation form; no angle is named. The one new direction fact needed here is the
sign-free repackaging `Plane.germs_split'`: the blueprint's `germs_split` assumes
`0 < det r₁ r₂`, but a polygon turns both ways, and it turns out that *which* named arc carries
the left germs does not depend on the sense of the turn — it is always `arcCCW r₂ r₁`. Only the
side of the smallness hypothesis moves.

## The constants

The blueprint says "the blocks may be chosen so that consecutive edge and vertex blocks overlap
in the prescribed small rectangles around the radial segments, while the closures of all
nonadjacent blocks are disjoint" without naming the constants. `Schoenflies.StripData` names
them: a cone radius `R`, a trim `lam` by which each edge block stops short of its endpoints, and
a half-width `rho`. They should be chosen in this order (this is the recipe the unproved
`exists_stripData` has to follow):

1. `R` from the vertex separations, from the distance of each vertex to the nonincident edges
   (with a factor `2` of slack, spent in `dist_core_vertex`), and from the prescribed open set;
2. `lam := R / 5`, which makes `2 * lam < R` (the cones reach past the ends of the blocks they
   must overlap) and `4 * lam < ‖edge‖` (the blocks are nonempty);
3. `rho` from the distance of each trimmed edge to the other edges, and from the *germ
   threshold* `rho * (1 + |⟪r₁, r₂⟫|) ≤ lam * |det r₁ r₂|` at every vertex — this last is the
   quantitative form of "make the strips narrow enough that this side matching holds in every
   vertex disk", and it is the only inequality in the list that is not a separation of compact
   sets.

## Blueprint

* `Plane.germs_split'` — the sign-free vertex matching inside Lemma 1.8.
* `Schoenflies.ClosedPolygon` — a simple closed polygonal curve presented by its cyclic vertex
  list.
* `Schoenflies.StripData` — the choice of constants, as a hypothesis.
* `Schoenflies.StripData.sideL`, `.sideR`, `.nbhd`, `.sideL_disjoint_sideR` — the two labelled
  sides of the collar, and that they are disjoint.

## Where the rest of Lemma 1.8 lives

This module builds the apparatus and proves the hard half: the germ matching at a corner and
the disjointness of the two labelled sides. The other two obligations are discharged next door,
and were split out only because they were built concurrently:

* `Schoenflies/StripConstants.lean` — `exists_stripData` and `exists_stripData_subset`, which
  produce the constants, the latter with the collar inside a prescribed open set.
* `Schoenflies/StripConnected.lean` — that each side is connected, and
  `nbhd \ carrier = sideL ∪ sideR`.

`Schoenflies.polygonal_collar` in `Schoenflies/Compose.lean` is the three composed into the
blueprint's Lemma 1.8 (a). `ClosedPolygon.collar` below is a *definition*, not the theorem.

What is still missing from Lemma 1.8 as a whole: the **local two-sidedness** clause (every
sufficiently small disk about a point of the curve meets the complement in exactly two
components, one in each side), and part **(b)**, the arc case.
-/

open Metric Set

namespace Schoenflies

namespace Plane

variable {u w d r₁ r₂ a x : Plane} {r t s c ρ : ℝ}

/-! ### A sign-free vertex matching

`Plane.germs_split` fixes the orientation with `0 < det r₁ r₂`. A polygon turns both ways, so
the collar needs the statement without that hypothesis. The content of the repackaging is that
the *conclusion* does not move: the two left germs always land on `arcCCW r₂ r₁` and the two
right germs on `arcCCW r₁ r₂`. What moves is which pair needs the smallness hypothesis, so the
sign-free form simply imposes it on both, with absolute values. -/

/-- **The vertex matching, sign-free.** With `r₁` the ray back along the incoming edge and `r₂`
the ray out along the outgoing edge, the two *left* half-strip germs lie on `arcCCW r₂ r₁` and
the two *right* ones on `arcCCW r₁ r₂`, whichever way the polygon turns. The hypothesis
`s * |⟪r₁, r₂⟫| < t * |det r₁ r₂|` is the blueprint's "`s/t` small", written without a division
and without a sign. -/
theorem germs_split' (h : det r₁ r₂ ≠ 0) (hs : 0 < s)
    (hsmall : s * |inner ℝ r₁ r₂| < t * |det r₁ r₂|) :
    (t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ ∧ t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁) ∧
      (t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ ∧ t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂) := by
  have hle : inner ℝ r₁ r₂ ≤ |inner ℝ r₁ r₂| := le_abs_self _
  have hle' : inner ℝ r₂ r₁ ≤ |inner ℝ r₁ r₂| := by
    rw [real_inner_comm]; exact hle
  rcases lt_or_gt_of_ne h with hneg | hpos
  · -- The turn is the other way: exchange the roles of the two rays in `germs_split`.
    have h' : 0 < det r₂ r₁ := by rw [det_comm r₂ r₁]; linarith
    have habs : |det r₁ r₂| = det r₂ r₁ := by rw [abs_of_neg hneg, det_comm r₁ r₂]; ring
    have hsmall' : s * inner ℝ r₂ r₁ < t * det r₂ r₁ := by
      rw [habs] at hsmall
      nlinarith
    have H := germs_split h' hs hsmall'
    exact ⟨⟨H.2.2, H.2.1⟩, ⟨H.1.2, H.1.1⟩⟩
  · have habs : |det r₁ r₂| = det r₁ r₂ := abs_of_pos hpos
    have hsmall' : s * inner ℝ r₁ r₂ < t * det r₁ r₂ := by
      rw [habs] at hsmall
      nlinarith
    exact germs_split hpos hs hsmall'

/-! ### The two arcs, without a sign hypothesis -/

/-- The two rays and the two arcs exhaust the nonzero vectors, whichever the sign of
`det r₁ r₂`. -/
theorem mem_ray_or_mem_arcCCW' (h : det r₁ r₂ ≠ 0) (hd : d ≠ 0) :
    (∃ c : ℝ, 0 < c ∧ d = c • r₁) ∨ (∃ c : ℝ, 0 < c ∧ d = c • r₂) ∨
      d ∈ arcCCW r₁ r₂ ∨ d ∈ arcCCW r₂ r₁ := by
  rcases lt_or_gt_of_ne h with hneg | hpos
  · have h' : 0 < det r₂ r₁ := by rw [det_comm r₂ r₁]; linarith
    rcases mem_ray_or_mem_arcCCW h' hd with h1 | h1 | h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inr h1))
    · exact Or.inr (Or.inr (Or.inl h1))
  · exact mem_ray_or_mem_arcCCW hpos hd

/-- A nonnegative multiple of a bounding ray lies on neither arc: the arcs are *open*, and `0`
is on neither. This is what keeps the two incident edges out of the vertex sectors. -/
theorem notMem_arcCCW_smul (u w : Plane) (hc : 0 ≤ c) :
    c • u ∉ arcCCW u w ∧ c • u ∉ arcCCW w u := by
  have e1 : det u (c • u) = 0 := by rw [det_smul_right, det_self, mul_zero]
  have e2 : det (c • u) u = 0 := by rw [det_smul_left, det_self, mul_zero]
  have e3 : det (c • u) w = c * det u w := det_smul_left _ _ _
  have e4 : det w (c • u) = c * det w u := det_smul_right _ _ _
  have e5 : det w u = -det u w := det_comm w u
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨_, h2⟩)
    · rw [e1] at h1; exact lt_irrefl 0 h1
    · rw [e3] at h1; rw [e5] at h2; nlinarith
    · rw [e1] at h2; exact lt_irrefl 0 h2
  · rintro (⟨_, h2⟩ | ⟨h2, _⟩ | ⟨h1, h2⟩)
    · rw [e2] at h2; exact lt_irrefl 0 h2
    · rw [e2] at h2; exact lt_irrefl 0 h2
    · rw [e4, e5] at h2; nlinarith

/-- Half-spaces through the origin are convex; `det u ·` is linear. -/
theorem isLinearMap_det_right (u : Plane) : IsLinearMap ℝ fun d : Plane => det u d :=
  ⟨fun x y => det_add_right u x y, fun c x => by rw [det_smul_right, smul_eq_mul]⟩

theorem isLinearMap_det_left (w : Plane) : IsLinearMap ℝ fun d : Plane => det d w :=
  ⟨fun x y => det_add_left x y w, fun c x => by rw [det_smul_left, smul_eq_mul]⟩

theorem convex_det_right_pos (u : Plane) : Convex ℝ {d : Plane | 0 < det u d} :=
  convex_halfSpace_gt (isLinearMap_det_right u) 0

theorem convex_det_right_neg (u : Plane) : Convex ℝ {d : Plane | det u d < 0} :=
  convex_halfSpace_lt (isLinearMap_det_right u) 0

theorem convex_det_left_pos (w : Plane) : Convex ℝ {d : Plane | 0 < det d w} :=
  convex_halfSpace_gt (isLinearMap_det_left w) 0

theorem convex_det_left_neg (w : Plane) : Convex ℝ {d : Plane | det d w < 0} :=
  convex_halfSpace_lt (isLinearMap_det_left w) 0

/-- An arc met with a ball about the origin is connected. When the arc is the short one it is an
intersection of two half-planes, hence convex; when it is the long one it is a *union* of two
half-planes, and `-(u + w)` lies in both. -/
theorem isConnected_arcCCW_ball (h : det u w ≠ 0) (hρ : 0 < ρ) :
    IsConnected (arcCCW u w ∩ ball (0 : Plane) ρ) := by
  -- A scaling factor small enough to put the witness inside the ball.
  have hne : u + w ≠ 0 := by
    intro hz
    have hw : w = -u := by linear_combination (norm := module) hz
    rw [hw, show (-u : Plane) = (-1 : ℝ) • u by module, det_smul_right, det_self,
      mul_zero] at h
    exact h rfl
  have hnpos : 0 < ‖u + w‖ := norm_pos_iff.2 hne
  obtain ⟨ε, hε, hεball⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * ‖u + w‖ < ρ := by
    refine ⟨ρ / (2 * ‖u + w‖), by positivity, ?_⟩
    have : ρ / (2 * ‖u + w‖) * ‖u + w‖ = ρ / 2 := by field_simp
    rw [this]; linarith
  have hball : ∀ σ : ℝ, |σ| = ε → σ • (u + w) ∈ ball (0 : Plane) ρ := by
    intro σ hσ
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, hσ]
    exact hεball
  rcases lt_or_gt_of_ne h with hneg | hpos
  · -- The long arc: `{det w d < 0} ∪ {det d u < 0}`, glued at `-(u + w)`.
    have h' : 0 < det w u := by rw [det_comm w u]; linarith
    have harc : arcCCW u w = {d : Plane | det w d < 0} ∪ {d : Plane | det d u < 0} := by
      ext d
      rw [mem_arcCCW_rev_iff h']
      simp only [mem_union, mem_setOf_eq]
    have hd0 : (-ε) • (u + w) ∈ ball (0 : Plane) ρ :=
      hball _ (by rw [abs_of_neg (neg_neg_iff_pos.2 hε), neg_neg])
    have hA : (-ε) • (u + w) ∈ {d : Plane | det w d < 0} := by
      change det w ((-ε) • (u + w)) < 0
      rw [det_smul_right, det_add_right, det_self, add_zero]
      nlinarith
    have hB : (-ε) • (u + w) ∈ {d : Plane | det d u < 0} := by
      change det ((-ε) • (u + w)) u < 0
      rw [det_smul_left, det_add_left, det_self, zero_add]
      nlinarith
    refine ⟨⟨_, by rw [harc]; exact ⟨Or.inl hA, hd0⟩⟩, ?_⟩
    rw [harc, union_inter_distrib_right]
    exact IsPreconnected.union _ ⟨hA, hd0⟩ ⟨hB, hd0⟩
      ((convex_det_right_neg w).inter (convex_ball _ _)).isPreconnected
      ((convex_det_left_neg u).inter (convex_ball _ _)).isPreconnected
  · -- The short arc: an intersection of two half-planes, hence convex.
    have harc : arcCCW u w = {d : Plane | 0 < det u d} ∩ {d : Plane | 0 < det d w} := by
      ext d
      rw [mem_arcCCW_iff hpos]
      simp only [mem_inter_iff, mem_setOf_eq]
    have hmem : ε • (u + w) ∈ arcCCW u w ∩ ball (0 : Plane) ρ := by
      refine ⟨?_, hball _ (abs_of_pos hε)⟩
      rw [harc]
      constructor
      · change 0 < det u (ε • (u + w))
        rw [det_smul_right, det_add_right, det_self, zero_add]
        positivity
      · change 0 < det (ε • (u + w)) w
        rw [det_smul_left, det_add_left, det_self, add_zero]
        positivity
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [harc]
    exact (((convex_det_right_pos u).inter (convex_det_left_pos w)).inter
      (convex_ball _ _)).isPreconnected

/-! ### Vertex sectors

The "small closed disk about a vertex" of the blueprint is replaced by an open *sector*: the
part of a ball about the vertex lying in a prescribed arc of directions. The two sectors cut out
by the two arcs are exactly the two components of the ball minus the two incident radial
segments, which is what makes the labelling at a vertex well defined. -/

/-- The open sector of radius `ρ` about `v` spanned by the set `A` of directions. -/
def cone (v : Plane) (A : Set Plane) (ρ : ℝ) : Set Plane := {x | x - v ∈ A} ∩ ball v ρ

theorem cone_subset_ball {v : Plane} {A : Set Plane} : cone v A ρ ⊆ ball v ρ := inter_subset_right

/-- A sector is the translate of an arc met with a ball at the origin, so it inherits its
connectedness from `Plane.isConnected_arcCCW_ball`. -/
theorem cone_eq_image (v : Plane) (A : Set Plane) (ρ : ℝ) :
    cone v A ρ = (fun d => v + d) '' (A ∩ ball (0 : Plane) ρ) := by
  ext y
  constructor
  · rintro ⟨hy, hb⟩
    refine ⟨y - v, ⟨hy, ?_⟩, ?_⟩
    · rw [mem_ball, dist_zero_right, ← dist_eq_norm]
      exact hb
    · change v + (y - v) = y
      module
  · rintro ⟨d, ⟨hd, hb⟩, rfl⟩
    have he : v + d - v = d := by module
    refine ⟨by rw [mem_setOf_eq, he]; exact hd, ?_⟩
    rw [mem_ball, dist_eq_norm, he]
    rw [mem_ball, dist_zero_right] at hb
    exact hb

theorem isConnected_cone_arcCCW (v : Plane) (h : det u w ≠ 0) (hρ : 0 < ρ) :
    IsConnected (cone v (arcCCW u w) ρ) := by
  rw [cone_eq_image]
  have hc : Continuous fun d : Plane => v + d := continuous_const.add continuous_id
  exact (isConnected_arcCCW_ball h hρ).image _ hc.continuousOn

/-! ### Edge blocks

The block around a directed edge is described in the edge's own frame: `coordAlong` is the
progress along the edge and `coordAcross` the signed distance to its line. Both are affine, so
the block is an intersection of four open half-planes — open and convex at a glance. -/

/-- Progress along the directed edge that starts at `a` with unit tangent `u`. -/
noncomputable def coordAlong (a u x : Plane) : ℝ := inner ℝ u (x - a)

/-- Signed distance from `x` to the line of the directed edge that starts at `a` with unit
tangent `u`; positive on the left. -/
def coordAcross (a u x : Plane) : ℝ := det u (x - a)

/-- The orientation form is the inner product against the turned vector. -/
theorem det_eq_inner_perp (u v : Plane) : det u v = inner ℝ (perp u) v := by
  rw [inner_eq, det]
  simp [perp]
  ring

theorem abs_det_le (u v : Plane) : |det u v| ≤ ‖u‖ * ‖v‖ := by
  rw [det_eq_inner_perp]
  calc |inner ℝ (perp u) v| ≤ ‖perp u‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ = ‖u‖ * ‖v‖ := by rw [norm_perp]

@[simp] theorem coordAlong_param (hu : IsDirection u) (a : Plane) (t s : ℝ) :
    coordAlong a u (a + t • u + s • perp u) = t := by
  have h : a + t • u + s • perp u - a = t • u + s • perp u := by module
  rw [coordAlong, h, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, inner_perp_self, hu.norm]
  ring

@[simp] theorem coordAcross_param (hu : IsDirection u) (a : Plane) (t s : ℝ) :
    coordAcross a u (a + t • u + s • perp u) = s := by
  have h : a + t • u + s • perp u - a = t • u + s • perp u := by module
  rw [coordAcross, h, det_germ_self, hu.norm]
  ring

/-- The frame is complete: every point is recovered from its two coordinates. -/
theorem frame_decomp (hu : IsDirection u) (a x : Plane) :
    x = a + (coordAlong a u x) • u + (coordAcross a u x) • perp u := by
  have hnorm : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have := hu.norm
    rw [EuclideanSpace.norm_eq] at this
    have h2 : Real.sqrt (∑ i, ‖u i‖ ^ 2) ^ 2 = 1 ^ 2 := by rw [this]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)] at h2
    simpa [Fin.sum_univ_two, sq_abs] using h2
  have hal : coordAlong a u x = u 0 * (x 0 - a 0) + u 1 * (x 1 - a 1) := by
    rw [coordAlong, inner_eq]; simp
  have hac : coordAcross a u x = u 0 * (x 1 - a 1) - u 1 * (x 0 - a 0) := by
    rw [coordAcross, det]; simp
  ext i
  fin_cases i
  · simp only [hal, hac]
    simp [perp]
    linear_combination (a 0 - x 0) * hnorm
  · simp only [hal, hac]
    simp [perp]
    linear_combination (a 1 - x 1) * hnorm

/-- Both coordinates are `1`-Lipschitz, which is how a small ball about a point of the edge
stays inside the block. -/
theorem abs_coordAlong_sub_le (hu : IsDirection u) (a x y : Plane) :
    |coordAlong a u x - coordAlong a u y| ≤ dist x y := by
  have h : coordAlong a u x - coordAlong a u y = inner ℝ u (x - y) := by
    rw [coordAlong, coordAlong, ← inner_sub_right]
    congr 1
    module
  rw [h, dist_eq_norm]
  calc |inner ℝ u (x - y)| ≤ ‖u‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
    _ = ‖x - y‖ := by rw [hu.norm, one_mul]

theorem abs_coordAcross_sub_le (hu : IsDirection u) (a x y : Plane) :
    |coordAcross a u x - coordAcross a u y| ≤ dist x y := by
  have h : coordAcross a u x - coordAcross a u y = det u (x - y) := by
    simp only [coordAcross, det]
    simp
    ring
  rw [h, dist_eq_norm]
  calc |det u (x - y)| ≤ ‖u‖ * ‖x - y‖ := abs_det_le _ _
    _ = ‖x - y‖ := by rw [hu.norm, one_mul]

/-- The open block around the directed edge from `a` with unit tangent `u`: the points whose
progress lies in `(t₁, t₂)` and whose signed distance lies in `(s₁, s₂)`. -/
def strip (a u : Plane) (t₁ t₂ s₁ s₂ : ℝ) : Set Plane :=
  {x | t₁ < coordAlong a u x ∧ coordAlong a u x < t₂ ∧
    s₁ < coordAcross a u x ∧ coordAcross a u x < s₂}

theorem mem_strip_iff {t₁ t₂ s₁ s₂ : ℝ} :
    x ∈ strip a u t₁ t₂ s₁ s₂ ↔ t₁ < coordAlong a u x ∧ coordAlong a u x < t₂ ∧
      s₁ < coordAcross a u x ∧ coordAcross a u x < s₂ := Iff.rfl

theorem continuous_coordAlong (a u : Plane) : Continuous (coordAlong a u) :=
  (continuous_const.inner (continuous_id.sub continuous_const))

theorem continuous_coordAcross (a u : Plane) : Continuous (coordAcross a u) :=
  (continuous_det_right u).comp (continuous_id.sub continuous_const)

theorem isOpen_strip (a u : Plane) (t₁ t₂ s₁ s₂ : ℝ) : IsOpen (strip a u t₁ t₂ s₁ s₂) := by
  have key : strip a u t₁ t₂ s₁ s₂ =
      ({x : Plane | t₁ < coordAlong a u x} ∩ {x : Plane | coordAlong a u x < t₂}) ∩
        ({x : Plane | s₁ < coordAcross a u x} ∩ {x : Plane | coordAcross a u x < s₂}) := by
    ext y
    simp only [mem_strip_iff, mem_inter_iff, mem_setOf_eq]
    tauto
  rw [key]
  exact ((isOpen_lt continuous_const (continuous_coordAlong a u)).inter
      (isOpen_lt (continuous_coordAlong a u) continuous_const)).inter
    ((isOpen_lt continuous_const (continuous_coordAcross a u)).inter
      (isOpen_lt (continuous_coordAcross a u) continuous_const))

theorem convex_strip (a u : Plane) (t₁ t₂ s₁ s₂ : ℝ) : Convex ℝ (strip a u t₁ t₂ s₁ s₂) := by
  have key : strip a u t₁ t₂ s₁ s₂ =
      ({x : Plane | t₁ + inner ℝ u a < inner ℝ u x} ∩ {x : Plane | inner ℝ u x < t₂ + inner ℝ u a})
        ∩ ({x : Plane | s₁ + det u a < det u x} ∩ {x : Plane | det u x < s₂ + det u a}) := by
    ext y
    have h1 : coordAlong a u y = inner ℝ u y - inner ℝ u a := by
      rw [coordAlong, inner_sub_right]
    have h2 : coordAcross a u y = det u y - det u a := by
      simp only [coordAcross, det]
      simp
      ring
    simp only [mem_strip_iff, mem_inter_iff, mem_setOf_eq, h1, h2]
    constructor
    · rintro ⟨a1, a2, a3, a4⟩; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · rintro ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  rw [key]
  have hlin : IsLinearMap ℝ fun x : Plane => inner ℝ u x :=
    ⟨fun x y => inner_add_right _ _ _, fun c x => by rw [real_inner_smul_right, smul_eq_mul]⟩
  exact ((convex_halfSpace_gt hlin _).inter (convex_halfSpace_lt hlin _)).inter
    ((convex_halfSpace_gt (isLinearMap_det_right u) _).inter
      (convex_halfSpace_lt (isLinearMap_det_right u) _))

/-- A point of a block is at distance `|coordAcross|` from the foot of its perpendicular on the
edge line, which is the point of the edge with the same progress. -/
theorem dist_foot (hu : IsDirection u) (a x : Plane) :
    dist x (a + (coordAlong a u x) • u) = |coordAcross a u x| := by
  have h := frame_decomp hu a x
  rw [dist_eq_norm]
  have hx : x - (a + (coordAlong a u x) • u) = (coordAcross a u x) • perp u := by
    nth_rewrite 1 [h]
    module
  rw [hx, norm_smul, Real.norm_eq_abs, norm_perp, hu.norm, mul_one]

end Plane

/-! ## Simple closed polygons

A polygon is presented by its cyclic vertex list. Indexing by `ZMod (m + 3)` builds in both the
cyclic successor and the requirement that there are at least three vertices, and it makes
`NeZero` available without a side hypothesis. -/

open Plane

variable {m : ℕ}

/-- A simple closed polygonal curve, presented by its cyclic vertex list. -/
structure ClosedPolygon (m : ℕ) where
  /-- The vertices, in cyclic order. -/
  vertex : ZMod (m + 3) → Plane
  /-- The vertices are distinct. -/
  vertex_inj : Function.Injective vertex
  /-- Simplicity: an edge meets any other edge only at one of its own endpoints. -/
  edges_meet : ∀ i j : ZMod (m + 3), i ≠ j →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) ⊆
      {vertex i, vertex (i + 1)}
  /-- No redundant vertex: the two edges at a vertex are not collinear. The blueprint deletes
  such vertices before starting, and the vertex matching needs `det ≠ 0` there. -/
  corner : ∀ i : ZMod (m + 3), det (vertex (i - 1) - vertex i) (vertex (i + 1) - vertex i) ≠ 0

namespace ClosedPolygon

variable (P : ClosedPolygon m) (i j : ZMod (m + 3)) (c t s : ℝ)

theorem one_ne_zero' : (1 : ZMod (m + 3)) ≠ 0 := by
  intro h
  rw [show (1 : ZMod (m + 3)) = ((1 : ℕ) : ZMod (m + 3)) by norm_num,
    ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd one_pos h
  omega

theorem succ_ne_self : i + 1 ≠ i := fun h => one_ne_zero' (m := m) (by linear_combination h)

theorem vertex_ne : P.vertex i ≠ P.vertex (i + 1) := fun h =>
  succ_ne_self i (P.vertex_inj h).symm

/-! ### Edges, in their own frame -/

/-- The length of the edge leaving vertex `i`. -/
noncomputable def len : ℝ := ‖P.vertex (i + 1) - P.vertex i‖

/-- The unit tangent of the edge leaving vertex `i`, which is also the outgoing ray at `i`. -/
noncomputable def tang : Plane := dir (P.vertex (i + 1) - P.vertex i)

/-- The incoming ray at vertex `i`: the direction back along the edge that arrives there. -/
noncomputable def rayIn : Plane := dir (P.vertex (i - 1) - P.vertex i)

/-- The point of the plane at progress `t` and signed offset `s` in the frame of edge `i`. -/
noncomputable def off : Plane := P.vertex i + t • P.tang i + s • perp (P.tang i)

/-- The point of edge `i` at distance `c` from its initial vertex. -/
noncomputable def pt : Plane := P.off i c 0

/-- The edge leaving vertex `i`. -/
def edge : Set Plane := segment ℝ (P.vertex i) (P.vertex (i + 1))

/-- The carrier of the polygon: the union of its edges. -/
def carrier : Set Plane := ⋃ i, P.edge i

variable {P i j c t s}

theorem sub_ne_zero_of_edge : P.vertex (i + 1) - P.vertex i ≠ 0 :=
  sub_ne_zero.2 (P.vertex_ne i).symm

theorem len_pos : 0 < P.len i := norm_pos_iff.2 sub_ne_zero_of_edge

theorem isDirection_tang : IsDirection (P.tang i) := isDirection_dir sub_ne_zero_of_edge

theorem len_smul_tang : (P.len i) • P.tang i = P.vertex (i + 1) - P.vertex i := by
  rw [tang, dir, smul_smul, len, mul_inv_cancel₀ (norm_ne_zero_iff.2 sub_ne_zero_of_edge),
    one_smul]

theorem off_zero_zero : P.off i 0 0 = P.vertex i := by rw [off]; module

theorem pt_zero : P.pt i 0 = P.vertex i := off_zero_zero

theorem pt_len : P.pt i (P.len i) = P.vertex (i + 1) := by
  rw [pt, off, zero_smul, add_zero, len_smul_tang]
  module

theorem off_sub_vertex : P.off i t s - P.vertex i = t • P.tang i + s • perp (P.tang i) := by
  rw [off]; module

theorem pt_sub_vertex : P.pt i c - P.vertex i = c • P.tang i := by
  rw [pt, off_sub_vertex, zero_smul, add_zero]

theorem dist_pt_vertex : dist (P.pt i c) (P.vertex i) = |c| := by
  rw [dist_eq_norm, pt_sub_vertex, norm_smul, Real.norm_eq_abs, isDirection_tang.norm, mul_one]

theorem dist_off_vertex_le : dist (P.off i t s) (P.vertex i) ≤ |t| + |s| := by
  rw [dist_eq_norm, off_sub_vertex]
  calc ‖t • P.tang i + s • perp (P.tang i)‖ ≤ ‖t • P.tang i‖ + ‖s • perp (P.tang i)‖ :=
        norm_add_le _ _
    _ = |t| + |s| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_perp,
          isDirection_tang.norm, mul_one, mul_one]

@[simp] theorem coordAlong_off : coordAlong (P.vertex i) (P.tang i) (P.off i t s) = t :=
  coordAlong_param isDirection_tang _ _ _

@[simp] theorem coordAcross_off : coordAcross (P.vertex i) (P.tang i) (P.off i t s) = s :=
  coordAcross_param isDirection_tang _ _ _

/-- Every point is the point of some frame position, so the two coordinates identify it. -/
theorem off_coord (P : ClosedPolygon m) (i : ZMod (m + 3)) (x : Plane) :
    x = P.off i (coordAlong (P.vertex i) (P.tang i) x) (coordAcross (P.vertex i) (P.tang i) x) :=
  frame_decomp isDirection_tang _ _

theorem mem_edge_iff {x : Plane} :
    x ∈ P.edge i ↔ ∃ c ∈ Set.Icc (0 : ℝ) (P.len i), x = P.pt i c := by
  rw [edge, segment_eq_image' ℝ]
  constructor
  · rintro ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    refine ⟨θ * P.len i, ⟨mul_nonneg hθ0 len_pos.le, ?_⟩, ?_⟩
    · nlinarith [len_pos (P := P) (i := i)]
    · rw [pt, off, zero_smul, add_zero, ← len_smul_tang]
      simp [smul_smul]
  · rintro ⟨c, ⟨hc0, hc1⟩, rfl⟩
    refine ⟨c / P.len i, ⟨div_nonneg hc0 len_pos.le, ?_⟩, ?_⟩
    · rw [div_le_one len_pos]; exact hc1
    · rw [pt, off, zero_smul, add_zero, ← len_smul_tang]
      simp [smul_smul, div_mul_cancel₀ _ (len_pos (P := P) (i := i)).ne']

theorem pt_mem_edge (hc : c ∈ Set.Icc (0 : ℝ) (P.len i)) : P.pt i c ∈ P.edge i :=
  mem_edge_iff.2 ⟨c, hc, rfl⟩

theorem vertex_mem_edge : P.vertex i ∈ P.edge i := by
  rw [← pt_zero]; exact pt_mem_edge ⟨le_refl _, len_pos.le⟩

theorem vertex_mem_carrier : P.vertex i ∈ P.carrier := Set.mem_iUnion.2 ⟨i, vertex_mem_edge⟩

theorem edge_subset_carrier : P.edge i ⊆ P.carrier := Set.subset_iUnion _ i

/-- The incoming ray at `i + 1` is the reverse of the tangent of edge `i`. This is the identity
that lets the two germs at a shared vertex be compared. -/
theorem rayIn_succ : P.rayIn (i + 1) = -P.tang i := by
  rw [rayIn, tang, add_sub_cancel_right, dir, dir, norm_sub_rev]
  module

theorem vertex_pred_ne : P.vertex (i - 1) - P.vertex i ≠ 0 := by
  have h := P.vertex_ne (i - 1)
  rw [sub_add_cancel] at h
  exact sub_ne_zero.2 h

theorem det_rays_ne_zero : det (P.rayIn i) (P.tang i) ≠ 0 := by
  obtain ⟨c₁, hc₁, h₁⟩ := dir_eq_smul (vertex_pred_ne (P := P) (i := i))
  obtain ⟨c₂, hc₂, h₂⟩ := dir_eq_smul (sub_ne_zero_of_edge (P := P) (i := i))
  rw [rayIn, tang, h₁, h₂, det_smul_left, det_smul_right]
  exact mul_ne_zero hc₁.ne' (mul_ne_zero hc₂.ne' (P.corner i))

/-- A point of the edge arriving at `i` is a nonnegative multiple of the incoming ray away from
the vertex; a point of the edge leaving `i` is a nonnegative multiple of the outgoing one. This
is what keeps the two incident edges out of both sectors at `i`. -/
theorem mem_edge_pred_sub {x : Plane} (hx : x ∈ P.edge (i - 1)) :
    ∃ c : ℝ, 0 ≤ c ∧ x - P.vertex i = c • P.rayIn i := by
  rw [mem_edge_iff] at hx
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := hx
  refine ⟨P.len (i - 1) - c, by linarith, ?_⟩
  have hsucc : i - 1 + 1 = i := sub_add_cancel i 1
  have hr : P.rayIn i = -P.tang (i - 1) := by
    have := rayIn_succ (P := P) (i := i - 1)
    rwa [hsucc] at this
  have hv : P.vertex i = P.vertex (i - 1 + 1) := by rw [hsucc]
  have hlen : P.vertex (i - 1 + 1) = P.vertex (i - 1) + (P.len (i - 1)) • P.tang (i - 1) := by
    rw [len_smul_tang]; module
  rw [pt, off, zero_smul, add_zero, hr, hv, hlen]
  module

theorem mem_edge_sub {x : Plane} (hx : x ∈ P.edge i) :
    ∃ c : ℝ, 0 ≤ c ∧ x - P.vertex i = c • P.tang i := by
  rw [mem_edge_iff] at hx
  obtain ⟨c, ⟨hc0, _⟩, rfl⟩ := hx
  exact ⟨c, hc0, pt_sub_vertex⟩

theorem pt_eq : P.pt i c = P.vertex i + c • P.tang i := by rw [pt, off, zero_smul, add_zero]

end ClosedPolygon

/-! ## The constants

`StripData` is the blueprint's "choose the blocks so that consecutive ones overlap and
nonadjacent closures are disjoint", with every constant named. The three numbers are a cone
radius `R`, a trim `lam` and a half-width `rho`; the separation hypotheses are exactly the
instances of Lemma 1.4 (b) that the construction consumes, and `germ` is the vertex-matching
threshold. Producing them is the unproved `exists_stripData`; see the Status section. -/

/-- The constants of the collar of a simple closed polygon. -/
structure StripData (P : ClosedPolygon m) where
  /-- The radius of the vertex sectors. -/
  R : ℝ
  /-- The distance by which an edge block stops short of each endpoint of its edge. -/
  lam : ℝ
  /-- The half-width of an edge block. -/
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_lam : rho < lam
  /-- The sectors reach past the ends of the blocks they have to overlap. -/
  two_lam_lt_R : 2 * lam < R
  /-- The blocks are nonempty, with room to spare at both ends. -/
  four_lam_lt_len : ∀ i, 4 * lam < P.len i
  /-- A sector does not run past the far end of an incident edge. -/
  R_le_len : ∀ i, R ≤ P.len i
  /-- Distinct vertices are `2R` apart, so distinct sectors are disjoint. -/
  sep_vertex : ∀ i j, i ≠ j → 2 * R ≤ dist (P.vertex i) (P.vertex j)
  /-- A vertex is `2R` away from every nonincident edge. The factor `2` is the slack that a
  block of half-width `rho ≤ R` needs in `notMem_sectorL_of_far`. -/
  sep_vertex_edge : ∀ i j, j ≠ i - 1 → j ≠ i → ∀ y ∈ P.edge j, 2 * R ≤ dist (P.vertex i) y
  /-- The trimmed edge `i` is `2 * rho` away from every other edge. -/
  sep_trim_edge : ∀ i j, j ≠ i → ∀ c ∈ Set.Icc lam (P.len i - lam), ∀ y ∈ P.edge j,
    2 * rho ≤ dist (P.pt i c) y
  /-- **The vertex-matching threshold.** This is the only hypothesis that is not a separation of
  compact sets: it says the blocks are narrow enough, relative to how far they stop short of the
  vertices, for `Plane.germs_split'` to apply at every corner. -/
  germ : ∀ i, rho * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤ lam * |det (P.rayIn i) (P.tang i)|

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i j : ZMod (m + 3)} {x : Plane}

theorem lam_pos : 0 < D.lam := lt_trans D.rho_pos D.rho_lt_lam

theorem R_pos : 0 < D.R := by have := D.lam_pos; linarith [D.two_lam_lt_R]

theorem rho_lt_R : D.rho < D.R := by
  have := D.lam_pos; have := D.rho_lt_lam; linarith [D.two_lam_lt_R]

/-! ### The four families of blocks -/

/-- The left block of edge `i`. -/
def blockL (i : ZMod (m + 3)) : Set Plane :=
  strip (P.vertex i) (P.tang i) D.lam (P.len i - D.lam) 0 D.rho

/-- The right block of edge `i`. -/
def blockR (i : ZMod (m + 3)) : Set Plane :=
  strip (P.vertex i) (P.tang i) D.lam (P.len i - D.lam) (-D.rho) 0

/-- The left sector at vertex `i`: the arc `arcCCW (tang i) (rayIn i)` is the one carrying both
left germs, by `Plane.germs_split'`. -/
def sectorL (i : ZMod (m + 3)) : Set Plane :=
  cone (P.vertex i) (arcCCW (P.tang i) (P.rayIn i)) D.R

/-- The right sector at vertex `i`. -/
def sectorR (i : ZMod (m + 3)) : Set Plane :=
  cone (P.vertex i) (arcCCW (P.rayIn i) (P.tang i)) D.R

/-- The left side of the collar. -/
def sideL : Set Plane := ⋃ i, (D.sectorL i ∪ D.blockL i)

/-- The right side of the collar. -/
def sideR : Set Plane := ⋃ i, (D.sectorR i ∪ D.blockR i)

/-- The collar itself. -/
def nbhd : Set Plane := D.sideL ∪ D.sideR ∪ P.carrier

theorem mem_blockL_iff : x ∈ D.blockL i ↔
    D.lam < coordAlong (P.vertex i) (P.tang i) x ∧
      coordAlong (P.vertex i) (P.tang i) x < P.len i - D.lam ∧
      0 < coordAcross (P.vertex i) (P.tang i) x ∧
      coordAcross (P.vertex i) (P.tang i) x < D.rho := Iff.rfl

theorem mem_blockR_iff : x ∈ D.blockR i ↔
    D.lam < coordAlong (P.vertex i) (P.tang i) x ∧
      coordAlong (P.vertex i) (P.tang i) x < P.len i - D.lam ∧
      -D.rho < coordAcross (P.vertex i) (P.tang i) x ∧
      coordAcross (P.vertex i) (P.tang i) x < 0 := Iff.rfl

theorem mem_blockL_off {t s : ℝ} : P.off i t s ∈ D.blockL i ↔
    D.lam < t ∧ t < P.len i - D.lam ∧ 0 < s ∧ s < D.rho := by
  rw [mem_blockL_iff, ClosedPolygon.coordAlong_off, ClosedPolygon.coordAcross_off]

theorem mem_blockR_off {t s : ℝ} : P.off i t s ∈ D.blockR i ↔
    D.lam < t ∧ t < P.len i - D.lam ∧ -D.rho < s ∧ s < 0 := by
  rw [mem_blockR_iff, ClosedPolygon.coordAlong_off, ClosedPolygon.coordAcross_off]

theorem convex_blockL : Convex ℝ (D.blockL i) := convex_strip _ _ _ _ _ _
theorem convex_blockR : Convex ℝ (D.blockR i) := convex_strip _ _ _ _ _ _

theorem isConnected_sectorL : IsConnected (D.sectorL i) :=
  isConnected_cone_arcCCW _ (by rw [det_comm]; exact neg_ne_zero.2 ClosedPolygon.det_rays_ne_zero)
    D.R_pos

theorem isConnected_sectorR : IsConnected (D.sectorR i) :=
  isConnected_cone_arcCCW _ ClosedPolygon.det_rays_ne_zero D.R_pos

/-! ### Where the blocks live

A block sits inside the `rho`-neighbourhood of the trimmed edge, and a sector inside the ball of
radius `R` about its vertex. Every "nonadjacent blocks are disjoint" step below is one of these
two containments against one of the separation hypotheses. -/

/-- The foot of the perpendicular from a point of a block lies on the trimmed edge, within `rho`
of the point. -/
theorem exists_foot (h : x ∈ D.blockL i ∪ D.blockR i) :
    ∃ c ∈ Set.Icc D.lam (P.len i - D.lam), dist x (P.pt i c) < D.rho := by
  refine ⟨coordAlong (P.vertex i) (P.tang i) x, ?_, ?_⟩
  · rcases h with h | h
    · exact ⟨(D.mem_blockL_iff.1 h).1.le, (D.mem_blockL_iff.1 h).2.1.le⟩
    · exact ⟨(D.mem_blockR_iff.1 h).1.le, (D.mem_blockR_iff.1 h).2.1.le⟩
  · rw [ClosedPolygon.pt_eq, dist_foot ClosedPolygon.isDirection_tang]
    rcases h with h | h
    · obtain ⟨_, _, h1, h2⟩ := D.mem_blockL_iff.1 h
      rw [abs_of_pos h1]; exact h2
    · obtain ⟨_, _, h1, h2⟩ := D.mem_blockR_iff.1 h
      rw [abs_of_neg h2]; linarith

theorem sector_subset_ball : D.sectorL i ⊆ ball (P.vertex i) D.R := cone_subset_ball
theorem sectorR_subset_ball : D.sectorR i ⊆ ball (P.vertex i) D.R := cone_subset_ball

/-! ### The germ argument at a vertex

These four lemmas are the whole content of "at a vertex the left sides of the incoming and
outgoing strips enter the same component of the vertex disk minus the two incident rays". Each
is one projection of `Plane.germs_split'`, applied to the frame decomposition of a point of a
block. -/

/-- The threshold hypothesis, specialised to a point of a block. -/
theorem germ_ineq {t s : ℝ} (ht : D.lam < t) (hs0 : 0 < s) (hs : s < D.rho) :
    s * |inner ℝ (P.rayIn i) (P.tang i)| < t * |det (P.rayIn i) (P.tang i)| := by
  have hd : 0 < |det (P.rayIn i) (P.tang i)| := abs_pos.2 ClosedPolygon.det_rays_ne_zero
  have habs : (0 : ℝ) ≤ |inner ℝ (P.rayIn i) (P.tang i)| := abs_nonneg _
  have h1 : s * |inner ℝ (P.rayIn i) (P.tang i)| ≤ s * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) := by
    nlinarith
  have h2 : s * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) <
      D.rho * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) := by nlinarith
  have h3 := D.germ i
  nlinarith

/-- A point of the left block of edge `i`, seen from the vertex it leaves, is the outgoing left
germ, hence in the left arc there. -/
theorem blockL_sub_mem_arcL_start (h : x ∈ D.blockL i) :
    x - P.vertex i ∈ arcCCW (P.tang i) (P.rayIn i) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockL_iff.1 h
  have hx := ClosedPolygon.off_coord P i x
  rw [hx, ClosedPolygon.off_sub_vertex]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero h3 (D.germ_ineq h1 h3 h4)).1.2

/-- The same point, seen from the vertex it arrives at, is the incoming left germ. -/
theorem blockL_sub_mem_arcL_finish (h : x ∈ D.blockL i) :
    x - P.vertex (i + 1) ∈ arcCCW (P.tang (i + 1)) (P.rayIn (i + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockL_iff.1 h
  set t := coordAlong (P.vertex i) (P.tang i) x with ht
  set s := coordAcross (P.vertex i) (P.tang i) x with hs
  have hx : x = P.off i t s := ClosedPolygon.off_coord P i x
  have hr : P.rayIn (i + 1) = -P.tang i := ClosedPolygon.rayIn_succ
  have hkey : x - P.vertex (i + 1) =
      (P.len i - t) • P.rayIn (i + 1) - s • perp (P.rayIn (i + 1)) := by
    have hv : P.vertex (i + 1) = P.vertex i + (P.len i) • P.tang i := by
      rw [ClosedPolygon.len_smul_tang]; module
    rw [hx, ClosedPolygon.off, hv, hr]
    have hp : perp (-P.tang i) = -perp (P.tang i) := by
      ext k; fin_cases k <;> simp [perp]
    rw [hp]
    module
  rw [hkey]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero h3
    (D.germ_ineq (i := i + 1) (by linarith) h3 h4)).1.1

/-- A point of the right block of edge `i`, seen from the vertex it leaves, is the outgoing right
germ, hence in the right arc there. -/
theorem blockR_sub_mem_arcR_start (h : x ∈ D.blockR i) :
    x - P.vertex i ∈ arcCCW (P.rayIn i) (P.tang i) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockR_iff.1 h
  set t := coordAlong (P.vertex i) (P.tang i) x with ht
  set s := coordAcross (P.vertex i) (P.tang i) x with hs
  have hx : x = P.off i t s := ClosedPolygon.off_coord P i x
  have hkey : x - P.vertex i = t • P.tang i - (-s) • perp (P.tang i) := by
    rw [hx, ClosedPolygon.off_sub_vertex]; module
  rw [hkey]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero (by linarith)
    (D.germ_ineq h1 (by linarith) (by linarith))).2.2

/-- The same point, seen from the vertex it arrives at, is the incoming right germ. -/
theorem blockR_sub_mem_arcR_finish (h : x ∈ D.blockR i) :
    x - P.vertex (i + 1) ∈ arcCCW (P.rayIn (i + 1)) (P.tang (i + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockR_iff.1 h
  set t := coordAlong (P.vertex i) (P.tang i) x with ht
  set s := coordAcross (P.vertex i) (P.tang i) x with hs
  have hx : x = P.off i t s := ClosedPolygon.off_coord P i x
  have hr : P.rayIn (i + 1) = -P.tang i := ClosedPolygon.rayIn_succ
  have hkey : x - P.vertex (i + 1) =
      (P.len i - t) • P.rayIn (i + 1) + (-s) • perp (P.rayIn (i + 1)) := by
    have hv : P.vertex (i + 1) = P.vertex i + (P.len i) • P.tang i := by
      rw [ClosedPolygon.len_smul_tang]; module
    rw [hx, ClosedPolygon.off, hv, hr]
    have hp : perp (-P.tang i) = -perp (P.tang i) := by
      ext k; fin_cases k <;> simp [perp]
    rw [hp]
    module
  rw [hkey]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero (by linarith)
    (D.germ_ineq (i := i + 1) (by linarith) (by linarith) (by linarith))).2.1

/-! ### Nonadjacent blocks are disjoint

Everything here is one of the separation hypotheses of `StripData` against one of the two
containments `exists_foot` and `sector_subset_ball`. -/

theorem pt_mem_edge_of_trim {c : ℝ} (hc : c ∈ Set.Icc D.lam (P.len i - D.lam)) :
    P.pt i c ∈ P.edge i :=
  ClosedPolygon.pt_mem_edge ⟨le_trans D.lam_pos.le hc.1, le_trans hc.2 (by linarith [D.lam_pos])⟩

/-- A block misses every edge but its own. -/
theorem block_notMem_edge (h : x ∈ D.blockL i ∪ D.blockR i) (hj : j ≠ i) : x ∉ P.edge j := by
  intro hx
  obtain ⟨c, hc, hd⟩ := D.exists_foot h
  have := D.sep_trim_edge i j hj c hc x hx
  rw [dist_comm] at hd
  linarith [D.rho_pos]

/-- A block misses its own edge, because its points have nonzero offset. -/
theorem block_notMem_own_edge (h : x ∈ D.blockL i ∪ D.blockR i) : x ∉ P.edge i := by
  intro hx
  rw [ClosedPolygon.mem_edge_iff] at hx
  obtain ⟨c, _, rfl⟩ := hx
  have hzero : coordAcross (P.vertex i) (P.tang i) (P.pt i c) = 0 := by
    rw [ClosedPolygon.pt]; exact ClosedPolygon.coordAcross_off
  rcases h with h | h
  · have hpos := (D.mem_blockL_iff.1 h).2.2.1
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · have hneg := (D.mem_blockR_iff.1 h).2.2.2
    rw [hzero] at hneg
    exact lt_irrefl 0 hneg

theorem block_notMem_carrier (h : x ∈ D.blockL i ∪ D.blockR i) : x ∉ P.carrier := by
  rintro hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  by_cases hij : j = i
  · exact D.block_notMem_own_edge h (hij ▸ hj)
  · exact D.block_notMem_edge h hij hj

/-- A sector misses every edge that is not incident to its vertex. -/
theorem sector_notMem_far_edge (h : x ∈ ball (P.vertex i) D.R) (hj1 : j ≠ i - 1) (hj2 : j ≠ i) :
    x ∉ P.edge j := by
  intro hx
  have := D.sep_vertex_edge i j hj1 hj2 x hx
  rw [mem_ball, dist_comm] at h
  linarith [D.R_pos]

/-- A sector misses the two edges incident to its vertex: their points lie on the two bounding
rays, and the arcs are open. -/
theorem sectorL_notMem_carrier (h : x ∈ D.sectorL i) : x ∉ P.carrier := by
  rintro hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  by_cases hji : j = i
  · rw [hji] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_sub hj
    exact ((notMem_arcCCW_smul (P.tang i) (P.rayIn i) hc).1) (he ▸ h.1)
  by_cases hjp : j = i - 1
  · rw [hjp] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_pred_sub (i := i) hj
    exact ((notMem_arcCCW_smul (P.rayIn i) (P.tang i) hc).2) (he ▸ h.1)
  · exact D.sector_notMem_far_edge (i := i) h.2 hjp hji hj

theorem sectorR_notMem_carrier (h : x ∈ D.sectorR i) : x ∉ P.carrier := by
  rintro hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  by_cases hji : j = i
  · rw [hji] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_sub hj
    exact ((notMem_arcCCW_smul (P.tang i) (P.rayIn i) hc).2) (he ▸ h.1)
  by_cases hjp : j = i - 1
  · rw [hjp] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_pred_sub (i := i) hj
    exact ((notMem_arcCCW_smul (P.rayIn i) (P.tang i) hc).1) (he ▸ h.1)
  · exact D.sector_notMem_far_edge (i := i) h.2 hjp hji hj

theorem sideL_disjoint_carrier : Disjoint D.sideL P.carrier := by
  rw [Set.disjoint_left]
  rintro y hy hc
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  rcases hi with hi | hi
  · exact D.sectorL_notMem_carrier hi hc
  · exact D.block_notMem_carrier (Or.inl hi) hc

theorem sideR_disjoint_carrier : Disjoint D.sideR P.carrier := by
  rw [Set.disjoint_left]
  rintro y hy hc
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  rcases hi with hi | hi
  · exact D.sectorR_notMem_carrier hi hc
  · exact D.block_notMem_carrier (Or.inr hi) hc

/-! ### The two sides are disjoint

Four families times four families. The pairs with distinct indices are settled by distance; the
pairs at a shared index are settled by `Plane.arcCCW_disjoint'` through the germ lemmas. -/

end StripData

end Schoenflies
end

section
-- module Solutions.Q146_CD.PolygonBridge
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The polygon bridge

Two independent representations of a closed polygon had grown up side by side and never met.
`Schoenflies/Strip.lean` carries `ClosedPolygon m`, a cyclic vertex list indexed by
`ZMod (m + 3)`, and everything the collar of Lemma 1.8 says is said about it.
`Schoenflies/Parity.lean` carries `List Piece` together with `IsClosedChain`, and everything
the crossing count of Lemma 2.1 and Lemma 2.2 says is said about *that*. Neither knew about
the other, and — worse — nothing anywhere produced a `ClosedPolygon`, so every theorem about
one was formally a theorem about a structure that might have been empty.

This module closes the three gaps.

## Non-vacuity

`Schoenflies.triangle` builds a `ClosedPolygon 0` out of any three points with nonzero
orientation determinant, and `Schoenflies.unitTriangle` is the concrete instance with vertices
`(0,0)`, `(1,0)`, `(0,1)`. The only real work is `edges_meet`: two edges of a triangle share
exactly one endpoint, and `Schoenflies.segment_inter_shared` says two segments meeting at an
endpoint whose far ends are off the shared line meet nowhere else. That lemma is proved by
taking the orientation form against the first segment's direction, which kills the first
segment's own parameter and forces the second's to vanish.

## The representation bridge

`ClosedPolygon.pieces` lists the `m + 3` edges as pairs of endpoints, in cyclic order.
It is a closed chain (`ClosedPolygon.isClosedChain_pieces`), every piece is nondegenerate
(`ClosedPolygon.pieces_nondeg`), and — the point of the exercise —
`ClosedPolygon.cover_pieces` says it occupies exactly the polygon's carrier. Closedness is a
telescoping sum: `Schoenflies.sum_range_boundary` evaluates the mod-`2` boundary of the chain
`0 → 1 → ⋯ → n` as the sum of its two ends, and the two ends of `0 → ⋯ → m + 3` are the same
vertex because `m + 3` is `0` in `ZMod (m + 3)`.

## The curve bridge

`ClosedPolygon.isJordanCurve_carrier` and `ClosedPolygon.isPolygonal_carrier` say the carrier
is a simple closed polygonal curve in the blueprint's sense, which is what the polygonal Jordan
curve theorem (Theorem 2.3) takes as its hypothesis. The loop is built by concatenating edge
parametrizations around the cycle: `ClosedPolygon.chain k` is the union of the edges leaving
vertices `0, …, k`, and `ClosedPolygon.isArcBetween_chain` grows it one edge at a time by
`IsArcBetween.concatenate`. The hypothesis that concatenation needs — the new edge meets what
came before only at the vertex they share — is exactly `edges_meet` twice over: once to place
the meeting point among the new edge's own two endpoints, and once more to rule out the far
one, which would otherwise let the polygon close early. The last edge closes the loop through
`IsJordanCurve.of_two_arcs`, and there the far endpoint is *not* ruled out: it is the second
shared point that makes the two arcs a curve rather than an arc.

## Both halves at once

The last section is what the bridge is for: the two statements of Lemma 2.2 — parity is
constant on a component of the complement, and it flips across an edge — restated for the
*carrier* of a `ClosedPolygon` rather than for the cover of an anonymous list. The flip needs
the edge list split around the edge being crossed, which is `List.append_of_mem` together with
`ClosedPolygon.pieces_nodup`; that the two remaining fragments miss the crossing point is
`edges_meet` a third time.

## Blueprint

* `Schoenflies.triangle`, `Schoenflies.unitTriangle` — witnesses that §1's "simple closed
  polygonal curve" is not vacuous.
* `ClosedPolygon.pieces`, `ClosedPolygon.cover_pieces`, `ClosedPolygon.isClosedChain_pieces` —
  the edge list the crossing count of §2 is defined on, and that it carries the polygon.
* `ClosedPolygon.isJordanCurve_carrier`, `ClosedPolygon.isPolygonal_carrier` — §1, "a simple
  closed polygonal curve"; jointly the hypothesis of Theorem 2.3.
* `ClosedPolygon.parity_eq_of_mem_connectedComponentIn_carrier`,
  `ClosedPolygon.parity_flip_carrier` — the two halves of Lemma 2.2, read off a
  `ClosedPolygon`. These are the statements Theorem 2.3 consumes.

One general lemma is stated here that does not belong here: `Schoenflies.exists_of_mem_cover`,
the destructor matching `Schoenflies.mem_cover`, whose home is `Schoenflies/Parity.lean`.
-/

open Metric Set

namespace Schoenflies

open Plane

variable {m : ℕ}

/-! ## Two segments that share an endpoint

The one piece of plane geometry this module needs. `Schoenflies/SegmentMeet.lean` describes
the intersection of two arbitrary segments; here the two are known to share an endpoint, and
the conclusion is sharper and the proof shorter. -/

/-- Two segments sharing the endpoint `b`, whose far ends are off the line through the other,
meet only at `b`. Taking the orientation form against `b - a` annihilates the first segment's
own parameter, so the second segment's parameter must vanish. -/
theorem segment_inter_shared {a b c : Plane} (h : det (b - a) (c - b) ≠ 0) :
    segment ℝ a b ∩ segment ℝ b c ⊆ {b} := by
  rintro z ⟨hz1, hz2⟩
  rw [segment_eq_image' ℝ a b] at hz1
  rw [segment_eq_image' ℝ b c] at hz2
  obtain ⟨s, -, hs⟩ := hz1
  obtain ⟨t, -, ht⟩ := hz2
  simp only at hs ht
  have hvec : t • (c - b) = (s - 1) • (b - a) := by
    have hz := ht.trans hs.symm
    linear_combination (norm := module) hz
  have key : t * det (b - a) (c - b) = 0 := by
    have h2 : det (b - a) (t • (c - b)) = det (b - a) ((s - 1) • (b - a)) := by rw [hvec]
    rw [det_smul_right, det_smul_right, det_self, mul_zero] at h2
    exact h2
  have ht0 : t = 0 := by
    rcases mul_eq_zero.1 key with h0 | h0
    · exact h0
    · exact absurd h0 h
  simp only [mem_singleton_iff]
  rw [← ht, ht0, zero_smul, add_zero]

/-! ## Non-vacuity: a triangle is a closed polygon

Nothing in the strip development ever built a `ClosedPolygon`, so `polygonal_collar` and every
theorem beside it was formally a theorem about a structure with no known inhabitant. A triangle
is the smallest witness, and no coordinates are needed: any three points with nonzero
orientation determinant will do. -/

section Triangle

variable {a b c : Plane}

/-- The orientation of a triple, read at its first corner and at its second, is the same. -/
theorem det_rot₁ (a b c : Plane) : det (b - a) (c - b) = det (b - a) (c - a) := by
  simp only [Plane.det, Plane.sub_apply] <;> ring

/-- The same, one corner further round. -/
theorem det_rot₂ (a b c : Plane) : det (c - b) (a - c) = det (b - a) (c - a) := by
  simp only [Plane.det, Plane.sub_apply] <;> ring

/-- And once more; the orientation form is invariant under cycling the triple. -/
theorem det_rot₃ (a b c : Plane) : det (a - c) (b - a) = det (b - a) (c - a) := by
  simp only [Plane.det, Plane.sub_apply] <;> ring

/-- **A triangle is a simple closed polygon.** Any three points that are not collinear, taken
in that cyclic order. `edges_meet` holds because two of the three edges always share exactly
one endpoint, and `corner` because the orientation form is what nonzero says. -/
def triangle (h : det (b - a) (c - a) ≠ 0) : ClosedPolygon 0 where
  vertex := ![a, b, c]
  vertex_inj := by
    have hab : a ≠ b := by
      rintro rfl
      exact h (by simp [Plane.det])
    have hbc : b ≠ c := by
      rintro rfl
      exact h (det_self _)
    have hac : a ≠ c := by
      rintro rfl
      exact h (by simp [Plane.det])
    intro i j hij
    have hi : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hi i with rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl
    · rfl
    · exact absurd (show a = b from hij) hab
    · exact absurd (show a = c from hij) hac
    · exact absurd (show a = b from hij.symm) hab
    · rfl
    · exact absurd (show b = c from hij) hbc
    · exact absurd (show a = c from hij.symm) hac
    · exact absurd (show b = c from hij.symm) hbc
    · rfl
  edges_meet := by
    have mab : segment ℝ a b ∩ segment ℝ b c ⊆ {b} :=
      segment_inter_shared (by rw [det_rot₁]; exact h)
    have mbc : segment ℝ b c ∩ segment ℝ c a ⊆ {c} :=
      segment_inter_shared (by rw [det_rot₂]; exact h)
    have mca : segment ℝ c a ∩ segment ℝ a b ⊆ {a} :=
      segment_inter_shared (by rw [det_rot₃]; exact h)
    intro i j hij
    have hi : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hi i with rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl
    · exact absurd rfl hij
    · change segment ℝ a b ∩ segment ℝ b c ⊆ {a, b}
      exact subset_trans mab (by simp)
    · change segment ℝ a b ∩ segment ℝ c a ⊆ {a, b}
      rw [Set.inter_comm]
      exact subset_trans mca (by simp)
    · change segment ℝ b c ∩ segment ℝ a b ⊆ {b, c}
      rw [Set.inter_comm]
      exact subset_trans mab (by simp)
    · exact absurd rfl hij
    · change segment ℝ b c ∩ segment ℝ c a ⊆ {b, c}
      exact subset_trans mbc (by simp)
    · change segment ℝ c a ∩ segment ℝ a b ⊆ {c, a}
      exact subset_trans mca (by simp)
    · change segment ℝ c a ∩ segment ℝ b c ⊆ {c, a}
      rw [Set.inter_comm]
      exact subset_trans mbc (by simp)
    · exact absurd rfl hij
  corner := by
    intro i
    have hi : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hi i with rfl | rfl | rfl
    · change det (c - a) (b - a) ≠ 0
      intro hc
      apply h
      simp only [Plane.det, Plane.sub_apply] at hc ⊢
      linarith
    · change det (a - b) (c - b) ≠ 0
      intro hc
      apply h
      simp only [Plane.det, Plane.sub_apply] at hc ⊢
      linarith
    · change det (b - c) (a - c) ≠ 0
      intro hc
      apply h
      simp only [Plane.det, Plane.sub_apply] at hc ⊢
      linarith

@[simp] theorem triangle_vertex_zero (h : det (b - a) (c - a) ≠ 0) :
    (triangle h).vertex 0 = a := rfl

@[simp] theorem triangle_vertex_one (h : det (b - a) (c - a) ≠ 0) :
    (triangle h).vertex 1 = b := rfl

@[simp] theorem triangle_vertex_two (h : det (b - a) (c - a) ≠ 0) :
    (triangle h).vertex 2 = c := rfl

end Triangle

/-! ## A telescoping sum mod two -/

/-- The mod-`2` boundary of the chain `0 → 1 → ⋯ → n` is the sum of its two ends: every
interior vertex is counted twice. This is the whole content of "a cycle is a closed chain". -/
theorem sum_range_boundary (g : ℕ → ZMod 2) :
    ∀ n : ℕ, ((List.range n).map fun j => g j + g (j + 1)).sum = g 0 + g n
  | 0 => by simpa using (add_self_zmod_two (g 0)).symm
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_boundary g n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    linear_combination add_self_zmod_two (g n)

namespace ClosedPolygon

/-! ## Natural-number indices

Both bridges run over the vertices with a natural number and cast into `ZMod (m + 3)`. Below
the modulus the cast is injective, which is what turns "these two indices are different
naturals" into "these are different edges" and back. -/

/-- Below the modulus, casting a natural number into `ZMod (m + 3)` is injective. -/
theorem natCast_inj {j k : ℕ} (hj : j < m + 3) (hk : k < m + 3)
    (h : (j : ZMod (m + 3)) = (k : ZMod (m + 3))) : j = k := by
  have hval := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt hj, ZMod.val_cast_of_lt hk] at hval

/-- The successor, pushed through the cast. -/
theorem natCast_succ (j : ℕ) : ((j + 1 : ℕ) : ZMod (m + 3)) = (j : ZMod (m + 3)) + 1 := by
  push_cast <;> ring

variable {P : ClosedPolygon m}

/-- **An edge meets an earlier edge only at its own initial vertex.** `edges_meet` puts the
meeting point at one of the two ends of the later edge; the far end is ruled out by applying
`edges_meet` the other way round, which would put the later edge's *terminal* vertex on the
earlier edge and hence make it one of two vertices it cannot be. This is what stops the
polygon from closing before it has run through all its vertices. -/
theorem edge_meet_earlier {j k : ℕ} (hjk : j < k) (hk : k + 1 < m + 3) {z : Plane}
    (hzj : z ∈ P.edge (j : ZMod (m + 3))) (hzk : z ∈ P.edge (k : ZMod (m + 3))) :
    z = P.vertex (k : ZMod (m + 3)) := by
  have hjn : j < m + 3 := by omega
  have hkn : k < m + 3 := by omega
  have hne : (k : ZMod (m + 3)) ≠ (j : ZMod (m + 3)) :=
    fun heq => (by omega : k ≠ j) (natCast_inj hkn hjn heq)
  have hmem := P.edges_meet _ _ hne (Set.mem_inter hzk hzj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · exact hmem
  -- The far end: it would have to be one of the earlier edge's two ends as well.
  exfalso
  have hmem2 := P.edges_meet _ _ (Ne.symm hne) (Set.mem_inter hzj hzk)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem2
  rw [← natCast_succ] at hmem
  rcases hmem2 with hmem2 | hmem2
  · have : k + 1 = j := natCast_inj hk hjn (P.vertex_inj (hmem ▸ hmem2))
    omega
  · rw [← natCast_succ] at hmem2
    have : k + 1 = j + 1 := natCast_inj hk (by omega) (P.vertex_inj (hmem ▸ hmem2))
    omega

/-- **The last edge meets every earlier edge only at a vertex it shares with the cycle's ends.**
Here the far end is *not* excluded: the last edge runs back to vertex `0`, so both of its ends
are legitimate meeting points, and that is precisely what makes the carrier a closed curve
rather than an arc. -/
theorem edge_meet_last {j : ℕ} (hj : j < m + 2) {z : Plane}
    (hzj : z ∈ P.edge (j : ZMod (m + 3)))
    (hz : z ∈ P.edge ((m + 2 : ℕ) : ZMod (m + 3))) :
    z = P.vertex 0 ∨ z = P.vertex ((m + 2 : ℕ) : ZMod (m + 3)) := by
  have hne : ((m + 2 : ℕ) : ZMod (m + 3)) ≠ (j : ZMod (m + 3)) :=
    fun heq => (by omega : m + 2 ≠ j) (natCast_inj (by omega) (by omega) heq)
  have hlast : ((m + 2 : ℕ) : ZMod (m + 3)) + 1 = 0 := by
    rw [← natCast_succ]
    exact ZMod.natCast_self (m + 3)
  have hmem := P.edges_meet _ _ hne (Set.mem_inter hz hzj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · exact Or.inr hmem
  · rw [hlast] at hmem
    exact Or.inl hmem

/-! ## The representation bridge

`Schoenflies/Parity.lean` counts crossings of a `List Piece`; `ClosedPolygon.pieces` is the
list it should be handed. The four obligations below are exactly what every parity statement
asks for: a list, closedness, nondegeneracy, and — the one that carries the geometry — that
the list occupies the polygon. -/

/-- The `m + 3` edges of the polygon, as a list of pieces in cyclic order. This is the form
the crossing count of §2 is defined on. -/
def pieces (P : ClosedPolygon m) : List Piece :=
  (List.range (m + 3)).map fun j : ℕ =>
    (P.vertex (j : ZMod (m + 3)), P.vertex ((j : ZMod (m + 3)) + 1))

/-- Every edge of the polygon is on the list. -/
theorem mem_pieces (P : ClosedPolygon m) (i : ZMod (m + 3)) :
    (P.vertex i, P.vertex (i + 1)) ∈ P.pieces := by
  refine List.mem_map.2 ⟨i.val, List.mem_range.2 (ZMod.val_lt i), ?_⟩
  rw [ZMod.natCast_rightInverse i]

/-- Every piece on the list is an edge of the polygon. -/
theorem exists_of_mem_pieces {P : ClosedPolygon m} {Q : Piece} (hQ : Q ∈ P.pieces) :
    ∃ i : ZMod (m + 3), Q = (P.vertex i, P.vertex (i + 1)) := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hQ
  exact ⟨(j : ZMod (m + 3)), rfl⟩

/-- No edge of a simple closed polygon is degenerate: consecutive vertices are distinct. -/
theorem pieces_nondeg (P : ClosedPolygon m) : ∀ Q ∈ P.pieces, Q.Nondeg := by
  intro Q hQ
  obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
  exact P.vertex_ne i

/-- **The edge list is a closed chain.** Each vertex is the terminal end of one edge and the
initial end of the next, so it is counted twice; the cycle closes because `m + 3` is `0` in
`ZMod (m + 3)`, which makes the two ends of the telescoping sum the same vertex. -/
theorem isClosedChain_pieces (P : ClosedPolygon m) : IsClosedChain P.pieces := by
  intro f
  have hmap : (P.pieces.map fun Q => f Q.1 + f Q.2)
      = (List.range (m + 3)).map fun j : ℕ =>
        f (P.vertex (j : ZMod (m + 3))) + f (P.vertex ((j + 1 : ℕ) : ZMod (m + 3))) := by
    rw [pieces, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, natCast_succ]
  rw [hmap]
  have key := sum_range_boundary (fun k : ℕ => f (P.vertex (k : ZMod (m + 3)))) (m + 3)
  rw [key, Nat.cast_zero, ZMod.natCast_self]
  exact add_self_zmod_two _

/-- **The edge list carries the polygon.** Without this equation no parity statement says
anything about a `ClosedPolygon`: the crossing count is defined against `cover`, and the collar
against `carrier`. -/
theorem cover_pieces (P : ClosedPolygon m) : cover P.pieces = P.carrier := by
  apply Set.Subset.antisymm
  · rw [cover]
    refine Set.iUnion₂_subset fun Q hQ => ?_
    obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
    exact Set.subset_iUnion (fun i => P.edge i) i
  · refine Set.iUnion_subset fun i => ?_
    exact fun z hz => mem_cover (P.mem_pieces i) hz

/-! ## The curve bridge

`chain k` is the union of the edges leaving vertices `0, …, k`. Each is an arc from vertex `0`
to vertex `k + 1`, obtained from its predecessor by `IsArcBetween.concatenate`; the whole
carrier is the last of them plus the edge that runs back to vertex `0`. -/

/-- The union of the edges leaving vertices `0, 1, …, k`. -/
def chain (P : ClosedPolygon m) : ℕ → Set Plane
  | 0 => P.edge 0
  | k + 1 => chain P k ∪ P.edge ((k + 1 : ℕ) : ZMod (m + 3))

theorem mem_chain_iff {z : Plane} {k : ℕ} :
    z ∈ P.chain k ↔ ∃ j ≤ k, z ∈ P.edge (j : ZMod (m + 3)) := by
  induction k with
  | zero =>
    constructor
    · intro hz
      exact ⟨0, le_rfl, by simpa [chain] using hz⟩
    · rintro ⟨j, hj, hzj⟩
      obtain rfl : j = 0 := Nat.le_zero.1 hj
      simpa [chain] using hzj
  | succ k ih =>
    simp only [chain, Set.mem_union]
    constructor
    · rintro (hz | hz)
      · obtain ⟨j, hj, hzj⟩ := ih.1 hz
        exact ⟨j, le_trans hj (Nat.le_succ k), hzj⟩
      · exact ⟨k + 1, le_rfl, hz⟩
    · rintro ⟨j, hj, hzj⟩
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact Or.inl (ih.2 ⟨j, Nat.lt_succ_iff.1 hlt, hzj⟩)
      · obtain rfl : j = k + 1 := le_antisymm hj hge
        exact Or.inr hzj

/-- Running through all `m + 3` edges exhausts the carrier. -/
theorem chain_eq_carrier (P : ClosedPolygon m) : P.chain (m + 2) = P.carrier := by
  ext z
  rw [mem_chain_iff]
  constructor
  · rintro ⟨j, -, hzj⟩
    exact Set.mem_iUnion.2 ⟨_, hzj⟩
  · intro hz
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.1 hz
    refine ⟨i.val, ?_, ?_⟩
    · have := ZMod.val_lt i
      omega
    · rwa [ZMod.natCast_rightInverse i]

/-- **The partial chains are arcs.** One edge at a time, glued at the vertex they share:
`edge_meet_earlier` is exactly the hypothesis `IsArcBetween.concatenate` asks for. The bound
`k + 1 < m + 3` is what keeps the growing arc from meeting its own start. -/
theorem isArcBetween_chain (P : ClosedPolygon m) :
    ∀ k : ℕ, k + 1 < m + 3 →
      IsArcBetween (P.chain k) (P.vertex 0) (P.vertex ((k + 1 : ℕ) : ZMod (m + 3))) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [natCast_succ]
    exact isArcBetween_segment (P.vertex_ne 0)
  | succ k ih =>
    intro hk
    have hA := ih (by omega)
    have hB : IsArcBetween (P.edge ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 + 1 : ℕ) : ZMod (m + 3))) := by
      rw [natCast_succ (k + 1)]
      exact isArcBetween_segment (P.vertex_ne _)
    have hmeet : ∀ z ∈ P.chain k, z ∈ P.edge ((k + 1 : ℕ) : ZMod (m + 3)) →
        z = P.vertex ((k + 1 : ℕ) : ZMod (m + 3)) := by
      intro z hz hze
      obtain ⟨j, hj, hzj⟩ := mem_chain_iff.1 hz
      exact edge_meet_earlier (by omega) (by omega) hzj hze
    exact hA.concatenate hB hmeet

/-- **The carrier of a simple closed polygon is a Jordan curve.** The arc through all but the
last edge, and the last edge running back to where it started, meet exactly at their two
shared endpoints. -/
theorem isJordanCurve_carrier (P : ClosedPolygon m) : IsJordanCurve P.carrier := by
  have hlast : ((m + 2 : ℕ) : ZMod (m + 3)) + 1 = 0 := by
    rw [← natCast_succ]
    exact ZMod.natCast_self (m + 3)
  have hA : IsArcBetween (P.chain (m + 1)) (P.vertex 0)
      (P.vertex ((m + 2 : ℕ) : ZMod (m + 3))) := P.isArcBetween_chain (m + 1) (by omega)
  have hedge : P.edge ((m + 2 : ℕ) : ZMod (m + 3))
      = segment ℝ (P.vertex ((m + 2 : ℕ) : ZMod (m + 3))) (P.vertex 0) := by
    rw [edge, hlast]
  have hB : IsArcBetween (P.edge ((m + 2 : ℕ) : ZMod (m + 3)))
      (P.vertex ((m + 2 : ℕ) : ZMod (m + 3))) (P.vertex 0) := by
    rw [hedge]
    refine isArcBetween_segment ?_
    rw [← hlast]
    exact P.vertex_ne _
  have hmeet : ∀ z ∈ P.chain (m + 1), z ∈ P.edge ((m + 2 : ℕ) : ZMod (m + 3)) →
      z = P.vertex 0 ∨ z = P.vertex ((m + 2 : ℕ) : ZMod (m + 3)) := by
    intro z hz hze
    obtain ⟨j, hj, hzj⟩ := mem_chain_iff.1 hz
    exact edge_meet_last (by omega) hzj hze
  have hcurve := IsJordanCurve.of_two_arcs hA hB hmeet
  have hsplit : P.chain (m + 2)
      = P.chain (m + 1) ∪ P.edge ((m + 2 : ℕ) : ZMod (m + 3)) := rfl
  rwa [← hsplit, chain_eq_carrier] at hcurve

/-! ### The carrier is polygonal

`IsPolygonal` asks for a vertex list whose `poly` carrier is the set. Cycling once round the
polygon and coming back to the first vertex is that list. -/

/-! ## The bridge in use

With both halves in place a parity statement can be read off a `ClosedPolygon` directly. -/

/-- A ray direction level for no edge of the polygon; the blueprint's "rotate the coordinate
system so that no edge is horizontal", with nothing rotated. -/
theorem exists_direction_pieces (P : ClosedPolygon m) :
    ∃ u : Plane, Plane.IsDirection u ∧ ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2 :=
  exists_direction_hgt_ne P.pieces P.pieces_nondeg

/-- **Crossing parity for a closed polygon** (Lemma 2.2): `π_C` is constant on the component
of the complement of the *carrier* containing a given point. -/
theorem parity_eq_of_mem_connectedComponentIn_carrier (P : ClosedPolygon m) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ P.carrier) (hy : y ∈ connectedComponentIn P.carrierᶜ x) :
    parity u P.pieces y = parity u P.pieces x := by
  rw [← P.cover_pieces] at hx hy
  exact parity_eq_of_mem_connectedComponentIn hu hL P.isClosedChain_pieces hx hy

/-! ### The flip across an edge

The second half of Lemma 2.2 is stated for the edge list split around the edge being crossed,
`L₁ ++ (a, b) :: L₂`. Splitting is `List.append_of_mem`; what has to be checked is that the two
remaining fragments miss the point being crossed, and that is `edges_meet` again — another edge
can reach an interior point of this one only at one of this one's two ends, which an interior
point is not. -/

/-- What a list of pieces occupies, taken apart. The counterpart of `Schoenflies.mem_cover`,
which only builds; **this belongs next to it in `Schoenflies/Parity.lean`.** -/
theorem exists_of_mem_cover {L : List Piece} {z : Plane} (hz : z ∈ cover L) :
    ∃ R ∈ L, z ∈ R.seg := by
  rw [cover] at hz
  simpa using hz

/-- An interior point of one edge lies on no other edge: `edges_meet` puts any other edge's
meeting point at an end of this one, and an interior point is neither end. -/
theorem notMem_edge_of_mem_openSegment {i j : ZMod (m + 3)} (hij : j ≠ i) {p : Plane}
    (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) : p ∉ P.edge j := by
  intro hpj
  have hmem := P.edges_meet i j (Ne.symm hij)
    (Set.mem_inter (openSegment_subset_segment ℝ _ _ hp) hpj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl
  · exact P.vertex_ne i (left_mem_openSegment_iff.1 hp)
  · exact P.vertex_ne i (right_mem_openSegment_iff.1 hp)

/-- The edge list has no repeated entry: distinct indices name distinct initial vertices. -/
theorem pieces_nodup (P : ClosedPolygon m) : P.pieces.Nodup := by
  rw [pieces]
  refine List.Nodup.map_on (fun j hj k hk heq => ?_) List.nodup_range
  exact natCast_inj (List.mem_range.1 hj) (List.mem_range.1 hk)
    (P.vertex_inj (congrArg Prod.fst heq))

/-- **Opposite sides of an edge, for a closed polygon** (Lemma 2.2, second half). Just before
and just after an interior point of an edge, in the ray direction, the base point is off the
carrier and the crossing parity differs by one. -/
theorem parity_flip_carrier (P : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) (i : ZMod (m + 3)) {p : Plane}
    (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      p - t • u ∉ P.carrier ∧ p + t • u ∉ P.carrier ∧
        parity u P.pieces (p - t • u) = parity u P.pieces (p + t • u) + 1 := by
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem (P.mem_pieces i)
  -- the edge being crossed occurs only once, so it is on neither fragment
  have hnodup := P.pieces_nodup
  rw [hsplit, List.nodup_append] at hnodup
  obtain ⟨-, hnd2, hdisj⟩ := hnodup
  have hQ₁ : (P.vertex i, P.vertex (i + 1)) ∉ L₁ := fun hmem => hdisj _ hmem _ (by simp) rfl
  have hQ₂ : (P.vertex i, P.vertex (i + 1)) ∉ L₂ := (List.nodup_cons.1 hnd2).1
  have hmiss : ∀ R ∈ L₁ ++ L₂, p ∉ Piece.seg R := by
    intro R hR
    have hRne : R ≠ (P.vertex i, P.vertex (i + 1)) := by
      rcases List.mem_append.1 hR with h | h
      · exact fun heq => hQ₁ (heq ▸ h)
      · exact fun heq => hQ₂ (heq ▸ h)
    have hRmem : R ∈ P.pieces := by
      rw [hsplit]
      rcases List.mem_append.1 hR with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    obtain ⟨j, rfl⟩ := exists_of_mem_pieces hRmem
    exact notMem_edge_of_mem_openSegment (fun heq => hRne (by rw [heq])) hp
  have h1 : p ∉ cover L₁ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_left _ hR) hpR
  have h2 : p ∉ cover L₂ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_right _ hR) hpR
  have hL' : ∀ R ∈ L₁ ++ (P.vertex i, P.vertex (i + 1)) :: L₂, hgt u R.1 ≠ hgt u R.2 := by
    rw [← hsplit]; exact hL
  obtain ⟨δ, hδ, hmain⟩ := parity_flip hu hL' hp h1 h2
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  obtain ⟨ha, hb, hc⟩ := hmain t ht htδ
  rw [← hsplit] at ha hb hc
  rw [P.cover_pieces] at ha hb
  exact ⟨ha, hb, hc⟩

end ClosedPolygon

end Schoenflies
end

section
-- module Solutions.Q146_CD.StripConnected
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The collar of a closed polygon is two-sided

`Schoenflies/Strip.lean` builds the blocks of Lemma 1.8 and proves the hard local half of the
statement: the two labelled sides are disjoint. This module closes the lemma for a *closed*
polygon by supplying the two remaining global facts.

* **Each side is connected.** The blueprint says "consecutive edge and vertex blocks overlap in
  a nonempty labelled half-strip, so the union of all left pieces is connected". Here that
  overlap is produced explicitly: `StripData.mem_overlapL_start` puts the point at frame
  position `(3 lam / 2, rho / 2)` in both `blockL i` and `sectorL i`, and
  `StripData.mem_overlapL_finish` puts the point at `(len i - 3 lam / 2, rho / 2)` in both
  `blockL i` and `sectorL (i + 1)`. The two `StripData` constraints that make these work are
  exactly the two the structure advertises for the purpose: `four_lam_lt_len` keeps the frame
  position inside the block, and `two_lam_lt_R` keeps it inside the sector, since
  `3 lam / 2 + rho / 2 < 2 lam < R`.

  The chaining is then a finite induction along `chainL`, and it does **not** need the
  wrap-around: connectedness of a union of connected sets only needs *some* spanning tree of
  the overlap graph, and the linear chain `0, 1, …, m + 2` is one. The blueprint's "the labels
  return consistently after one circuit" is a statement about the *labelling*, not about
  connectedness, and it is `Strip.sideL_disjoint_sideR`, already proved: it is what makes
  `sideL` and `sideR` two sets rather than one.

* **The collar is a neighbourhood, and removing the curve leaves exactly the two sides.**
  `StripData.nbhd_diff_carrier` is immediate from the two disjointness results of `Strip.lean`.
  Openness of `nbhd` is not: `nbhd` contains the curve, so it has to be recognised as a union
  of open sets. `StripData.nbhd_eq` does that, rewriting it as the union of the vertex balls
  and the full edge tubes; the two inclusions are `ball_diff_carrier_subset` and
  `tube_diff_carrier_subset` one way, and the covering of each edge by "near the first vertex,
  near the second vertex, or in the trimmed middle" the other way.

## Blueprint

* `Schoenflies.StripData.isConnected_sideL`, `.isConnected_sideR` — "the union of all left
  pieces is connected; the same is true on the right", inside Lemma 1.8 (a).
* `Schoenflies.StripData.nbhd_diff_carrier` — `N \ P = N_L ⊔ N_R`, Lemma 1.8 (a).
* `Schoenflies.StripData.collar` — Lemma 1.8 (a) for a closed polygon, given the constants.

Producing the constants is `exists_stripData`, which lives elsewhere; every statement here is
for a given `D : StripData P`, exactly as in `Schoenflies/Strip.lean`.
-/

open Metric Set

namespace Schoenflies

open Plane

variable {m : ℕ}

namespace ClosedPolygon

variable {P : ClosedPolygon m} {i : ZMod (m + 3)} {c t s : ℝ}

/-! ### Two frames at one edge

Everything below needs the edge frame read from *both* ends: `Strip.lean` has the departure
end, and the overlap with the sector at the far vertex needs the arrival end. -/

/-- The incoming ray at a vertex is a unit vector. -/
theorem isDirection_rayIn : IsDirection (P.rayIn i) := isDirection_dir vertex_pred_ne

/-- The far vertex of edge `i` sits at frame position `(len i, 0)`. -/
theorem off_sub_vertex_succ :
    P.off i t s - P.vertex (i + 1) = (t - P.len i) • P.tang i + s • perp (P.tang i) := by
  have hv : P.vertex (i + 1) = P.vertex i + (P.len i) • P.tang i := by
    rw [len_smul_tang]; module
  rw [off, hv]; module

/-- The block-to-far-sector distance bound, the mirror of `dist_off_vertex_le`. -/
theorem dist_off_vertex_succ_le : dist (P.off i t s) (P.vertex (i + 1)) ≤ |t - P.len i| + |s| := by
  rw [dist_eq_norm, off_sub_vertex_succ]
  calc ‖(t - P.len i) • P.tang i + s • perp (P.tang i)‖
      ≤ ‖(t - P.len i) • P.tang i‖ + ‖s • perp (P.tang i)‖ := norm_add_le _ _
    _ = |t - P.len i| + |s| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_perp,
          isDirection_tang.norm, mul_one, mul_one]

/-- The distance from a point of edge `i` to the edge's far endpoint, the mirror of
`dist_pt_vertex`. -/
theorem dist_pt_vertex_succ : dist (P.pt i c) (P.vertex (i + 1)) = |c - P.len i| := by
  rw [pt, dist_eq_norm, off_sub_vertex_succ, zero_smul, add_zero, norm_smul, Real.norm_eq_abs,
    isDirection_tang.norm, mul_one]

/-! ### The two incident edges, as rays out of a vertex

`mem_edge_sub` and `mem_edge_pred_sub` read a point of an incident edge as a multiple of a ray.
The converses are what says that a ball about a vertex minus the curve is covered by the two
sectors: a direction on one of the two rays is *on the curve*, not beside it. -/

/-- Walking back along the incoming ray from vertex `i` traverses the previous edge. -/
theorem vertex_add_smul_rayIn (P : ClosedPolygon m) (i : ZMod (m + 3)) (c : ℝ) :
    P.vertex i + c • P.rayIn i = P.pt (i - 1) (P.len (i - 1) - c) := by
  have hsucc : i - 1 + 1 = i := sub_add_cancel i 1
  have hr : P.rayIn i = -P.tang (i - 1) := by
    have h := rayIn_succ (P := P) (i := i - 1)
    rwa [hsucc] at h
  have hlen : P.vertex i = P.vertex (i - 1) + (P.len (i - 1)) • P.tang (i - 1) := by
    rw [len_smul_tang, hsucc]; module
  rw [pt_eq, hr, hlen]
  module

/-- A point of the incoming ray at distance at most the previous edge's length lies on that
edge. -/
theorem mem_edge_pred_of_smul_rayIn (hc0 : 0 ≤ c) (hc1 : c ≤ P.len (i - 1)) :
    P.vertex i + c • P.rayIn i ∈ P.edge (i - 1) := by
  rw [vertex_add_smul_rayIn]
  exact pt_mem_edge ⟨by linarith, by linarith⟩

/-- A point of the outgoing ray at distance at most the edge's length lies on that edge. -/
theorem mem_edge_of_smul_tang (hc0 : 0 ≤ c) (hc1 : c ≤ P.len i) :
    P.vertex i + c • P.tang i ∈ P.edge i := by
  rw [← pt_eq]
  exact pt_mem_edge ⟨hc0, hc1⟩

end ClosedPolygon

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i j : ZMod (m + 3)} {x : Plane}

/-! ### The overlaps

The blueprint's "consecutive edge and vertex blocks overlap in a nonempty labelled half-strip".
Both witnesses sit at across-coordinate `rho / 2`, at along-coordinate `3 lam / 2` from the
vertex in question. The two hypotheses of `StripData` that were put there for this are
`four_lam_lt_len` — which gives `3 lam / 2 < len i - lam`, so the point is inside the block —
and `two_lam_lt_R` together with `rho < lam` — which gives
`3 lam / 2 + rho / 2 < 2 lam < R`, so the point is inside the sector. -/

/-- The along-coordinate of the witnesses clears the near trim. -/
theorem lam_lt_three_halves_lam : D.lam < 3 * D.lam / 2 := by have := D.lam_pos; linarith

/-- …and stays short of the far one, by `four_lam_lt_len`. -/
theorem three_halves_lam_lt : 3 * D.lam / 2 < P.len i - D.lam := by
  have := D.lam_pos
  have := D.four_lam_lt_len i
  linarith

/-- …and the whole witness stays inside the sector, by `rho_lt_lam` and `two_lam_lt_R`. -/
theorem overlap_dist_lt : 3 * D.lam / 2 + D.rho / 2 < D.R := by
  have := D.rho_lt_lam
  have := D.two_lam_lt_R
  linarith

/-- **The overlap at the departure vertex.** The point at frame position `(3 lam / 2, rho / 2)`
of edge `i` lies both in the left block of that edge and in the left sector at `i`. -/
theorem mem_overlapL_start :
    P.off i (3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i ∩ D.sectorL i := by
  have hmem : P.off i (3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i :=
    D.mem_blockL_off.2 ⟨D.lam_lt_three_halves_lam, D.three_halves_lam_lt,
      by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockL_sub_mem_arcL_start hmem, ?_⟩
  -- The sector reaches this far because `3 lam / 2 + rho / 2 < 2 lam < R`.
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_le ?_
  rw [abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

/-- **The overlap at the arrival vertex.** The point at frame position
`(len i - 3 lam / 2, rho / 2)` of edge `i` lies both in the left block of that edge and in the
left sector at `i + 1`. -/
theorem mem_overlapL_finish :
    P.off i (P.len i - 3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i ∩ D.sectorL (i + 1) := by
  have h1 : D.lam < P.len i - 3 * D.lam / 2 := by
    have := D.lam_pos; have := D.four_lam_lt_len i; linarith
  have h2 : P.len i - 3 * D.lam / 2 < P.len i - D.lam := by have := D.lam_pos; linarith
  have hmem : P.off i (P.len i - 3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i :=
    D.mem_blockL_off.2 ⟨h1, h2, by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockL_sub_mem_arcL_finish hmem, ?_⟩
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_succ_le ?_
  rw [show P.len i - 3 * D.lam / 2 - P.len i = -(3 * D.lam / 2) by ring,
    abs_neg, abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

/-- The right-hand mirror of `mem_overlapL_start`. -/
theorem mem_overlapR_start :
    P.off i (3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i ∩ D.sectorR i := by
  have hmem : P.off i (3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i :=
    D.mem_blockR_off.2 ⟨D.lam_lt_three_halves_lam, D.three_halves_lam_lt,
      by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockR_sub_mem_arcR_start hmem, ?_⟩
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_le ?_
  rw [abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_neg, abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

/-- The right-hand mirror of `mem_overlapL_finish`. -/
theorem mem_overlapR_finish :
    P.off i (P.len i - 3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i ∩ D.sectorR (i + 1) := by
  have h1 : D.lam < P.len i - 3 * D.lam / 2 := by
    have := D.lam_pos; have := D.four_lam_lt_len i; linarith
  have h2 : P.len i - 3 * D.lam / 2 < P.len i - D.lam := by have := D.lam_pos; linarith
  have hmem : P.off i (P.len i - 3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i :=
    D.mem_blockR_off.2 ⟨h1, h2, by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockR_sub_mem_arcR_finish hmem, ?_⟩
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_succ_le ?_
  rw [show P.len i - 3 * D.lam / 2 - P.len i = -(3 * D.lam / 2) by ring,
    abs_neg, abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_neg, abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

theorem blockL_nonempty : (D.blockL i).Nonempty := ⟨_, D.mem_overlapL_start.1⟩
theorem blockR_nonempty : (D.blockR i).Nonempty := ⟨_, D.mem_overlapR_start.1⟩

theorem isConnected_blockL : IsConnected (D.blockL i) :=
  D.convex_blockL.isConnected D.blockL_nonempty

theorem isConnected_blockR : IsConnected (D.blockR i) :=
  D.convex_blockR.isConnected D.blockR_nonempty

end StripData

/-! ## Chaining a cyclic family

The union of the left pieces is connected because consecutive pieces overlap. This is a fact
about any cyclically indexed family, and it is worth isolating: it is used once on the left and
once on the right, and it is where the "cyclic" of the blueprint gets examined.

The point to notice is that the closing overlap `F (last) ∩ F 0` is **not used**. A union of
connected sets is connected as soon as the overlap graph is connected, and the path
`0 — 1 — ⋯ — N-1` already spans it; the extra edge back to `0` is a cycle, not a new vertex.
The blueprint's "the labels return consistently after one circuit" is therefore not needed
*here*: it is needed to know that the left label and the right label never collide, which is
`StripData.sideL_disjoint_sideR`, and that is already proved. -/

/-- A cyclically indexed family of connected sets in which every member meets its successor has
connected union. Only the overlaps along the linear chain `0, 1, …, N - 1` are consumed. -/
theorem isConnected_iUnion_zmod {α : Type*} [TopologicalSpace α] {N : ℕ} [NeZero N]
    (F : ZMod N → Set α) (hconn : ∀ i, IsConnected (F i))
    (hmeet : ∀ i, (F i ∩ F (i + 1)).Nonempty) : IsConnected (⋃ i, F i) := by
  -- `chain k` is the union of the pieces with index the cast of some `j ≤ k`.
  set chain : ℕ → Set α := fun k => ⋃ j : ℕ, ⋃ _ : j ≤ k, F (j : ZMod N) with hchain
  have hstep : ∀ k : ℕ, chain (k + 1) = chain k ∪ F ((k + 1 : ℕ) : ZMod N) := by
    intro k
    ext y
    simp only [hchain, Set.mem_iUnion, Set.mem_union, exists_prop]
    constructor
    · rintro ⟨j, hj, hy⟩
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact Or.inl ⟨j, Nat.lt_succ_iff.1 h, hy⟩
      · exact Or.inr ((le_antisymm hj h) ▸ hy)
    · rintro (⟨j, hj, hy⟩ | hy)
      · exact ⟨j, le_trans hj (Nat.le_succ k), hy⟩
      · exact ⟨k + 1, le_refl _, hy⟩
  have hzero : chain 0 = F 0 := by
    ext y
    simp only [hchain, Set.mem_iUnion, Nat.le_zero, exists_prop]
    constructor
    · rintro ⟨j, rfl, hy⟩; simpa using hy
    · intro hy; exact ⟨0, rfl, by simpa using hy⟩
  have key : ∀ k : ℕ, IsConnected (chain k) := by
    intro k
    induction k with
    | zero => rw [hzero]; exact hconn 0
    | succ k ih =>
        rw [hstep k]
        refine IsConnected.union ?_ ih (hconn _)
        -- The overlap of the last two links, transported along `((k+1 : ℕ) : ZMod N) = k + 1`.
        obtain ⟨y, hy1, hy2⟩ := hmeet ((k : ℕ) : ZMod N)
        refine ⟨y, ?_, ?_⟩
        · exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨le_refl k, hy1⟩⟩
        · rwa [show ((k + 1 : ℕ) : ZMod N) = ((k : ℕ) : ZMod N) + 1 by push_cast; ring]
  have hcover : (⋃ i, F i) = chain (N - 1) := by
    refine Set.Subset.antisymm ?_ ?_
    · refine Set.iUnion_subset fun i y hy => ?_
      have hval : ((i.val : ℕ) : ZMod N) = i := ZMod.natCast_rightInverse i
      have hlt : i.val < N := ZMod.val_lt i
      refine Set.mem_iUnion.2 ⟨i.val, Set.mem_iUnion.2 ⟨by omega, ?_⟩⟩
      rw [hval]
      exact hy
    · refine Set.iUnion_subset fun j => Set.iUnion_subset fun _ => Set.subset_iUnion _ _
  rw [hcover]
  exact key _

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i j : ZMod (m + 3)} {x : Plane}

/-! ### The two sides are connected -/

/-- The left piece at index `i`: the left sector at vertex `i` glued to the left block of the
edge leaving `i`. -/
def pieceL (i : ZMod (m + 3)) : Set Plane := D.sectorL i ∪ D.blockL i

/-- The right piece at index `i`. -/
def pieceR (i : ZMod (m + 3)) : Set Plane := D.sectorR i ∪ D.blockR i

theorem sideL_eq_iUnion : D.sideL = ⋃ i, D.pieceL i := rfl
theorem sideR_eq_iUnion : D.sideR = ⋃ i, D.pieceR i := rfl

/-- A piece is connected: its sector and its block overlap, at `mem_overlapL_start`. -/
theorem isConnected_pieceL : IsConnected (D.pieceL i) :=
  IsConnected.union ⟨_, D.mem_overlapL_start.2, D.mem_overlapL_start.1⟩ D.isConnected_sectorL
    D.isConnected_blockL

theorem isConnected_pieceR : IsConnected (D.pieceR i) :=
  IsConnected.union ⟨_, D.mem_overlapR_start.2, D.mem_overlapR_start.1⟩ D.isConnected_sectorR
    D.isConnected_blockR

/-- Consecutive pieces overlap: the block of edge `i` reaches into the sector at `i + 1`. -/
theorem pieceL_inter_succ_nonempty : (D.pieceL i ∩ D.pieceL (i + 1)).Nonempty :=
  ⟨_, Or.inr D.mem_overlapL_finish.1, Or.inl D.mem_overlapL_finish.2⟩

theorem pieceR_inter_succ_nonempty : (D.pieceR i ∩ D.pieceR (i + 1)).Nonempty :=
  ⟨_, Or.inr D.mem_overlapR_finish.1, Or.inl D.mem_overlapR_finish.2⟩

/-- **The left side of the collar is connected.** -/
theorem isConnected_sideL : IsConnected D.sideL := by
  rw [D.sideL_eq_iUnion]
  exact isConnected_iUnion_zmod _ (fun i => D.isConnected_pieceL)
    (fun i => D.pieceL_inter_succ_nonempty)

/-- **The right side of the collar is connected.** -/
theorem isConnected_sideR : IsConnected D.sideR := by
  rw [D.sideR_eq_iUnion]
  exact isConnected_iUnion_zmod _ (fun i => D.isConnected_pieceR)
    (fun i => D.pieceR_inter_succ_nonempty)

/-! ### The collar minus the curve is exactly the two sides

`nbhd` was *defined* as `sideL ∪ sideR ∪ carrier`, so this is only the two disjointness
statements of `Strip.lean` read backwards. -/

/-- **Lemma 1.8 (a), the set equality.** Removing the curve from the collar leaves exactly the
two labelled sides. With `sideL_disjoint_sideR` this is `N \ P = N_L ⊔ N_R`. -/
theorem nbhd_diff_carrier : D.nbhd \ P.carrier = D.sideL ∪ D.sideR := by
  ext y
  constructor
  · rintro ⟨hy, hyc⟩
    rcases hy with h | h
    · exact h
    · exact absurd h hyc
  · intro hy
    refine ⟨Or.inl hy, ?_⟩
    rcases hy with h | h
    · exact fun hc => Set.disjoint_left.1 D.sideL_disjoint_carrier h hc
    · exact fun hc => Set.disjoint_left.1 D.sideR_disjoint_carrier h hc

theorem carrier_subset_nbhd : P.carrier ⊆ D.nbhd := fun _ hy => Or.inr hy

/-! ### The collar is open

`nbhd` contains the curve, so openness is not formal: it has to be exhibited as a union of open
sets. The two families are the vertex balls and the *full* edge tubes — the block of half-width
`rho` on both sides of the trimmed edge, core included. Each of the two is covered by
`nbhd` because its points off the curve are labelled (`ball_diff_carrier_subset`,
`tube_diff_carrier_subset`); conversely they cover `nbhd`, the only nontrivial part being that
they cover the curve itself, which is the three-way split of an edge into "within `R` of the
first vertex", "within `R` of the second", and "in the trimmed middle". -/

/-- The full tube of edge `i`: the trimmed edge thickened by `rho` on both sides. It is the
union of the two blocks with the piece of the edge between them. -/
def tube (i : ZMod (m + 3)) : Set Plane :=
  strip (P.vertex i) (P.tang i) D.lam (P.len i - D.lam) (-D.rho) D.rho

theorem isOpen_tube : IsOpen (D.tube i) := isOpen_strip _ _ _ _ _ _

theorem mem_tube_off {t s : ℝ} : P.off i t s ∈ D.tube i ↔
    D.lam < t ∧ t < P.len i - D.lam ∧ -D.rho < s ∧ s < D.rho := by
  rw [tube, mem_strip_iff, ClosedPolygon.coordAlong_off, ClosedPolygon.coordAcross_off]

theorem blockL_subset_tube : D.blockL i ⊆ D.tube i := by
  intro y hy
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockL_iff.1 hy
  exact ⟨h1, h2, by linarith [D.rho_pos], h4⟩

theorem blockR_subset_tube : D.blockR i ⊆ D.tube i := by
  intro y hy
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockR_iff.1 hy
  exact ⟨h1, h2, h3, by linarith [D.rho_pos]⟩

/-- **A vertex ball minus the curve is covered by the two sectors at that vertex.** A point of
the ball off the curve points in some direction from the vertex; by `mem_ray_or_mem_arcCCW'`
that direction is either one of the two incident rays — and then the point is *on* the incident
edge, because `R_le_len` says the sector does not run past the far end — or on one of the two
arcs, and then the point is in the corresponding sector. -/
theorem ball_diff_carrier_subset :
    ball (P.vertex i) D.R \ P.carrier ⊆ D.sectorL i ∪ D.sectorR i := by
  rintro y ⟨hy, hyc⟩
  have hne : y - P.vertex i ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    apply hyc
    rw [h]
    exact ClosedPolygon.vertex_mem_carrier
  rcases mem_ray_or_mem_arcCCW' (ClosedPolygon.det_rays_ne_zero (P := P) (i := i)) hne with
    ⟨c, hc, hcy⟩ | ⟨c, hc, hcy⟩ | harc | harc
  · -- Back along the incoming edge: the point lies on edge `i - 1`.
    exfalso
    apply hyc
    have hd : dist y (P.vertex i) = c := by
      rw [dist_eq_norm, hcy, norm_smul, Real.norm_eq_abs,
        ClosedPolygon.isDirection_rayIn.norm, mul_one, abs_of_pos hc]
    rw [mem_ball, hd] at hy
    have hy' : y = P.vertex i + c • P.rayIn i := by rw [← hcy]; module
    rw [hy']
    exact ClosedPolygon.edge_subset_carrier (ClosedPolygon.mem_edge_pred_of_smul_rayIn hc.le
      (le_trans hy.le (D.R_le_len (i - 1))))
  · -- Out along the outgoing edge: the point lies on edge `i`.
    exfalso
    apply hyc
    have hd : dist y (P.vertex i) = c := by
      rw [dist_eq_norm, hcy, norm_smul, Real.norm_eq_abs,
        ClosedPolygon.isDirection_tang.norm, mul_one, abs_of_pos hc]
    rw [mem_ball, hd] at hy
    have hy' : y = P.vertex i + c • P.tang i := by rw [← hcy]; module
    rw [hy']
    exact ClosedPolygon.edge_subset_carrier (ClosedPolygon.mem_edge_of_smul_tang hc.le
      (le_trans hy.le (D.R_le_len i)))
  · exact Or.inr ⟨harc, hy⟩
  · exact Or.inl ⟨harc, hy⟩

/-- **A tube minus the curve is its two blocks.** The only points of a tube on the curve are
those on the core of its own edge. -/
theorem tube_diff_carrier_subset : D.tube i \ P.carrier ⊆ D.blockL i ∪ D.blockR i := by
  rintro y ⟨⟨h1, h2, h3, h4⟩, hyc⟩
  rcases lt_trichotomy (coordAcross (P.vertex i) (P.tang i) y) 0 with h | h | h
  · exact Or.inr (D.mem_blockR_iff.2 ⟨h1, h2, h3, h⟩)
  · exfalso
    apply hyc
    have hy0 : y = P.pt i (coordAlong (P.vertex i) (P.tang i) y) := by
      rw [ClosedPolygon.pt, ← h]
      exact ClosedPolygon.off_coord P i y
    rw [hy0]
    exact ClosedPolygon.edge_subset_carrier (ClosedPolygon.pt_mem_edge
      ⟨by linarith [D.lam_pos], by linarith [D.lam_pos]⟩)
  · exact Or.inl (D.mem_blockL_iff.2 ⟨h1, h2, h, h4⟩)

/-- Each edge is covered by the ball at its first vertex, the ball at its second, and its own
tube: `lam < R` leaves no gap in the middle. -/
theorem carrier_subset_balls_union_tubes :
    P.carrier ⊆ (⋃ i, ball (P.vertex i) D.R) ∪ (⋃ i, D.tube i) := by
  rintro y hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  rw [ClosedPolygon.mem_edge_iff] at hi
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := hi
  rcases lt_or_ge c D.R with h1 | h1
  · refine Or.inl (Set.mem_iUnion.2 ⟨i, ?_⟩)
    rw [mem_ball, ClosedPolygon.dist_pt_vertex, abs_of_nonneg hc0]
    exact h1
  rcases lt_or_ge (P.len i - D.R) c with h2 | h2
  · refine Or.inl (Set.mem_iUnion.2 ⟨i + 1, ?_⟩)
    rw [mem_ball, ClosedPolygon.dist_pt_vertex_succ, abs_of_nonpos (by linarith)]
    linarith
  · refine Or.inr (Set.mem_iUnion.2 ⟨i, ?_⟩)
    rw [ClosedPolygon.pt]
    have hlam := D.lam_pos
    have hR := D.two_lam_lt_R
    exact D.mem_tube_off.2 ⟨by linarith, by linarith, by linarith [D.rho_pos], D.rho_pos⟩

/-- The collar is the union of the vertex balls and the edge tubes. This is the presentation
that makes it visibly open. -/
theorem nbhd_eq : D.nbhd = (⋃ i, ball (P.vertex i) D.R) ∪ (⋃ i, D.tube i) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ((hy | hy) | hy)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      rcases hi with hi | hi
      · exact Or.inl (Set.mem_iUnion.2 ⟨i, D.sector_subset_ball hi⟩)
      · exact Or.inr (Set.mem_iUnion.2 ⟨i, D.blockL_subset_tube hi⟩)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      rcases hi with hi | hi
      · exact Or.inl (Set.mem_iUnion.2 ⟨i, D.sectorR_subset_ball hi⟩)
      · exact Or.inr (Set.mem_iUnion.2 ⟨i, D.blockR_subset_tube hi⟩)
    · exact D.carrier_subset_balls_union_tubes hy
  · rintro y (hy | hy)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      by_cases hc : y ∈ P.carrier
      · exact Or.inr hc
      · rcases D.ball_diff_carrier_subset ⟨hi, hc⟩ with h | h
        · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, Or.inl h⟩))
        · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, Or.inl h⟩))
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      by_cases hc : y ∈ P.carrier
      · exact Or.inr hc
      · rcases D.tube_diff_carrier_subset ⟨hi, hc⟩ with h | h
        · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, Or.inr h⟩))
        · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, Or.inr h⟩))

theorem isOpen_nbhd : IsOpen D.nbhd := by
  rw [D.nbhd_eq]
  exact (isOpen_iUnion fun _ => isOpen_ball).union (isOpen_iUnion fun _ => D.isOpen_tube)

/-! ### Lemma 1.8 (a) -/

end StripData

end Schoenflies
end

section
-- module Solutions.Q146_CD.StripConstants
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The constants of a polygonal collar exist

`Schoenflies.StripData` names the three numbers the two-sided strip lemma runs on — a cone
radius `R`, a trim `lam` and a half-width `rho` — together with the separation hypotheses they
have to satisfy. Everything in `Schoenflies/Strip.lean` is stated *for a given* `StripData`;
this module produces one, removing that parameter from the resulting theorem.

The recipe is the blueprint's own, in the blueprint's order:

1. `R` from three sources — the pairwise vertex separations, the distance from each vertex to
   each nonincident edge, and the prescribed open set — each an instance of Lemma 1.4, plus
   `R ≤ len i` so that a sector cannot run past the far end of an incident edge. The vertex
   separations are asked for with a factor `2` of slack, which is what the block-versus-sector
   estimates of `Strip.lean` spend.
2. `lam := R / 5`, which gives `2 * lam < R` and, through `R ≤ len i`, also `4 * lam < len i`.
3. `rho` from the distance of each *trimmed* edge to every other edge, and from the germ
   threshold `rho * (1 + |⟪r₁, r₂⟫|) ≤ lam * |det r₁ r₂|` at every vertex. The determinant is
   nonzero at a corner, so the threshold is a positive upper bound on `rho` and is met by
   shrinking; `rho < lam` is one more shrinking.

Steps 1 and 3 are finite families of positive bounds, combined by
`Schoenflies.exists_pos_forall_of_finite`.

## What simplicity is used for

Two of the separations are *false* for a self-touching closed polygonal curve, and each is the
exact point where `ClosedPolygon.edges_meet` is consumed:

* `ClosedPolygon.vertex_notMem_edge` — a vertex lies on no edge but the two incident to it.
  This is what makes `{vertex i}` and `edge j` disjoint compact sets.
* `ClosedPolygon.trimmed_disjoint_edge` — the trimmed core of an edge misses every other edge.
  Here the two endpoints allowed by `edges_meet` are excluded by the trim itself, since a point
  of the core is at distance at least `lam` from both.

`edges_meet` as stated is one-sided (`edge i ∩ edge j ⊆ {vertex i, vertex (i + 1)}`), but it is
quantified over all ordered pairs, so the symmetric instance is available and both proofs below
use whichever side is convenient. It carries enough simplicity for both statements.

## Blueprint

* `Schoenflies.exists_stripData_subset` — the constants of Lemma 1.8 (Two-sided polygonal
  strips), chosen inside a prescribed open set containing the curve; this is the "Lemma 1.4 (a)
  lets all disks and strips be chosen inside the prescribed open set" of the last paragraph of
  the proof.
* `Schoenflies.exists_stripData` — the same without a prescribed open set.
* `Schoenflies.ClosedPolygon.exists_cone_radius`,
  `Schoenflies.ClosedPolygon.exists_half_width` — steps 1 and 3 of the recipe, which are the
  instances of Lemma 1.4 that Lemma 1.8 consumes.
* `Schoenflies.StripData.nbhd_subset_thickening` — the collar of Lemma 1.8 lies in the
  `R`-neighbourhood of the curve, which is how the prescribed open set is honoured.
-/

open Metric Set

namespace Schoenflies

open Plane

variable {m : ℕ}

namespace ClosedPolygon

variable {P : ClosedPolygon m} {i j : ZMod (m + 3)} {c lam : ℝ}

/-! ### Compactness of the pieces -/

theorem isCompact_edge : IsCompact (P.edge i) := isCompact_segment _ _

theorem isCompact_carrier (P : ClosedPolygon m) : IsCompact P.carrier :=
  isCompact_iUnion fun _ => isCompact_edge

theorem continuous_pt (P : ClosedPolygon m) (i : ZMod (m + 3)) : Continuous (P.pt i) := by
  have h : P.pt i = fun c : ℝ => P.vertex i + c • P.tang i := funext fun _ => pt_eq
  rw [h]
  exact continuous_const.add (continuous_id.smul continuous_const)

/-! ### What simplicity gives

The two statements below are the only consumers of `ClosedPolygon.edges_meet` in the whole
choice of constants, and neither is true without it. -/

/-- **Simplicity, first form.** A vertex lies on no edge but the two edges incident to it.
Without this the "a vertex is `2R` away from every nonincident edge" hypothesis of `StripData`
would be unsatisfiable, since the vertex would sit *on* one of those edges. -/
theorem vertex_notMem_edge (hj1 : j ≠ i - 1) (hj2 : j ≠ i) : P.vertex i ∉ P.edge j := by
  intro hx
  -- Use `edges_meet` in the order that puts the *other* edge's endpoints on the right.
  have hmem : P.vertex i ∈ P.edge j ∩ P.edge i := ⟨hx, vertex_mem_edge⟩
  have hsub := P.edges_meet j i hj2 hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with h | h
  · exact hj2 (P.vertex_inj h).symm
  · exact hj1 (by rw [P.vertex_inj h]; ring)

/-- The trimmed core of edge `i`: the points of the edge at distance at least `lam` from both
of its endpoints. An edge block of `StripData` hugs this core. -/
def trimmed (P : ClosedPolygon m) (i : ZMod (m + 3)) (lam : ℝ) : Set Plane :=
  P.pt i '' Set.Icc lam (P.len i - lam)

theorem pt_mem_trimmed (hc : c ∈ Set.Icc lam (P.len i - lam)) : P.pt i c ∈ P.trimmed i lam :=
  ⟨c, hc, rfl⟩

theorem isCompact_trimmed : IsCompact (P.trimmed i lam) :=
  isCompact_Icc.image (P.continuous_pt i)

/-- **Simplicity, second form.** The trimmed core of an edge misses every other edge. The two
common points `edges_meet` allows are the endpoints of the edge, and the trim removes them: a
core point is at distance at least `lam` from either endpoint. No lower bound on the edge
length is needed: if the trim eats the whole edge the core is empty. -/
theorem trimmed_disjoint_edge (hlam : 0 < lam) (hij : j ≠ i) :
    Disjoint (P.trimmed i lam) (P.edge j) := by
  rw [Set.disjoint_left]
  rintro x ⟨c, hc, rfl⟩ hx
  have hc0 : (0 : ℝ) ≤ c := le_trans hlam.le hc.1
  have hcl : c ≤ P.len i := le_trans hc.2 (by linarith)
  have hmem : P.pt i c ∈ P.edge i ∩ P.edge j := ⟨pt_mem_edge ⟨hc0, hcl⟩, hx⟩
  have hsub := P.edges_meet i j (Ne.symm hij) hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with h | h
  · -- The core point is the initial vertex, so its progress is `0`, below the trim.
    have h0 : |c| = 0 := by rw [← dist_pt_vertex (P := P) (i := i) (c := c), h, dist_self]
    rw [abs_of_nonneg hc0] at h0
    linarith [hc.1]
  · -- The core point is the terminal vertex, so its progress is `len i`, above the trim.
    have h0 : |c| = P.len i := by
      rw [← dist_pt_vertex (P := P) (i := i) (c := c), h, len, dist_eq_norm]
    rw [abs_of_nonneg hc0] at h0
    linarith [hc.2]

end ClosedPolygon

/-! ## Where the collar lives

The collar sits inside the `R`-neighbourhood of the curve: a sector is inside a ball of radius
`R` about a point of the curve, and a block is within `rho < R` of the foot of its
perpendicular, which is on the curve. This is the whole content of "the neighbourhoods may be
chosen inside any prescribed open set containing the curve". -/

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P)

/-- The collar of `Strip.lean` lies in the `R`-neighbourhood of the polygon. -/
theorem nbhd_subset_thickening : D.nbhd ⊆ thickening D.R P.carrier := by
  intro x hx
  have hx' : x ∈ D.sideL ∪ D.sideR ∪ P.carrier := hx
  rcases hx' with (hL | hR) | hc
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hL
    rcases hi with hi | hi
    · exact mem_thickening_iff.2 ⟨P.vertex i, ClosedPolygon.vertex_mem_carrier, hi.2⟩
    · obtain ⟨c, hcmem, hd⟩ := D.exists_foot (Or.inl hi)
      exact mem_thickening_iff.2 ⟨P.pt i c,
        ClosedPolygon.edge_subset_carrier (D.pt_mem_edge_of_trim hcmem), lt_trans hd D.rho_lt_R⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hR
    rcases hi with hi | hi
    · exact mem_thickening_iff.2 ⟨P.vertex i, ClosedPolygon.vertex_mem_carrier, hi.2⟩
    · obtain ⟨c, hcmem, hd⟩ := D.exists_foot (Or.inr hi)
      exact mem_thickening_iff.2 ⟨P.pt i c,
        ClosedPolygon.edge_subset_carrier (D.pt_mem_edge_of_trim hcmem), lt_trans hd D.rho_lt_R⟩
  · exact self_subset_thickening D.R_pos _ hc

end StripData

/-! ## Choosing the constants -/

namespace ClosedPolygon

/-- **Step 1: the cone radius.** One positive `R` that is below every edge length, that
separates the vertices pairwise with a factor `2` to spare, that keeps every vertex `2R` away
from every nonincident edge, and whose neighbourhood of the curve stays inside the prescribed
open set. -/
theorem exists_cone_radius (P : ClosedPolygon m) {U : Set Plane} (hU : IsOpen U)
    (hPU : P.carrier ⊆ U) :
    ∃ R > 0, (∀ i, R ≤ P.len i) ∧
      (∀ i j, i ≠ j → 2 * R ≤ dist (P.vertex i) (P.vertex j)) ∧
      (∀ i j, j ≠ i - 1 → j ≠ i → ∀ y ∈ P.edge j, 2 * R ≤ dist (P.vertex i) y) ∧
      thickening R P.carrier ⊆ U := by
  -- (1) below every edge length
  obtain ⟨e₁, he₁, hlen⟩ :=
    exists_pos_le_of_finite (Set.finite_univ (α := ZMod (m + 3))) (f := fun i => P.len i)
      (fun _ _ => len_pos)
  -- (2) the pairwise vertex separations: distinct vertices are distinct points
  have h₂ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.1 ≠ p.2 → ε ≤ dist (P.vertex p.1) (P.vertex p.2)) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h hne
      exact le_trans hδε (h hne)
    · rintro ⟨i, j⟩ -
      by_cases hij : i = j
      · exact ⟨1, one_pos, fun h => absurd hij h⟩
      · exact ⟨dist (P.vertex i) (P.vertex j),
          dist_pos.2 fun h => hij (P.vertex_inj h), fun _ => le_refl _⟩
  -- (3) a vertex against the edges it is not incident to: simplicity makes them disjoint
  have h₃ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.2 ≠ p.1 - 1 → p.2 ≠ p.1 → ∀ y ∈ P.edge p.2, ε ≤ dist (P.vertex p.1) y) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h h1 h2 y hy
      exact le_trans hδε (h h1 h2 y hy)
    · rintro ⟨i, j⟩ -
      by_cases hj1 : j = i - 1
      · exact ⟨1, one_pos, fun h => absurd hj1 h⟩
      by_cases hj2 : j = i
      · exact ⟨1, one_pos, fun _ h => absurd hj2 h⟩
      · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos isCompact_singleton isCompact_edge
          (Set.disjoint_singleton_left.2 (vertex_notMem_edge hj1 hj2))
        exact ⟨ρ, hρ, fun _ _ y hy => hsep _ rfl y hy⟩
  -- (4) the prescribed open set
  obtain ⟨e₄, he₄, hthick⟩ := Plane.exists_thickening_subset (isCompact_carrier P) hU hPU
  obtain ⟨e₂, he₂, hvv⟩ := h₂
  obtain ⟨e₃, he₃, hve⟩ := h₃
  refine ⟨min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄),
    lt_min (lt_min he₁ (by linarith)) (lt_min (by linarith) he₄), fun i => ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (hlen i (Set.mem_univ i))
  · intro i j hij
    have h := hvv (i, j) (Set.mem_univ _) hij
    have : min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄) ≤ e₂ / 2 :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  · intro i j hj1 hj2 y hy
    have h := hve (i, j) (Set.mem_univ _) hj1 hj2 y hy
    have : min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄) ≤ e₃ / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  · exact subset_trans
      (thickening_mono (le_trans (min_le_right _ _) (min_le_right _ _)) _) hthick

/-- The germ threshold at a single vertex. The corner condition makes `det ≠ 0`, so the right
side is positive and the inequality is a genuine upper bound on the half-width. -/
theorem exists_germ_bound (P : ClosedPolygon m) (i : ZMod (m + 3)) {lam : ℝ} (hlam : 0 < lam) :
    ∃ ε > 0, ε * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤
      lam * |det (P.rayIn i) (P.tang i)| := by
  have hb : 0 < |det (P.rayIn i) (P.tang i)| := abs_pos.2 det_rays_ne_zero
  have ha : 0 < 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
    have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
  refine ⟨lam * |det (P.rayIn i) (P.tang i)| / (1 + |inner ℝ (P.rayIn i) (P.tang i)|),
    div_pos (mul_pos hlam hb) ha, le_of_eq ?_⟩
  field_simp

/-- **Step 3: the half-width.** One positive `rho` below `lam`, separating each trimmed edge
from every other edge with a factor `2` to spare, and meeting the germ threshold at every
vertex. Only `0 < lam` is needed: if `lam` were so large that a trimmed edge came out empty,
its separation clause would be vacuous. -/
theorem exists_half_width (P : ClosedPolygon m) {lam : ℝ} (hlam : 0 < lam) :
    ∃ rho > 0, rho < lam ∧
      (∀ i j, j ≠ i → ∀ c ∈ Set.Icc lam (P.len i - lam), ∀ y ∈ P.edge j,
        2 * rho ≤ dist (P.pt i c) y) ∧
      (∀ i, rho * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤
        lam * |det (P.rayIn i) (P.tang i)|) := by
  -- (1) each trimmed edge against every other edge: two disjoint compact sets
  have h₁ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.2 ≠ p.1 → ∀ x ∈ P.trimmed p.1 lam, ∀ y ∈ P.edge p.2, ε ≤ dist x y) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h hne x hx y hy
      exact le_trans hδε (h hne x hx y hy)
    · rintro ⟨i, j⟩ -
      by_cases hij : j = i
      · exact ⟨1, one_pos, fun h => absurd hij h⟩
      · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos isCompact_trimmed isCompact_edge
          (trimmed_disjoint_edge hlam hij)
        exact ⟨ρ, hρ, fun _ => hsep⟩
  -- (2) the germ threshold at every vertex
  have h₂ : ∃ ε > 0, ∀ i : ZMod (m + 3), i ∈ (Set.univ : Set _) →
      ε * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤ lam * |det (P.rayIn i) (P.tang i)| := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro i δ ε _ hδε h
      have hnn : (0 : ℝ) ≤ 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
        have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
      nlinarith
    · intro i _
      exact P.exists_germ_bound i hlam
  obtain ⟨ε₁, hε₁, htrim⟩ := h₁
  obtain ⟨ε₂, hε₂, hgerm⟩ := h₂
  refine ⟨min (min (ε₁ / 2) ε₂) (lam / 2),
    lt_min (lt_min (by linarith) hε₂) (by linarith), ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · intro i j hij c hc y hy
    have h := htrim (i, j) (Set.mem_univ _) hij _ (pt_mem_trimmed hc) y hy
    have hm : min (min (ε₁ / 2) ε₂) (lam / 2) ≤ ε₁ / 2 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  · intro i
    have h := hgerm i (Set.mem_univ _)
    have hnn : (0 : ℝ) ≤ 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
      have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
    have hm : min (min (ε₁ / 2) ε₂) (lam / 2) ≤ ε₂ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith

end ClosedPolygon

open ClosedPolygon

/-- **Lemma 1.8, the constants.** Every simple closed polygon carries a `StripData`, and its
collar can be put inside any prescribed open set containing the curve. This is what makes
`Schoenflies/Strip.lean` with the required constants supplied. -/
theorem exists_stripData_subset (P : ClosedPolygon m) {U : Set Plane} (hU : IsOpen U)
    (hPU : P.carrier ⊆ U) : ∃ D : StripData P, D.nbhd ⊆ U := by
  obtain ⟨R, hR, hRlen, hRvv, hRve, hRU⟩ := P.exists_cone_radius hU hPU
  have hlam : (0 : ℝ) < R / 5 := by linarith
  have hlen4 : ∀ i, 4 * (R / 5) < P.len i := fun i => by have := hRlen i; linarith
  obtain ⟨rho, hrho, hrl, htrim, hgerm⟩ := P.exists_half_width hlam
  refine ⟨⟨R, R / 5, rho, hrho, hrl, by linarith, hlen4, hRlen, hRvv, hRve, htrim, hgerm⟩, ?_⟩
  exact subset_trans (StripData.nbhd_subset_thickening _) hRU

/-- Every simple closed polygon carries a `StripData`. -/
theorem exists_stripData (P : ClosedPolygon m) : Nonempty (StripData P) :=
  ⟨(exists_stripData_subset P isOpen_univ (subset_univ _)).choose⟩

end Schoenflies
end

section
-- module Solutions.Q146_CD.StripLocal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.Plane.supDist_self _root_.Schoenflies.Plane.supDist_zero _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.poly_pair _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The local two-sidedness assertion of Lemma 1.8

`Schoenflies/Strip.lean`, `Schoenflies/StripConstants.lean` and `Schoenflies/StripConnected.lean`
build the collar of a simple closed polygon and prove the *global* half of Lemma 1.8 (a): the
collar minus the curve is the disjoint union of two connected open sets. This module adds the
*local* half, the sentence of the blueprint that begins "In either case the two sets `N_L`, `N_R`
are the two local sides of the curve in the following precise sense".

Two statements come out of it, and they are the two the polygonal Jordan curve theorem consumes.

* `Schoenflies.StripData.local_two_sided` and its packaging
  `Schoenflies.StripData.exists_reference_points`: a small enough disk about a point of the
  *relative interior* of an edge meets the polygon exactly in that edge, and the rest of the disk
  is the two open half-disks, one in each side. This is what supplies the two reference points
  `z_L`, `z_R` of the parity argument, together with the fact that they are separated by a single
  crossing of the curve.
* `Schoenflies.StripData.carrier_subset_closure_sideL` and `…_sideR`: every point of the polygon
  is in the closure of both sides. With `StripData.sideL_disjoint_carrier` this says the polygon
  is contained in the boundary of each side, which is what turns "there are exactly two regions"
  into "both regions have boundary `C`".

## What is proved, and how

The disk argument along an edge is `StripData.core_ball_trichotomy`: both frame coordinates are
`1`-Lipschitz, so a ball of radius at most `min lam rho` about a point of the middle stretch of
an edge cannot leave the block range in the longitudinal coordinate nor the block width in the
transverse one; the sign of the transverse coordinate then reads off which of the three pieces —
left block, edge, right block — the point is in.

Approaching a point of the polygon from a given side is `StripData.exists_near_sides`. Away from
the vertices the block does it. Near a vertex the block is not available (it stops short by
`lam`), and the approach is through the *sector*, reached by shrinking the transverse offset with
the longitudinal one held fixed: the germ lemmas `ClosedPolygon.off_sub_mem_arcL_start` and
friends need only that the offset be small against the progress, so at a point at distance `t > 0`
from the vertex any offset below `t · |det| / (1 + |⟪·,·⟫|)` works. At the vertex itself neither
is available and the approach is instead by shrinking a point of the sector towards the vertex,
which stays in the sector because an arc of directions is a cone (`Plane.smul_mem_arcCCW`).

## Blueprint

* `Schoenflies.StripData.local_two_sided`, `Schoenflies.StripData.exists_reference_points` —
  Lemma 1.8, the local two-sidedness assertion, along the relative interior of an edge.
* `Schoenflies.StripData.carrier_subset_closure_sideL`, `…_sideR` — the consequence of it used
  for "both regions have boundary `C`".
* `Schoenflies.ClosedPolygon.exists_two_sided_collar` — Lemma 1.8 (a) with those two clauses
  added, in existential form.

The local two-sidedness assertion *at a vertex* is not proved here; see the module note at the
end.
-/

open Metric Set

namespace Schoenflies

namespace Plane

variable {u w : Plane}

/-- The origin is on no arc: the arcs are open arcs of *directions*. -/
theorem zero_notMem_arcCCW (u w : Plane) : (0 : Plane) ∉ arcCCW u w := by
  have h := (notMem_arcCCW_smul u w (le_refl (0 : ℝ))).1
  rwa [zero_smul] at h

end Plane

open Plane

variable {m : ℕ}

namespace ClosedPolygon

variable {P : ClosedPolygon m} {i : ZMod (m + 3)} {t s : ℝ}

/-- Seen from the vertex it arrives at, a frame position of edge `i` is a germ at the incoming
ray there. This is the companion of `ClosedPolygon.off_sub_vertex`, which does the same at the
vertex the edge leaves. -/
theorem off_sub_vertex_succ_ray : P.off i t s - P.vertex (i + 1) =
    (P.len i - t) • P.rayIn (i + 1) - s • perp (P.rayIn (i + 1)) := by
  have hr : P.rayIn (i + 1) = -P.tang i := rayIn_succ
  have hp : perp (-P.tang i) = -perp (P.tang i) := by ext k; fin_cases k <;> simp [perp]
  rw [off_sub_vertex_succ, hr, hp]
  module

/-! ### The four germs, for an arbitrary frame position

`StripData.blockL_sub_mem_arcL_start` and its three companions apply `Plane.germs_split'` to a
point of a *block*, where the smallness of the offset comes from the `germ` field of the
`StripData`. The four lemmas here are the same projections with the smallness left as a
hypothesis, which is what an approach to a point of the curve needs: there the progress `t` is
fixed by the point being approached and only the offset shrinks. -/

theorem off_sub_mem_arcL_start (hs : 0 < s)
    (hsm : s * |inner ℝ (P.rayIn i) (P.tang i)| < t * |det (P.rayIn i) (P.tang i)|) :
    P.off i t s - P.vertex i ∈ arcCCW (P.tang i) (P.rayIn i) := by
  rw [off_sub_vertex]
  exact (germs_split' det_rays_ne_zero hs hsm).1.2

theorem off_sub_mem_arcR_start (hs : s < 0)
    (hsm : (-s) * |inner ℝ (P.rayIn i) (P.tang i)| < t * |det (P.rayIn i) (P.tang i)|) :
    P.off i t s - P.vertex i ∈ arcCCW (P.rayIn i) (P.tang i) := by
  have h : P.off i t s - P.vertex i = t • P.tang i - (-s) • perp (P.tang i) := by
    rw [off_sub_vertex]; module
  rw [h]
  exact (germs_split' det_rays_ne_zero (by linarith) hsm).2.2

theorem off_sub_mem_arcL_finish (hs : 0 < s)
    (hsm : s * |inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| <
      (P.len i - t) * |det (P.rayIn (i + 1)) (P.tang (i + 1))|) :
    P.off i t s - P.vertex (i + 1) ∈ arcCCW (P.tang (i + 1)) (P.rayIn (i + 1)) := by
  rw [off_sub_vertex_succ_ray]
  exact (germs_split' det_rays_ne_zero hs hsm).1.1

theorem off_sub_mem_arcR_finish (hs : s < 0)
    (hsm : (-s) * |inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| <
      (P.len i - t) * |det (P.rayIn (i + 1)) (P.tang (i + 1))|) :
    P.off i t s - P.vertex (i + 1) ∈ arcCCW (P.rayIn (i + 1)) (P.tang (i + 1)) := by
  have h : P.off i t s - P.vertex (i + 1) =
      (P.len i - t) • P.rayIn (i + 1) + (-s) • perp (P.rayIn (i + 1)) := by
    rw [off_sub_vertex_succ_ray]; module
  rw [h]
  exact (germs_split' det_rays_ne_zero (by linarith) hsm).2.1

/-- Offsetting a point of an edge moves it exactly the offset. -/
theorem dist_off_pt : dist (P.off i t s) (P.pt i t) = |s| := by
  rw [ClosedPolygon.pt, dist_eq_norm, show P.off i t s - P.off i t 0 = s • perp (P.tang i) by
    rw [off, off]; module, norm_smul, Real.norm_eq_abs, norm_perp, isDirection_tang.norm,
    mul_one]

end ClosedPolygon

/-- One positive number below several prescribed thresholds at once. Used to offset a point of an
edge by less than the germ threshold at both of its endpoints, less than the block half-width and
less than a prescribed accuracy. -/
theorem exists_common_bound {a b X₁ X₂ K₁ K₂ Y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hY : 0 < Y) :
    ∃ σ : ℝ, 0 < σ ∧ σ < a ∧ σ < b ∧ σ * K₁ ≤ X₁ ∧ σ * K₂ ≤ X₂ ∧ σ < Y := by
  refine ⟨min (min (a / 2) (b / 2)) (min (min (X₁ / K₁) (X₂ / K₂)) (Y / 2)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lt_min_iff, lt_min_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith, by linarith⟩, ⟨div_pos hX₁ hK₁, div_pos hX₂ hK₂⟩, by linarith⟩
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  · have h : min (min (a / 2) (b / 2)) (min (min (X₁ / K₁) (X₂ / K₂)) (Y / 2)) ≤ X₁ / K₁ :=
      le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
    have h2 := mul_le_mul_of_nonneg_right h hK₁.le
    rwa [div_mul_cancel₀ _ hK₁.ne'] at h2
  · have h : min (min (a / 2) (b / 2)) (min (min (X₁ / K₁) (X₂ / K₂)) (Y / 2)) ≤ X₂ / K₂ :=
      le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
    have h2 := mul_le_mul_of_nonneg_right h hK₂.le
    rwa [div_mul_cancel₀ _ hK₂.ne'] at h2
  · exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i : ZMod (m + 3)}

/-! ### The disk about a point in the middle of an edge -/

/-- **The local picture along an edge.** A ball of radius at most `min lam rho` about a point of
the middle stretch of an edge is split by the sign of the transverse coordinate: positive is the
left block, negative the right block, zero the edge itself. Both coordinates are `1`-Lipschitz,
which is the whole proof. -/
theorem core_ball_trichotomy {c η : ℝ} (h1 : 2 * D.lam ≤ c) (h2 : c ≤ P.len i - 2 * D.lam)
    (hη : η ≤ min D.lam D.rho) {y : Plane} (hy0 : y ∈ ball (P.pt i c) η) :
    (0 < coordAcross (P.vertex i) (P.tang i) y → y ∈ D.blockL i) ∧
      (coordAcross (P.vertex i) (P.tang i) y < 0 → y ∈ D.blockR i) ∧
      (coordAcross (P.vertex i) (P.tang i) y = 0 → y ∈ P.edge i) := by
  have hy : dist y (P.pt i c) < min D.lam D.rho := lt_of_lt_of_le (mem_ball.1 hy0) hη
  set t := coordAlong (P.vertex i) (P.tang i) y with ht
  set σ := coordAcross (P.vertex i) (P.tang i) y with hσ
  have hyeq : y = P.off i t σ := ClosedPolygon.off_coord P i y
  have hpt : P.pt i c = P.off i c 0 := rfl
  have hta : |t - c| ≤ dist y (P.pt i c) := by
    have h := abs_coordAlong_sub_le (u := P.tang i) ClosedPolygon.isDirection_tang (P.vertex i) y
      (P.pt i c)
    rw [hpt, ClosedPolygon.coordAlong_off] at h
    exact h
  have hsa : |σ| ≤ dist y (P.pt i c) := by
    have h := abs_coordAcross_sub_le (u := P.tang i) ClosedPolygon.isDirection_tang (P.vertex i) y
      (P.pt i c)
    rw [hpt, ClosedPolygon.coordAcross_off, sub_zero] at h
    exact h
  have hlam : dist y (P.pt i c) < D.lam := lt_of_lt_of_le hy (min_le_left _ _)
  have hrho : dist y (P.pt i c) < D.rho := lt_of_lt_of_le hy (min_le_right _ _)
  have htlow : D.lam < t := by
    have h := abs_lt.1 (lt_of_le_of_lt hta hlam)
    linarith [h.1]
  have hthigh : t < P.len i - D.lam := by
    have h := abs_lt.1 (lt_of_le_of_lt hta hlam)
    linarith [h.2]
  refine ⟨fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
  · rw [hyeq]
    exact D.mem_blockL_off.2 ⟨htlow, hthigh, hs, by
      have h := abs_lt.1 (lt_of_le_of_lt hsa hrho); linarith [h.2]⟩
  · rw [hyeq]
    exact D.mem_blockR_off.2 ⟨htlow, hthigh, by
      have h := abs_lt.1 (lt_of_le_of_lt hsa hrho); linarith [h.1], hs⟩
  · rw [hyeq, hs, ← ClosedPolygon.pt]
    exact ClosedPolygon.pt_mem_edge ⟨by linarith [D.lam_pos], by linarith [D.lam_pos]⟩

/-- **Local two-sidedness at an interior point of an edge.** A small enough disk about a point in
the middle stretch of an edge meets the polygon exactly in that edge; off the edge the disk lies
in the two blocks, one on each side; and both sides are met, at the two points obtained by
offsetting the centre. -/
theorem local_two_sided {c η : ℝ} (h1 : 2 * D.lam ≤ c) (h2 : c ≤ P.len i - 2 * D.lam)
    (hηpos : 0 < η) (hη : η ≤ min D.lam D.rho) :
    ball (P.pt i c) η ∩ P.carrier ⊆ P.edge i ∧
      (∀ y ∈ ball (P.pt i c) η, y ∉ P.carrier →
        (0 < coordAcross (P.vertex i) (P.tang i) y ∧ y ∈ D.sideL) ∨
          (coordAcross (P.vertex i) (P.tang i) y < 0 ∧ y ∈ D.sideR)) ∧
      P.off i c (η / 2) ∈ ball (P.pt i c) η ∩ D.sideL ∧
      P.off i c (-(η / 2)) ∈ ball (P.pt i c) η ∩ D.sideR := by
  have hsplit : ∀ y ∈ ball (P.pt i c) η,
      (0 < coordAcross (P.vertex i) (P.tang i) y → y ∈ D.sideL) ∧
        (coordAcross (P.vertex i) (P.tang i) y < 0 → y ∈ D.sideR) ∧
        (coordAcross (P.vertex i) (P.tang i) y = 0 → y ∈ P.edge i) := by
    intro y hy
    obtain ⟨hL, hR, hE⟩ := D.core_ball_trichotomy h1 h2 hη hy
    exact ⟨fun hs => Set.mem_iUnion.2 ⟨i, Or.inr (hL hs)⟩,
      fun hs => Set.mem_iUnion.2 ⟨i, Or.inr (hR hs)⟩, hE⟩
  have hball : ∀ σ : ℝ, |σ| < η → P.off i c σ ∈ ball (P.pt i c) η := by
    intro σ hσ
    rw [mem_ball, ClosedPolygon.dist_off_pt]
    exact hσ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro y ⟨hy, hyc⟩
    rcases lt_trichotomy (coordAcross (P.vertex i) (P.tang i) y) 0 with hs | hs | hs
    · exact absurd hyc (Set.disjoint_left.1 D.sideR_disjoint_carrier ((hsplit y hy).2.1 hs))
    · exact (hsplit y hy).2.2 hs
    · exact absurd hyc (Set.disjoint_left.1 D.sideL_disjoint_carrier ((hsplit y hy).1 hs))
  · intro y hy hyc
    rcases lt_trichotomy (coordAcross (P.vertex i) (P.tang i) y) 0 with hs | hs | hs
    · exact Or.inr ⟨hs, (hsplit y hy).2.1 hs⟩
    · exact absurd (ClosedPolygon.edge_subset_carrier ((hsplit y hy).2.2 hs)) hyc
    · exact Or.inl ⟨hs, (hsplit y hy).1 hs⟩
  · have hmem := hball (η / 2) (by rw [abs_of_pos (by linarith)]; linarith)
    refine ⟨hmem, (hsplit _ hmem).1 ?_⟩
    rw [ClosedPolygon.coordAcross_off]
    linarith
  · have hmem := hball (-(η / 2)) (by rw [abs_of_neg (by linarith)]; linarith)
    refine ⟨hmem, (hsplit _ hmem).2.1 ?_⟩
    rw [ClosedPolygon.coordAcross_off]
    linarith

/-! ### Every point of the polygon is on the boundary of both sides -/

/-- A sector comes arbitrarily close to its vertex: shrink a point of it towards the vertex, which
stays in the arc because an arc of directions is a cone. -/
theorem exists_near_sectorL {ε : ℝ} (hε : 0 < ε) (i : ZMod (m + 3)) :
    ∃ y ∈ D.sectorL i, dist y (P.vertex i) < ε := by
  obtain ⟨z, hz⟩ := (D.isConnected_sectorL (i := i)).nonempty
  have harc : z - P.vertex i ∈ arcCCW (P.tang i) (P.rayIn i) := hz.1
  have hwne : z - P.vertex i ≠ 0 := fun h => zero_notMem_arcCCW _ _ (h ▸ harc)
  have hwpos : 0 < ‖z - P.vertex i‖ := norm_pos_iff.2 hwne
  have hzR : ‖z - P.vertex i‖ < D.R := by rw [← dist_eq_norm]; exact hz.2
  refine ⟨P.vertex i + (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i), ⟨?_, ?_⟩, ?_⟩ <;>
    (have hδpos : 0 < min 1 (ε / (2 * ‖z - P.vertex i‖)) := lt_min one_pos (by positivity)
     have hsub : P.vertex i + (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) -
         P.vertex i = (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) := by module)
  · rw [Set.mem_setOf_eq, hsub]
    exact (smul_mem_arcCCW hδpos).2 harc
  · rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h1 : min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ 1 := min_le_left _ _
    nlinarith
  · rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h2 : min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ ε / (2 * ‖z - P.vertex i‖) := min_le_right _ _
    have hkey : ε / (2 * ‖z - P.vertex i‖) * ‖z - P.vertex i‖ = ε / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2 hwpos.le]

theorem exists_near_sectorR {ε : ℝ} (hε : 0 < ε) (i : ZMod (m + 3)) :
    ∃ y ∈ D.sectorR i, dist y (P.vertex i) < ε := by
  obtain ⟨z, hz⟩ := (D.isConnected_sectorR (i := i)).nonempty
  have harc : z - P.vertex i ∈ arcCCW (P.rayIn i) (P.tang i) := hz.1
  have hwne : z - P.vertex i ≠ 0 := fun h => zero_notMem_arcCCW _ _ (h ▸ harc)
  have hwpos : 0 < ‖z - P.vertex i‖ := norm_pos_iff.2 hwne
  have hzR : ‖z - P.vertex i‖ < D.R := by rw [← dist_eq_norm]; exact hz.2
  refine ⟨P.vertex i + (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i), ⟨?_, ?_⟩, ?_⟩ <;>
    (have hδpos : 0 < min 1 (ε / (2 * ‖z - P.vertex i‖)) := lt_min one_pos (by positivity)
     have hsub : P.vertex i + (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) -
         P.vertex i = (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) := by module)
  · rw [Set.mem_setOf_eq, hsub]
    exact (smul_mem_arcCCW hδpos).2 harc
  · rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h1 : min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ 1 := min_le_left _ _
    nlinarith
  · rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h2 : min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ ε / (2 * ‖z - P.vertex i‖) := min_le_right _ _
    have hkey : ε / (2 * ‖z - P.vertex i‖) * ‖z - P.vertex i‖ = ε / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2 hwpos.le]

/-- **Both sides come arbitrarily close to every point of the polygon.** Away from the vertices
this is the block; at a vertex it is `exists_near_sectorL`; in between it is the germ with the
progress held fixed and the offset shrunk below the corner's threshold. -/
theorem exists_near_sides {x : Plane} (hx : x ∈ P.carrier) {ε : ℝ} (hε : 0 < ε) :
    (∃ y ∈ D.sideL, dist x y < ε) ∧ (∃ y ∈ D.sideR, dist x y < ε) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := ClosedPolygon.mem_edge_iff.1 hi
  rcases eq_or_lt_of_le hc0 with hc0' | hc0'
  · -- the initial vertex
    rw [← hc0', ClosedPolygon.pt_zero]
    obtain ⟨y, hy, hd⟩ := D.exists_near_sectorL hε i
    obtain ⟨y', hy', hd'⟩ := D.exists_near_sectorR hε i
    exact ⟨⟨y, Set.mem_iUnion.2 ⟨i, Or.inl hy⟩, by rw [dist_comm]; exact hd⟩,
      ⟨y', Set.mem_iUnion.2 ⟨i, Or.inl hy'⟩, by rw [dist_comm]; exact hd'⟩⟩
  rcases eq_or_lt_of_le hc1 with hc1' | hc1'
  · -- the terminal vertex
    rw [hc1', ClosedPolygon.pt_len]
    obtain ⟨y, hy, hd⟩ := D.exists_near_sectorL hε (i + 1)
    obtain ⟨y', hy', hd'⟩ := D.exists_near_sectorR hε (i + 1)
    exact ⟨⟨y, Set.mem_iUnion.2 ⟨i + 1, Or.inl hy⟩, by rw [dist_comm]; exact hd⟩,
      ⟨y', Set.mem_iUnion.2 ⟨i + 1, Or.inl hy'⟩, by rw [dist_comm]; exact hd'⟩⟩
  -- an interior point of the edge: offset it, by less than every threshold at once
  have hL₁ : 0 < |det (P.rayIn i) (P.tang i)| := abs_pos.2 ClosedPolygon.det_rays_ne_zero
  have hL₂ : 0 < |det (P.rayIn (i + 1)) (P.tang (i + 1))| :=
    abs_pos.2 ClosedPolygon.det_rays_ne_zero
  have hK₁ : (0 : ℝ) < 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by positivity
  have hK₂ : (0 : ℝ) < 1 + |inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| := by positivity
  have hRlam : D.lam < D.R := by have := D.lam_pos; linarith [D.two_lam_lt_R]
  obtain ⟨σ, hσpos, hσε, hσrho, hσ1, hσ2, hσR⟩ := exists_common_bound hε D.rho_pos
    (mul_pos hc0' hL₁) (mul_pos (show (0:ℝ) < P.len i - c by linarith) hL₂) hK₁ hK₂
    (show (0:ℝ) < D.R - D.lam by linarith)
  have hg1 : σ * |inner ℝ (P.rayIn i) (P.tang i)| < c * |det (P.rayIn i) (P.tang i)| := by
    nlinarith
  have hg2 : σ * |inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| <
      (P.len i - c) * |det (P.rayIn (i + 1)) (P.tang (i + 1))| := by nlinarith
  have hdistL : dist (P.pt i c) (P.off i c σ) < ε := by
    rw [dist_comm, ClosedPolygon.dist_off_pt, abs_of_pos hσpos]; linarith
  have hdistR : dist (P.pt i c) (P.off i c (-σ)) < ε := by
    rw [dist_comm, ClosedPolygon.dist_off_pt, abs_of_neg (by linarith : -σ < 0)]; linarith
  by_cases hmid : D.lam < c ∧ c < P.len i - D.lam
  · -- the block does it
    exact ⟨⟨P.off i c σ, Set.mem_iUnion.2 ⟨i, Or.inr
        (D.mem_blockL_off.2 ⟨hmid.1, hmid.2, hσpos, hσrho⟩)⟩, hdistL⟩,
      ⟨P.off i c (-σ), Set.mem_iUnion.2 ⟨i, Or.inr
        (D.mem_blockR_off.2 ⟨hmid.1, hmid.2, by linarith, by linarith⟩)⟩, hdistR⟩⟩
  push Not at hmid
  by_cases hnear : c ≤ D.lam
  · -- near the initial vertex: the sector there, reached by the germ
    have hdv : ∀ τ : ℝ, |τ| ≤ σ → dist (P.off i c τ) (P.vertex i) < D.R := by
      intro τ hτ
      have h := ClosedPolygon.dist_off_vertex_le (P := P) (i := i) (t := c) (s := τ)
      rw [abs_of_pos hc0'] at h
      linarith
    refine ⟨⟨P.off i c σ, Set.mem_iUnion.2 ⟨i, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcL_start hσpos hg1,
          hdv σ (by rw [abs_of_pos hσpos])⟩⟩, hdistL⟩,
      ⟨P.off i c (-σ), Set.mem_iUnion.2 ⟨i, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcR_start (by linarith) (by rw [neg_neg]; exact hg1),
          hdv (-σ) (by rw [abs_of_neg (by linarith : -σ < 0), neg_neg])⟩⟩, hdistR⟩⟩
  · -- near the terminal vertex
    push Not at hnear
    have hfar : P.len i - c ≤ D.lam := by have h := hmid hnear; linarith
    have hdv : ∀ τ : ℝ, |τ| ≤ σ → dist (P.off i c τ) (P.vertex (i + 1)) < D.R := by
      intro τ hτ
      have h := ClosedPolygon.dist_off_vertex_succ_le (P := P) (i := i) (t := c) (s := τ)
      rw [abs_sub_comm, abs_of_pos (by linarith : (0:ℝ) < P.len i - c)] at h
      linarith
    refine ⟨⟨P.off i c σ, Set.mem_iUnion.2 ⟨i + 1, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcL_finish hσpos hg2,
          hdv σ (by rw [abs_of_pos hσpos])⟩⟩, hdistL⟩,
      ⟨P.off i c (-σ), Set.mem_iUnion.2 ⟨i + 1, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcR_finish (by linarith) (by rw [neg_neg]; exact hg2),
          hdv (-σ) (by rw [abs_of_neg (by linarith : -σ < 0), neg_neg])⟩⟩, hdistR⟩⟩

/-- Every point of the polygon is in the closure of the left side. With
`StripData.sideL_disjoint_carrier` this says the polygon is contained in the boundary of the left
side. -/
theorem carrier_subset_closure_sideL : P.carrier ⊆ closure D.sideL := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨⟨y, hy, hd⟩, -⟩ := D.exists_near_sides hx hε
  exact ⟨y, hy, hd⟩

theorem carrier_subset_closure_sideR : P.carrier ⊆ closure D.sideR := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨-, ⟨y, hy, hd⟩⟩ := D.exists_near_sides hx hε
  exact ⟨y, hy, hd⟩

end StripData

/-!
## What is still missing from Lemma 1.8

Two things.

* The local two-sidedness assertion *at a vertex*. `StripData.ball_diff_carrier_subset` already
  says that a ball of radius `R` about a vertex minus the polygon lies in the two sectors there,
  and `StripData.sectorL_disjoint_sectorR` (through `sideL_disjoint_sideR`) says those are
  disjoint; what is not proved is that each of the two intersections
  `ball (P.vertex i) η ∩ sectorL i` is *connected*, i.e. that the ball minus the curve has
  exactly two components at a vertex rather than merely being covered by two disjoint open sets.
  For a ball of radius `η ≤ R` this is true and the proof is the one in
  `Plane.isConnected_arcCCW_ball`, since `ball (P.vertex i) η ∩ sectorL i = cone (P.vertex i) A η`
  for the same arc `A`. Nothing in the polygonal Jordan curve theorem needs it.
* Lemma 1.8 (b), the case of a polygonal *arc* with a compact subarc of its interior. The blocks
  and sectors here are built from a cyclic vertex family; the arc case needs the same
  construction along a linear chain, with the two end cross-sections and no cap. None of it is
  formalised.
-/

end Schoenflies
end

section
-- module Solutions.Q146_CD.PolygonalJordan
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The polygonal Jordan curve theorem

Theorem 2.3: the complement of a simple closed polygon has exactly two regions, one bounded and
one unbounded, and each has the polygon as its frontier. Moreover the crossing parity of §2 is
`1` on the bounded region and `0` on the unbounded one.

## The three inputs, and where each is spent

* **Lemma 1.8, the collar** (`Schoenflies.StripData`, `StripData.local_two_sided`,
  `StripData.carrier_subset_closure_sideL`). It supplies the two *tracks* `N_L`, `N_R`: connected,
  disjoint, off the curve, together filling `N ∖ C`, and each with the whole curve in its closure.
* **Lemma 1.3, the nearest-point segment** (`Plane.notMem_of_mem_segment_of_isMinOn`). It gets an
  arbitrary point of the complement onto a track: walk from it to a nearest point of the curve;
  the walk misses the curve, and its final stretch is inside the collar.
* **Lemma 2.2, crossing parity** (`ClosedPolygon.parity_eq_of_mem_connectedComponentIn_carrier`,
  `ClosedPolygon.parity_flip_carrier`). It keeps the two tracks apart: they cannot be joined
  inside the complement, because a point just before and a point just after an edge differ in
  parity and parity is constant on a connected subset of the complement.

## Blueprint

* `Schoenflies.ClosedPolygon.exists_opposite_parity_sides`,
  `…parity_ne_of_mem_sides`, `…connectedComponentIn_ne_of_mem_sides` — the two tracks of the
  collar carry different parities, hence lie in different components. The "at least two" half.
* `Schoenflies.ClosedPolygon.exists_mem_sides_connectedComponentIn`,
  `…connectedComponentIn_eq_of_notMem` — every point of the complement lies in the component of a
  point of a track. The "at most two" half.
* `Schoenflies.ClosedPolygon.isSeparating_carrier` — **Theorem 2.3**, in the form Definition 2.4
  asks for: `IsSeparating P.carrier`. With it come `inside P.carrier` and `outside P.carrier` as
  the blueprint's `Int(C)` and `Ext(C)`, and the whole `IsSeparating` API of
  `Schoenflies/CrosscutCells.lean`.
* `Schoenflies.ClosedPolygon.connectedComponentIn_eq_inside_or_outside` — "exactly two regions",
  explicitly: the component of any point off the polygon is one of the two named regions.
* `Schoenflies.ClosedPolygon.parity_eq_one_of_mem_inside`,
  `…parity_eq_zero_of_mem_outside` — the last sentence of Theorem 2.3, `π_C = 1` inside and
  `π_C = 0` outside, for **every** admissible ray direction, not just for one chosen at the start.
* `Schoenflies.ClosedPolygon.polygonal_jordan` — the same theorem with `IsSeparating` unfolded,
  for a reader who wants the statement without the definition.
* `Schoenflies.isSeparating_unitTriangle` — non-vacuity: the whole chain applies to the one
  polygon the development constructs.

## Two facts restated

`isBounded_closedSquare` and `not_isBounded_beyondSquare` below are stated `private`. They are
*not* new: they exist as `Graph.isBounded_closedSquare` and `Graph.not_isBounded_beyondSquare` in
`Schoenflies/Graph/OuterFace.lean`. Neither has any graph content — they are plane facts about
`Schoenflies.Plane.closedSquare` whose home is `Schoenflies/Bounded.lean` — and importing the
whole plane-graph layer into the polygonal Jordan curve theorem, which every later graph
argument depends on, would invert the layering. They are `private` so that the duplicate names
cannot collide when the integrator hoists the originals.
-/

open Bornology Metric Set

namespace Schoenflies

open Plane

variable {m : ℕ}

/-! ### Two plane facts about squares

See the module docstring: these belong in `Schoenflies/Bounded.lean` and are restated here only
to keep the graph layer out of the import graph of Theorem 2.3. -/

/-- A closed axis-parallel square is bounded. -/
theorem isBounded_closedSquare (r : ℝ) : IsBounded (Plane.closedSquare 0 r) := by
  refine (Metric.isBounded_closedBall (x := (0 : Plane)) (r := Real.sqrt 2 * r)).subset ?_
  intro x hx
  have hsup : Plane.supNorm x ≤ r := by simpa [Plane.closedSquare] using hx
  have : ‖x‖ ≤ Real.sqrt 2 * r :=
    le_trans (Plane.norm_le_sqrt_two_mul_supNorm x)
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2))
  simpa [Metric.mem_closedBall, dist_eq_norm] using this

/-- The outside of a square is unbounded: it contains points of every size. -/
theorem not_isBounded_beyondSquare (r : ℝ) : ¬ IsBounded (Plane.beyondSquare r) := by
  intro hb
  obtain ⟨s, -, hs⟩ := Plane.exists_closedSquare_of_isBounded hb
  set t : ℝ := max (max r s) 0 + 1 with ht
  have ht0 : 0 ≤ t := by have := le_max_right (max r s) 0; simp only [ht] <;> linarith
  have htr : r < t := by
    have h1 := le_max_left r s
    have h2 := le_max_left (max r s) 0
    simp only [ht] <;> linarith
  have hts : s < t := by
    have h1 := le_max_right r s
    have h2 := le_max_left (max r s) 0
    simp only [ht] <;> linarith
  have hmem : Plane.mk t 0 ∈ Plane.beyondSquare r :=
    Or.inl (show r < |t| by rw [abs_of_nonneg ht0]; exact htr)
  have hin : Plane.supDist (Plane.mk t 0) 0 ≤ s := hs hmem
  rw [Plane.supDist_zero] at hin
  have h1 : |t| ≤ Plane.supNorm (Plane.mk t 0) := by
    simp only [Plane.supNorm]; exact le_max_left _ _
  rw [abs_of_nonneg ht0] at h1
  linarith

/-! ### Small arithmetic and topology helpers -/

/-- In `ZMod 2` nothing is its own successor; this is what "the parities differ" comes down to. -/
theorem zmod_two_ne_add_one (x : ZMod 2) : x ≠ x + 1 := by revert x; decide

/-- Two points joined by a preconnected subset of `F` have the same component of `F`. -/
theorem comp_eq_of_isPreconnected {F S : Set Plane} (hS : IsPreconnected S) (hSF : S ⊆ F)
    {x y : Plane} (hx : x ∈ S) (hy : y ∈ S) :
    connectedComponentIn F x = connectedComponentIn F y :=
  connectedComponentIn_eq (hS.subset_connectedComponentIn hx hSF hy)

/-- Distinct components are disjoint. -/
theorem comp_disjoint {F : Set Plane} {x y : Plane}
    (h : connectedComponentIn F x ≠ connectedComponentIn F y) :
    Disjoint (connectedComponentIn F x) (connectedComponentIn F y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  exact h ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)

namespace ClosedPolygon

variable {P : ClosedPolygon m}

theorem isClosed_carrier (P : ClosedPolygon m) : IsClosed P.carrier :=
  P.isCompact_carrier.isClosed

theorem carrier_nonempty (P : ClosedPolygon m) : P.carrier.Nonempty :=
  ⟨P.vertex 0, vertex_mem_carrier⟩

theorem sideL_subset_compl (D : StripData P) : D.sideL ⊆ P.carrierᶜ :=
  fun _ hz => Set.disjoint_left.1 D.sideL_disjoint_carrier hz

theorem sideR_subset_compl (D : StripData P) : D.sideR ⊆ P.carrierᶜ :=
  fun _ hz => Set.disjoint_left.1 D.sideR_disjoint_carrier hz

/-- **No edge is parallel to an admissible ray direction.** "No edge is horizontal" says exactly
that the two ends of an edge are at different heights, which is that the edge's tangent and the
ray direction span the plane. -/
theorem det_tang_ne_zero {u : Plane} (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2)
    (i : ZMod (m + 3)) : det (P.tang i) u ≠ 0 := by
  have hne : hgt u (P.vertex i) ≠ hgt u (P.vertex (i + 1)) := hL _ (P.mem_pieces i)
  have hsub : det u (P.vertex (i + 1) - P.vertex i) ≠ 0 := by
    rw [show det u (P.vertex (i + 1) - P.vertex i) = hgt u (P.vertex (i + 1) - P.vertex i) from rfl,
      hgt_sub, sub_ne_zero]
    exact Ne.symm hne
  rw [← len_smul_tang, det_smul_right] at hsub
  intro hz
  exact hsub (by rw [det_comm, hz, neg_zero, mul_zero])

/-! ### At least two regions: the two tracks are separated by one crossing

The blueprint: "Choose a sufficiently small disk `B` around an interior point of an edge, and
reference points `z_L ∈ B ∩ N_L`, `z_R ∈ B ∩ N_R` in its two components. The two reference points
have opposite parity."

The disk is the one of `StripData.local_two_sided`; the two reference points are the two points
just before and just after the midpoint of the edge *in the ray direction*, which is what makes
`parity_flip_carrier` applicable to them. That they land in the two different tracks is read off
the sign of their transverse coordinate `det (tang i) (· - vertex i)`, and the two signs are
opposite and nonzero because `det (tang i) u ≠ 0` — the edge is not parallel to the ray. -/

/-- **The two tracks of the collar carry different parities.** The witnesses are a point just
before and a point just after the midpoint of the edge `i` in the ray direction: they lie in the
two different tracks, and the crossing count changes by one between them. -/
theorem exists_opposite_parity_sides (P : ClosedPolygon m) (D : StripData P)
    (i : ZMod (m + 3)) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∃ zL ∈ D.sideL, ∃ zR ∈ D.sideR, parity u P.pieces zL ≠ parity u P.pieces zR := by
  have h4 := D.four_lam_lt_len i
  have hlam := D.lam_pos
  have hlen : 0 < P.len i := len_pos
  have hlow : 2 * D.lam ≤ P.len i / 2 := by linarith
  have hhigh : P.len i / 2 ≤ P.len i - 2 * D.lam := by linarith
  have hηpos : 0 < min D.lam D.rho := lt_min hlam D.rho_pos
  obtain ⟨-, hsides, -, -⟩ := D.local_two_sided (i := i) hlow hhigh hηpos le_rfl
  -- the midpoint of the edge is an interior point of it
  have hmid : P.vertex i + ((P.len i / 2) / P.len i) • (P.vertex (i + 1) - P.vertex i)
      = P.pt i (P.len i / 2) := by
    rw [← len_smul_tang, smul_smul, div_mul_cancel₀ _ hlen.ne', pt_eq]
  have hp : P.pt i (P.len i / 2) ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) := by
    rw [openSegment_eq_image' ℝ]
    exact ⟨(P.len i / 2) / P.len i,
      ⟨div_pos (by linarith) hlen, by rw [div_lt_one hlen]; linarith⟩, hmid⟩
  obtain ⟨δ, hδ, hflip⟩ := P.parity_flip_carrier hu hL i hp
  have ht0 : 0 < min (δ / 2) (min D.lam D.rho / 2) := lt_min (by linarith) (by linarith)
  have htδ : min (δ / 2) (min D.lam D.rho / 2) < δ :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htη : min (δ / 2) (min D.lam D.rho / 2) < min D.lam D.rho :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set t : ℝ := min (δ / 2) (min D.lam D.rho / 2)
  obtain ⟨hbef, haft, hpar⟩ := hflip t ht0 htδ
  -- both test points lie in the disk of `local_two_sided`
  have hball : ∀ r : ℝ, |r| < min D.lam D.rho →
      P.pt i (P.len i / 2) + r • u ∈ ball (P.pt i (P.len i / 2)) (min D.lam D.rho) := by
    intro r hr
    rw [mem_ball, dist_eq_norm,
      show P.pt i (P.len i / 2) + r • u - P.pt i (P.len i / 2) = r • u by abel,
      norm_smul, Real.norm_eq_abs, hu.norm, mul_one]
    exact hr
  have hbaft := hball t (by rw [abs_of_pos ht0]; exact htη)
  have hbbef : P.pt i (P.len i / 2) - t • u ∈ ball (P.pt i (P.len i / 2)) (min D.lam D.rho) := by
    have h := hball (-t) (by rw [abs_of_neg (by linarith), neg_neg]; exact htη)
    rwa [neg_smul, ← sub_eq_add_neg] at h
  -- the transverse coordinate of a point offset from the edge in the ray direction
  have hkey : ∀ r : ℝ, coordAcross (P.vertex i) (P.tang i) (P.pt i (P.len i / 2) + r • u)
      = r * det (P.tang i) u := by
    intro r
    rw [coordAcross, show P.pt i (P.len i / 2) + r • u - P.vertex i
        = (P.len i / 2) • P.tang i + r • u by rw [pt_eq]; module,
      det_add_right, det_smul_right, det_self, mul_zero, zero_add, det_smul_right]
  have hcaaft := hkey t
  have hcabef : coordAcross (P.vertex i) (P.tang i) (P.pt i (P.len i / 2) - t • u)
      = -(t * det (P.tang i) u) := by
    have h := hkey (-t)
    rw [neg_smul, ← sub_eq_add_neg] at h
    rw [h]; ring
  have hsaft := hsides _ hbaft haft
  have hsbef := hsides _ hbbef hbef
  rcases lt_or_gt_of_ne (det_tang_ne_zero hL i) with hneg | hpos
  · -- the ray points to the right of the edge: the earlier test point is on the left
    have hlt : t * det (P.tang i) u < 0 := mul_neg_of_pos_of_neg ht0 hneg
    refine ⟨P.pt i (P.len i / 2) - t • u, ?_, P.pt i (P.len i / 2) + t • u, ?_, ?_⟩
    · rcases hsbef with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [hcabef] at h; linarith
    · rcases hsaft with ⟨h, -⟩ | ⟨-, h⟩
      · rw [hcaaft] at h; linarith
      · exact h
    · rw [hpar]; exact Ne.symm (zmod_two_ne_add_one _)
  · have hgt0 : 0 < t * det (P.tang i) u := mul_pos ht0 hpos
    refine ⟨P.pt i (P.len i / 2) + t • u, ?_, P.pt i (P.len i / 2) - t • u, ?_, ?_⟩
    · rcases hsaft with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [hcaaft] at h; linarith
    · rcases hsbef with ⟨h, -⟩ | ⟨-, h⟩
      · rw [hcabef] at h; linarith
      · exact h
    · rw [hpar]; exact zmod_two_ne_add_one _

/-- The crossing parity is constant on the left track: it is connected and misses the polygon. -/
theorem parity_eq_of_mem_sideL (P : ClosedPolygon m) (D : StripData P) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∈ D.sideL) (hy : y ∈ D.sideL) : parity u P.pieces x = parity u P.pieces y :=
  parity_eq_of_isPreconnected hu hL P.isClosedChain_pieces D.isConnected_sideL.isPreconnected
    (fun z hz => by rw [P.cover_pieces]; exact sideL_subset_compl D hz) hx hy

/-- The crossing parity is constant on the right track. -/
theorem parity_eq_of_mem_sideR (P : ClosedPolygon m) (D : StripData P) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∈ D.sideR) (hy : y ∈ D.sideR) : parity u P.pieces x = parity u P.pieces y :=
  parity_eq_of_isPreconnected hu hL P.isClosedChain_pieces D.isConnected_sideR.isPreconnected
    (fun z hz => by rw [P.cover_pieces]; exact sideR_subset_compl D hz) hx hy

/-- **The two tracks of the collar have opposite parity**, whichever points of them are chosen.
This is the "at least two regions" half of Theorem 2.3: no connected subset of the complement
meets both tracks, since parity is constant on such a subset. -/
theorem parity_ne_of_mem_sides (P : ClosedPolygon m) (D : StripData P) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∈ D.sideL) (hy : y ∈ D.sideR) : parity u P.pieces x ≠ parity u P.pieces y := by
  obtain ⟨zL, hzL, zR, hzR, hne⟩ := P.exists_opposite_parity_sides D 0 hu hL
  rw [P.parity_eq_of_mem_sideL D hu hL hx hzL, P.parity_eq_of_mem_sideR D hu hL hy hzR]
  exact hne

/-- The two tracks lie in different components of the complement. -/
theorem connectedComponentIn_ne_of_mem_sides (P : ClosedPolygon m) (D : StripData P) {x y : Plane}
    (hx : x ∈ D.sideL) (hy : y ∈ D.sideR) :
    connectedComponentIn P.carrierᶜ x ≠ connectedComponentIn P.carrierᶜ y := by
  obtain ⟨u, hu, hL⟩ := P.exists_direction_pieces
  intro heq
  refine P.parity_ne_of_mem_sides D hu hL hx hy ?_
  have hxc : x ∈ connectedComponentIn P.carrierᶜ y := by
    rw [← heq]; exact mem_connectedComponentIn (sideL_subset_compl D hx)
  exact P.parity_eq_of_mem_connectedComponentIn_carrier hu hL (sideR_subset_compl D hy) hxc

/-! ### At most two regions: walk to the nearest point of the polygon

The blueprint: "Let `x ∉ C`, and choose a nearest point `a ∈ C`. By Lemma 1.3, `[x, a)` avoids
`C`. Its final portion lies in `N_L` or `N_R`, and that track is connected. Hence `x` lies in the
component of either `z_L` or `z_R`." -/

/-- **At most two regions.** Every point of the complement lies in the component of a point of one
of the two tracks: walk towards a nearest point of the polygon — Lemma 1.3 says the walk misses
the polygon — and stop just short of it, inside the collar. -/
theorem exists_mem_sides_connectedComponentIn (P : ClosedPolygon m) (D : StripData P) {x : Plane}
    (hx : x ∉ P.carrier) :
    ∃ y ∈ D.sideL ∪ D.sideR,
      connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ y := by
  -- a nearest point of the polygon, and the segment towards it
  obtain ⟨a, haC, hmin⟩ := P.isCompact_carrier.exists_isMinOn P.carrier_nonempty
    (continuous_const.dist continuous_id).continuousOn
  have hmin' : ∀ b ∈ P.carrier, dist x a ≤ dist x b := isMinOn_iff.1 hmin
  have hax : a ≠ x := fun h => hx (h ▸ haC)
  have hvne : a - x ≠ 0 := sub_ne_zero.2 hax
  have hvpos : 0 < ‖a - x‖ := norm_pos_iff.2 hvne
  have hcont : Continuous (fun θ : ℝ => x + θ • (a - x)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  -- Lemma 1.3: the half-open segment misses the polygon
  have hoff : ∀ θ : ℝ, θ ∈ Ico (0 : ℝ) 1 → x + θ • (a - x) ∉ P.carrier := by
    intro θ hθ
    refine Plane.notMem_of_mem_segment_of_isMinOn haC hx hmin' ?_ ?_
    · rw [segment_eq_image' ℝ x a]; exact ⟨θ, ⟨hθ.1, hθ.2.le⟩, rfl⟩
    · intro h
      have h0 : (θ - 1) • (a - x) = 0 := by linear_combination (norm := module) h
      rcases smul_eq_zero.1 h0 with h1 | h1
      · have := hθ.2; linarith
      · exact hvne h1
  have hSΩ : (fun θ : ℝ => x + θ • (a - x)) '' Ico 0 1 ⊆ P.carrierᶜ := by
    rintro z ⟨θ, hθ, rfl⟩
    exact hoff θ hθ
  have hSpre : IsPreconnected ((fun θ : ℝ => x + θ • (a - x)) '' Ico 0 1) :=
    isPreconnected_Ico.image _ hcont.continuousOn
  -- the collar is a neighbourhood of the nearest point, so the final stretch lies in it
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.1 D.isOpen_nbhd a (D.carrier_subset_nbhd haC)
  have hmpos : 0 < min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)) := lt_min (by norm_num) (by positivity)
  have hmhalf : min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)) ≤ 1 / 2 := min_le_left _ _
  have hθmem : (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) ∈ Ico (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  have hprod : ε / (2 * ‖a - x‖) * ‖a - x‖ = ε / 2 := by
    field_simp
  have hdist : dist (x + (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) • (a - x)) a < ε := by
    rw [dist_eq_norm, show x + (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) • (a - x) - a
        = (-(min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)))) • (a - x) by module,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hmpos]
    calc min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)) * ‖a - x‖
        ≤ ε / (2 * ‖a - x‖) * ‖a - x‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) hvpos.le
      _ = ε / 2 := hprod
      _ < ε := by linarith
  set y : Plane := x + (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) • (a - x) with hy
  have hyLR : y ∈ D.sideL ∪ D.sideR := by
    rw [← D.nbhd_diff_carrier]
    exact ⟨hεball (mem_ball.2 hdist), hoff _ hθmem⟩
  exact ⟨y, hyLR, comp_eq_of_isPreconnected hSpre hSΩ ⟨0, ⟨le_rfl, one_pos⟩, by simp⟩
    ⟨_, hθmem, hy.symm⟩⟩

/-- Every point of the complement lies in the component of one of two fixed reference points,
one on each track. This is `exists_mem_sides_connectedComponentIn` with the track collapsed to a
point, which is possible because each track is connected. -/
theorem connectedComponentIn_eq_of_notMem (P : ClosedPolygon m) (D : StripData P)
    {zL zR : Plane} (hzL : zL ∈ D.sideL) (hzR : zR ∈ D.sideR) {x : Plane} (hx : x ∉ P.carrier) :
    connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ zL ∨
      connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ zR := by
  obtain ⟨y, hy, hyx⟩ := P.exists_mem_sides_connectedComponentIn D hx
  rcases hy with hy | hy
  · exact Or.inl (hyx.trans (comp_eq_of_isPreconnected D.isConnected_sideL.isPreconnected
      (sideL_subset_compl D) hy hzL))
  · exact Or.inr (hyx.trans (comp_eq_of_isPreconnected D.isConnected_sideR.isPreconnected
      (sideR_subset_compl D) hy hzR))

end ClosedPolygon

/-! ### Packaging: from "exactly two components" to `IsSeparating`

`Schoenflies/CrosscutCells.lean` defines `inside C` and `outside C` as the union of the bounded
and of the unbounded components of `Cᶜ`, *without* any separation hypothesis, and Definition 2.4
is the assertion that each of the two is a single region with boundary `C`. So the last step of
Theorem 2.3 is to identify the two components found above with `inside C` and `outside C`, and
that identification needs no case analysis on which of them is which: the one that swallows the
outside of a containing square is the unbounded one by definition, and the other is caught inside
the square. -/

/-- With exactly two components and the outside of a square inside the second, the first is the
bounded part of the complement and the second the unbounded part. -/
theorem inside_outside_of_two_components {C : Set Plane} {r : ℝ} {z₁ z₂ : Plane}
    (hne : connectedComponentIn Cᶜ z₁ ≠ connectedComponentIn Cᶜ z₂)
    (hall : ∀ x ∉ C, connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₁ ∨
      connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₂)
    (hbey : Plane.beyondSquare r ⊆ connectedComponentIn Cᶜ z₂) :
    inside C = connectedComponentIn Cᶜ z₁ ∧ outside C = connectedComponentIn Cᶜ z₂ := by
  have hdisj := comp_disjoint hne
  -- the first component misses the outside of the square, hence sits inside it
  have h1sq : connectedComponentIn Cᶜ z₁ ⊆ Plane.closedSquare 0 r := by
    intro w hw
    by_contra hwq
    exact Set.disjoint_left.1 hdisj hw (hbey (by rw [Plane.beyondSquare_eq_compl]; exact hwq))
  have h1bdd : IsBounded (connectedComponentIn Cᶜ z₁) := (isBounded_closedSquare r).subset h1sq
  have h2unb : ¬ IsBounded (connectedComponentIn Cᶜ z₂) := fun hb =>
    not_isBounded_beyondSquare r (hb.subset hbey)
  constructor
  · ext w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · rcases hall w hw.1 with h | h
      · rw [← h]; exact mem_connectedComponentIn hw.1
      · exact absurd (h ▸ hw.2) h2unb
    · refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
      rw [← connectedComponentIn_eq hw]
      exact h1bdd
  · ext w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · rcases hall w hw.1 with h | h
      · exact absurd (h ▸ h1bdd) hw.2
      · rw [← h]; exact mem_connectedComponentIn hw.1
    · refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
      rw [← connectedComponentIn_eq hw]
      exact h2unb

/-- A component of the complement of a closed set has that set as its frontier as soon as the set
is in its closure: one inclusion is Appendix C item 5, the other is that the component misses the
set altogether. -/
theorem frontier_connectedComponentIn_eq {C : Set Plane} (hC : IsClosed C) (z : Plane)
    (hcl : C ⊆ closure (connectedComponentIn Cᶜ z)) :
    frontier (connectedComponentIn Cᶜ z) = C := by
  refine Set.Subset.antisymm (Plane.frontier_connectedComponentIn_compl_subset hC z) fun w hw => ?_
  rw [(Plane.isOpen_connectedComponentIn hC.isOpen_compl).frontier_eq]
  exact ⟨hcl hw, fun hmem => connectedComponentIn_subset _ _ hmem hw⟩

/-- The packaging step: two distinct components exhausting the complement, each with the curve in
its closure, and the outside of a containing square inside the second, make the curve
separating. -/
theorem isSeparating_of_two_components {C : Set Plane} (hJ : IsJordanCurve C)
    (hC : IsClosed C) {r : ℝ} {z₁ z₂ : Plane} (h₁ : z₁ ∉ C) (h₂ : z₂ ∉ C)
    (hne : connectedComponentIn Cᶜ z₁ ≠ connectedComponentIn Cᶜ z₂)
    (hall : ∀ x ∉ C, connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₁ ∨
      connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₂)
    (hcl₁ : C ⊆ closure (connectedComponentIn Cᶜ z₁))
    (hcl₂ : C ⊆ closure (connectedComponentIn Cᶜ z₂))
    (hbey : Plane.beyondSquare r ⊆ connectedComponentIn Cᶜ z₂) :
    IsSeparating C := by
  obtain ⟨hin, hout⟩ := inside_outside_of_two_components hne hall hbey
  refine ⟨hJ, ?_, ?_, ?_, ?_⟩
  · rw [hin]; exact ⟨⟨z₁, mem_connectedComponentIn h₁⟩, isPreconnected_connectedComponentIn⟩
  · rw [hout]; exact ⟨⟨z₂, mem_connectedComponentIn h₂⟩, isPreconnected_connectedComponentIn⟩
  · rw [hin]; exact frontier_connectedComponentIn_eq hC z₁ hcl₁
  · rw [hout]; exact frontier_connectedComponentIn_eq hC z₂ hcl₂

namespace ClosedPolygon

variable {P : ClosedPolygon m}

/-- **The polygonal Jordan curve theorem** (Theorem 2.3), in the form Definition 2.4 asks for.
The complement of a simple closed polygon has exactly two regions, one bounded and one unbounded,
and each has the polygon as its frontier.

The bounded region is `Schoenflies.inside P.carrier` and the unbounded one
`Schoenflies.outside P.carrier`; everything the blueprint writes `Int(C)` and `Ext(C)` for, and
the whole `IsSeparating` API of `Schoenflies/CrosscutCells.lean`, comes with this statement. -/
theorem isSeparating_carrier (P : ClosedPolygon m) : IsSeparating P.carrier := by
  obtain ⟨D⟩ := exists_stripData P
  obtain ⟨zL, hzL⟩ := D.isConnected_sideL.nonempty
  obtain ⟨zR, hzR⟩ := D.isConnected_sideR.nonempty
  have hzLC : zL ∉ P.carrier := sideL_subset_compl D hzL
  have hzRC : zR ∉ P.carrier := sideR_subset_compl D hzR
  have hne := P.connectedComponentIn_ne_of_mem_sides D hzL hzR
  have hall : ∀ x ∉ P.carrier, connectedComponentIn P.carrierᶜ x =
      connectedComponentIn P.carrierᶜ zL ∨
      connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ zR :=
    fun x hx => P.connectedComponentIn_eq_of_notMem D hzL hzR hx
  -- each track is inside the component of its reference point, so the curve is in its closure
  have hsubL : D.sideL ⊆ connectedComponentIn P.carrierᶜ zL :=
    D.isConnected_sideL.isPreconnected.subset_connectedComponentIn hzL (sideL_subset_compl D)
  have hsubR : D.sideR ⊆ connectedComponentIn P.carrierᶜ zR :=
    D.isConnected_sideR.isPreconnected.subset_connectedComponentIn hzR (sideR_subset_compl D)
  have hclL : P.carrier ⊆ closure (connectedComponentIn P.carrierᶜ zL) :=
    subset_trans D.carrier_subset_closure_sideL (closure_mono hsubL)
  have hclR : P.carrier ⊆ closure (connectedComponentIn P.carrierᶜ zR) :=
    subset_trans D.carrier_subset_closure_sideR (closure_mono hsubR)
  -- a square containing the polygon; its outside lies in one of the two components
  obtain ⟨r, -, hrC⟩ := Plane.IsCompact.exists_closedSquare P.isCompact_carrier
  have hbeyC : Plane.beyondSquare r ⊆ P.carrierᶜ := by
    rw [Plane.beyondSquare_eq_compl]; exact compl_subset_compl.2 hrC
  obtain ⟨w, hw⟩ := (Plane.isConnected_beyondSquare r).nonempty
  have hbeysub : Plane.beyondSquare r ⊆ connectedComponentIn P.carrierᶜ w :=
    (Plane.isConnected_beyondSquare r).isPreconnected.subset_connectedComponentIn hw hbeyC
  rcases hall w (hbeyC hw) with hcw | hcw
  · exact isSeparating_of_two_components P.isJordanCurve_carrier P.isClosed_carrier hzRC hzLC
      (Ne.symm hne) (fun x hx => (hall x hx).symm) hclR hclL (hcw ▸ hbeysub)
  · exact isSeparating_of_two_components P.isJordanCurve_carrier P.isClosed_carrier hzLC hzRC
      hne hall hclL hclR (hcw ▸ hbeysub)

/-! ### The parity values

The blueprint: "take a point `q` whose coordinate along the ray exceeds that of every point of the
compact set `C`. No edge crosses the level line through `q` beyond `q`, so `π_C(q) = 0`; and `q`
lies in the unbounded region." Here `q` is chosen to be beyond a containing *square* as well, so
that it visibly lies in the unbounded region: the outside of that square is connected, misses the
polygon, and is unbounded. -/

/-! ### The theorem, unpacked -/

end ClosedPolygon

end Schoenflies
end

section
-- module Solutions.Q146_CD.ParitySplitting
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.edgesCover_cons _root_.Graph.edgesCover_nil _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Parity splitting: a crosscut adds the two crossing counts

Lemma 2.7. A crosscut `P` of a simple closed polygon `C` cuts it into two arcs `A₁, A₂`, and
the two closed curves `Jᵢ = Aᵢ ∪ P` satisfy `π_C = π_{J₁} + π_{J₂}` off `C ∪ P`. The blueprint
calls this identity "the whole of the polygonal crosscut theorem": Lemma 2.6 exhibits two cells
of `Ω ∖ P`, and this is what says there are no others.

## Where the split is made, and why

The crossing count of `Schoenflies/Parity.lean` is a function of a `List Piece`, not of a set,
and not of a `ClosedPolygon`. Two edge lists with the same carrier can have different parity —
a list that traverses one segment twice is the obvious example — so the identity cannot be
stated for the sets `Aᵢ ∪ P`. It is stated, and proved, for **edge lists**:

    the edge list of `C` is `A₁ ++ A₂`, that of `Jᵢ` is `Aᵢ ++ K`,

where `K` is the edge list of the crosscut. Then `π_{J₁} + π_{J₂} = π_{A₁} + π_{A₂} + 2 π_K`
and the crosscut's contribution cancels mod `2`. That is `parity_split`, and it needs no
geometry at all — no simplicity, no direction, no separation. Everything the blueprint's
picture contributes is in the *hypothesis* that the lists decompose that way.

Two mismatches between "the edge list of `Jᵢ` is `Aᵢ` together with `K`" and literal list
equality have to be absorbed, because a consumer building `Jᵢ` as a `ClosedPolygon` controls
neither:

* the edges come in some cyclic order of that polygon's own choosing, and
* one of the two curves must traverse the crosscut backwards, so its pieces are the *reversed*
  pairs.

`SameEdges` is the equivalence that forgives exactly these two: a permutation of the lists
after each piece has been put in canonical order by `Schoenflies.orientPiece`. Parity, carrier,
closedness and non-levelness are all invariant under it (`SameEdges.parity_eq`,
`SameEdges.cover_eq`, `SameEdges.isChainFrom`, `SameEdges.hgt_ne`), so a consumer may hand over
its edge list in whatever order and orientation it happens to have —
`sameEdges_of_perm_reverse_swap` absorbs both mismatches in one step.

Nothing is assumed about the *sets*: `ClosedPolygon.carrier_eq_of_sameEdges` derives
`Jᵢ.carrier = Aᵢ ∪ P` from the edge lists alone, so the geometric hypothesis a consumer has to
discharge is only ever combinatorial.

## The construction

`ClosedPolygon.arcPieces C a k` is the edge list of the arc of `C` that leaves vertex `a` and
runs forward through `k` edges — the object the split produces, exported as an object rather
than hidden behind an existential. Its two governing facts are

* `ClosedPolygon.arcPieces_split_perm`: `arcPieces C a k ++ arcPieces C (a + k) (m + 3 - k)` is
  a permutation of `C.pieces` — the arcs really do partition the edges; and
* `ClosedPolygon.isChainFrom_arcPieces`: the arc's mod-`2` boundary is its two end vertices,
  which is what makes `Aᵢ ++ K` a *closed* chain and hence eligible for every parity theorem.

`IsChainFrom` is the open-path companion of `Schoenflies.IsClosedChain`, stated by the same
duality; `IsChainFrom.isClosedChain_append` is the one-line reason that an arc and a crosscut
with the same two ends close up. `pathPieces` turns a polyline into such a chain, which is how
the crosscut itself is normally presented.

The endpoints of the crosscut are taken to be **vertices** of `C`; the blueprint's opening
move, "subdivide `C` at `p` and `q`", is what puts them there, and is `parity_subdivide`
(Lemma 2.1) applied before any of this. Nothing below re-proves it. A consumer whose crosscut
lands in the interiors of edges rewrites with `parity_subdivide` first and then applies
`parity_split` to the subdivided list, whose hypotheses are about lists and not about polygons;
what such a consumer must supply for itself is the decomposition of the *subdivided* list into
two arcs, which `arcPieces` does not provide — `arcPieces` splits `C.pieces` at vertices.

## Blueprint

* `SameEdges`, `IsChainFrom`, `pathPieces`, `ClosedPolygon.arcPieces` — the definition of the
  split. "After the subdivision the edge set of `C` is the disjoint union of the edge sets of
  `A₁` and `A₂`, and the edge set of `Jᵢ` is that of `Aᵢ` together with that of `P`."
* `parity_split`, `ClosedPolygon.parity_splitting` — Lemma 2.7, equation (2.2)
  `π_C = π_{J₁} + π_{J₂}`.
* `ClosedPolygon.crosscut_inside_exactly_one`, `ClosedPolygon.crosscut_outside_agree` — the
  "Consequently" of Lemma 2.7, which is where Theorem 2.3 enters: a point of `Int(C)` off `P`
  lies inside exactly one of `J₁, J₂`, and a point of `Ext(C)` off `P` lies inside both or
  inside neither.
* `ClosedPolygon.parity_eq_one_iff` — the two halves of the last sentence of Theorem 2.3, read
  as a single criterion.
* `ClosedPolygon.carrier_eq_of_sameEdges`, `ClosedPolygon.notMem_carrier_of_sameEdges` — the
  bridge back to the sets: `Jᵢ` occupies `Aᵢ ∪ P`, so "off `C` and off `P`" is "off `Jᵢ`".

One lemma here strengthens one on `main`: `mark_swap'` drops the non-levelness hypothesis of
`Schoenflies.mark_swap`, because a level edge is crossed from nowhere and so contributes `0`
under either name. Its home is `Schoenflies/Parity.lean`.
-/

open Metric Set

namespace Schoenflies

variable {u p q r : Plane} {L L₁ L₂ L₃ : List Piece} {m : ℕ}

/-! ## Edge lists up to order and orientation

Parity, carrier and closedness are all functions of the *multiset of unoriented* edges. This
section says so, so that a consumer may present the edge list of a curve in any order and with
either name for each edge. -/

/-- A level edge is crossed from nowhere: the ray from `q` would have to leave at a height both
`≥` and `<` the common height of the two ends. -/
theorem not_crosses_of_level {c d : Plane} (h : hgt u c = hgt u d) (q : Plane) :
    ¬ Crosses u (c, d) q := by
  intro hcr
  obtain ⟨h1, h2, -⟩ := hcr
  have e1 : ((c, d) : Piece).1 = c := rfl
  have e2 : ((c, d) : Piece).2 = d := rfl
  rw [e1, e2, h, min_self] at h1
  rw [e1, e2, h, max_self] at h2
  linarith

/-- **The contribution of an edge does not depend on which end is named first.** This is
`Schoenflies.mark_swap` with its non-levelness hypothesis removed: a level edge contributes `0`
under either name. -/
theorem mark_swap' (u : Plane) (P : Piece) (q : Plane) : mark u (P.2, P.1) q = mark u P q := by
  obtain ⟨a, b⟩ := P
  by_cases h : hgt u a = hgt u b
  · rw [mark, mark, if_neg (not_crosses_of_level h.symm q), if_neg (not_crosses_of_level h q)]
  · exact mark_swap h q

/-- Reordering the edges does not change the count. -/
theorem parity_perm (h : L₁.Perm L₂) (u q : Plane) : parity u L₁ q = parity u L₂ q :=
  (h.map fun P => mark u P q).sum_eq

/-- Reordering the edges does not change what they occupy. -/
theorem cover_perm (h : L₁.Perm L₂) : cover L₁ = cover L₂ := by
  ext z
  simp only [cover, mem_iUnion, exists_prop]
  exact ⟨fun ⟨P, hP, hz⟩ => ⟨P, h.mem_iff.1 hP, hz⟩, fun ⟨P, hP, hz⟩ => ⟨P, h.mem_iff.2 hP, hz⟩⟩

/-- `orientPiece` either leaves a piece alone or reverses it; that is all this file uses. -/
theorem orientPiece_eq_or (P : Piece) : orientPiece P = P ∨ orientPiece P = (P.2, P.1) := by
  by_cases h : Precedes P.1 P.2
  · exact Or.inl (orientPiece_of_precedes h)
  · exact Or.inr (orientPiece_of_not_precedes h)

theorem mark_orientPiece (u : Plane) (P : Piece) (q : Plane) :
    mark u (orientPiece P) q = mark u P q := by
  rcases orientPiece_eq_or P with h | h
  · rw [h]
  · rw [h, mark_swap']

theorem parity_map_orientPiece (u : Plane) (L : List Piece) (q : Plane) :
    parity u (L.map orientPiece) q = parity u L q := by
  simp only [parity, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun P _ => mark_orientPiece u P q)

theorem hgt_ne_orientPiece {P : Piece} (h : hgt u P.1 ≠ hgt u P.2) :
    hgt u (orientPiece P).1 ≠ hgt u (orientPiece P).2 := by
  rcases orientPiece_eq_or P with e | e
  · rw [e]; exact h
  · rw [e]; exact fun hh => h hh.symm

theorem hgt_ne_of_orientPiece {P : Piece} (h : hgt u (orientPiece P).1 ≠ hgt u (orientPiece P).2) :
    hgt u P.1 ≠ hgt u P.2 := by
  rcases orientPiece_eq_or P with e | e
  · rw [e] at h; exact h
  · rw [e] at h; exact fun hh => h hh.symm

/-- **Two edge lists carry the same edges**: they agree after reordering, each edge being free
to be named by either of its two ends first. This is the relation under which "the edge list of
`Jᵢ` is that of `Aᵢ` together with that of `P`" is true — a `ClosedPolygon` built on `Aᵢ ∪ P`
lists its edges in its own cyclic order, and traverses one of the two pieces backwards. -/
def SameEdges (L₁ L₂ : List Piece) : Prop := (L₁.map orientPiece).Perm (L₂.map orientPiece)

@[refl] theorem SameEdges.refl (L : List Piece) : SameEdges L L := List.Perm.refl _

theorem SameEdges.symm (h : SameEdges L₁ L₂) : SameEdges L₂ L₁ := List.Perm.symm h

/-- A reordering is in particular the same edges. -/
theorem SameEdges.of_perm (h : L₁.Perm L₂) : SameEdges L₁ L₂ := h.map _

theorem SameEdges.append {L₁' L₂' : List Piece} (h₁ : SameEdges L₁ L₁') (h₂ : SameEdges L₂ L₂') :
    SameEdges (L₁ ++ L₂) (L₁' ++ L₂') := by
  simpa only [SameEdges, List.map_append] using List.Perm.append h₁ h₂

theorem SameEdges.parity_eq (h : SameEdges L₁ L₂) (u q : Plane) :
    parity u L₁ q = parity u L₂ q := by
  rw [← parity_map_orientPiece u L₁ q, ← parity_map_orientPiece u L₂ q]
  exact parity_perm h u q

theorem SameEdges.cover_eq (h : SameEdges L₁ L₂) : cover L₁ = cover L₂ := by
  rw [← cover_map_orientPiece L₁, ← cover_map_orientPiece L₂]
  exact cover_perm h

/-- Every edge of `L₁` is an edge of `L₂`, up to the naming of its two ends. -/
theorem SameEdges.exists_mem (h : SameEdges L₁ L₂) {Q : Piece} (hQ : Q ∈ L₁) :
    ∃ R ∈ L₂, orientPiece R = orientPiece Q := by
  have hmem : orientPiece Q ∈ L₂.map orientPiece :=
    h.mem_iff.1 (List.mem_map_of_mem (f := orientPiece) hQ)
  obtain ⟨R, hR, hRQ⟩ := List.mem_map.1 hmem
  exact ⟨R, hR, hRQ⟩

/-- Non-levelness for a direction transfers: it is a property of the unoriented edge. -/
theorem SameEdges.hgt_ne (h : SameEdges L₁ L₂) (hL : ∀ Q ∈ L₂, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ L₁, hgt u Q.1 ≠ hgt u Q.2 := by
  intro Q hQ
  obtain ⟨R, hR, hRQ⟩ := h.exists_mem hQ
  exact hgt_ne_of_orientPiece (hRQ ▸ hgt_ne_orientPiece (hL R hR))

theorem hgt_ne_append (h₁ : ∀ Q ∈ L₁, hgt u Q.1 ≠ hgt u Q.2)
    (h₂ : ∀ Q ∈ L₂, hgt u Q.1 ≠ hgt u Q.2) : ∀ Q ∈ L₁ ++ L₂, hgt u Q.1 ≠ hgt u Q.2 := by
  intro Q hQ
  rcases List.mem_append.1 hQ with h | h
  · exact h₁ Q h
  · exact h₂ Q h

/-! ## Chains with two ends

`Schoenflies.IsClosedChain` says the mod-`2` boundary of an edge list vanishes. An arc and a
crosscut are not closed; each has a boundary, namely its two ends, and closing them up is the
statement that the two boundaries agree. Stated by the same duality as `IsClosedChain`, so that
the two definitions compose with nothing but `List.sum_append`. -/

/-! ### The edges of a polyline

How a crosscut is normally presented: a list of points. `pathPieces` reads off its edges, and
`isChainFrom_pathPieces` says its boundary is the two ends of the list. -/

/-- The edges of the polyline `v₀, v₁, …, v_k`. -/
def pathPieces : List Plane → List Piece
  | [] => []
  | [_] => []
  | v :: w :: rest => (v, w) :: pathPieces (w :: rest)

@[simp] theorem pathPieces_nil : pathPieces [] = [] := rfl

@[simp] theorem pathPieces_singleton (v : Plane) : pathPieces [v] = [] := rfl

@[simp] theorem pathPieces_cons_cons (v w : Plane) (rest : List Plane) :
    pathPieces (v :: w :: rest) = (v, w) :: pathPieces (w :: rest) := rfl

/-! ## The two arcs of a polygon

`arcPieces C a k` is the edge list of the arc of `C` that leaves vertex `a` and runs forward
through `k` edges. Its two ends are vertices `a` and `a + k`, and for `k ≤ m + 3` the two arcs
`arcPieces C a k` and `arcPieces C (a + k) (m + 3 - k)` between them use each edge of `C`
exactly once. -/

namespace ClosedPolygon

variable {C : ClosedPolygon m} {a : ZMod (m + 3)} {k : ℕ}

/-- The edge list of the arc of `C` that leaves vertex `a` and runs forward through `k` edges.
For `k ≤ m + 3` this is one of the two arcs a crosscut with endpoints `C.vertex a` and
`C.vertex (a + k)` cuts `C` into; the other is `arcPieces C (a + k) (m + 3 - k)`. -/
def arcPieces (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) : List Piece :=
  (List.range k).map fun t : ℕ => (C.vertex (a + t), C.vertex (a + t + 1))

@[simp] theorem arcPieces_zero (C : ClosedPolygon m) (a : ZMod (m + 3)) :
    C.arcPieces a 0 = [] := rfl

end ClosedPolygon

/-! ## The identity

Everything above was the definition. The identity itself is one line of `ZMod 2` arithmetic:
the crosscut is counted once in each of `π_{J₁}` and `π_{J₂}`, so its contribution cancels. -/

/-- **Parity splitting** (Lemma 2.7), in edge-list form and with no geometry whatever. If the
edge list of `C` is the two arcs `A₁, A₂` and the edge list of `Jᵢ` is `Aᵢ` together with the
crosscut's list `K` — in each case up to reordering and up to reversing individual edges — then
`π_{J₁} + π_{J₂} = π_C` at *every* point of the plane.

The hypotheses carry all of the blueprint's picture; the proof is that `K` is counted twice. -/
theorem parity_split (u : Plane) {LC A₁ A₂ K : List Piece}
    (hC : SameEdges LC (A₁ ++ A₂)) (h₁ : SameEdges L₁ (A₁ ++ K)) (h₂ : SameEdges L₂ (A₂ ++ K))
    (q : Plane) : parity u L₁ q + parity u L₂ q = parity u LC q := by
  rw [h₁.parity_eq u q, h₂.parity_eq u q, hC.parity_eq u q, parity_append, parity_append,
    parity_append]
  linear_combination add_self_zmod_two (parity u K q)

end Schoenflies
end

section
-- module Solutions.Q146_CD.PolygonalCrosscut
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Theorem 2.8: two-sided polygonal crosscuts

A crosscut `P` of a simple closed polygon `C` cuts one of the two regions of `ℝ² ∖ C` into
exactly two, bounded by the two curves `Jᵢ = Aᵢ ∪ P`; and `ℝ² ∖ (C ∪ P)` then has exactly three
regions, with boundaries `C, J₁, J₂`.

## One theorem, not two

The blueprint splits the statement into case (a), the crosscut inside `C`, and case (b), the
crosscut outside. The two cases differ only in *which* region of `ℝ² ∖ Jᵢ` is the new cell: in
case (a) it is `Int(Jᵢ)` for both `i`, while in case (b) it is `Ext(J₁)` for one index and
`Int(J₂)` for the other, and which is which is not determined by the data. What *is* uniform is
the description "the region of `ℝ² ∖ Jᵢ` on the far side from a point `y` of the region of
`ℝ² ∖ C` that the crosscut does not enter". So the whole theorem is proved once, for

    farRegion J y  =  the region of `ℝ² ∖ J` that does not contain `y`,

and the two cases of the blueprint are then read off by identifying `farRegion` with `inside`
or with `outside` (`IsSeparating.farRegion_eq_inside`, `…_eq_outside`). A reference point `y`
in the untouched region is the one extra datum this costs, and it is exactly the datum the
blueprint hides in the phrase "let `Ω` be the region containing `P ∖ {p, q}`".

## Exhaustion is pure parity, in both cases at once

Lemma 2.6 (`Schoenflies.crosscut_cells`) already exhibits the two cells as components of
`Ω ∖ P`. All that Theorem 2.8 adds is that there are no others, and the blueprint reads this
off Lemma 2.7. Here the reading is uniform. Write `πJ` for the crossing count of a curve `J`.
For points `x, y` off `J` — Theorem 2.3 —

    `x` and `y` lie in different regions of `ℝ² ∖ J`  ↔  `πJ(x) ≠ πJ(y)`,

which is `ClosedPolygon.parity_ne_iff_mem_farRegion`. Lemma 2.7 gives
`πJ₁ + πJ₂ = πC` at every point, so subtracting the identity at `y` from the identity at `x`
turns "`x` is separated from `y` by `C`" into "`x` is separated from `y` by exactly one of
`J₁, J₂`" — `IsPolygonalCrosscut.separates_xor`, whose entire proof is sixteen cases of `ZMod 2`
arithmetic. No case distinction on inside/outside is made anywhere.

## The hypotheses, bundled

`IsPolygonalCrosscut C J₁ J₂ K a k y` collects the seven hypotheses of the theorem: the two
curves of the split carry the right edges (`Schoenflies.SameEdges`, from Lemma 2.7), the
crosscut meets `C` only in points common to both arcs, and the reference point `y` lies off `C`
in a region the crosscut does not enter. It is closed under swapping the two arcs
(`IsPolygonalCrosscut.symm`), which is why every statement below is proved for index `1` only.

Realizing `J₁` and `J₂` as `ClosedPolygon`s is the consumer's job, exactly as in Lemma 2.7 —
see the note there about the `corner` field. Nothing in this file inspects `corner`.

## Blueprint

* `farRegion`, `IsSeparating.isRegionPair_farRegion`, `IsSeparating.farRegion_eq_inside`,
  `IsSeparating.farRegion_eq_outside` — the blueprint's `Ω`, `Ω†`, `Vᵢ` and `Wᵢ` named as
  functions of a reference point instead of by an existential.
* `ClosedPolygon.arc` — the arcs `A₁, A₂` of Theorem 2.8, as sets; `…vertex_mem_arc`,
  `…vertex_add_mem_arc`, `…endpoints_subset_arc`, `…endpoints_subset_arc'` — the two cut
  vertices lie on both arcs, which is what "the crosscut meets `C` only in its endpoints" has
  to say to be usable.
* `ClosedPolygon.parity_ne_iff_mem_farRegion` — Theorem 2.3 read as a separation criterion.
* `IsPolygonalCrosscut` — the hypotheses of Theorem 2.8; `IsPolygonalCrosscut.of_endpoints` is
  the constructor a consumer should use, and `IsPolygonalCrosscut.symm` swaps the two arcs.
* `IsPolygonalCrosscut.separates_xor` — Lemma 2.7's "consequently", in the uniform form.
* `IsPolygonalCrosscut.region_eq`, `…cells_disjoint`, `…cells_ne`, `…cell_isComponent₁/₂`,
  `…frontier_cell₁/₂`, `…closure_cell_inter₁/₂` — the two cells of `Ω ∖ P`.
* `IsPolygonalCrosscut.inside_diff_eq` — Theorem 2.8(a).
* `IsPolygonalCrosscut.outside_diff_eq`, `…inside_exactly_one` — Theorem 2.8(b).
* `IsPolygonalCrosscut.compl_eq`, `…isComponent`, `…near_isComponent`,
  `…cell_isComponent_compl₁/₂`, `…cell_ne_near₁/₂`, `…frontier_near` — "in either case
  `ℝ² ∖ (C ∪ P)` has exactly three regions, with boundaries `C, J₁, J₂`".
* `polygonal_crosscut` — Theorem 2.8, bundled.
-/

open Bornology Set

namespace Schoenflies

variable {C J P Ω Ω' W V : Set Plane} {x y z : Plane}

/-! ## The region on the far side of a point

The blueprint names the four regions in play — `Ω`, `Ω†`, `Wᵢ`, `Vᵢ` — by their relation to one
another: `Ω†` is the region of `ℝ² ∖ C` the crosscut does not enter, and `Vᵢ` is the region of
`ℝ² ∖ Jᵢ` on the other side of `Jᵢ` from `Ω†`. Fixing a point `y ∈ Ω†` turns all four into
functions of the data. -/

/-- The region of `ℝ² ∖ C` that does **not** contain `y`: everything off `C` except the
component of `y`. For a separating curve this really is the other region
(`IsSeparating.isRegionPair_farRegion`); no hypothesis is needed to define it. -/
def farRegion (C : Set Plane) (y : Plane) : Set Plane := Cᶜ \ connectedComponentIn Cᶜ y

/-- Off the curve, being in the far region is exactly being in another component. -/
theorem mem_farRegion_iff_connectedComponentIn_ne (hx : x ∉ C) :
    x ∈ farRegion C y ↔ connectedComponentIn Cᶜ x ≠ connectedComponentIn Cᶜ y := by
  refine ⟨fun h hEq => h.2 (hEq ▸ mem_connectedComponentIn hx), fun h => ⟨hx, fun hmem => ?_⟩⟩
  exact h (connectedComponentIn_eq hmem).symm

/-- The crosscut misses the region of `y`, so all of it off the curve is in the far region. -/
theorem diff_subset_farRegion (hdis : Disjoint P (connectedComponentIn Cᶜ y)) :
    P \ C ⊆ farRegion C y :=
  fun _ hz => ⟨hz.2, fun hmem => Set.disjoint_left.1 hdis hz.1 hmem⟩

theorem compl_diff_inside (C : Set Plane) : Cᶜ \ inside C = outside C := by
  ext w
  constructor
  · rintro ⟨hw, hwin⟩
    have hcov : w ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hw
    exact hcov.resolve_left hwin
  · exact fun hw => ⟨hw.1, fun h => Set.disjoint_left.1 disjoint_inside_outside h hw⟩

theorem compl_diff_outside (C : Set Plane) : Cᶜ \ outside C = inside C := by
  ext w
  constructor
  · rintro ⟨hw, hwout⟩
    have hcov : w ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hw
    exact hcov.resolve_right hwout
  · exact fun hw => ⟨hw.1, fun h => Set.disjoint_left.1 disjoint_inside_outside hw h⟩

/-- The component of `y` and the far region are *the* two regions of `ℝ² ∖ C`. -/
theorem IsSeparating.isRegionPair_farRegion (hC : IsSeparating C) (hy : y ∉ C) :
    IsRegionPair C (connectedComponentIn Cᶜ y) (farRegion C y) := by
  rcases hC.isRegionOf_connectedComponentIn hy with hc | hc
  · exact Or.inl ⟨hc, by rw [farRegion, hc, compl_diff_inside]⟩
  · exact Or.inr ⟨hc, by rw [farRegion, hc, compl_diff_outside]⟩

/-! ## The three regions of `ℝ² ∖ (C ∪ P)`, abstractly

Lemma 2.6 places the two cells inside `Ω ∖ P`; the last paragraph of the proof of Theorem 2.8
places all three regions inside `ℝ² ∖ (C ∪ P)`, and the argument is the same each time: an open
connected set whose frontier misses the ambient open set is a component of it (Lemma 1.7). -/

/-! ## The arcs of a polygon, and parity as a separation criterion -/

/-- Going `k` steps forward and then the remaining `m + 3 - k` returns to where one started:
the second arc of a split ends at the first arc's starting vertex. -/
theorem zmod_add_sub_cancel {m k : ℕ} (hk : k ≤ m + 3) (a : ZMod (m + 3)) :
    a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = a := by
  have hcast : ((k : ℕ) : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = 0 := by
    rw [← Nat.cast_add, show k + (m + 3 - k) = m + 3 by omega]
    exact ZMod.natCast_self _
  rw [add_assoc, hcast, add_zero]

namespace ClosedPolygon

variable {m : ℕ} {C : ClosedPolygon m} {a : ZMod (m + 3)} {k : ℕ}

/-- The arc of `C` that leaves vertex `a` and runs forward through `k` edges, as a set: the
blueprint's `A₁` for `k` edges and `A₂` for the remaining `m + 3 - k`. -/
def arc (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) : Set Plane := cover (C.arcPieces a k)

end ClosedPolygon

/-! ## The hypotheses of Theorem 2.8 -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.SimpleArc
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.arcPieces_zero _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.hgt_self _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.subarc_one _root_.Schoenflies.subarc_zero _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Simple polygonal arcs

`Schoenflies/PolyPath.lean` joins two points of a region by a polygonal *path* — a vertex list
whose carrier stays inside the region. A path may cross itself, so it is not an arc. This
module supplies the missing half of Lemma 1.1 and, with it, Lemma 1.2, by running the
blueprint's recipe: *subdivide at all intersections, delete duplicate subsegments, and take a
simple path in the resulting finite graph.*

The three steps are already available.

* Subdividing and deduplicating is `Schoenflies.overlayGraph`: a finite list of nondegenerate
  segments becomes a finite plane graph whose point set is exactly their union
  (`Schoenflies.overlayGraph_pointSet`).
* A simple path in that graph is `Graph.IsPath`, produced by `Graph.Reaches.exists_isPath`.
* Its realisation is an arc between its ends, by `Graph.IsDrawing.path_isArcBetween`.

## What actually has to be proved here

Two things, and neither is in the list above.

**The graph is connected when the union is.** The overlay is built from geometry, so nothing
so far says that two points joined *in the plane* are joined *along edges*. The argument is a
clopen one: for a vertex `a`, the points carried by the edges the walk relation can reach from
`a` form a compact set, the points carried by the other edges form another, the two are
disjoint — a common point would be a vertex incident with edges from both classes, by the
drawing condition — and together they are the whole union. Preconnectedness then forces the
second class to carry nothing.

**The realisation of a path is `poly` of a vertex list.** `Graph.IsDrawing.path_isArcBetween`
delivers `Graph.edgesCover`, a union of edge arcs with no order in it, while `IsPolygonal` and
every polygonal consumer downstream want a vertex list. `Schoenflies.exists_poly_eq_edgesCover`
recovers one by induction along the walk. Its statement returns the list, not the bare
existence of *some* polygonal set, so a consumer that needs the vertices — the redrawing
argument does — still has them.

Both endpoints have to be vertices of the overlay, which is arranged by putting them on the
list of cut points: `EndsAreCut` and `MeetsAreCut` only ask that certain points *occur* in
that list, so lengthening it is free.

## Blueprint

* `Schoenflies.segsOf`, `Schoenflies.cover_segsOf` — a vertex list read as a list of
  nondegenerate segments, the input format the overlay wants.
* `Schoenflies.overlayGraph_reaches` — the overlay graph of a connected union is connected.
* `Schoenflies.exists_simple_poly_of_cover` — Lemma 1.2 (finite polygonal unions), for a union
  given as a finite list of nondegenerate segments.
* `Schoenflies.exists_simple_poly_of_poly`, `Schoenflies.exists_simple_poly_of_isPolygonal` —
  Lemma 1.2 for a set presented as a polygonal carrier.
* `Schoenflies.exists_simple_poly_of_biUnion`, `Schoenflies.exists_simple_poly_of_union` —
  Lemma 1.2 as the blueprint states it, for a finite union of polygonal sets.
* `Schoenflies.exists_simple_poly_of_isPreconnected`,
  `Schoenflies.exists_simple_arc_of_isPreconnected` — Lemma 1.1 (polygonal connectedness), in
  full: any two points of a region are joined in it by a *simple* polygonal arc.

## Two lemmas that belong elsewhere

`Schoenflies.cover_flatMap_list` generalises `Schoenflies.cover_flatMap` to an arbitrary index
list and belongs beside it in `Schoenflies/Subdivide.lean`; `Schoenflies.subset_of_finite_diff`
is a general fact about preconnected sets. Both are here only because their homes are on
`main`.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

variable {pieces : List Piece} {points : List Plane} {Ω : Set Plane} {a b x y : Plane}

/-! ### One more shape of `poly`

`poly_cons_cons` peels a segment off a list of length at least two. The overlay's induction
peels one off a list known only to be nonempty, so it needs the head as a term rather than as
a pattern. -/

/-! ### The segments of a vertex list

`poly` is a *chain*: consecutive vertices, with repetitions allowed. The overlay takes a list
of pieces and insists that each be nondegenerate, so a repetition has to be dropped rather
than passed on. Dropping one is harmless — a degenerate segment is a single point, and that
point is an end of the neighbouring segment — except when the whole chain degenerates to a
point, which is the second disjunct of `cover_segsOf`. -/

open scoped Classical in
/-- The nondegenerate segments of a polygonal chain, in order. A repeated vertex contributes
nothing. -/
noncomputable def segsOf : List Plane → List Piece
  | [] => []
  | [_] => []
  | u :: v :: rest => if u = v then segsOf (v :: rest) else (u, v) :: segsOf (v :: rest)

@[simp] theorem segsOf_nil : segsOf [] = [] := rfl

@[simp] theorem segsOf_singleton (v : Plane) : segsOf [v] = [] := rfl

/-! ### The realisation of a walk is a polygonal chain

`Graph.edgesCover` is a union with no order in it. The walk supplies the order, and the
induction reads the vertex list off it. -/

/-! ### The overlay graph of a connected union is connected

Nothing built so far relates the plane topology of the union to the walk relation of the
graph. This is where they meet. -/

/-! ### Lemma 1.2, and then Lemma 1.1 -/

/-! ### A finite union of polygonal arcs

The blueprint states Lemma 1.2 for a finite union, which `Schoenflies.cover` already is. The
only thing standing between the two readings is that a member of the union may have collapsed
to a single point, contributing no segment at all. A collapsed member is harmless: were its
point missing from the segments, it would be clopen in the union, which a connected set with
more than one point does not tolerate. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.Realization
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Realizing a polygonal Jordan curve as a `ClosedPolygon`

The blueprint's "simple closed polygonal curve" is set-theoretic: an `IsJordanCurve` that is
also `IsPolygonal`, with no condition on vertices at all. The development works instead with
`Schoenflies.ClosedPolygon`, a cyclic vertex list carrying a `corner` field — no three
consecutive vertices collinear. That field is a *presentation* condition, strictly stronger than
the blueprint's notion, and until now nothing said that a set-level polygonal Jordan curve
admits such a presentation. This module proves it.

## How the vertex list is found

The curve is *not* read off the vertex list `IsPolygonal` hands over: that list may retrace
itself, cross itself, and repeat segments, and it carries no order along the curve. Two
structures are laid over the point set instead and then matched.

* **From the plane side**, the overlay of `Schoenflies/OverlayGraph.lean`, with the graph
  discarded: `Schoenflies.IsClean` is a finite list of nondegenerate segments occupying the
  curve, with pairwise disjoint interiors and no end interior to any of them. Around an interior
  point of a piece the curve *is* that piece (`IsClean.exists_ball_subset_seg`), so the piece
  interiors are separated by honest open sets of the plane (`Schoenflies.nearPiece`) and a
  connected subset of the curve away from the ends lies inside a single piece.
* **From the curve side**, the loop's parameters at which it reaches an end of a piece. They
  form a finite subset of `[0, 1)` containing `0` — `0` because the loop's start is put on the
  cut list, so that the last gap is the one that closes the curve — and, listed in increasing
  order, they cut `[0, 1)` into gaps.

The two match: a gap image is connected and misses the ends, so it lies in one piece interior;
and the interior is connected and covered by the *closed* gap images, so it lies in that one
gap. Gaps and pieces therefore correspond one to one, the ends of a gap are the ends of its
piece, and the ends listed in the loop's order are a cyclic vertex list whose edges are the
pieces. That list satisfies `vertex_inj` and `edges_meet` but not `corner`, which is what
`Schoenflies.PrePolygon` is for; `corner` is then arranged by deleting redundant vertices.

## Blueprint

* `Schoenflies.PrePolygon` — a `ClosedPolygon` less the `corner` field: the blueprint's simple
  closed polygonal curve *presented by a vertex list*, redundant vertices allowed.
* `Schoenflies.PrePolygon.deleteLast`, `Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`
  — the blueprint's opening move in Lemma 1.8, "delete redundant vertices at which two
  consecutive edges are collinear", as an operation rather than an invariant.
* `Schoenflies.IsClean`, `Schoenflies.exists_isClean` — Lemma 3.7 (polygonal overlay) with the
  combinatorics dropped: what the overlay says about the point set alone.
* `Schoenflies.par`, `Schoenflies.parNext`, `Schoenflies.exists_mem_gap` — the parameters in
  increasing order, and that their gaps tile `[0, 1)`.
* `Schoenflies.exists_prePolygon_of_isJordanCurve`, `Schoenflies.exists_closedPolygon` — §1:
  every simple closed polygonal curve, in the blueprint's set-level sense, is the carrier of a
  `ClosedPolygon`.
* `Schoenflies.IsStraightAt`, `Schoenflies.IsCornerAt`,
  `Schoenflies.ClosedPolygon.exists_vertex_eq_of_isCornerAt`,
  `Schoenflies.ClosedPolygon.isCornerAt_vertex` — the vertex set of a realization is *exactly*
  the set of points at which the curve does not run straight. So a named point can be required
  to be a vertex precisely when it is a corner, and no realization has any choice about it.
* `Schoenflies.ClosedPolygon.rotate`, `…isArcBetween_arc`, `…arc_inter` — the two arcs of a
  splitting, as arcs between the two cut vertices meeting exactly there.
* `Schoenflies.two_arcs_unique` — two points cut a Jordan curve into two arcs in only one way.
* `Schoenflies.exists_closedPolygon_corners`, `Schoenflies.exists_closedPolygon_split`,
  `Schoenflies.exists_closedPolygon_arcs`, `Schoenflies.exists_closedPolygon_arcs_ordered` — the
  realization with named corners, with the splitting indices, and with the two arcs identified.
  The last is the shape `Graph.IsHexRealization` asks for.

## The corner hypothesis is not an artefact

`exists_closedPolygon_arcs` requires the two cut points to be corners.
`ClosedPolygon.isCornerAt_vertex` shows that this cannot be dropped: every vertex of every
realization is a corner, so a cut point at which the curve runs straight is a vertex of *no*
realization, and no `ClosedPolygon` with that carrier has an arc ending there. A consumer that
needs to cut at a straight point has to change the curve — bend it there — which is a different
theorem, and is exactly the freedom `Graph.IsK33Config.not_isDrawing` reserves for itself.
-/

open Metric Set unitInterval

namespace Schoenflies

open Plane

/-! ## Polygons before normalization

`PrePolygon` is `ClosedPolygon` with the `corner` field removed. Everything the curve bridge of
`Schoenflies/PolygonBridge.lean` proves about a `ClosedPolygon` — that its carrier is a Jordan
curve, that it is polygonal — uses only `vertex_inj` and `edges_meet`, so it is already true
here; what `corner` buys is the germ argument of the strip lemma, and nothing else. -/

/-- A simple closed polygonal curve presented by its cyclic vertex list, with redundant
vertices allowed: `ClosedPolygon` less its `corner` field. -/
structure PrePolygon (m : ℕ) where
  /-- The vertices, in cyclic order. -/
  vertex : ZMod (m + 3) → Plane
  /-- The vertices are distinct. -/
  vertex_inj : Function.Injective vertex
  /-- Simplicity: an edge meets any other edge only at one of its own endpoints. -/
  edges_meet : ∀ i j : ZMod (m + 3), i ≠ j →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) ⊆
      {vertex i, vertex (i + 1)}

namespace PrePolygon

variable {m : ℕ} (P : PrePolygon m)

/-- The edge leaving vertex `i`. -/
def edge (i : ZMod (m + 3)) : Set Plane := segment ℝ (P.vertex i) (P.vertex (i + 1))

/-- The carrier: the union of the edges. -/
def carrier : Set Plane := ⋃ i, P.edge i

variable {P}

theorem edge_subset_carrier (i : ZMod (m + 3)) : P.edge i ⊆ P.carrier := Set.subset_iUnion _ i

theorem vertex_ne_succ (i : ZMod (m + 3)) : P.vertex i ≠ P.vertex (i + 1) := fun h =>
  ClosedPolygon.succ_ne_self i (P.vertex_inj h).symm

end PrePolygon

/-- A `ClosedPolygon` read as a `PrePolygon`: forget the `corner` field. -/
def ClosedPolygon.toPre {m : ℕ} (P : ClosedPolygon m) : PrePolygon m :=
  ⟨P.vertex, P.vertex_inj, P.edges_meet⟩

@[simp] theorem ClosedPolygon.carrier_toPre {m : ℕ} (P : ClosedPolygon m) :
    P.toPre.carrier = P.carrier := rfl

/-! ## Small facts about the cyclic index

`ZMod (m + 3)` has at least three elements; `0`, `1` and `2` are distinct, which is what makes
a vertex, its successor and its predecessor three different vertices. -/

namespace PrePolygon

variable {m : ℕ}

theorem val_one_eq : (1 : ZMod (m + 3)).val = 1 := by
  rw [show (1 : ZMod (m + 3)) = ((1 : ℕ) : ZMod (m + 3)) by norm_num]
  exact ZMod.val_cast_of_lt (by omega)

/-- The successor of a non-final index is the next one. -/
theorem val_succ_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) : (j + 1).val = j.val + 1 := by
  rw [ZMod.val_add, val_one_eq, Nat.mod_eq_of_lt h]

/-- The successor of the final index wraps to `0`. -/
theorem val_succ_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : (j + 1).val = 0 := by
  rw [ZMod.val_add, val_one_eq, h, Nat.mod_self]

/-! ## Rotation

Reading the same cyclic list from a different starting vertex. It is used once, to bring the
vertex that is about to be deleted to the end of the list. -/

/-- The same closed polygon, read from vertex `a` onwards. -/
def rotate (P : PrePolygon m) (a : ZMod (m + 3)) : PrePolygon m where
  vertex j := P.vertex (a + j)
  vertex_inj i j h := add_left_cancel (P.vertex_inj h)
  edges_meet i j hij := by
    have hi : a + (i + 1) = a + i + 1 := by ring
    have hj : a + (j + 1) = a + j + 1 := by ring
    simp only [hi, hj]
    exact P.edges_meet _ _ fun h => hij (add_left_cancel h)

@[simp] theorem rotate_vertex (P : PrePolygon m) (a j : ZMod (m + 3)) :
    (P.rotate a).vertex j = P.vertex (a + j) := rfl

/-- Rotating does not move the curve: the edges are the same, listed from elsewhere. -/
theorem carrier_rotate (P : PrePolygon m) (a : ZMod (m + 3)) :
    (P.rotate a).carrier = P.carrier := by
  have hedge : ∀ j : ZMod (m + 3), (P.rotate a).edge j = P.edge (a + j) := by
    intro j
    rw [edge, edge, rotate_vertex, rotate_vertex, show a + (j + 1) = a + j + 1 by ring]
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) (Set.iUnion_subset fun i => ?_)
  · rw [hedge]; exact edge_subset_carrier _
  · refine le_trans (le_of_eq ?_) (edge_subset_carrier (P := P.rotate a) (i - a))
    rw [hedge, add_sub_cancel]

/-! ## Deleting the last vertex

The blueprint's opening move in the strip lemma. The vertex to be deleted is brought to the end
of the list by `rotate`, so only that one case has to be treated. `emb` is the inclusion of the
shortened index set into the old one: the same numeral, one modulus smaller. -/

section Delete

variable {m : ℕ}

/-- An index of the shortened list, read in the original one: the same numeral. -/
def emb (j : ZMod (m + 3)) : ZMod (m + 1 + 3) := ((j.val : ℕ) : ZMod (m + 1 + 3))

theorem neg_one_eq_cast : (-1 : ZMod (m + 1 + 3)) = ((m + 3 : ℕ) : ZMod (m + 1 + 3)) := by
  have h0 : ((m + 1 + 3 : ℕ) : ZMod (m + 1 + 3)) = 0 := ZMod.natCast_self _
  push_cast at h0 ⊢
  linear_combination -h0

theorem neg_two_eq_cast : (-1 - 1 : ZMod (m + 1 + 3)) = ((m + 2 : ℕ) : ZMod (m + 1 + 3)) := by
  have h0 : ((m + 1 + 3 : ℕ) : ZMod (m + 1 + 3)) = 0 := ZMod.natCast_self _
  push_cast at h0 ⊢
  linear_combination -h0

theorem emb_injective : Function.Injective (emb (m := m)) := fun i j h =>
  ZMod.val_injective _ (ClosedPolygon.natCast_inj (m := m + 1)
    (by have := ZMod.val_lt i; omega) (by have := ZMod.val_lt j; omega) h)

theorem emb_succ_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) : emb (j + 1) = emb j + 1 := by
  rw [emb, emb, val_succ_of_lt h, Nat.cast_add, Nat.cast_one]

theorem emb_succ_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : emb (j + 1) = 0 := by
  rw [emb, val_succ_last h, Nat.cast_zero]

theorem emb_eq_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : emb j = -1 - 1 := by
  rw [emb, neg_two_eq_cast, show j.val = m + 2 by omega]

/-- Below the last index, `emb` misses both the deleted vertex and its predecessor. -/
theorem emb_ne_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    emb j ≠ -1 ∧ emb j ≠ -1 - 1 := by
  have hj := ZMod.val_lt j
  constructor
  · rw [neg_one_eq_cast]
    exact fun he => (by omega : j.val ≠ m + 3)
      (ClosedPolygon.natCast_inj (m := m + 1) (by omega) (by omega) he)
  · rw [neg_two_eq_cast]
    exact fun he => (by omega : j.val ≠ m + 2)
      (ClosedPolygon.natCast_inj (m := m + 1) (by omega) (by omega) he)

/-- Every index other than the deleted vertex and its predecessor is hit by `emb`. -/
theorem exists_emb_eq {i : ZMod (m + 1 + 3)} (h1 : i ≠ -1) (h2 : i ≠ -1 - 1) :
    ∃ j : ZMod (m + 3), j.val + 1 < m + 3 ∧ emb j = i := by
  have hi := ZMod.val_lt i
  have hne1 : i.val ≠ m + 3 := by
    rintro he
    exact h1 (by rw [neg_one_eq_cast, ← he, ZMod.natCast_rightInverse i])
  have hne2 : i.val ≠ m + 2 := by
    rintro he
    exact h2 (by rw [neg_two_eq_cast, ← he, ZMod.natCast_rightInverse i])
  refine ⟨(i.val : ZMod (m + 3)), ?_, ?_⟩
  · rw [ZMod.val_cast_of_lt (show i.val < m + 3 by omega)]; omega
  · rw [emb, ZMod.val_cast_of_lt (show i.val < m + 3 by omega), ZMod.natCast_rightInverse i]

variable (P : PrePolygon (m + 1))

/-- The vertex list with its last entry dropped. -/
def dropVertex (j : ZMod (m + 3)) : Plane := P.vertex (emb j)

variable {P}

theorem dropVertex_injective : Function.Injective P.dropVertex :=
  fun _ _ h => emb_injective (P.vertex_inj h)

/-- Away from the deleted vertex the edges are unchanged. -/
theorem dropVertex_edge_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) = P.edge (emb j) := by
  rw [dropVertex, dropVertex, emb_succ_of_lt h, edge]

/-- The final edge of the shortened list is the union of the two edges at the deleted vertex —
which is a segment precisely because the deleted vertex is interior to it. -/
theorem dropVertex_edge_last
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0))
    {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) = P.edge (-1 - 1) ∪ P.edge (-1) := by
  have e1 : (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 := by ring
  have e2 : (-1 : ZMod (m + 1 + 3)) + 1 = 0 := by ring
  rw [dropVertex, dropVertex, emb_succ_last h, emb_eq_last h, edge, edge, e1, e2]
  exact segment_split (openSegment_subset_segment ℝ _ _ hcol)

/-- The deleted vertex lies on no edge but its own two: `edges_meet` puts a meeting point at an
end of the other edge, and the deleted vertex is an end only of the two edges at it. -/
theorem vertex_last_notMem_edge {i : ZMod (m + 1 + 3)} (h1 : i ≠ -1) (h2 : i ≠ -1 - 1) :
    P.vertex (-1) ∉ P.edge i := by
  intro hmem
  have hself : P.vertex (-1) ∈ P.edge (-1) := left_mem_segment ℝ _ _
  have hme := P.edges_meet i (-1) h1 (Set.mem_inter hmem hself)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme
  rcases hme with he | he
  · exact h1 (P.vertex_inj he).symm
  · exact h2 (by linear_combination -P.vertex_inj he)

/-- **Simplicity survives the deletion.** The only new edge is the merged one, and the point
that has to be kept out of it — the deleted vertex — lies on no other edge at all. -/
theorem dropVertex_edges_meet
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0))
    (j k : ZMod (m + 3)) (hjk : j ≠ k) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) ∩
      segment ℝ (P.dropVertex k) (P.dropVertex (k + 1)) ⊆
      {P.dropVertex j, P.dropVertex (j + 1)} := by
  have e1 : (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 := by ring
  have e2 : (-1 : ZMod (m + 1 + 3)) + 1 = 0 := by ring
  have hjv : j.val + 1 ≤ m + 3 := ZMod.val_lt j
  have hkv : k.val + 1 ≤ m + 3 := ZMod.val_lt k
  rcases eq_or_lt_of_le hjv with hj | hj
  · -- `j` is the last index, so its edge is the merged one.
    have hdj : P.dropVertex j = P.vertex (-1 - 1) := by rw [dropVertex, emb_eq_last hj]
    have hdj1 : P.dropVertex (j + 1) = P.vertex 0 := by rw [dropVertex, emb_succ_last hj]
    rcases eq_or_lt_of_le hkv with hk | hk
    · exact absurd (ZMod.val_injective _ (by omega : j.val = k.val)) hjk
    obtain ⟨hk1, hk2⟩ := emb_ne_of_lt hk
    have hout := vertex_last_notMem_edge (P := P) hk1 hk2
    rw [dropVertex_edge_last hcol hj, dropVertex_edge_of_lt hk, hdj, hdj1]
    rintro x ⟨hx1 | hx1, hx2⟩
    · have hme := P.edges_meet _ _ (fun h => hk2 h.symm) (Set.mem_inter hx1 hx2)
      rw [e1] at hme
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme ⊢
      exact hme.imp id fun h => absurd (h ▸ hx2) hout
    · have hme := P.edges_meet _ _ (fun h => hk1 h.symm) (Set.mem_inter hx1 hx2)
      rw [e2] at hme
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme ⊢
      exact Or.inr (hme.resolve_left fun h => absurd (h ▸ hx2) hout)
  · -- `j` is an ordinary index, so its edge is unchanged.
    obtain ⟨hj1, hj2⟩ := emb_ne_of_lt hj
    have hdj : P.dropVertex j = P.vertex (emb j) := rfl
    have hdj1 : P.dropVertex (j + 1) = P.vertex (emb j + 1) := by
      rw [dropVertex, emb_succ_of_lt hj]
    rw [dropVertex_edge_of_lt hj, hdj, hdj1]
    rcases eq_or_lt_of_le hkv with hk | hk
    · rw [dropVertex_edge_last hcol hk]
      rintro x ⟨hx1, hx2 | hx2⟩
      · exact P.edges_meet _ _ hj2 (Set.mem_inter hx1 hx2)
      · exact P.edges_meet _ _ hj1 (Set.mem_inter hx1 hx2)
    · rw [dropVertex_edge_of_lt hk]
      exact fun x hx => P.edges_meet _ _ (fun h => hjk (emb_injective h)) hx

/-- **The polygon with a redundant vertex deleted.** -/
def deleteLast (P : PrePolygon (m + 1))
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) : PrePolygon m where
  vertex := P.dropVertex
  vertex_inj := dropVertex_injective
  edges_meet := dropVertex_edges_meet hcol

/-- **Deleting a redundant vertex does not move the curve.** -/
theorem carrier_deleteLast
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) :
    (deleteLast P hcol).carrier = P.carrier := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) (Set.iUnion_subset fun i => ?_)
  · have hjv : j.val + 1 ≤ m + 3 := ZMod.val_lt j
    rcases eq_or_lt_of_le hjv with hj | hj
    · rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_last hcol hj]
      exact Set.union_subset (edge_subset_carrier _) (edge_subset_carrier _)
    · rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_of_lt hj]
      exact edge_subset_carrier _
  · by_cases hi : i = -1 ∨ i = -1 - 1
    · -- The two edges at the deleted vertex are both inside the merged one.
      set j : ZMod (m + 3) := ((m + 2 : ℕ) : ZMod (m + 3)) with hjdef
      have hj : j.val + 1 = m + 3 := by rw [hjdef, ZMod.val_cast_of_lt (by omega)]
      have hmerge : (deleteLast P hcol).edge j = P.edge (-1 - 1) ∪ P.edge (-1) :=
        dropVertex_edge_last hcol hj
      refine le_trans ?_ (le_trans (le_of_eq hmerge.symm) (edge_subset_carrier j))
      rcases hi with rfl | rfl
      · exact Set.subset_union_right
      · exact Set.subset_union_left
    · push Not at hi
      obtain ⟨j, hj, hemb⟩ := exists_emb_eq hi.1 hi.2
      have : (deleteLast P hcol).edge j = P.edge i := by
        rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_of_lt hj, hemb]
      exact le_trans (le_of_eq this.symm) (edge_subset_carrier j)

end Delete

/-! ## Recognising a redundant vertex

The `corner` field is `det ≠ 0` at every vertex. Where it fails the vertex is *interior* to the
segment joining its two neighbours, never an endpoint of it. That is the geometric content of
`edges_meet`: two edges leaving a vertex in the *same* direction would overlap in a
nondegenerate segment, and `edges_meet` would then put a whole segment inside a two-point
set. -/

/-- A nondegenerate segment is not contained in the pair of its own endpoints. -/
theorem exists_mem_segment_ne {a b : Plane} (hab : a ≠ b) :
    ∃ p ∈ segment ℝ a b, p ≠ a ∧ p ≠ b := by
  have hmem : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈ openSegment ℝ a b :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  refine ⟨_, openSegment_subset_segment ℝ a b hmem, ?_, ?_⟩
  · intro h
    rw [h] at hmem
    exact hab (left_mem_openSegment_iff.1 hmem)
  · intro h
    rw [h] at hmem
    exact hab (right_mem_openSegment_iff.1 hmem)

/-- **Three collinear points meeting only at the shared one are in the order that makes the
middle one interior.** The alternative — the two segments running the same way out of `b` —
makes them overlap in a nondegenerate segment, which the meeting hypothesis forbids. -/
theorem mem_openSegment_of_det_eq_zero' {a b c : Plane} (hab : a ≠ b) (hcb : c ≠ b)
    (hmeet : segment ℝ a b ∩ segment ℝ b c ⊆ {a, b})
    (h : det (a - b) (c - b) = 0) : b ∈ openSegment ℝ a c := by
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  obtain ⟨r, hr⟩ := (det_eq_zero_iff_smul _ _ hab').1 h
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_eq_zero] at hr
    exact hcb hr
  have hcexp : c = b + r • (a - b) := by linear_combination (norm := module) hr
  have hrneg : r < 0 := by
    rcases lt_trichotomy r 0 with hlt | heq | hgt
    · exact hlt
    · exact absurd heq hr0
    exfalso
    -- A short step out of `b` towards `a` is then also a step towards `c`.
    have hμpos : 0 < min 1 r / 2 := by positivity
    set μ : ℝ := min 1 r / 2 with hμdef
    have hμ1 : μ < 1 := by
      have h1 : min 1 r ≤ 1 := min_le_left _ _
      rw [hμdef]; linarith
    have hμler : μ / r < 1 := by
      rw [div_lt_one hgt]
      have h1 : min 1 r ≤ r := min_le_right _ _
      rw [hμdef]; linarith
    have hμr : μ / r * r = μ := div_mul_cancel₀ _ (ne_of_gt hgt)
    have hz₁ : μ • a + (1 - μ) • b ∈ segment ℝ a b :=
      ⟨μ, 1 - μ, hμpos.le, by linarith, by ring, rfl⟩
    have hz₂ : μ • a + (1 - μ) • b ∈ segment ℝ b c := by
      refine ⟨1 - μ / r, μ / r, by linarith, by positivity, by ring, ?_⟩
      have expand : (1 - μ / r) • b + (μ / r) • (b + r • (a - b))
          = (μ / r * r) • a + (1 - μ / r * r) • b := by module
      rw [hcexp, expand, hμr]
    have hmem := hmeet ⟨hz₁, hz₂⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with he | he
    · have hkey : (1 - μ) • (a - b) = 0 := by linear_combination (norm := module) -he
      rcases smul_eq_zero.1 hkey with h' | h'
      · exact (by linarith : (0 : ℝ) < 1 - μ).ne' h'
      · exact hab' h'
    · have hkey : μ • (a - b) = 0 := by linear_combination (norm := module) he
      rcases smul_eq_zero.1 hkey with h' | h'
      · exact hμpos.ne' h'
      · exact hab' h'
  -- Opposite directions: the vertex is a strict convex combination of its neighbours.
  have hden : (0 : ℝ) < 1 - r := by linarith
  refine ⟨-r / (1 - r), 1 / (1 - r), div_pos (by linarith) hden, div_pos one_pos hden,
    by field_simp <;> ring, ?_⟩
  have expand : (-r / (1 - r)) • a + (1 / (1 - r)) • (b + r • (a - b))
      = (-r / (1 - r) + 1 / (1 - r) * r) • a + (1 / (1 - r) - 1 / (1 - r) * r) • b := by module
  rw [hcexp, expand, show -r / (1 - r) + 1 / (1 - r) * r = 0 by field_simp; ring,
    show (1 : ℝ) / (1 - r) - 1 / (1 - r) * r = 1 by field_simp, zero_smul, one_smul, zero_add]

variable {m : ℕ} {P : PrePolygon m}

/-- **A redundant vertex is interior to the segment joining its neighbours.** -/
theorem mem_openSegment_of_det_eq_zero (i : ZMod (m + 3))
    (h : det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) = 0) :
    P.vertex i ∈ openSegment ℝ (P.vertex (i - 1)) (P.vertex (i + 1)) := by
  have hpred : i - 1 + 1 = i := sub_add_cancel i 1
  have hne : i - 1 ≠ i := fun he =>
    ClosedPolygon.succ_ne_self (i - 1) (by rw [hpred]; exact he.symm)
  have hmeet := P.edges_meet (i - 1) i hne
  rw [hpred] at hmeet
  exact mem_openSegment_of_det_eq_zero' (fun he => hne (P.vertex_inj he))
    (fun he => ClosedPolygon.succ_ne_self i (P.vertex_inj he)) hmeet h

/-! ## Normalization

Delete redundant vertices until none is left. Each deletion shortens the list by one, and the
list can never shrink below three vertices: a triangle with a redundant vertex would have one
edge inside another, which `edges_meet` forbids. -/

/-- A three-vertex polygon has no redundant vertex: were the last one interior to the segment
joining the other two, the edge before it would lie inside the edge opposite it. -/
theorem not_collinear_triangle (P : PrePolygon 0) :
    P.vertex (-1) ∉ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0) := by
  intro hcol
  have e1 : (-1 - 1 : ZMod (0 + 3)) + 1 = -1 := by decide
  have e2 : (-1 : ZMod (0 + 3)) ≠ -1 - 1 := by decide
  have hsplit : segment ℝ (P.vertex (-1 - 1)) (P.vertex 0)
      = segment ℝ (P.vertex (-1 - 1)) (P.vertex (-1)) ∪ segment ℝ (P.vertex (-1)) (P.vertex 0) :=
    segment_split (openSegment_subset_segment ℝ _ _ hcol)
  -- The edge before the redundant vertex sits inside the edge opposite it.
  have hsub : P.edge (-1 - 1) ⊆ P.edge (-1 - 1 - 1) := by
    have e3 : (-1 - 1 - 1 : ZMod (0 + 3)) = 0 := by decide
    have e4 : (0 : ZMod (0 + 3)) + 1 = -1 - 1 := by decide
    rw [edge, edge, e1, e3, e4, segment_symm ℝ (P.vertex 0) (P.vertex (-1 - 1)), hsplit]
    exact Set.subset_union_left
  obtain ⟨p, hp, hp1, hp2⟩ := exists_mem_segment_ne (P.vertex_ne_succ (-1 - 1))
  rcases P.edges_meet (-1 - 1) (-1 - 1 - 1) (by decide) ⟨hp, hsub hp⟩ with h | h
  exacts [hp1 h, hp2 h]

/-- **Every `PrePolygon` normalizes to a `ClosedPolygon` with the same carrier.** This is the
blueprint's "delete redundant vertices at which two consecutive edges are collinear", run to
completion; the induction is on the number of vertices, which each deletion lowers by one. -/
theorem exists_closedPolygon_of_prePolygon :
    ∀ (m : ℕ) (P : PrePolygon m), ∃ (m' : ℕ) (P' : ClosedPolygon m'), P'.carrier = P.carrier := by
  intro m
  induction m with
  | zero =>
    intro P
    by_cases hc : ∀ i : ZMod (0 + 3),
        det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0
    · exact ⟨0, ⟨P.vertex, P.vertex_inj, P.edges_meet, hc⟩, rfl⟩
    · push Not at hc
      obtain ⟨i, hi⟩ := hc
      refine absurd ?_ (not_collinear_triangle (P.rotate (i + 1)))
      have e1 : i + 1 + (-1 : ZMod (0 + 3)) = i := by ring
      have e2 : i + 1 + (-1 - 1 : ZMod (0 + 3)) = i - 1 := by ring
      have e3 : i + 1 + (0 : ZMod (0 + 3)) = i + 1 := by ring
      rw [rotate_vertex, rotate_vertex, rotate_vertex, e1, e2, e3]
      exact mem_openSegment_of_det_eq_zero i hi
  | succ m ih =>
    intro P
    by_cases hc : ∀ i : ZMod (m + 1 + 3),
        det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0
    · exact ⟨m + 1, ⟨P.vertex, P.vertex_inj, P.edges_meet, hc⟩, rfl⟩
    · push Not at hc
      obtain ⟨i, hi⟩ := hc
      have hcol : (P.rotate (i + 1)).vertex (-1) ∈
          openSegment ℝ ((P.rotate (i + 1)).vertex (-1 - 1)) ((P.rotate (i + 1)).vertex 0) := by
        have e1 : i + 1 + (-1 : ZMod (m + 1 + 3)) = i := by ring
        have e2 : i + 1 + (-1 - 1 : ZMod (m + 1 + 3)) = i - 1 := by ring
        have e3 : i + 1 + (0 : ZMod (m + 1 + 3)) = i + 1 := by ring
        rw [rotate_vertex, rotate_vertex, rotate_vertex, e1, e2, e3]
        exact mem_openSegment_of_det_eq_zero i hi
      obtain ⟨m', P', hP'⟩ := ih (deleteLast (P.rotate (i + 1)) hcol)
      exact ⟨m', P', by rw [hP', carrier_deleteLast, carrier_rotate]⟩

end PrePolygon

/-! ## Clean pieces

The overlay of `Schoenflies/OverlayGraph.lean`, stripped of the graph. All that is wanted from
it is a finite list of segments occupying the curve whose interiors are pairwise disjoint and
none of whose ends is interior to any of them — the geometric content of `lem:polygonal-overlay`
with the combinatorics left out. -/

/-- A finite list of segments presenting a polygonal set as a plane graph would: occupying it,
nondegenerate, with pairwise disjoint interiors, and with no end interior to any piece. -/
structure IsClean (Q : List Piece) (C : Set Plane) : Prop where
  /-- The pieces occupy the set. -/
  cover_eq : cover Q = C
  /-- No piece is a point. -/
  nondeg : ∀ R ∈ Q, R.Nondeg
  /-- No end of any piece is interior to any piece. -/
  ends : ∀ R ∈ Q, ∀ S ∈ Q, ∀ z, (z = R.1 ∨ z = R.2) → z ∉ S.interior
  /-- Distinct pieces have disjoint interiors. -/
  interiors : ∀ R ∈ Q, ∀ S ∈ Q, R ≠ S → ∀ x ∈ R.interior, x ∉ S.interior

/-- A point of a piece is interior to it or one of its ends. -/
theorem mem_interior_or_end {R : Piece} {x : Plane} (hx : x ∈ R.seg) :
    x ∈ R.interior ∨ x = R.1 ∨ x = R.2 := by
  by_cases hcon : x = R.1 ∨ x = R.2
  · exact Or.inr hcon
  · push Not at hcon
    exact Or.inl (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hx)

/-- The open set that isolates one piece from the others: the union of the balls in which the
curve is that piece alone. -/
def nearPiece (C : Set Plane) (R : Piece) : Set Plane :=
  {y | ∃ x ∈ R.interior, ∃ r > 0, y ∈ ball x r ∧ ball x r ∩ C ⊆ R.seg}

theorem isOpen_nearPiece {C : Set Plane} {R : Piece} : IsOpen (nearPiece C R) := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨x, hx, r, hr, hyb, hsub⟩
  exact ⟨ball x r, fun z hz => ⟨x, hx, r, hr, hz, hsub⟩, isOpen_ball, hyb⟩

namespace IsClean

variable {Q : List Piece} {C : Set Plane} {R S : Piece} {x : Plane} (h : IsClean Q C)
include h

/-- **Two distinct clean pieces meet only at ends of the first.** This is `edges_meet`, before
the pieces have been put in cyclic order. -/
theorem seg_inter_subset (hR : R ∈ Q) (hS : S ∈ Q) (hRS : R ≠ S) :
    R.seg ∩ S.seg ⊆ {R.1, R.2} := by
  rintro z ⟨hzR, hzS⟩
  rcases mem_interior_or_end hzR with hz | hz
  · exfalso
    rcases mem_interior_or_end hzS with hz' | hz'
    · exact h.interiors R hR S hS hRS z hz hz'
    · exact h.ends S hS R hR z hz' hz
  · exact hz

theorem seg_subset (hR : R ∈ Q) : R.seg ⊆ C := by
  rw [← h.cover_eq]
  exact fun z hz => mem_cover hR hz

theorem mem_cover_of_mem (hz : x ∈ C) : x ∈ cover Q := by rw [h.cover_eq]; exact hz

/-- **The curve minus the ends is the disjoint union of the piece interiors.** -/
theorem diff_endSet_eq : C \ endSet Q = ⋃ R ∈ Q, R.interior := by
  refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover (h.mem_cover_of_mem hz.1)
    refine Set.mem_iUnion₂.2 ⟨R, hR, ?_⟩
    rcases mem_interior_or_end hzR with hz' | hz'
    · exact hz'
    · exact absurd (show z ∈ endSet Q from ⟨R, hR, hz'⟩) hz.2
  · obtain ⟨R, hR, hzR⟩ := Set.mem_iUnion₂.1 hz
    exact ⟨h.seg_subset hR (openSegment_subset_segment ℝ _ _ hzR),
      fun ⟨S, hS, hz'⟩ => h.ends S hS R hR z hz' hzR⟩

/-- **Near an interior point the curve is that piece alone.** The other pieces are finitely many
closed sets missing the point: interior points are not shared, and an end of another piece
cannot be interior to this one. -/
theorem exists_ball_subset_seg (hR : R ∈ Q) (hx : x ∈ R.interior) :
    ∃ r > 0, ball x r ∩ C ⊆ R.seg := by
  have hmiss : ∀ S ∈ Q, S ≠ R → x ∉ S.seg := by
    intro S hS hSR hxS
    rcases mem_interior_or_end hxS with hz | hz
    · exact h.interiors S hS R hR hSR x hz hx
    · exact h.ends S hS R hR x hz hx
  obtain ⟨r, hr, hball⟩ := exists_pos_forall_of_finite
    (S := {S : Piece | S ∈ Q ∧ S ≠ R}) (Q.finite_toSet.subset fun _ hS => hS.1)
    (P := fun S ε => ∀ y ∈ ball x ε, y ∉ S.seg)
    (fun _ _ _ _ hδε hP y hy => hP y (ball_subset_ball hδε hy))
    (fun S hS => by
      obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1
        (isCompact_segment S.1 S.2).isClosed.isOpen_compl x (hmiss S hS.1 hS.2)
      exact ⟨ρ, hρ, fun y hy => hsub hy⟩)
  refine ⟨r, hr, ?_⟩
  rintro z ⟨hzb, hzC⟩
  obtain ⟨S, hS, hzS⟩ := ClosedPolygon.exists_of_mem_cover (h.mem_cover_of_mem hzC)
  by_cases hSR : S = R
  · exact hSR ▸ hzS
  · exact absurd hzS (hball S ⟨hS, hSR⟩ z hzb)

theorem interior_subset_nearPiece (hR : R ∈ Q) : R.interior ⊆ nearPiece C R := by
  intro y hy
  obtain ⟨r, hr, hsub⟩ := h.exists_ball_subset_seg hR hy
  exact ⟨y, hy, r, hr, mem_ball_self hr, hsub⟩

omit h in
theorem nearPiece_inter_diff (hR : R ∈ Q) : nearPiece C R ∩ (C \ endSet Q) ⊆ R.interior := by
  rintro z ⟨⟨y, hy, r, hr, hzb, hsub⟩, hzC, hzV⟩
  rcases mem_interior_or_end (hsub ⟨hzb, hzC⟩) with hz | hz
  · exact hz
  · exact absurd (show z ∈ endSet Q from ⟨R, hR, hz⟩) hzV

/-- **A connected piece of the curve away from the ends lies inside a single piece.** The
`nearPiece` sets are honest open sets of the plane that trace out the pieces on the curve, so
`IsPreconnected` can be applied to them directly. -/
theorem preconnected_subset_interior {A : Set Plane} (hA : IsPreconnected A) (hA0 : A.Nonempty)
    (hAsub : A ⊆ C \ endSet Q) : ∃ R ∈ Q, A ⊆ R.interior := by
  obtain ⟨x₀, hx₀⟩ := hA0
  have hAint : A ⊆ ⋃ R ∈ Q, R.interior := by rw [← h.diff_endSet_eq]; exact hAsub
  obtain ⟨R, hR, hx₀R⟩ := Set.mem_iUnion₂.1 (hAint hx₀)
  refine ⟨R, hR, ?_⟩
  set W : Set Plane := ⋃ S ∈ {S : Piece | S ∈ Q ∧ S ≠ R}, nearPiece C S with hW
  have hWopen : IsOpen W := isOpen_biUnion fun _ _ => isOpen_nearPiece
  have hcover : A ⊆ nearPiece C R ∪ W := by
    intro z hz
    obtain ⟨S, hS, hzS⟩ := Set.mem_iUnion₂.1 (hAint hz)
    by_cases hSR : S = R
    · exact Or.inl (h.interior_subset_nearPiece hR (hSR ▸ hzS))
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨S, ⟨hS, hSR⟩, h.interior_subset_nearPiece hS hzS⟩)
  have hempty : ¬ (A ∩ (nearPiece C R ∩ W)).Nonempty := by
    rintro ⟨z, hzA, hzR, hzW⟩
    obtain ⟨S, hS, hzS⟩ := Set.mem_iUnion₂.1 hzW
    exact h.interiors R hR S hS.1 (Ne.symm hS.2) z (nearPiece_inter_diff hR ⟨hzR, hAsub hzA⟩)
      (nearPiece_inter_diff hS.1 ⟨hzS, hAsub hzA⟩)
  have hnotW : ¬ (A ∩ W).Nonempty := fun hv =>
    hempty (hA _ _ isOpen_nearPiece hWopen hcover ⟨x₀, hx₀, h.interior_subset_nearPiece hR hx₀R⟩ hv)
  intro z hz
  refine nearPiece_inter_diff hR ⟨?_, hAsub hz⟩
  exact (hcover hz).resolve_right fun hzW => hnotW ⟨z, hz, hzW⟩

end IsClean

/-! ## The gaps between the parameters

The loop's parameters at which it visits an end of a piece form a finite subset of `[0, 1)`
containing `0`. Listed in increasing order they cut `[0, 1)` into gaps, one per piece; the last
gap runs to `1`, where the loop closes. This section is pure order theory on `ℝ`. -/

/-- A closed interval is its interior together with its two ends. -/
theorem Icc_eq_Ioo_union_ends {a b : ℝ} (hab : a ≤ b) : Icc a b = Ioo a b ∪ {a, b} := by
  ext x
  simp only [mem_Icc, mem_union, mem_Ioo, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rcases eq_or_lt_of_le h1 with rfl | h1'
    · exact Or.inr (Or.inl rfl)
    · rcases eq_or_lt_of_le h2 with rfl | h2'
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨h1', h2'⟩
  · rintro (⟨h1, h2⟩ | rfl | rfl)
    · exact ⟨h1.le, h2.le⟩
    · exact ⟨le_refl _, hab⟩
    · exact ⟨hab, le_refl _⟩

/-! ## From a clean presentation to a cyclic vertex list

The loop reaches an end of a piece at finitely many parameters. Between two consecutive ones it
runs through one whole piece interior — the gap image is connected and misses the ends, so it
lies in one interior; and the interior, being connected and covered by the closed gap images,
lies in that one gap. So the ends, listed in the order the loop reaches them, are the cyclic
vertex list of a `PrePolygon` whose edges are the pieces. -/

/-! ## The realization theorem -/

/-! ## Corners

A realization cannot put a vertex wherever it likes: `corner` forbids a vertex at which the
curve runs straight through. The points that *must* be vertices are exactly the ones at which
it does not, and this is what a consumer needing a named point to be a vertex has to check. -/

/-! ## The two arcs of a splitting

`ClosedPolygon.arc a k` and `ClosedPolygon.arc (a + k) (m + 3 - k)` are what a consumer tracking
a decomposition of the curve has to be handed. This section says what they are: two arcs between
the two cut vertices, covering the curve and meeting exactly there. -/

namespace ClosedPolygon

variable {m : ℕ}

/-- The same closed polygon, read from vertex `a` onwards. -/
def rotate (P : ClosedPolygon m) (a : ZMod (m + 3)) : ClosedPolygon m where
  vertex j := P.vertex (a + j)
  vertex_inj i j h := add_left_cancel (P.vertex_inj h)
  edges_meet i j hij := by
    have hi : a + (i + 1) = a + i + 1 := by ring
    have hj : a + (j + 1) = a + j + 1 := by ring
    simp only [hi, hj]
    exact P.edges_meet _ _ fun h => hij (add_left_cancel h)
  corner i := by
    have h1 : a + (i - 1) = a + i - 1 := by ring
    have h2 : a + (i + 1) = a + i + 1 := by ring
    simp only [h1, h2]
    exact P.corner (a + i)

@[simp] theorem rotate_vertex (P : ClosedPolygon m) (a j : ZMod (m + 3)) :
    (P.rotate a).vertex j = P.vertex (a + j) := rfl

end ClosedPolygon

/-! ## The two-arc decomposition is unique

Two points cut a Jordan curve into two arcs, and *only* into those two: the interior of any arc
of the curve between them is connected and misses both, so it lies on one side of any other such
splitting. Without this a realization could name two arcs and still not be known to name the two
arcs a consumer started from. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.FaceCyclesProof
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Face cycles: the proof

`lem:face-cycles` — *every face of a finite 2-connected polygonal plane graph has a cycle as its
boundary and is one of the two complementary regions of that cycle*. `Schoenflies/FaceCycles.lean`
built the base cycle, its 2-connectivity, and the topology of adding an ear; this module runs
the induction of the blueprint's proof on top of them.

## READ THIS FIRST: what is assumed

`Graph.face_cycles` **carries a hypothesis, `Schoenflies.CrosscutSplitsRegion`, which nothing
proves.** It is the exhaustion clause of `thm:polygonal-crosscut` — "the crosscut replaces `F`
by exactly two regions" — stated for a crosscut whose two endpoints are *arbitrary points of
the curve*. Everything else in the blueprint's proof is discharged here without hypotheses, and
each of those pieces is a standalone theorem below.

`main`'s Theorem 2.8 does **not** discharge it, and the obstruction is not a missing bridge.
`Schoenflies.IsPolygonalCrosscut` states its two splitting hypotheses against
`ClosedPolygon.arcPieces C a k`, which cuts the polygon's edge list at two of *its vertices*;
and `Schoenflies.ClosedPolygon.isCornerAt_vertex` says every vertex of every realization of a
curve is a corner of it. In the induction below the two cut points are the ear's endpoints —
graph vertices at which the two cycle edges may leave along opposite rays, so that the boundary
curve runs *straight* through the cut point. Such a point is a vertex of no `ClosedPolygon`
with that carrier, and `Schoenflies.exists_closedPolygon_split` (whose `IsCornerAt` hypotheses
are therefore not an artefact) cannot be applied.

There is a **second, independent** reason, and it bites even when both cut points *are*
corners. `IsPolygonalCrosscut.edges₁` asks for `SameEdges J₁.pieces (C.arcPieces a k ++ K)`,
a multiset equality of unoriented segments. The list on the right has two pieces ending at the
cut point `q` — the arc's last and the crosscut's first. If those two are collinear, the curve
`J₁ = A₁ ∪ P` runs straight through `q`, so `q` is a vertex of no `ClosedPolygon` with that
carrier and *no* piece of `J₁.pieces` ends there: the multiset equality is unsatisfiable. Since
the crosscut may perfectly well leave a cut vertex along the ray opposite the arriving arc edge,
`edges₁` and `edges₂` are not dischargeable as stated. Deleting the redundant vertex —
`Schoenflies.PrePolygon.deleteLast` — repairs the *realization* and breaks `SameEdges` in the
same move.

Closing the gap therefore means restating Theorem 2.8 with the edge lists related by *parity*
rather than by `SameEdges`, for a split made at arbitrary points of the curve. The tools exist:
`Schoenflies.parity_split` is already stated for arbitrary lists, and
`Schoenflies.parity_subdivide` (Lemma 2.1) absorbs the difference between a merged piece and its
two halves. What is missing is the parity theory of presentations carrying redundant vertices —
`Schoenflies.parity_eq_one_iff` for `Schoenflies.PrePolygon` rather than only for
`ClosedPolygon`, obtained by carrying the parity along the normalization induction of
`Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`. That is a separate module.

## Main results

* **The realisation of a cycle is a separating curve** (`Graph.IsDrawing.cycle_isSeparating`),
  which is what the base case needed and what `main` could not say. It composes
  `Graph.IsDrawing.cycle_isJordanCurve` with `Schoenflies.exists_closedPolygon` and
  `Schoenflies.ClosedPolygon.isSeparating_carrier`. The polygonality half needed a bridge that
  `main` did not have: `Schoenflies.IsPolygonal` is the carrier of *one* vertex list, so a union
  of edge arcs is polygonal only once each arc is known to be a polyline running from one of its
  ends to the other (`Schoenflies.IsArcBetween.exists_poly_eq`, which rests on the arc
  uniqueness `Schoenflies.IsArcBetween.eq_of_subset`).
* **The base case** (`Graph.IsDrawing.hasFaceCycles_cycleGraph`): the cycle subgraph occupies
  exactly the cycle's realisation, so its faces are the two regions of that curve.
* **Cutting a cycle at two of its vertices** (`Graph.IsCycleThrough.split_at`) and **splicing an
  ear onto an arc** (`Graph.exists_spliced_cycle`) — the combinatorics of "both bounded by
  cycles" — together with the geometric reading of the split
  (`Graph.IsDrawing.arcs_of_split`).
* **The step's topology**: the enlarged exterior is the old one minus the ear
  (`Graph.IsDrawing.pointSet_pathGraphOf`), a face the ear misses survives with its cycle
  (`Graph.IsFaceCycle.mono`), and the face the ear cuts is cut only inside itself
  (`Schoenflies.connectedComponentIn_diff`).

## For the integrator

`Graph.IsPath.append`, `Graph.IsPath.split_meet`, `Graph.IsWalk.walkVertices_eq_covered`,
`Graph.IsWalk.walkVertices_reverse_eq`, `Graph.coveredVertices_congr_of_le`,
`Graph.walkVertices_congr_of_le` and `Graph.edgesCover_append` / `…_perm` / `…_reverse` are
general and belong in `Schoenflies/Graph/Walk.lean` and `Schoenflies/Graph/CycleJordan.lean`.
`Schoenflies.IsArcBetween.eq_of_subset` belongs in `Schoenflies/Subarc.lean` and
`Schoenflies.poly_append_join` in `Schoenflies/PolyPath.lean`.

## Blueprint

* `Schoenflies.IsArcBetween.eq_of_subset`, `Schoenflies.IsArcBetween.exists_poly_eq`,
  `Graph.IsDrawing.exists_poly_eq_edgesCover`, `Graph.IsDrawing.isPolygonal_edgesCover` — §1,
  the polygonality of what a walk draws.
* `Graph.IsDrawing.cycle_isSeparating` — `thm:polygonal-jordan` for the realisation of a cycle:
  "This is true for the initial cycle by Theorem `thm:polygonal-jordan`."
* `Graph.IsFaceCycle`, `Graph.HasFaceCycles` — the conclusion of `lem:face-cycles`, at one face
  and at all of them.
* `Graph.IsDrawing.hasFaceCycles_cycleGraph` — the base case.
* `Graph.IsCycleThrough.split_at`, `Graph.IsDrawing.arcs_of_split`,
  `Graph.exists_spliced_cycle` — "Theorem `thm:polygonal-crosscut` replaces `F` by exactly two
  regions, both bounded by cycles", combinatorially.
* `Schoenflies.CrosscutSplitsRegion` — **the assumed** exhaustion clause of
  `thm:polygonal-crosscut` at arbitrary cut points.
* `Graph.IsDrawing.hasFaceCycles_union` — one ear.
* `Graph.face_cycles` — `lem:face-cycles`, modulo `Schoenflies.CrosscutSplitsRegion`.
-/

open Metric Set unitInterval
open scoped Graph

namespace Graph

/-! ## Cutting and joining paths

Two general facts about paths that `Schoenflies/Graph/Walk.lean` does not have, and that the
splitting of a cycle at two of its vertices runs on. **The integrator should hoist both into
`Schoenflies/Graph/Walk.lean`**, next to `Graph.IsPath.split`, which is the weaker form of the
second. -/

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z a b : Plane} {W D : List β}

/-! ## What a walk of a polygonal plane graph draws -/

/-! ## The realisation of a cycle is a separating curve

This is the composition the base case of `lem:face-cycles` needs, and the one thing that was
missing from it: `Graph.IsDrawing.cycle_isJordanCurve` says the realisation is a Jordan curve
and `Graph.IsDrawing.isPolygonal_edgesCover` says it is polygonal, and
`Schoenflies.exists_closedPolygon` — the realization theorem — turns that pair into a
`Schoenflies.ClosedPolygon`, whose carrier `Schoenflies.ClosedPolygon.isSeparating_carrier`
knows to separate the plane. Nothing here inspects the polygon; it is used and discarded. -/

/-! ## What a subgraph spanned by a walk occupies -/

/-! ## The conclusion of `lem:face-cycles`, at one face -/

/-- **A face bounded by a named cycle.** The face `face G drawing z` is one of the two regions
of the complement of the realisation of the cycle `e :: D` — which is the blueprint's "every
face … has a cycle as its boundary *and is one of the two complementary regions of that
cycle*". The cycle is a parameter rather than an existential so that a consumer that has
produced one keeps it. -/
structure IsFaceCycle (G : Graph Plane β) (drawing : β → ℝ → Plane) (z : Plane)
    (e : β) (u v : Plane) (D : List β) : Prop where
  /-- The named data really is a cycle of the graph. -/
  isCycle : G.IsCycleThrough e u v D
  /-- Its realisation separates the plane into exactly two regions. -/
  isSeparating : IsSeparating (edgesCover drawing (e :: D))
  /-- The face is one of those two. -/
  isRegionOf : IsRegionOf (edgesCover drawing (e :: D)) (face G drawing z)

/-- **`lem:face-cycles`, as a property of a plane graph**: every face has a cycle as its
boundary and is one of the two complementary regions of that cycle. -/
def HasFaceCycles (G : Graph Plane β) (drawing : β → ℝ → Plane) : Prop :=
  ∀ z ∈ exterior G drawing, ∃ (e : β) (u v : Plane) (D : List β), IsFaceCycle G drawing z e u v D

/-! ## The base case: the faces of a single cycle

"This is true for the initial cycle by Theorem `thm:polygonal-jordan`." The cycle subgraph
occupies exactly the cycle's realisation, so its faces are literally the components of the
complement of that curve, and the curve is separating. -/

/-! ## The two arcs a cycle is cut into, as sets

The combinatorial split of `Graph.IsCycleThrough.split_at` becomes the geometric one: the two
arcs of the Jordan curve between the two cut vertices. The drawing condition is used once, to
turn "the two edge lists are disjoint" into "the two arcs meet only at vertices". -/

end Graph
end

section
-- module Solutions.Q146_CD.PrePolygonSep
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Separation and crossing parity before normalization

`Schoenflies.ClosedPolygon` carries a `corner` field — no three consecutive vertices collinear —
and `Schoenflies.ClosedPolygon.isCornerAt_vertex` shows that field is not slack: a point at which
the curve runs straight is a vertex of *no* `ClosedPolygon` presentation of it. So a consumer that
must present a curve with vertices at prescribed points cannot use `ClosedPolygon` at all, and the
plane-graph arguments are exactly such consumers: the branch points of a drawing land wherever the
drawing puts them.

`Schoenflies.PrePolygon` is the presentation without that field, and vertices may be put anywhere.
This module gives it everything the crosscut chain asks of a simple closed polygon: an edge list
for the crossing count, the curve statements, the polygonal Jordan curve theorem, and the two
parity values.

## Everything transports across normalization, except the parity

`Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon` deletes redundant vertices and returns
a genuine `ClosedPolygon` **with the same carrier**. Any property of the carrier *as a set* is
therefore free: `isJordanCurve_carrier`, `isPolygonal_carrier` and `isSeparating_carrier` below are
each three lines, and none of them needs a word about vertices.

The crossing parity is not a property of the carrier. It is computed from a *list of edges*, and
normalization changes that list: it merges collinear edges, so `P.pieces` is a subdivision of the
normalized polygon's. Lemma 2.1 (`Schoenflies.parity_subdivide`) says subdivision does not change
the parity, which is why one *expects* the parity to transport — but the normalization theorem is
an existence statement and keeps no record of which points were deleted, so there is no
subdivision in hand to feed it. See the note at the end of this docstring.

The parity is therefore re-derived here, and the derivation turns out not to need the collar at
all. Once the curve is known to separate, the two values are forced:

* far along the ray direction the count is zero, and the half-plane where it is zero is convex and
  unbounded, hence lies in the unbounded region — so `π_C = 0` on the outside;
* across an interior point of any one edge the count jumps by one (Lemma 2.2), and the two test
  points lie off the curve, so they lie in different regions — so the other region carries `1`.

Both steps are stated for an arbitrary closed chain whose cover separates the plane
(`Schoenflies.parity_eq_zero_of_mem_outside_cover`, `…parity_eq_one_of_mem_inside_cover`); the
`PrePolygon` statements are instances. **The `ClosedPolygon` versions in
`Schoenflies/PolygonalJordan.lean` are instances too** — `ClosedPolygon.parity_eq_one_of_mem_inside`
currently goes through `StripData`, and does not have to.

## Blueprint

* `Schoenflies.PrePolygon.pieces`, `…cover_pieces`, `…isClosedChain_pieces`, `…pieces_nondeg` —
  the edge list the crossing count of §2 is defined on, for a vertex list that has not been
  normalized. Same list as `ClosedPolygon.pieces`; `PrePolygon.pieces_toPre` is `rfl`.
* `Schoenflies.PrePolygon.isJordanCurve_carrier`, `…isPolygonal_carrier` — §1, "a simple closed
  polygonal curve"; jointly the hypothesis of Theorem 2.3.
* `Schoenflies.PrePolygon.isSeparating_carrier` — **Theorem 2.3** in the form Definition 2.4 asks
  for, for a polygon presented with redundant vertices.
* `Schoenflies.PrePolygon.parity_flip_carrier` — Lemma 2.2, second half.
* `Schoenflies.parity_eq_zero_of_mem_outside_cover`,
  `Schoenflies.parity_eq_one_of_mem_inside_cover` — the last sentence of Theorem 2.3, for an
  arbitrary closed chain whose cover separates.
* `Schoenflies.PrePolygon.parity_eq_zero_of_mem_outside`, `…parity_eq_one_of_mem_inside`,
  `…parity_eq_zero_iff`, `…parity_eq_one_iff` — the same, read off a `PrePolygon`.

## Two notes for the integrator

**`PrePolygon.pieces` duplicates `ClosedPolygon.pieces`.** The two definitions are literally the
same expression and `PrePolygon.pieces_toPre` proves them equal by `rfl`. The right arrangement is
to define `ClosedPolygon.pieces P := P.toPre.pieces` and to keep only the `PrePolygon` proofs — the
proofs of `cover_pieces`, `isClosedChain_pieces`, `pieces_nondeg`, `pieces_nodup`,
`notMem_edge_of_mem_openSegment` and `parity_flip_carrier` in `Schoenflies/PolygonBridge.lean` use
`vertex_inj` and `edges_meet` and nothing else, so they are the proofs below with `ClosedPolygon`
written for `PrePolygon`. That refactor cannot happen inside this module: `PrePolygon` is declared
in `Schoenflies/Realization.lean`, which is *downstream* of `PolygonBridge`. It needs `PrePolygon`
moved up beside `ClosedPolygon` in `Schoenflies/Strip.lean`.

**Merging collinear edges is a subdivision, but not one this development can point at.** Deleting
a redundant vertex `v` replaces the two edges at `v` by their union, which is exactly undoing
`Schoenflies.splitAt v` on the merged edge; iterating, `P.pieces` is `subdivide P'.pieces vs` for
the list `vs` of deleted vertices — *up to the order of the list*, which `rotate` disturbs. So two
things are missing before `parity_subdivide` could be used here: `Schoenflies.parity` invariance
under `List.Perm` (immediate, `parity` is a sum over the list), and a strengthening of
`exists_closedPolygon_of_prePolygon` to
`∃ m' (P' : ClosedPolygon m') (vs : List Plane), P'.carrier = P.carrier ∧
  P.pieces ~ subdivide P'.pieces vs`, carried through the induction. The direct argument below is
shorter than either.
-/

open Bornology Metric Set

namespace Schoenflies

open Plane

/-! ## Small arithmetic helpers

Copies of two `private` facts of `Schoenflies/PolygonalJordan.lean`; they are `private` there and
so are these. -/

/-- In `ZMod 2` nothing is its own successor: this is what "the parities differ" comes down to. -/
theorem ne_add_one_zmod_two (x : ZMod 2) : x ≠ x + 1 := by revert x; decide

/-- The only two values, named. -/
theorem eq_one_of_ne_zero_zmod_two {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert h; revert x; decide

/-! ## The two parity values from separation alone

The blueprint reads the two values off a point far along the ray direction and off a point either
side of an edge. Neither step knows anything about vertices, so both are stated here for an
arbitrary closed chain whose cover separates the plane. -/

section GeneralParity

variable {L : List Piece} {u : Plane}

/-- The forward coordinate is linear. This is all that is needed to see that a half-plane is
convex. -/
theorem isLinearMap_fwd (u : Plane) : IsLinearMap ℝ (fwd u) where
  map_add x y := by simp only [fwd_eq, Plane.add_apply] <;> ring
  map_smul c x := by simp only [fwd_eq, Plane.smul_apply, smul_eq_mul] <;> ring

/-- The half-plane of points more than `R` along the ray direction. Beyond a bound on the polygon
it is the region in which the crossing count is visibly zero, and it is unbounded, which is what
places it in the unbounded region. -/
def farSide (u : Plane) (R : ℝ) : Set Plane := {z | R < fwd u z}

theorem convex_farSide (u : Plane) (R : ℝ) : Convex ℝ (farSide u R) :=
  convex_halfSpace_gt (isLinearMap_fwd u) R

/-- The forward coordinate of a multiple of the direction is the multiple. -/
theorem fwd_smul_self (hu : Plane.IsDirection u) (s : ℝ) : fwd u (s • u) = s := by
  have h : fwd u (s • u) = s * fwd u u := by simp only [fwd_eq, Plane.smul_apply] <;> ring
  rw [h, fwd_self hu, mul_one]

/-- The half-plane is unbounded: it contains points of every size along the direction. -/
theorem not_isBounded_farSide (hu : Plane.IsDirection u) (R : ℝ) :
    ¬ IsBounded (farSide u R) := by
  intro hb
  obtain ⟨R', hR'⟩ := hb.subset_closedBall (0 : Plane)
  set t : ℝ := max (max R R') 0 + 1 with htdef
  have h0 : 0 ≤ max (max R R') 0 := le_max_right _ _
  have hpos : 0 < t := by rw [htdef]; linarith
  have hR1 : R < t := by
    have := le_trans (le_max_left R R') (le_max_left (max R R') 0)
    rw [htdef]; linarith
  have hR2 : R' < t := by
    have := le_trans (le_max_right R R') (le_max_left (max R R') 0)
    rw [htdef]; linarith
  have hmem : t • u ∈ farSide u R := by
    change R < fwd u (t • u)
    rw [fwd_smul_self hu]; exact hR1
  have hnorm : ‖t • u‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_of_pos hpos]
  have := mem_closedBall_zero_iff.1 (hR' hmem)
  rw [hnorm] at this
  linarith

/-- **`π_C = 0` on the unbounded region** (Theorem 2.3, last sentence), for any closed chain whose
cover separates the plane.

The blueprint's argument: a point far enough along the ray direction is crossed by no edge, and the
whole half-plane of such points is convex — hence connected — and unbounded, so it lies in the
unbounded region. Parity is constant there (Lemma 2.2), and the value is the one read off the far
point. -/
theorem parity_eq_zero_of_mem_outside_cover (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ L, hgt u Q.1 ≠ hgt u Q.2) (hC : IsClosedChain L)
    (hsep : IsSeparating (cover L)) {x : Plane} (hx : x ∈ outside (cover L)) :
    parity u L x = 0 := by
  obtain ⟨R, hR⟩ := (isCompact_cover L).isBounded.subset_closedBall (0 : Plane)
  have hcov : ∀ z ∈ cover L, fwd u z ≤ R := fun z hz =>
    le_trans (le_trans (le_abs_self _) (abs_fwd_le_norm hu z)) (mem_closedBall_zero_iff.1 (hR hz))
  have hdisj : farSide u R ⊆ (cover L)ᶜ := fun z hz hzc => absurd (hcov z hzc) (not_le.2 hz)
  have hqf : fwd u ((R + 1) • u) = R + 1 := fwd_smul_self hu (R + 1)
  have hqmem : (R + 1) • u ∈ farSide u R := by
    change R < fwd u ((R + 1) • u)
    rw [hqf]; linarith
  -- the far point is in the unbounded region, because the whole half-plane is
  have hqout : (R + 1) • u ∈ outside (cover L) := by
    refine ⟨hdisj hqmem, fun hb => not_isBounded_farSide hu R (hb.subset ?_)⟩
    exact (convex_farSide u R).isPreconnected.subset_connectedComponentIn hqmem hdisj
  have hq0 : parity u L ((R + 1) • u) = 0 :=
    parity_eq_zero_of_lt hL fun z hz => lt_of_le_of_lt (hcov z hz) (by rw [hqf]; linarith)
  rw [← hq0]
  exact parity_eq_of_isPreconnected hu hL hC hsep.isConnected_outside.isPreconnected
    (fun z hz => hz.1) hx hqout

/-- **`π_C = 1` on the bounded region** (Theorem 2.3, last sentence), for any closed chain whose
cover separates the plane and which has *some* two points of the complement with different
parities.

Those two points cannot be in the same region, since parity is constant on a region; so one of them
is inside and the other outside. The outside carries `0`, hence the inside does not.

For a polygon the two points are supplied by Lemma 2.2: just before and just after an interior
point of any single edge. -/
theorem parity_eq_one_of_mem_inside_cover (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ L, hgt u Q.1 ≠ hgt u Q.2) (hC : IsClosedChain L)
    (hsep : IsSeparating (cover L)) {a b : Plane} (ha : a ∉ cover L) (hb : b ∉ cover L)
    (hab : parity u L a ≠ parity u L b) {x : Plane} (hx : x ∈ inside (cover L)) :
    parity u L x = 1 := by
  have hzero : ∀ y ∈ outside (cover L), parity u L y = 0 := fun y hy =>
    parity_eq_zero_of_mem_outside_cover hu hL hC hsep hy
  have hconst : ∀ y ∈ inside (cover L), parity u L y = parity u L x := fun y hy =>
    parity_eq_of_isPreconnected hu hL hC hsep.isConnected_inside.isPreconnected
      (fun z hz => hz.1) hy hx
  have hma : a ∈ inside (cover L) ∪ outside (cover L) := by rw [inside_union_outside]; exact ha
  have hmb : b ∈ inside (cover L) ∪ outside (cover L) := by rw [inside_union_outside]; exact hb
  refine eq_one_of_ne_zero_zmod_two ?_
  rcases hma with h | h <;> rcases hmb with h' | h'
  · exact absurd ((hconst a h).trans (hconst b h').symm) hab
  · rw [hzero b h'] at hab
    rw [← hconst a h]
    exact hab
  · rw [hzero a h] at hab
    rw [← hconst b h']
    exact Ne.symm hab
  · exact absurd ((hzero a h).trans (hzero b h').symm) hab

end GeneralParity

namespace PrePolygon

variable {m : ℕ}

/-! ## The edge list

Verbatim `Schoenflies.ClosedPolygon.pieces` with the structure changed; `pieces_toPre` records
that the two are the same list. -/

/-- The `m + 3` edges of the polygon, as a list of pieces in cyclic order. This is the form the
crossing count of §2 is defined on. -/
def pieces (P : PrePolygon m) : List Piece :=
  (List.range (m + 3)).map fun j : ℕ =>
    (P.vertex (j : ZMod (m + 3)), P.vertex ((j : ZMod (m + 3)) + 1))

/-- Forgetting the `corner` field does not change the edge list. -/
@[simp] theorem pieces_toPre (P : ClosedPolygon m) : P.toPre.pieces = P.pieces := rfl

/-- Every edge of the polygon is on the list. -/
theorem mem_pieces (P : PrePolygon m) (i : ZMod (m + 3)) :
    (P.vertex i, P.vertex (i + 1)) ∈ P.pieces := by
  refine List.mem_map.2 ⟨i.val, List.mem_range.2 (ZMod.val_lt i), ?_⟩
  rw [ZMod.natCast_rightInverse i]

/-- Every piece on the list is an edge of the polygon. -/
theorem exists_of_mem_pieces {P : PrePolygon m} {Q : Piece} (hQ : Q ∈ P.pieces) :
    ∃ i : ZMod (m + 3), Q = (P.vertex i, P.vertex (i + 1)) := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hQ
  exact ⟨(j : ZMod (m + 3)), rfl⟩

/-- No edge is degenerate: consecutive vertices are distinct. Redundant vertices are allowed, but
repeated ones are not. -/
theorem pieces_nondeg (P : PrePolygon m) : ∀ Q ∈ P.pieces, Q.Nondeg := by
  intro Q hQ
  obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
  exact vertex_ne_succ i

/-- **The edge list is a closed chain.** Each vertex ends one edge and starts the next, so it is
counted twice; the cycle closes because `m + 3` is `0` in `ZMod (m + 3)`. -/
theorem isClosedChain_pieces (P : PrePolygon m) : IsClosedChain P.pieces := by
  intro f
  have hmap : (P.pieces.map fun Q => f Q.1 + f Q.2)
      = (List.range (m + 3)).map fun j : ℕ =>
        f (P.vertex (j : ZMod (m + 3))) + f (P.vertex ((j + 1 : ℕ) : ZMod (m + 3))) := by
    rw [pieces, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, ClosedPolygon.natCast_succ]
  rw [hmap]
  have key := sum_range_boundary (fun k : ℕ => f (P.vertex (k : ZMod (m + 3)))) (m + 3)
  rw [key, Nat.cast_zero, ZMod.natCast_self]
  exact add_self_zmod_two _

/-- **The edge list carries the polygon.** This is the equation that turns every parity statement,
which is about `cover`, into a statement about the carrier. -/
theorem cover_pieces (P : PrePolygon m) : cover P.pieces = P.carrier := by
  apply Set.Subset.antisymm
  · rw [cover]
    refine Set.iUnion₂_subset fun Q hQ => ?_
    obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
    exact Set.subset_iUnion (fun i => P.edge i) i
  · refine Set.iUnion_subset fun i => ?_
    exact fun z hz => mem_cover (P.mem_pieces i) hz

/-- The edge list has no repeated entry: distinct indices name distinct initial vertices. -/
theorem pieces_nodup (P : PrePolygon m) : P.pieces.Nodup := by
  rw [pieces]
  refine List.Nodup.map_on (fun j hj k hk heq => ?_) List.nodup_range
  exact ClosedPolygon.natCast_inj (List.mem_range.1 hj) (List.mem_range.1 hk)
    (P.vertex_inj (congrArg Prod.fst heq))

/-! ## The curve statements, and separation

All three are properties of the carrier as a set, and normalization keeps the carrier, so all three
come across from the `ClosedPolygon` versions with nothing to check. -/

/-- **The polygonal Jordan curve theorem** (Theorem 2.3) for a polygon presented with redundant
vertices, in the form Definition 2.4 asks for.

This is the statement the crosscut machinery of `Schoenflies/CrosscutCells.lean` onwards consumes,
and `IsSeparating` speaks only of the carrier, so normalizing and quoting
`ClosedPolygon.isSeparating_carrier` is the whole proof. -/
theorem isSeparating_carrier (P : PrePolygon m) : IsSeparating P.carrier := by
  obtain ⟨m', P', hP'⟩ := exists_closedPolygon_of_prePolygon m P
  rw [← hP']
  exact P'.isSeparating_carrier

/-- Exactly two regions: the component of any point off the polygon is one of the two named
ones. -/
theorem connectedComponentIn_eq_inside_or_outside (P : PrePolygon m) {x : Plane}
    (hx : x ∉ P.carrier) :
    connectedComponentIn P.carrierᶜ x = inside P.carrier ∨
      connectedComponentIn P.carrierᶜ x = outside P.carrier := by
  have h : x ∈ inside P.carrier ∪ outside P.carrier := by rw [inside_union_outside]; exact hx
  rcases h with h | h
  · exact Or.inl (P.isSeparating_carrier.connectedComponentIn_eq_inside h)
  · exact Or.inr (P.isSeparating_carrier.connectedComponentIn_eq_outside h)

/-! ## The crossing parity

The list-level statements of `Schoenflies/Parity.lean`, read off a `PrePolygon`. -/

/-- **Crossing parity** (Lemma 2.2): `π_C` is constant on the component of the complement of the
carrier containing a given point. -/
theorem parity_eq_of_mem_connectedComponentIn_carrier (P : PrePolygon m) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ P.carrier) (hy : y ∈ connectedComponentIn P.carrierᶜ x) :
    parity u P.pieces y = parity u P.pieces x := by
  rw [← P.cover_pieces] at hx hy
  exact parity_eq_of_mem_connectedComponentIn hu hL P.isClosedChain_pieces hx hy

/-- An interior point of one edge lies on no other edge: `edges_meet` puts any other edge's meeting
point at an end of this one, and an interior point is neither end. -/
theorem notMem_edge_of_mem_openSegment {P : PrePolygon m} {i j : ZMod (m + 3)} (hij : j ≠ i)
    {p : Plane} (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) : p ∉ P.edge j := by
  intro hpj
  have hmem := P.edges_meet i j (Ne.symm hij)
    (Set.mem_inter (openSegment_subset_segment ℝ _ _ hp) hpj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl
  · exact vertex_ne_succ i (left_mem_openSegment_iff.1 hp)
  · exact vertex_ne_succ i (right_mem_openSegment_iff.1 hp)

/-- **Opposite sides of an edge** (Lemma 2.2, second half). Just before and just after an interior
point of an edge, in the ray direction, the base point is off the carrier and the crossing parity
differs by one.

The edge being crossed is split out of the list by `List.append_of_mem`; that the two remaining
fragments miss the crossing point is `edges_meet`, through
`PrePolygon.notMem_edge_of_mem_openSegment`. -/
theorem parity_flip_carrier (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) (i : ZMod (m + 3)) {p : Plane}
    (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      p - t • u ∉ P.carrier ∧ p + t • u ∉ P.carrier ∧
        parity u P.pieces (p - t • u) = parity u P.pieces (p + t • u) + 1 := by
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem (P.mem_pieces i)
  -- the edge being crossed occurs only once, so it is on neither fragment
  have hnodup := P.pieces_nodup
  rw [hsplit, List.nodup_append] at hnodup
  obtain ⟨-, hnd2, hdisj⟩ := hnodup
  have hQ₁ : (P.vertex i, P.vertex (i + 1)) ∉ L₁ := fun hmem => hdisj _ hmem _ (by simp) rfl
  have hQ₂ : (P.vertex i, P.vertex (i + 1)) ∉ L₂ := (List.nodup_cons.1 hnd2).1
  have hmiss : ∀ R ∈ L₁ ++ L₂, p ∉ Piece.seg R := by
    intro R hR
    have hRne : R ≠ (P.vertex i, P.vertex (i + 1)) := by
      rcases List.mem_append.1 hR with h | h
      · exact fun heq => hQ₁ (heq ▸ h)
      · exact fun heq => hQ₂ (heq ▸ h)
    have hRmem : R ∈ P.pieces := by
      rw [hsplit]
      rcases List.mem_append.1 hR with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    obtain ⟨j, rfl⟩ := exists_of_mem_pieces hRmem
    exact notMem_edge_of_mem_openSegment (fun heq => hRne (by rw [heq])) hp
  -- `exists_of_mem_cover` is the destructor matching `Schoenflies.mem_cover`; it lives, by
  -- accident, inside the `ClosedPolygon` namespace in `Schoenflies/PolygonBridge.lean`.
  have h1 : p ∉ cover L₁ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := ClosedPolygon.exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_left _ hR) hpR
  have h2 : p ∉ cover L₂ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := ClosedPolygon.exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_right _ hR) hpR
  have hL' : ∀ R ∈ L₁ ++ (P.vertex i, P.vertex (i + 1)) :: L₂, hgt u R.1 ≠ hgt u R.2 := by
    rw [← hsplit]; exact hL
  obtain ⟨δ, hδ, hmain⟩ := parity_flip hu hL' hp h1 h2
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  obtain ⟨ha, hb, hc⟩ := hmain t ht htδ
  rw [← hsplit] at ha hb hc
  rw [P.cover_pieces] at ha hb
  exact ⟨ha, hb, hc⟩

/-- Two points off the curve at which the parity differs: just before and just after the midpoint
of the first edge. This is what turns the separation theorem into the two parity *values*. -/
theorem exists_parity_ne (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∃ a b : Plane, a ∉ P.carrier ∧ b ∉ P.carrier ∧
      parity u P.pieces a ≠ parity u P.pieces b := by
  have hpmem : (1 / 2 : ℝ) • P.vertex 0 + (1 / 2 : ℝ) • P.vertex 1
      ∈ openSegment ℝ (P.vertex 0) (P.vertex (0 + 1)) := by
    rw [zero_add]
    exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  obtain ⟨δ, hδ, hmain⟩ := P.parity_flip_carrier hu hL 0 hpmem
  obtain ⟨h1, h2, h3⟩ := hmain (δ / 2) (by linarith) (by linarith)
  refine ⟨_, _, h1, h2, fun hh => ?_⟩
  rw [h3] at hh
  exact ne_add_one_zmod_two _ hh.symm

/-- **`π_C = 0` on the unbounded region** (Theorem 2.3), for a polygon presented with redundant
vertices. -/
theorem parity_eq_zero_of_mem_outside (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ outside P.carrier) :
    parity u P.pieces x = 0 := by
  have hcov := P.cover_pieces
  refine parity_eq_zero_of_mem_outside_cover hu hL P.isClosedChain_pieces ?_ ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact hx

/-- **`π_C = 1` on the bounded region** (Theorem 2.3), for a polygon presented with redundant
vertices. -/
theorem parity_eq_one_of_mem_inside (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ inside P.carrier) :
    parity u P.pieces x = 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := P.exists_parity_ne hu hL
  have hcov := P.cover_pieces
  refine parity_eq_one_of_mem_inside_cover (a := a) (b := b) hu hL P.isClosedChain_pieces
    ?_ ?_ ?_ hab ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact ha
  · rw [hcov]; exact hb
  · rw [hcov]; exact hx

end PrePolygon

/-! ## The `ClosedPolygon` parity values are instances

A machine check of the claim made in this module's docstring. `Schoenflies/PolygonalJordan.lean`
proves `ClosedPolygon.parity_eq_one_of_mem_inside` from a `StripData` — the collar of Lemma 1.8,
which is where `corner` is used. The collar is needed for Theorem 2.3 itself, but *not* a second
time for the parity value: given separation, the two values follow from the general lemmas above.
The two `example`s below are the same statements, re-proved that way. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.PrePolygonArc
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The arcs of a `PrePolygon`, and inserting a vertex

`Schoenflies.PrePolygon` is `Schoenflies.ClosedPolygon` without the `corner` field, so its
vertices may sit anywhere on the curve. This module carries §1 and §2 of the blueprint for such
a presentation: the edge list of an arc, the arc as a set, the two arcs of a splitting, and the
construction that makes the whole thing worth having — a prescribed point of the curve can be
made a vertex.

Everything below is the `Schoenflies.ClosedPolygon` development of
`Schoenflies/PolygonBridge.lean`, `Schoenflies/ParitySplitting.lean`,
`Schoenflies/PolygonalCrosscut.lean` and `Schoenflies/Realization.lean` with the structure
changed; every proof uses only `vertex_inj` and `edges_meet`, and `corner` is never mentioned.

## Why this module exists

`Schoenflies/Graph/K33Land.lean` and `Schoenflies/FaceCyclesLand.lean` each needed the same
apparatus and each transcribed it, the second under an `FC` suffix. The two copies were not
alpha-equivalent — `insertLast` in particular carried an extra hypothesis in one of them — so
the import checker never complained, and there were two of everything. This module is the
single copy; both consumers import it.

The one signature that genuinely differed is `Schoenflies.PrePolygon.insertLast`. The
`FaceCyclesLand` copy took, besides `hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0)`, a
hypothesis `∀ j, P.vertex j ≠ z` saying the new point is not already a vertex. That is not an
extra assumption but a consequence: `Schoenflies.PrePolygon.vertex_ne_of_mem_openSegment`
derives it from `hz`. The general form — the one with `hz` alone — is what survives here.

## Inserting a vertex, and why it is the crux

`Schoenflies.PrePolygon.deleteLast` removes a vertex at which the curve runs straight (the
blueprint's Lemma 1.8); `Schoenflies.PrePolygon.insertLast` is the inverse move, and it is the
reason `PrePolygon` is the right structure for a consumer that needs named points to be
vertices. The vertex is inserted at the end of the list, interior to the last edge, so that the
only edge that changes is the last one, which splits in two;
`Schoenflies.PrePolygon.rotate` brings any edge there. Simplicity survives because the far end
of the split edge lies on neither half.

## Blueprint

* `Schoenflies.PrePolygon.vertex_natCast_ne`, `…edge_meet_earlier` — the elementary simplicity
  facts, §1.
* `Schoenflies.PrePolygon.chain`, `…mem_chain_iff`, `…isArcBetween_chain` — the union of the
  first `k` edges, and that it is an arc.
* `Schoenflies.PrePolygon.arcPieces`, `…arcPieces_add`, `…arcPieces_full`,
  `…isChainFrom_arcPieces`, `…arcPieces_split_perm`, `…sameEdges_arcPieces_split`,
  `…parity_splitting` — the edge list of an arc, and Lemma 2.7 for it.
* `Schoenflies.PrePolygon.arc`, `…arc_union`, `…arc_inter`, `…isArcBetween_arc`,
  `…arc_not_subset_endpoints`, `…isCompact_arc` — the two arcs of a splitting, §2.
* `Schoenflies.PrePolygon.parity_ne_iff_mem_farRegion` — `thm:polygonal-jordan` read as a
  separation criterion.
* `Schoenflies.PrePolygon.arcList`, `…poly_arcList`, `…isPolygonal_arc` — an arc as a polyline,
  which is how it is glued to a crosscut.
* `Schoenflies.segment_halves_inter`, `Schoenflies.right_notMem_left_half`,
  `Schoenflies.left_notMem_right_half` — §1: cutting a segment at an interior point, in order.
  General-purpose; they belong beside `Schoenflies.segment_split` in `Schoenflies/SegmentCut.lean`.
* `Schoenflies.PrePolygon.insertLast`, `…carrier_insertLast`,
  `Schoenflies.PrePolygon.exists_prePolygon_insert`, `…exists_prePolygon_vertices` — the inverse
  of the blueprint's "delete redundant vertices" (Lemma 1.8): *insert* one, anywhere on the curve.
* `Schoenflies.exists_prePolygon_points`, `…exists_prePolygon_split` — §1, the realization
  theorem **with the cut points anywhere on the curve**. Compare
  `Schoenflies.exists_closedPolygon_split`, which requires them to be corners.
-/

open Bornology Metric Set

namespace Schoenflies

open Plane

namespace PrePolygon

variable {m : ℕ} {P : PrePolygon m} {a : ZMod (m + 3)} {k : ℕ} {u : Plane}

/-! ## Indices, edges and the elementary simplicity facts

Verbatim the `Schoenflies.ClosedPolygon` facts of `Schoenflies/PolygonBridge.lean` whose proofs
use only `vertex_inj` and `edges_meet`. -/

/-- **An edge meets an earlier edge only at its own initial vertex.** -/
theorem edge_meet_earlier {j l : ℕ} (hjl : j < l) (hl : l + 1 < m + 3) {z : Plane}
    (hzj : z ∈ P.edge (j : ZMod (m + 3))) (hzl : z ∈ P.edge (l : ZMod (m + 3))) :
    z = P.vertex (l : ZMod (m + 3)) := by
  have hjn : j < m + 3 := by omega
  have hln : l < m + 3 := by omega
  have hne : (l : ZMod (m + 3)) ≠ (j : ZMod (m + 3)) :=
    fun heq => (by omega : l ≠ j) (ClosedPolygon.natCast_inj hln hjn heq)
  have hmem := P.edges_meet _ _ hne (Set.mem_inter hzl hzj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · exact hmem
  exfalso
  have hmem2 := P.edges_meet _ _ (Ne.symm hne) (Set.mem_inter hzj hzl)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem2
  rw [← ClosedPolygon.natCast_succ] at hmem
  rcases hmem2 with hmem2 | hmem2
  · have : l + 1 = j := ClosedPolygon.natCast_inj hl hjn (P.vertex_inj (hmem ▸ hmem2))
    omega
  · rw [← ClosedPolygon.natCast_succ] at hmem2
    have : l + 1 = j + 1 :=
      ClosedPolygon.natCast_inj hl (by omega) (P.vertex_inj (hmem ▸ hmem2))
    omega

/-! ## The chain of the first `k` edges, and that it is an arc -/

/-- The union of the edges leaving vertices `0, 1, …, k`. -/
def chain (P : PrePolygon m) : ℕ → Set Plane
  | 0 => P.edge 0
  | k + 1 => chain P k ∪ P.edge ((k + 1 : ℕ) : ZMod (m + 3))

theorem mem_chain_iff {z : Plane} : z ∈ P.chain k ↔ ∃ j ≤ k, z ∈ P.edge (j : ZMod (m + 3)) := by
  induction k with
  | zero =>
    constructor
    · intro hz
      exact ⟨0, le_rfl, by simpa [chain] using hz⟩
    · rintro ⟨j, hj, hzj⟩
      obtain rfl : j = 0 := Nat.le_zero.1 hj
      simpa [chain] using hzj
  | succ k ih =>
    simp only [chain, Set.mem_union]
    constructor
    · rintro (hz | hz)
      · obtain ⟨j, hj, hzj⟩ := ih.1 hz
        exact ⟨j, le_trans hj (Nat.le_succ k), hzj⟩
      · exact ⟨k + 1, le_rfl, hz⟩
    · rintro ⟨j, hj, hzj⟩
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact Or.inl (ih.2 ⟨j, Nat.lt_succ_iff.1 hlt, hzj⟩)
      · obtain rfl : j = k + 1 := le_antisymm hj hge
        exact Or.inr hzj

/-- **The partial chains are arcs.** One edge at a time, glued at the vertex they share. -/
theorem isArcBetween_chain (P : PrePolygon m) :
    ∀ k : ℕ, k + 1 < m + 3 →
      IsArcBetween (P.chain k) (P.vertex 0) (P.vertex ((k + 1 : ℕ) : ZMod (m + 3))) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [ClosedPolygon.natCast_succ]
    exact isArcBetween_segment (vertex_ne_succ 0)
  | succ k ih =>
    intro hk
    have hA := ih (by omega)
    have hB : IsArcBetween (P.edge ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 + 1 : ℕ) : ZMod (m + 3))) := by
      rw [ClosedPolygon.natCast_succ (k + 1)]
      exact isArcBetween_segment (vertex_ne_succ _)
    have hmeet : ∀ z ∈ P.chain k, z ∈ P.edge ((k + 1 : ℕ) : ZMod (m + 3)) →
        z = P.vertex ((k + 1 : ℕ) : ZMod (m + 3)) := by
      intro z hz hze
      obtain ⟨j, hj, hzj⟩ := mem_chain_iff.1 hz
      exact edge_meet_earlier (by omega) (by omega) hzj hze
    exact hA.concatenate hB hmeet

/-! ## The edge list of an arc

`Schoenflies.ClosedPolygon.arcPieces` with the structure changed; every proof below uses only
`vertex_inj` and `edges_meet`, so it is the old proof verbatim. -/

/-- The edge list of the arc of `P` that leaves vertex `a` and runs forward through `k` edges. -/
def arcPieces (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : List Piece :=
  (List.range k).map fun t : ℕ => (P.vertex (a + t), P.vertex (a + t + 1))

/-- Forgetting the `corner` field does not change the edge list of an arc. -/
@[simp] theorem arcPieces_toPre (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    C.toPre.arcPieces a k = C.arcPieces a k := rfl

@[simp] theorem arcPieces_zero (P : PrePolygon m) (a : ZMod (m + 3)) : P.arcPieces a 0 = [] := rfl

/-- Running through `k + l` edges is running through `k` and then through `l`. -/
theorem arcPieces_add (P : PrePolygon m) (a : ZMod (m + 3)) (k l : ℕ) :
    P.arcPieces a (k + l) = P.arcPieces a k ++ P.arcPieces (a + k) l := by
  rw [arcPieces, arcPieces, arcPieces, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, Nat.cast_add, ← add_assoc]

/-- Running through all `m + 3` edges from vertex `0` is the whole edge list. -/
theorem arcPieces_full (P : PrePolygon m) : P.arcPieces 0 (m + 3) = P.pieces := by
  rw [arcPieces, pieces]
  exact List.map_congr_left fun t _ => by rw [zero_add]

/-- Every edge of an arc is an edge of the polygon. -/
theorem mem_pieces_of_mem_arcPieces {Q : Piece} (hQ : Q ∈ P.arcPieces a k) : Q ∈ P.pieces := by
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hQ
  exact P.mem_pieces _

theorem arcPieces_hgt_ne (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ P.arcPieces a k, hgt u Q.1 ≠ hgt u Q.2 :=
  fun _ hQ => hL _ (mem_pieces_of_mem_arcPieces hQ)

/-- **The two arcs from a vertex use every edge exactly once.** -/
theorem arcPieces_full_perm (P : PrePolygon m) (a : ZMod (m + 3)) :
    (P.arcPieces a (m + 3)).Perm P.pieces := by
  have hlt : a.val < m + 3 := ZMod.val_lt a
  have hcast : ((a.val : ℕ) : ZMod (m + 3)) = a := ZMod.natCast_rightInverse a
  have hzero : a + ((m + 3 - a.val : ℕ) : ZMod (m + 3)) = 0 := by
    rw [Nat.cast_sub hlt.le, hcast]
    simp
  have hsplit1 : P.arcPieces a (m + 3)
      = P.arcPieces a (m + 3 - a.val) ++ P.arcPieces 0 a.val := by
    have h1 : (m + 3 - a.val) + a.val = m + 3 := by omega
    have h2 := arcPieces_add P a (m + 3 - a.val) a.val
    rwa [h1, hzero] at h2
  have hsplit2 : P.pieces = P.arcPieces 0 a.val ++ P.arcPieces a (m + 3 - a.val) := by
    have h1 : a.val + (m + 3 - a.val) = m + 3 := by omega
    have h2 := arcPieces_add P 0 a.val (m + 3 - a.val)
    rw [h1, arcPieces_full, zero_add, hcast] at h2
    exact h2
  rw [hsplit1, hsplit2]
  exact List.perm_append_comm

/-- **The split.** For `k ≤ m + 3` the two arcs at `a` and `a + k` between them use every edge
of `P` exactly once. -/
theorem arcPieces_split_perm (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    (P.arcPieces a k ++ P.arcPieces (a + k) (m + 3 - k)).Perm P.pieces := by
  rw [← arcPieces_add, Nat.add_sub_cancel' hk]
  exact arcPieces_full_perm P a

theorem sameEdges_arcPieces_split (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    SameEdges P.pieces (P.arcPieces a k ++ P.arcPieces (a + k) (m + 3 - k)) :=
  SameEdges.of_perm (arcPieces_split_perm P a hk).symm

/-- The two arcs between them carry the polygon. -/
theorem cover_arcPieces_union (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    cover (P.arcPieces a k) ∪ cover (P.arcPieces (a + k) (m + 3 - k)) = P.carrier := by
  rw [← cover_append, cover_perm (arcPieces_split_perm P a hk), cover_pieces]

theorem cover_arcPieces_subset (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    cover (P.arcPieces a k) ⊆ P.carrier := by
  intro z hz
  obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
  rw [← cover_pieces]
  exact mem_cover (mem_pieces_of_mem_arcPieces hR) hzR

theorem arcPieces_append_hgt_ne {K : List Piece}
    (hC : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) (hK : ∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ P.arcPieces a k ++ K, hgt u Q.1 ≠ hgt u Q.2 :=
  hgt_ne_append (arcPieces_hgt_ne hC) hK

/-- **A curve of the split occupies its arc together with the crosscut.** -/
theorem carrier_eq_of_sameEdges {m' : ℕ} {J : PrePolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (P.arcPieces a k ++ K)) :
    J.carrier = cover (P.arcPieces a k) ∪ cover K := by
  rw [← cover_pieces, h.cover_eq, cover_append]

/-- A point off `P` and off the crosscut is off `J`. -/
theorem notMem_carrier_of_sameEdges {m' : ℕ} {J : PrePolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (P.arcPieces a k ++ K)) {x : Plane} (hxC : x ∉ P.carrier)
    (hxK : x ∉ cover K) : x ∉ J.carrier := by
  rw [carrier_eq_of_sameEdges h]
  rintro (hx | hx)
  · exact hxC (cover_arcPieces_subset P a k hx)
  · exact hxK hx

/-- **Parity splitting** (Lemma 2.7) for a polygon presented with redundant vertices. -/
theorem parity_splitting (P : PrePolygon m) (u : Plane) (a : ZMod (m + 3)) (hk : k ≤ m + 3)
    {L₁ L₂ K : List Piece} (h₁ : SameEdges L₁ (P.arcPieces a k ++ K))
    (h₂ : SameEdges L₂ (P.arcPieces (a + k) (m + 3 - k) ++ K)) (q : Plane) :
    parity u L₁ q + parity u L₂ q = parity u P.pieces q :=
  parity_split u (sameEdges_arcPieces_split P a hk) h₁ h₂ q

/-! ## The arcs as sets -/

/-- The arc of `P` that leaves vertex `a` and runs forward through `k` edges, as a set. -/
def arc (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : Set Plane := cover (P.arcPieces a k)

@[simp] theorem arc_toPre (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    C.toPre.arc a k = C.arc a k := rfl

theorem arc_subset_carrier (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.arc a k ⊆ P.carrier := cover_arcPieces_subset P a k

theorem arc_union (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    P.arc a k ∪ P.arc (a + k) (m + 3 - k) = P.carrier := cover_arcPieces_union P a hk

theorem mem_arc_iff {z : Plane} :
    z ∈ P.arc a k ↔ ∃ t < k, z ∈ P.edge (a + (t : ZMod (m + 3))) := by
  constructor
  · intro hz
    obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hR
    exact ⟨t, List.mem_range.1 ht, hzR⟩
  · rintro ⟨t, ht, hz⟩
    exact mem_cover (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩) hz

/-- The first vertex of a nonempty arc lies on it. -/
theorem vertex_mem_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.vertex a ∈ P.arc a k := by
  refine mem_arc_iff.2 ⟨0, hk, ?_⟩
  rw [Nat.cast_zero, add_zero, edge]
  exact left_mem_segment ℝ _ _

/-- The last vertex of a nonempty arc lies on it. -/
theorem vertex_add_mem_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.vertex (a + k) ∈ P.arc a k := by
  have hlast : a + ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = a + (k : ZMod (m + 3)) := by
    have h : ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = ((k : ℕ) : ZMod (m + 3)) := by
      rw [show ((k : ℕ) : ZMod (m + 3)) = (((k - 1) + 1 : ℕ) : ZMod (m + 3)) by
        congr 1; omega, Nat.cast_add, Nat.cast_one]
    rw [add_assoc, h]
  refine mem_arc_iff.2 ⟨k - 1, by omega, ?_⟩
  rw [edge, hlast]
  exact right_mem_segment ℝ _ _

/-- **The two cut vertices lie on both arcs.** -/
theorem endpoints_subset_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    ({P.vertex a, P.vertex (a + k)} : Set Plane) ⊆ P.arc a k := by
  rintro w (rfl | rfl)
  · exact P.vertex_mem_arc a hk
  · exact P.vertex_add_mem_arc a hk

theorem endpoints_subset_arc' (P : PrePolygon m) (a : ZMod (m + 3)) (hk2 : k ≤ m + 2) :
    ({P.vertex a, P.vertex (a + k)} : Set Plane) ⊆ P.arc (a + k) (m + 3 - k) := by
  have hpos : 1 ≤ m + 3 - k := by omega
  have hwrap := zmod_add_sub_cancel (k := k) (by omega) a
  rintro w (rfl | rfl)
  · have hm := P.vertex_add_mem_arc (a + k) hpos
    rwa [hwrap] at hm
  · exact P.vertex_mem_arc (a + k) hpos

/-- Distinct index numerals below the modulus name distinct vertices, after any shift. -/
theorem natCast_shift_inj (P : PrePolygon m) (a : ZMod (m + 3)) {x z : ℕ} (hx : x < m + 3)
    (hz : z < m + 3) (he : P.vertex (a + (x : ZMod (m + 3))) = P.vertex (a + (z : ZMod (m + 3)))) :
    x = z :=
  ClosedPolygon.natCast_inj hx hz (add_left_cancel (P.vertex_inj he))

/-- An arc of `P` is a chain of the polygon read from its first vertex. -/
theorem arc_eq_chain (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.arc a k = (P.rotate a).chain (k - 1) := by
  have hedge : ∀ j : ZMod (m + 3), (P.rotate a).edge j = P.edge (a + j) := by
    intro j
    rw [edge, edge, rotate_vertex, rotate_vertex, show a + (j + 1) = a + j + 1 by ring]
  ext z
  rw [mem_arc_iff, mem_chain_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    exact ⟨t, by omega, by rw [hedge]; exact hz⟩
  · rintro ⟨j, hj, hz⟩
    rw [hedge] at hz
    exact ⟨j, by omega, hz⟩

/-- **An arc of a splitting is an arc between the two cut vertices.** -/
theorem isArcBetween_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k)
    (hk2 : k ≤ m + 2) : IsArcBetween (P.arc a k) (P.vertex a) (P.vertex (a + k)) := by
  have h := (P.rotate a).isArcBetween_chain (k - 1) (by omega)
  rw [← arc_eq_chain P a hk1, show ((k - 1 + 1 : ℕ) : ZMod (m + 3)) = (k : ZMod (m + 3)) by
    congr 1; omega] at h
  simpa using h

/-- **The two arcs of a splitting meet exactly at the two cut vertices.** -/
theorem arc_inter (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) :
    P.arc a k ∩ P.arc (a + k) (m + 3 - k) = {P.vertex a, P.vertex (a + k)} := by
  refine Set.Subset.antisymm ?_ (Set.subset_inter (P.endpoints_subset_arc a hk1)
    (P.endpoints_subset_arc' a hk2))
  rintro z ⟨hz1, hz2⟩
  obtain ⟨s, hs, hzs⟩ := mem_arc_iff.1 hz1
  obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hz2
  have hkt : k + t < m + 3 := by omega
  rw [show a + (k : ZMod (m + 3)) + (t : ZMod (m + 3)) = a + ((k + t : ℕ) : ZMod (m + 3)) by
    push_cast; ring] at hzt
  have hij : a + (s : ZMod (m + 3)) ≠ a + ((k + t : ℕ) : ZMod (m + 3)) := fun he =>
    absurd (ClosedPolygon.natCast_inj (by omega) hkt (add_left_cancel he)) (by omega)
  have hsucc₁ : a + (s : ZMod (m + 3)) + 1 = a + ((s + 1 : ℕ) : ZMod (m + 3)) := by
    push_cast <;> ring
  have hsucc₂ : a + ((k + t : ℕ) : ZMod (m + 3)) + 1 = a + ((k + t + 1 : ℕ) : ZMod (m + 3)) := by
    push_cast <;> ring
  have hA := P.edges_meet _ _ hij (Set.mem_inter hzs hzt)
  have hB := P.edges_meet _ _ (Ne.symm hij) (Set.mem_inter hzt hzs)
  rw [hsucc₁] at hA
  rw [hsucc₂] at hB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB ⊢
  have hzero : k + t + 1 = m + 3 →
      ((k + t + 1 : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by
    intro he
    rw [he, Nat.cast_zero, ZMod.natCast_self]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (hA.symm.trans hB) fun he => hij (P.vertex_inj he)
  · rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_inj a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have hs0 : s = 0 := P.natCast_shift_inj a (by omega) (by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      exact Or.inl (by rw [hA, hs0, Nat.cast_zero, add_zero])
  · have hst : s + 1 = k + t := P.natCast_shift_inj a (by omega) hkt (hA.symm.trans hB)
    exact Or.inr (by rw [hA, show s + 1 = k by omega])
  · exfalso
    rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_inj a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have := P.natCast_shift_inj a (show s + 1 < m + 3 by omega) (show 0 < m + 3 by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      omega

/-- **The crossing count separates points exactly as the polygon does** (Theorem 2.3, read as a
criterion), for a polygon presented with redundant vertices. -/
theorem parity_ne_iff_mem_farRegion (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ P.carrier) (hy : y ∉ P.carrier) :
    parity u P.pieces x ≠ parity u P.pieces y ↔ x ∈ farRegion P.carrier y := by
  rw [mem_farRegion_iff_connectedComponentIn_ne hx]
  constructor
  · intro hne heq
    exact hne (P.parity_eq_of_mem_connectedComponentIn_carrier hu hL hy
      (heq ▸ mem_connectedComponentIn hx))
  · intro hne
    rcases P.connectedComponentIn_eq_inside_or_outside hx with hxr | hxr <;>
      rcases P.connectedComponentIn_eq_inside_or_outside hy with hyr | hyr
    · exact absurd (hxr.trans hyr.symm) hne
    · rw [P.parity_eq_one_of_mem_inside hu hL (hxr ▸ mem_connectedComponentIn hx),
        P.parity_eq_zero_of_mem_outside hu hL (hyr ▸ mem_connectedComponentIn hy)]
      decide
    · rw [P.parity_eq_zero_of_mem_outside hu hL (hxr ▸ mem_connectedComponentIn hx),
        P.parity_eq_one_of_mem_inside hu hL (hyr ▸ mem_connectedComponentIn hy)]
      decide
    · exact absurd (hxr.trans hyr.symm) hne

/-! ### An arc as a polyline

`arc a k` is the carrier of the vertex list `v a, v (a+1), …, v (a+k)`; that is how it is seen
to be polygonal, and how it is glued to a crosscut. -/

end PrePolygon

/-! ## Cutting a segment at an interior point, in order

The two halves of a cut segment meet only at the cut, and neither reaches the far end of the
other. Both are read off `Schoenflies/SegmentOrder.lean`: along a nondegenerate segment the
distance from one end is a coordinate. -/

/-- **The two halves of a cut segment meet only at the cut point.** -/
theorem segment_halves_inter {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    segment ℝ u w ∩ segment ℝ w v ⊆ {w} := by
  rintro x ⟨hx1, hx2⟩
  have hws : w ∈ segment ℝ u v := openSegment_subset_segment ℝ _ _ hw
  have hwd := dist_le_of_mem_segment huv (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)
    (by simp) hws
  have h1 := dist_le_of_mem_segment huv (left_mem_segment ℝ u v) hws (by simp) hx1
  have h2 := dist_le_of_mem_segment huv hws (right_mem_segment ℝ u v) hwd.2 hx2
  have hxs : x ∈ segment ℝ u v :=
    (convex_segment u v).segment_subset (left_mem_segment ℝ u v) hws hx1
  exact eq_of_dist_left_eq huv hxs hws (le_antisymm h1.2 h2.1)

/-- The far end of a cut segment is not on the near half. -/
theorem right_notMem_left_half {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    v ∉ segment ℝ u w := by
  intro hv
  have hvw : v = w := segment_halves_inter huv hw ⟨hv, right_mem_segment ℝ w v⟩
  rw [← hvw] at hw
  exact huv (right_mem_openSegment_iff.1 hw)

/-- The near end of a cut segment is not on the far half. -/
theorem left_notMem_right_half {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    u ∉ segment ℝ w v := by
  intro hu
  have huw : u = w := segment_halves_inter huv hw ⟨left_mem_segment ℝ u w, hu⟩
  rw [← huw] at hw
  exact huv (left_mem_openSegment_iff.1 hw)

namespace PrePolygon

/-! ## Inserting a vertex

`Schoenflies.PrePolygon.deleteLast` removes a redundant vertex; this is the inverse operation,
and it is what makes `PrePolygon` the right presentation for a consumer that must cut the curve
at prescribed points. The vertex is inserted at the end of the list, interior to the last edge;
`Schoenflies.PrePolygon.rotate` brings any edge there. -/

section Insert

variable {m : ℕ} {P : PrePolygon m} {z : Plane}

/-- The index `-1` of a cyclic list of length `m + 3`, as a numeral. -/
theorem val_neg_one : (-1 : ZMod (m + 3)).val = m + 2 := by
  have h : (-1 : ZMod (m + 3)) = ((m + 2 : ℕ) : ZMod (m + 3)) := by
    have h0 : ((m + 3 : ℕ) : ZMod (m + 3)) = 0 := ZMod.natCast_self _
    push_cast at h0 ⊢
    linear_combination -h0
  rw [h, ZMod.val_cast_of_lt (by omega)]

/-- The last edge, with its second endpoint written as vertex `0`. -/
theorem edge_neg_one (P : PrePolygon m) :
    P.edge (-1) = segment ℝ (P.vertex (-1)) (P.vertex 0) := by
  rw [edge, show (-1 : ZMod (m + 3)) + 1 = 0 by ring]

/-- **A point interior to an edge is a vertex of no index.** -/
theorem vertex_ne_of_mem_openSegment {i : ZMod (m + 3)} {w : Plane}
    (hw : w ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) (j : ZMod (m + 3)) :
    P.vertex j ≠ w := by
  intro he
  by_cases hji : j = i
  · rw [hji] at he
    rw [← he] at hw
    exact vertex_ne_succ i (left_mem_openSegment_iff.1 hw)
  · have hmem : w ∈ P.edge j := by rw [edge, ← he]; exact left_mem_segment ℝ _ _
    exact notMem_edge_of_mem_openSegment hji hw hmem

/-- The vertex family with `z` appended at the end: the old numerals name the old vertices, and
the one new index names `z`. -/
def insVertex (P : PrePolygon m) (z : Plane) (j : ZMod (m + 1 + 3)) : Plane :=
  if j.val < m + 3 then P.vertex ((j.val : ℕ) : ZMod (m + 3)) else z

theorem insVertex_emb (P : PrePolygon m) (z : Plane) (j : ZMod (m + 3)) :
    insVertex P z (emb j) = P.vertex j := by
  have hlt : j.val < m + 3 := ZMod.val_lt j
  have hval : (emb j).val = j.val := by
    rw [emb, ZMod.val_cast_of_lt (by omega)]
  rw [insVertex, if_pos (by rw [hval]; exact hlt), hval, ZMod.natCast_rightInverse j]

theorem val_neg_one' : (-1 : ZMod (m + 1 + 3)).val = m + 3 := by
  rw [neg_one_eq_cast, ZMod.val_cast_of_lt (by omega)]

theorem insVertex_neg_one (P : PrePolygon m) (z : Plane) : insVertex P z (-1) = z := by
  rw [insVertex, if_neg (by rw [val_neg_one' (m := m)]; omega)]

/-- Away from the inserted vertex the edges are unchanged. -/
theorem insEdge_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    segment ℝ (insVertex P z (emb j)) (insVertex P z (emb j + 1)) = P.edge j := by
  rw [← emb_succ_of_lt h, insVertex_emb, insVertex_emb, edge]

/-- The penultimate edge of the lengthened list: the near half of the cut edge. -/
theorem insEdge_pen (P : PrePolygon m) (z : Plane) :
    segment ℝ (insVertex P z (-1 - 1)) (insVertex P z (-1 - 1 + 1))
      = segment ℝ (P.vertex (-1)) z := by
  have he : emb (-1 : ZMod (m + 3)) = -1 - 1 := emb_eq_last (by rw [val_neg_one])
  have h1 : insVertex P z (-1 - 1) = P.vertex (-1) := by rw [← he, insVertex_emb]
  have h2 : insVertex P z (-1 - 1 + 1) = z := by
    rw [show (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 by ring, insVertex_neg_one]
  rw [h1, h2]

/-- The last edge of the lengthened list: the far half of the cut edge. -/
theorem insEdge_last (P : PrePolygon m) (z : Plane) :
    segment ℝ (insVertex P z (-1)) (insVertex P z (-1 + 1)) = segment ℝ z (P.vertex 0) := by
  have hemb0 : emb (0 : ZMod (m + 3)) = 0 := by rw [emb, ZMod.val_zero, Nat.cast_zero]
  have h1 : insVertex P z (-1) = z := insVertex_neg_one P z
  have h2 : insVertex P z (-1 + 1) = P.vertex 0 := by
    rw [show (-1 : ZMod (m + 1 + 3)) + 1 = 0 by ring, ← hemb0, insVertex_emb]
  rw [h1, h2]

theorem vertex_neg_one_ne_zero (P : PrePolygon m) : P.vertex (-1) ≠ P.vertex 0 := by
  have h := vertex_ne_succ (P := P) (-1)
  rwa [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at h

variable (hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0))
include hz

/-- The two new edges cover the edge they replace. -/
theorem insEdge_union : segment ℝ (P.vertex (-1)) z ∪ segment ℝ z (P.vertex 0) = P.edge (-1) := by
  rw [edge_neg_one]
  exact (segment_split (openSegment_subset_segment ℝ _ _ hz)).symm

theorem insEdge_pen_subset : segment ℝ (P.vertex (-1)) z ⊆ P.edge (-1) := by
  rw [← insEdge_union hz]; exact Set.subset_union_left

theorem insEdge_last_subset : segment ℝ z (P.vertex 0) ⊆ P.edge (-1) := by
  rw [← insEdge_union hz]; exact Set.subset_union_right

/-- **The polygon with one extra vertex, interior to its last edge** — equivalently, with the
last edge split in two at a prescribed interior point. -/
def insertLast (P : PrePolygon m) (hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0)) :
    PrePolygon (m + 1) where
  vertex := insVertex P z
  vertex_inj := by
    intro i j hij
    have hzv : ∀ l : ZMod (m + 3), P.vertex l ≠ z := by
      intro l
      refine vertex_ne_of_mem_openSegment (i := -1) ?_ l
      rwa [show (-1 : ZMod (m + 3)) + 1 = 0 by ring]
    simp only [insVertex] at hij
    have hi := ZMod.val_lt i
    have hj := ZMod.val_lt j
    by_cases hli : i.val < m + 3 <;> by_cases hlj : j.val < m + 3
    · rw [if_pos hli, if_pos hlj] at hij
      exact ZMod.val_injective _
        (ClosedPolygon.natCast_inj hli hlj (P.vertex_inj hij))
    · rw [if_pos hli, if_neg hlj] at hij
      exact absurd hij (hzv _)
    · rw [if_neg hli, if_pos hlj] at hij
      exact absurd hij.symm (hzv _)
    · exact ZMod.val_injective _ (by omega)
  edges_meet := by
    have hne0 : P.vertex (-1) ≠ P.vertex 0 := vertex_neg_one_ne_zero P
    have hhalf := segment_halves_inter hne0 hz
    have hpen := insEdge_pen P z
    have hlast := insEdge_last P z
    -- The shape of the edge at each of the three kinds of index.
    have hshape : ∀ i : ZMod (m + 1 + 3),
        (∃ j : ZMod (m + 3), j.val + 1 < m + 3 ∧ emb j = i ∧
            segment ℝ (insVertex P z i) (insVertex P z (i + 1)) = P.edge j ∧
            ({insVertex P z i, insVertex P z (i + 1)} : Set Plane)
              = {P.vertex j, P.vertex (j + 1)}) ∨
          (i = -1 - 1 ∧ segment ℝ (insVertex P z i) (insVertex P z (i + 1))
              = segment ℝ (P.vertex (-1)) z) ∨
          (i = -1 ∧ segment ℝ (insVertex P z i) (insVertex P z (i + 1))
              = segment ℝ z (P.vertex 0)) := by
      intro i
      by_cases h1 : i = -1
      · exact Or.inr (Or.inr ⟨h1, by rw [h1]; exact hlast⟩)
      by_cases h2 : i = -1 - 1
      · exact Or.inr (Or.inl ⟨h2, by rw [h2]; exact hpen⟩)
      obtain ⟨j, hjv, rfl⟩ := exists_emb_eq h1 h2
      refine Or.inl ⟨j, hjv, rfl, insEdge_of_lt hjv, ?_⟩
      rw [insVertex_emb, ← emb_succ_of_lt hjv, insVertex_emb]
    intro i j hij
    have hi := hshape i
    have hj := hshape j
    -- The names of the two ends of the edge at `i`, in each case.
    rcases hi with ⟨ji, hjiv, rfl, hEi, hVi⟩ | ⟨rfl, hEi⟩ | ⟨rfl, hEi⟩
    · have hjine : ji ≠ -1 := by
        intro he
        rw [he, val_neg_one] at hjiv
        omega
      rw [hEi, hVi]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, hEj⟩ | ⟨rfl, hEj⟩
      · rw [hEj]
        exact P.edges_meet ji jj fun he => hij (by rw [he])
      · rw [hEj]
        exact fun x hx =>
          P.edges_meet ji (-1) hjine ⟨hx.1, insEdge_pen_subset hz hx.2⟩
      · rw [hEj]
        exact fun x hx =>
          P.edges_meet ji (-1) hjine ⟨hx.1, insEdge_last_subset hz hx.2⟩
    · rw [hEi]
      have hV : ({insVertex P z (-1 - 1), insVertex P z (-1 - 1 + 1)} : Set Plane)
          = {P.vertex (-1), z} := by
        have he : emb (-1 : ZMod (m + 3)) = -1 - 1 := emb_eq_last (by rw [val_neg_one])
        rw [show insVertex P z (-1 - 1) = P.vertex (-1) by rw [← he, insVertex_emb],
          show insVertex P z (-1 - 1 + 1) = z by
            rw [show (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 by ring, insVertex_neg_one]]
      rw [hV]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, -⟩ | ⟨rfl, hEj⟩
      · have hjjne : jj ≠ -1 := by
          intro he
          rw [he, val_neg_one] at hjjv
          omega
        rw [hEj]
        rintro x ⟨hx1, hx2⟩
        have hmem := P.edges_meet (-1) jj (Ne.symm hjjne)
          ⟨insEdge_pen_subset hz hx1, hx2⟩
        rw [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
        rcases hmem with hmem | hmem
        · exact Or.inl hmem
        · exact absurd (hmem ▸ hx1) (right_notMem_left_half hne0 hz)
      · exact absurd rfl hij
      · rw [hEj]
        exact fun x hx => Or.inr (hhalf hx)
    · rw [hEi]
      have hV : ({insVertex P z (-1), insVertex P z (-1 + 1)} : Set Plane)
          = {z, P.vertex 0} := by
        have hemb0 : emb (0 : ZMod (m + 3)) = 0 := by rw [emb, ZMod.val_zero, Nat.cast_zero]
        rw [insVertex_neg_one,
          show insVertex P z (-1 + 1) = P.vertex 0 by
            rw [show (-1 : ZMod (m + 1 + 3)) + 1 = 0 by ring, ← hemb0, insVertex_emb]]
      rw [hV]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, hEj⟩ | ⟨rfl, -⟩
      · have hjjne : jj ≠ -1 := by
          intro he
          rw [he, val_neg_one] at hjjv
          omega
        rw [hEj]
        rintro x ⟨hx1, hx2⟩
        have hmem := P.edges_meet (-1) jj (Ne.symm hjjne)
          ⟨insEdge_last_subset hz hx1, hx2⟩
        rw [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
        rcases hmem with hmem | hmem
        · exact absurd (hmem ▸ hx1) (left_notMem_right_half hne0 hz)
        · exact Or.inr hmem
      · rw [hEj]
        exact fun x hx => Or.inl (hhalf ⟨hx.2, hx.1⟩)
      · exact absurd rfl hij

@[simp] theorem insertLast_vertex : (insertLast P hz).vertex = insVertex P z := rfl

/-- **Inserting a vertex does not move the curve.** -/
theorem carrier_insertLast : (insertLast P hz).carrier = P.carrier := by
  have hpen := insEdge_pen P z
  have hlast := insEdge_last P z
  refine Set.Subset.antisymm (Set.iUnion_subset fun i => ?_) (Set.iUnion_subset fun j => ?_)
  · by_cases h1 : i = -1
    · subst h1
      refine le_trans (le_of_eq ?_) (le_trans (insEdge_last_subset hz) (edge_subset_carrier _))
      exact hlast
    by_cases h2 : i = -1 - 1
    · subst h2
      refine le_trans (le_of_eq ?_) (le_trans (insEdge_pen_subset hz) (edge_subset_carrier _))
      exact hpen
    · obtain ⟨j, hjv, rfl⟩ := exists_emb_eq h1 h2
      refine le_trans (le_of_eq ?_) (edge_subset_carrier j)
      exact insEdge_of_lt hjv
  · by_cases hjlast : j.val + 1 < m + 3
    · refine le_trans (le_of_eq ?_) (edge_subset_carrier (P := insertLast P hz) (emb j))
      exact (insEdge_of_lt hjlast (P := P) (z := z)).symm
    · have hjm : j = -1 := by
        have := ZMod.val_lt j
        exact ZMod.val_injective _ (by rw [val_neg_one]; omega)
      subst hjm
      rw [← insEdge_union hz]
      refine Set.union_subset ?_ ?_
      · refine le_trans (le_of_eq hpen.symm)
          (edge_subset_carrier (P := insertLast P hz) (-1 - 1))
      · refine le_trans (le_of_eq hlast.symm)
          (edge_subset_carrier (P := insertLast P hz) (-1))

/-- The inserted vertex is a vertex. -/
theorem insertLast_mem_vertex : ∃ j, (insertLast P hz).vertex j = z :=
  ⟨-1, insVertex_neg_one P z⟩

/-- The old vertices are still vertices. -/
theorem insertLast_old_vertex (i : ZMod (m + 3)) : ∃ j, (insertLast P hz).vertex j = P.vertex i :=
  ⟨emb i, insVertex_emb P z i⟩

end Insert

/-- **A named point of the curve becomes a vertex**, and the old vertices stay vertices. Either
the point already is a vertex, or it is interior to exactly one edge, and then that edge is
brought to the end of the list by `Schoenflies.PrePolygon.rotate` and cut by
`Schoenflies.PrePolygon.insertLast`. -/
theorem exists_prePolygon_insert {m : ℕ} (P : PrePolygon m) {z : Plane} (hz : z ∈ P.carrier) :
    ∃ (m' : ℕ) (P' : PrePolygon m'), P'.carrier = P.carrier ∧ (∃ j, P'.vertex j = z) ∧
      ∀ i, ∃ j, P'.vertex j = P.vertex i := by
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.1 hz
  by_cases hend : z = P.vertex i ∨ z = P.vertex (i + 1)
  · exact ⟨m, P, rfl, by rcases hend with rfl | rfl; exacts [⟨i, rfl⟩, ⟨i + 1, rfl⟩],
      fun i => ⟨i, rfl⟩⟩
  · push Not at hend
    have hopen : z ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) :=
      mem_openSegment_of_ne_left_right (Ne.symm hend.1) (Ne.symm hend.2) hzi
    -- Rotate so that the edge in question is the last one.
    set Q : PrePolygon m := P.rotate (i + 1) with hQ
    have hQm : Q.vertex (-1) = P.vertex i := by
      rw [hQ, rotate_vertex, show i + 1 + (-1 : ZMod (m + 3)) = i by ring]
    have hQ0 : Q.vertex 0 = P.vertex (i + 1) := by
      rw [hQ, rotate_vertex, add_zero]
    have hopen' : z ∈ openSegment ℝ (Q.vertex (-1)) (Q.vertex 0) := by rw [hQm, hQ0]; exact hopen
    refine ⟨m + 1, insertLast Q hopen', ?_, insertLast_mem_vertex hopen', fun l => ?_⟩
    · rw [carrier_insertLast hopen', hQ, carrier_rotate]
    · obtain ⟨j, hj⟩ := insertLast_old_vertex hopen' (l - (i + 1))
      exact ⟨j, by rw [hj, hQ, rotate_vertex, add_sub_cancel]⟩

/-- **Every point of a finite list on the curve can be made a vertex at once.** -/
theorem exists_prePolygon_vertices : ∀ (S : List Plane) {m : ℕ} (P : PrePolygon m),
    (∀ z ∈ S, z ∈ P.carrier) →
      ∃ (m' : ℕ) (P' : PrePolygon m'), P'.carrier = P.carrier ∧
        (∀ z ∈ S, ∃ j, P'.vertex j = z) ∧ (∀ i, ∃ j, P'.vertex j = P.vertex i)
  | [], m, P, _ => ⟨m, P, rfl, by simp, fun i => ⟨i, rfl⟩⟩
  | z :: S, m, P, hS => by
    obtain ⟨m₁, P₁, hcar₁, ⟨j₀, hj₀⟩, hold₁⟩ :=
      exists_prePolygon_insert P (hS z (List.mem_cons_self ..))
    obtain ⟨m₂, P₂, hcar₂, hnew₂, hold₂⟩ := exists_prePolygon_vertices S P₁
      (fun w hw => by rw [hcar₁]; exact hS w (List.mem_cons_of_mem _ hw))
    refine ⟨m₂, P₂, by rw [hcar₂, hcar₁], fun w hw => ?_, fun i => ?_⟩
    · rcases List.mem_cons.1 hw with rfl | hw'
      · obtain ⟨j, hj⟩ := hold₂ j₀
        exact ⟨j, by rw [hj, hj₀]⟩
      · exact hnew₂ w hw'
    · obtain ⟨j₁, hj₁⟩ := hold₁ i
      obtain ⟨j, hj⟩ := hold₂ j₁
      exact ⟨j, by rw [hj, hj₁]⟩

/-- A one-edge arc is that edge. -/
theorem arc_one {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) : P.arc a 1 = P.edge a := by
  ext z
  rw [mem_arc_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    obtain rfl : t = 0 := by omega
    rwa [Nat.cast_zero, add_zero] at hz
  · intro hz
    exact ⟨0, by omega, by rwa [Nat.cast_zero, add_zero]⟩

/-- **A vertex on an edge is one of that edge's own two ends.** -/
theorem vertex_mem_edge_elim {m : ℕ} {P : PrePolygon m} {c i : ZMod (m + 3)}
    (hc : P.vertex c ∈ P.edge i) :
    P.vertex c ∈ ({P.vertex i, P.vertex (i + 1)} : Set Plane) := by
  by_cases hci : c = i
  · exact Or.inl (by rw [hci])
  · exact P.edges_meet i c (Ne.symm hci) ⟨hc, left_mem_segment ℝ _ _⟩

end PrePolygon

/-! ## The realization theorem, with the cut points anywhere on the curve

`Schoenflies.exists_closedPolygon_split` requires the two cut points to be *corners*, and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` that requirement cannot be dropped while the
realization is a `ClosedPolygon`. For a `PrePolygon` there is no such obstruction: a point of the
curve is either already a vertex or interior to an edge, and an edge may be cut. -/

end Schoenflies
end

section
-- module Solutions.Q146_CD.OuterChain
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The outer face of a chain of plane graphs

`lem:outer-chain`. Let `Γ 0, …, Γ n` (`n ≥ 2`, so at least three graphs) be finite 2-connected
polygonal plane graphs, consecutive ones sharing at least two vertices and nonconsecutive ones
disjoint. If a point `x` is in the outer face of every consecutive pair `Γ p ∪ Γ (p+1)`, then it
is in the outer face of `Γ 0 ∪ ⋯ ∪ Γ n`.

## How the chain is formalised

The blueprint says "after subdividing common points into vertices". Here that is true by
construction rather than by a theorem: the family shares **one** ambient edge type `β` and
**one** drawing `drawing : β → ℝ → Plane`, and every member is a subgraph of a single plane
graph `G` — see `Graph.IsPlaneChain`. Two members therefore agree about the ends of a shared
edge, meet only where `G` lets them meet, and `Γ p ∪ Γ q` is `Graph.union` with nothing to
check. The ambient `G` is allowed to be larger than the chain's own union; a consumer that has
built all its pieces inside one polygonal overlay hands that overlay over as `G`.

`Graph.chainUnion Γ i m` is the block `Γ i ∪ Γ (i+1) ∪ ⋯ ∪ Γ (i+m)`, indexed by its **length**
`m` rather than by its right endpoint, so that the recursion is on `m` and the blueprint's
"choose `i ≤ j` with `j - i` minimum" is a plain strong induction on `m`. A consecutive pair is
`chainUnion Γ p 1`.

"`x` is in the outer face of `H`" is spelled, as everywhere in this development, as *`x` is off
the drawing and the face through it is unbounded* — `x ∈ exterior H drawing` together with
`¬ Bornology.IsBounded (face H drawing x)`. `Graph.unbounded_face_unique` is what makes that
"the" outer face, and `Graph.beyondSquare_subset_face` is how a consumer proves it.

## What is proved and what is assumed

The blueprint's proof is a minimal-counterexample argument on two measures: first the length of
the index interval, then the number of edges of the enclosing cycle lying outside `Γ (j-1)`.
Both minimisations are carried out here, as strong inductions, together with

* the reduction of "`x` lies in a bounded face" to "some cycle encloses `x`"
  (`Graph.encloses_of_isBounded_face`, from `Graph.face_cycles'`) and back
  (`Graph.isBounded_face_of_encloses`);
* 2-connectivity of every block, by iterating `Graph.IsTwoConnected.union`
  (`lem:union-two-connected`);
* the base case `j - i ≤ 1`, which is the blueprint's paragraph "If `j-i ≤ 1`, choose a
  consecutive pair `H` containing that union …";
* the two minimality consequences "`C` contains an edge of `Γ j` outside `Γ (j-1)`" and "`C`
  contains an edge of the earlier chain outside `Γ (j-1)`", each proved by pushing the cycle
  down into a shorter block with `Graph.IsCycleThrough.anti`;
* the splicing of a crosscut onto each of the two arcs (`Graph.exists_spliced_cycles`, from
  `Graph.exists_spliced_cycle`) and the edge count that makes the splice a strict improvement
  (`Graph.edgesOutside_splice_lt`, `Graph.exists_cycle_edgesOutside_lt`).

`Graph.Descent` is the middle paragraph of the blueprint's proof — from a cycle `C` of
`Γ i ∪ ⋯ ∪ Γ j` enclosing `x` and having an edge of `Γ j` and an edge of `Γ i ∪ ⋯ ∪ Γ (j-2)`
outside `Γ (j-1)`, produce a cycle of the same block enclosing `x` with strictly fewer edges
outside `Γ (j-1)`. It is a statement about **one** step, not about the chain's outer face.

It was assumed when this module was written. Both halves are now proved:

* `Schoenflies/CrosscutExists.lean` — combinatorial: build the crosscut, as
  `Graph.IsPlaneChain.crosscutExists`. Nothing geometric enters beyond
  `Graph.IsPlaneChain.disjoint_block_far`, "`Γ j` meets the earlier chain only through
  `Γ (j-1)`".
* `Schoenflies/CrosscutEncloses.lean` — geometric: "the path `R` lies on one side of `C` and is
  a crosscut there; by `thm:polygonal-crosscut`, at least one of `R ∪ C₁`, `R ∪ C₂` encloses
  `x`", as `Graph.crosscutEnclosesOff`. That module also carries the counterexample showing why
  the clause `x ∈ exterior H drawing` cannot be dropped — see the comment below, where the false
  version of it used to stand.

`Schoenflies/OuterChainClosed.lean` combines the two, and states `lem:outer-chain` with nothing
assumed.

## Blueprint

* `Graph.chainUnion` — `Γ i ∪ ⋯ ∪ Γ (i+m)`, with `chainUnion_le`, `le_chainUnion`,
  `chainUnion_finite`, `chainUnion_isTwoConnected` (the last is repeated
  `lem:union-two-connected`).
* `Graph.Encloses` — "that face is the interior of its boundary cycle, which therefore encloses
  `x`", as a property of a graph.
* `Graph.encloses_of_isBounded_face`, `Graph.isBounded_face_of_encloses` — the two directions
  of that reduction; the second is the blueprint's "the face of `H` containing `x` … lies in the
  bounded set `Int(C)` and therefore is not the outer face of `H`".
* `Graph.IsPlaneChain` — the hypotheses of `lem:outer-chain`; `Graph.OuterOnPairs` — its
  hypothesis on consecutive pairs.
* `Graph.IsCycleCrosscut` — the crosscut `R` of the cycle `C`, with the two arcs it cuts.
* `Graph.exists_spliced_cycles` — the two cycles `R ∪ C₁`, `R ∪ C₂`.
* `Graph.edgesOutside`, `Graph.edgesOutside_splice_lt`,
  `Graph.exists_cycle_edgesOutside_lt` — "it has fewer edges outside `Γ (j-1)` than `C`, since
  one nonempty outside portion of `C` has been replaced by `R ⊆ Γ (j-1)`".
* `Graph.Descent` — the crosscut paragraph of the proof; discharged in
  `Schoenflies/CrosscutEncloses.lean` from `Graph.CrosscutExists` alone.
* `Graph.IsPlaneChain.not_encloses` — the double minimisation.
* `Graph.IsPlaneChain.outer_chain` — **`lem:outer-chain`**, from `Graph.Descent`;
  `Graph.IsPlaneChain.outer_chain'` in `Schoenflies/OuterChainClosed.lean` is the same
  statement with nothing assumed.
-/

open Set Schoenflies
open scoped _root_.Graph

namespace Graph

/-! ## Blocks of a chain -/

section General

variable {α β : Type*} {Γ : ℕ → Graph α β} {G K : Graph α β} {i m p : ℕ}

/-- `chainUnion Γ i m` is `Γ i ∪ Γ (i+1) ∪ ⋯ ∪ Γ (i+m)`.

Indexed by the **length** `m` of the block rather than by its right endpoint: the blueprint
minimises `j - i`, and with this indexing that is a strong induction on the second argument
with no subtraction anywhere. -/
def chainUnion (Γ : ℕ → Graph α β) (i : ℕ) : ℕ → Graph α β
  | 0 => Γ i
  | m + 1 => (chainUnion Γ i m).union (Γ (i + m + 1))

@[simp]
theorem chainUnion_zero (Γ : ℕ → Graph α β) (i : ℕ) : chainUnion Γ i 0 = Γ i := rfl

@[simp]
theorem chainUnion_succ (Γ : ℕ → Graph α β) (i m : ℕ) :
    chainUnion Γ i (m + 1) = (chainUnion Γ i m).union (Γ (i + m + 1)) := rfl

/-! ### Reading a cycle inside a subgraph

`Graph.IsCycleThrough.anti` is the cycle counterpart of `Graph.IsPath.anti`; it is what turns
"no edge of `C` is outside this block" into "`C` is a cycle of this block". -/

/-! ### A crosscut of a cycle, with the two arcs it cuts

This is the combinatorial output of the blueprint's crosscut paragraph, bundled: the path `R` in
`F = Γ (j-1)`, its two endpoints `a, b` on the cycle, and the two arcs `D₁, D₂` the endpoints cut
the cycle into. Both arcs are required to carry an edge that `F` does not have — the blueprint's
"each arc contains an edge outside `Γ (j-1)`, because its endpoints belong to different maximal
subpaths of the intersection" — which is what makes the splice a strict improvement on **both**
sides, so that it does not matter which of the two spliced cycles turns out to enclose `x`. -/

/-- **A crosscut of a cycle.** `R` is a path of `H` between two vertices `a ≠ b` of the cycle
`e :: D`, lying in `F`, using no edge of the cycle and no vertex of it internally; `D₁, D₂` are
the two arcs the cycle splits into, each carrying an edge outside `F`. -/
structure IsCycleCrosscut (H F : Graph α β) (e : β) (u v : α) (D : List β) (a b : α)
    (R D₁ D₂ : List β) : Prop where
  /-- The two cut points are distinct. -/
  ne : a ≠ b
  /-- The first arc runs from `a` to `b`. -/
  arc₁ : H.IsPath a D₁ b
  /-- The second arc runs back. -/
  arc₂ : H.IsPath b D₂ a
  /-- Together the arcs use every edge of the cycle exactly once. -/
  split : (D₁ ++ D₂).Perm (e :: D)
  /-- The crosscut is a path between the two cut points. -/
  isPath : H.IsPath a R b
  /-- The first cut point is on the cycle. -/
  mem_left : a ∈ H.walkVertices u D
  /-- So is the second. -/
  mem_right : b ∈ H.walkVertices u D
  /-- The crosscut lies in `F`. -/
  edges_mem : ∀ g ∈ R, g ∈ E(F)
  /-- **"No edge of `R` is an edge of `C`."** -/
  edges_new : ∀ g ∈ R, g ∉ D ++ [e]
  /-- **"Its internal vertices do not lie on `C`."** -/
  interior : ∀ y ∈ H.walkVertices a R, y ≠ a → y ≠ b → y ∉ H.walkVertices u D
  /-- **"Each arc contains an edge outside `Γ (j-1)`."** -/
  outside₁ : ∃ g ∈ D₁, g ∉ E(F)
  /-- The same for the other arc. -/
  outside₂ : ∃ g ∈ D₂, g ∉ E(F)

/-- The edges of a walk that the graph `H` does not have. The second measure of the blueprint's
minimal-counterexample argument is the size of this set for `H = Γ (j-1)`. -/
def edgesOutside (H : Graph α β) (W : List β) : Set β := {g | g ∈ W ∧ g ∉ E(H)}

end General

/-! ## Enclosing a point -/

section Plane

variable {β : Type*} {H K : Graph Plane β} {drawing : β → ℝ → Plane} {x : Plane}

/-- **"That face is the interior of its boundary cycle, which therefore encloses `x`."** A graph
*encloses* a point when some cycle of it has that point in its interior. -/
def Encloses (H : Graph Plane β) (drawing : β → ℝ → Plane) (x : Plane) : Prop :=
  ∃ (e : β) (u v : Plane) (D : List β),
    H.IsCycleThrough e u v D ∧ x ∈ inside (edgesCover drawing (e :: D))

/-- A cycle of a subgraph encloses whatever it enclosed. -/
theorem Encloses.mono (hHK : H ≤ K) (h : Encloses H drawing x) : Encloses K drawing x := by
  obtain ⟨e, u, v, D, hc, hin⟩ := h
  exact ⟨e, u, v, D, ⟨hc.isLink.mono hHK, hc.isPath.mono hHK, hc.notMem⟩, hin⟩

end Plane

/-! ## The chain -/

section Chain

variable {β : Type*} {Γ : ℕ → Graph Plane β} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {n : ℕ} {x : Plane}

/-! ### The assumed step

Everything in the blueprint's proof except this one paragraph is discharged below. -/

/-- **The crosscut step of `lem:outer-chain`, assumed.**

Given a cycle `C` of the block `Γ i ∪ ⋯ ∪ Γ (i+m+2)` that encloses `x`, which has an edge of the
last member `Γ (i+m+2)` outside `Γ (i+m+1)` *and* an edge of the earlier chain
`Γ i ∪ ⋯ ∪ Γ (i+m)` outside `Γ (i+m+1)`, there is a cycle of the same block that encloses `x`
and has strictly fewer edges outside `Γ (i+m+1)`.

This is the blueprint's paragraph beginning "Minimality of the interval implies that `C`
contains an edge of `Γ j` outside `Γ (j-1)`": choose points `a, b` in the interiors of the two
edges; each of the two arcs of `C` from `a` to `b` must meet `Γ (j-1)`, because `Γ j` meets the
earlier chain only through `Γ (j-1)`; take the two maximal subpaths of `C ∩ Γ (j-1)` they
contain and a minimum-length path `R` in `Γ (j-1)` from one to the other; `R` is a crosscut of
the side of `C` it lies in, and `thm:polygonal-crosscut` says exactly one of `R ∪ C₁`, `R ∪ C₂`
encloses `x`. That cycle stays in the block, and one nonempty outside portion of `C` has been
replaced by `R ⊆ Γ (j-1)`.

It is a statement about a single descent step, not about outer faces, and it does not mention
`n` except to keep the block inside the chain. A discharging module has
`Graph.IsCycleThrough.split_at`, `Graph.exists_spliced_cycle`, `Graph.IsDrawing.arcs_of_split`
and `Schoenflies.crosscutSplitsRegion` available. -/
def Descent (Γ : ℕ → Graph Plane β) (drawing : β → ℝ → Plane) (n : ℕ) (x : Plane) : Prop :=
  ∀ (i m : ℕ), i + (m + 2) ≤ n →
    ∀ (e : β) (u v : Plane) (D : List β),
      (chainUnion Γ i (m + 2)).IsCycleThrough e u v D →
      x ∈ inside (edgesCover drawing (e :: D)) →
      (∃ g ∈ e :: D, g ∈ E(Γ (i + m + 2)) ∧ g ∉ E(Γ (i + m + 1))) →
      (∃ g ∈ e :: D, g ∈ E(chainUnion Γ i m) ∧ g ∉ E(Γ (i + m + 1))) →
      ∃ (e' : β) (u' v' : Plane) (D' : List β),
        (chainUnion Γ i (m + 2)).IsCycleThrough e' u' v' D' ∧
          x ∈ inside (edgesCover drawing (e' :: D')) ∧
          (edgesOutside (Γ (i + m + 1)) (e' :: D')).ncard <
            (edgesOutside (Γ (i + m + 1)) (e :: D)).ncard

/-! ### `Descent`, split into a combinatorial and a geometric half

`Graph.Descent` is what the main theorem consumes, and `Graph.descent_of_crosscut` derives it
from the two halves below, doing the splicing and the edge count in between. A module wishing to
discharge `Descent` may therefore prove these two instead, which is the natural division of
labour: `CrosscutExists` is a statement about walks in graphs with no geometry in it beyond the
disjointness of nonconsecutive members, and `CrosscutEncloses` is a statement about **one**
plane graph, **one** cycle and **one** crosscut, with no chain in it at all. -/

/-- **The combinatorial half of the descent step.** The blueprint's "choose points `a, b` in the
relative interiors of these two edges … each of those two arcs must meet `Γ (j-1)` … choose such
a path `R` of minimum length": from a cycle of the block enclosing `x` with an edge of the last
member and an edge of the earlier chain outside `Γ (j-1)`, build a crosscut of that cycle inside
`Γ (j-1)`.

The hypothesis that `x` is enclosed is carried along because it costs nothing and a discharger
may want it; the construction in the blueprint does not use it. -/
def CrosscutExists (Γ : ℕ → Graph Plane β) (drawing : β → ℝ → Plane) (n : ℕ) (x : Plane) :
    Prop :=
  ∀ (i m : ℕ), i + (m + 2) ≤ n →
    ∀ (e : β) (u v : Plane) (D : List β),
      (chainUnion Γ i (m + 2)).IsCycleThrough e u v D →
      x ∈ inside (edgesCover drawing (e :: D)) →
      (∃ g ∈ e :: D, g ∈ E(Γ (i + m + 2)) ∧ g ∉ E(Γ (i + m + 1))) →
      (∃ g ∈ e :: D, g ∈ E(chainUnion Γ i m) ∧ g ∉ E(Γ (i + m + 1))) →
      ∃ (a b : Plane) (R D₁ D₂ : List β),
        IsCycleCrosscut (chainUnion Γ i (m + 2)) (Γ (i + m + 1)) e u v D a b R D₁ D₂

/- The geometric half of the descent step **used to be stated here**, as `CrosscutEncloses`:
the same statement as `Graph.CrosscutEnclosesOff` in `Schoenflies/CrosscutEncloses.lean` but
without the clause `x ∈ exterior H drawing`. In that form it is FALSE, and it stood here as an
assumed hypothesis for a whole wave before anyone tried to prove it.

Nothing in its hypotheses stopped the crosscut from being drawn *through* `x`. Take the unit
square cycle with cut points `(0,0)` and `(1,1)`, let `R` be the two straight edges
`(0,0) → (1/2,1/2) → (1,1)` through a fresh vertex, and let `x = (2/5, 2/5)`. Every field of
`IsCycleCrosscut` holds and `x ∈ inside (edgesCover drawing (e :: D))`; but `x` lies *on* both
spliced curves, and `Schoenflies.mem_inside_iff` puts a point of a curve inside neither region.

The repair costs the consumer nothing, because `Graph.OuterOnPairs` already places `x` off the
whole chain: `Graph.IsPlaneChain.descent_of_crosscutOff` proves `Graph.Descent` below verbatim,
supplying the missing clause from `hout`. This is what the standing rule about naming a missing
result as an explicit hypothesis buys — the defect surfaced at the discharger, with a
counterexample, instead of as a `sorry` nobody revisited. -/

end Chain

end Graph
end

section
-- module Solutions.Q146_CD.CrosscutEncloses
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# `thm:polygonal-crosscut` at the level of sets, and the geometric half of the outer-chain descent

The blueprint sentence this module discharges is one line of the proof of `lem:outer-chain`:

> The path `R` lies on one side of `C` and is a crosscut there. By `thm:polygonal-crosscut`,
> exactly one of the two cycles `R ∪ C₁`, `R ∪ C₂` encloses `x`.

`Graph.CrosscutEncloses` of `Schoenflies/OuterChain.lean` is that sentence weakened to *at least*
one, which is all the descent uses; the weakening is not undone here.

## One theorem, no case split

The blueprint — and the note in `Schoenflies/OuterChain.lean` — distinguishes the crosscut running
inside `C` (settled by `Schoenflies.crosscutSplitsRegion`) from the crosscut running outside it
(`Schoenflies.IsPolygonalCrosscut.inside_exactly_one`). **Neither case distinction is needed.**
Both are consequences of Lemma 2.7, the parity identity

    π_{A₁ ∪ P} + π_{A₂ ∪ P} = π_J        at *every* point of the plane,

which holds with no geometry whatever (`Schoenflies.parity_split`), together with the *one*
direction of Theorem 2.3 that needs no realization of the two spliced curves:

    a closed chain whose cover separates has crossing count `0` on the unbounded region

(`Schoenflies.parity_eq_zero_of_mem_outside_cover`). If `x` were outside both spliced curves the
identity would read `0 + 0 = π_J(x)`, whereas `π_J(x) = 1` because `x` is inside `J`. That is the
whole proof of `Schoenflies.crosscut_inside_at_least_one`, and it is uniform in which side the
crosscut runs on. The `ClosedPolygon`-level `Schoenflies.IsPolygonalCrosscut.inside_exactly_one`,
whose `SameEdges` hypotheses cannot be met at graph vertices (see the section docstring of
`Schoenflies/FaceCyclesLand.lean`), is therefore not used at all.

The price is that the conclusion is "at least one" rather than "exactly one": the converse
direction of Theorem 2.3 for the spliced curves — `π = 1` forces the bounded region — *does* need
them realized, and the descent does not want it.

## The set-level statement is the artefact

`Schoenflies.crosscut_inside_at_least_one` takes sets and arcs, not polygons and not graphs:

    `J` a polygonal Jordan curve, `A₁, A₂` arcs from `p` to `q` covering it, `P` a polygonal arc
    from `p` to `q` meeting `J` only at `p, q`; then a point inside `J` and off `P` is inside
    `A₁ ∪ P` or inside `A₂ ∪ P`.

That is `thm:polygonal-crosscut` in the shape every plane-graph consumer wants, and
`Graph.crosscutEnclosesOff` is a two-page corollary of it. A second general fact falls out on the
way: `Schoenflies.two_arcs_inter_of_union` — two arcs with the same ends that cover a Jordan curve
meet **exactly** at those ends. That removes the "the two arcs meet only at the cut points" clause
from every consumer's obligations, which matters here because `Graph.IsCycleCrosscut` does not
record it (see below).

## Two defects of the interface handed to this module — read before integrating

**1. `Graph.CrosscutEncloses` as stated on `main` is false**, and the deliverable is
`Graph.CrosscutEnclosesOff`, which is it plus one hypothesis: `x ∈ exterior H drawing`. Nothing in
`Graph.CrosscutEncloses` prevents `x` from lying **on the crosscut's own drawing**: `x` is only
assumed to be inside the cycle `C`, and a crosscut running inside `C` may pass through `x`. Then
`x ∈ (A₁ ∪ P) ∩ (A₂ ∪ P)`, so `x` is inside neither spliced curve and the conclusion fails.

**The repair costs the chain nothing.** `Graph.OuterOnPairs` already puts `x` off the whole chain
(`Graph.IsPlaneChain.mem_exterior_chain`), and every block lies inside the chain
(`Graph.pointSet_mono`), so the clause can be produced where it is needed instead of being carried.
`Graph.IsPlaneChain.descent_of_crosscutOff` below therefore proves `Graph.Descent` **exactly as it
stands on `main`**, and `Graph.IsPlaneChain.outer_chain_of_crosscutExists` is `lem:outer-chain` with
`Graph.CrosscutEncloses` discharged outright. Nothing in `Schoenflies/OuterChain.lean` has to
change; `Graph.CrosscutEncloses` should simply be deleted, together with
`Graph.IsPlaneChain.descent_of_crosscut` and `Graph.IsPlaneChain.outer_chain_of_crosscut`, which the
two theorems here replace.

**2. `Graph.IsCycleCrosscut` does not record that the two arcs meet only at the two cut points**,
although `Graph.IsCycleThrough.split_at` — the theorem that builds them — produces exactly that
clause. It is not needed here, because `Schoenflies.two_arcs_inter_of_union` recovers the geometric
consequence from the Jordan curve; but a consumer that wants the *combinatorial* statement will
have to add the field.

## Blueprint

* `Schoenflies.two_arcs_inter_of_union` — §1: two arcs with the same ends covering a Jordan curve
  meet exactly at those ends. General; belongs beside `Schoenflies.two_arcs_unique` in
  `Schoenflies/Realization.lean`.
* `Schoenflies.crosscut_inside_at_least_one` — **`thm:polygonal-crosscut`**, at the level of sets:
  a point inside the curve and off the crosscut is inside one of the two spliced curves.
* `Graph.IsDrawing.mem_edgesCover_of_mem_walkVertices` — the converse of
  `Graph.IsDrawing.mem_walkVertices_of_mem_edgesCover`; general, belongs in
  `Schoenflies/Graph/CycleJordan.lean`.
* `Graph.CrosscutEnclosesOff`, `Graph.crosscutEnclosesOff` — the geometric half of the descent
  step of `lem:outer-chain`: `Graph.CrosscutEncloses` with the missing hypothesis restored,
  **proved**.
* `Graph.IsPlaneChain.descent_of_crosscutOff` — `Graph.Descent` from `Graph.CrosscutExists` alone;
  a drop-in replacement for `Graph.IsPlaneChain.descent_of_crosscut`.
* `Graph.IsPlaneChain.outer_chain_of_crosscutExists` — **`lem:outer-chain`**, assuming only the
  combinatorial half `Graph.CrosscutExists`.
-/

open Bornology Set

namespace Graph

open scoped Graph

open Schoenflies

variable {β : Type*} {H F : Graph Plane β} {drawing : β → ℝ → Plane}

/-! ## What a walk visits lies on what it draws

`Graph.IsDrawing.mem_walkVertices_of_mem_edgesCover` goes the other way; this direction is the
first half of the proof of `Graph.IsDrawing.pointSet_pathGraphOf`, extracted. -/

/-! ## The geometric half of the descent step

`Graph.CrosscutEncloses` of `Schoenflies/OuterChain.lean`, plus the hypothesis it is missing. -/

/-- **`Graph.CrosscutEncloses` with the clause it is missing**: `x` is off the drawing of `H`.

Without it the statement is false — see the module docstring. `Graph.CrosscutEncloses` puts `x`
inside the cycle `C` and nothing more, so a crosscut running inside `C` may pass through `x`; then
`x` lies on both spliced curves and is inside neither. Everything else is
`Graph.CrosscutEncloses` verbatim, so that the substitution into
`Graph.IsPlaneChain.descent_of_crosscut` is mechanical once `Graph.Descent` carries the same
clause. -/
def CrosscutEnclosesOff (drawing : β → ℝ → Plane) (x : Plane) : Prop :=
  ∀ (H F : Graph Plane β), H.Finite → IsDrawing H drawing →
    (∀ g ∈ E(H), IsPolygonal (edgeArc drawing g)) → x ∈ exterior H drawing →
    ∀ (e : β) (u v a b : Plane) (D R D₁ D₂ : List β),
      H.IsCycleThrough e u v D → IsCycleCrosscut H F e u v D a b R D₁ D₂ →
      x ∈ inside (edgesCover drawing (e :: D)) →
      ∀ (e₁ e₂ : β) (u₁ v₁ u₂ v₂ : Plane) (T₁ T₂ : List β),
        H.IsCycleThrough e₁ u₁ v₁ T₁ → H.IsCycleThrough e₂ u₂ v₂ T₂ →
        (e₁ :: T₁).Perm (D₁ ++ R) → (e₂ :: T₂).Perm (D₂ ++ R) →
        x ∈ inside (edgesCover drawing (e₁ :: T₁)) ∨
          x ∈ inside (edgesCover drawing (e₂ :: T₂))

/-! ## `lem:outer-chain` needs only the combinatorial half now

The extra hypothesis of `Graph.CrosscutEnclosesOff` does **not** have to be threaded through
`Graph.Descent`: the chain hypothesis `Graph.OuterOnPairs` already puts `x` off the whole chain
(`Graph.IsPlaneChain.mem_exterior_chain`), and every block of the chain lies inside it. So the
repair costs the interface nothing at all — `Graph.Descent` is used here exactly as it stands on
`main`, and the two theorems below are drop-in replacements for
`Graph.IsPlaneChain.descent_of_crosscut` and `Graph.IsPlaneChain.outer_chain_of_crosscut` with
`Graph.CrosscutEncloses` discharged. -/

end Graph
end

section
-- module Solutions.Q146_CD.Graph_K33
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The utility graph `K(3,3)` inside a plane graph

The blueprint's proof of `lem:k33` is four sentences: regard `K(3,3)` as the six-cycle
`x₀y₀x₁y₁x₂y₂x₀` together with the three remaining edges `x₀y₁, x₁y₂, x₂y₀`; the six-cycle is
a Jordan curve; each remaining edge lies wholly on one side of it; two of the three lie on the
same side, and their endpoints alternate on the six-cycle, contrary to
`cor:alternating-crosscuts`.

**Everything in that proof except the last two citations is established here.** What is left is
the polygonal Jordan curve theorem — which supplies "the two sides" — and the alternating
crosscut corollary itself; neither exists yet, so `lem:k33` is not stated. See the note at the
end of this docstring for exactly how the last step will read.

## `K(3,3)` is a configuration, not a graph

There is no `K33 : Graph α β`. A copy of `K(3,3)` inside `G` is `Graph.IsK33Config G x y e`:
six vertices `x 0, x 1, x 2, y 0, y 1, y 2`, all distinct, and nine edge names `e i j` with
`e i j` linking `x i` to `y j`. Nothing says `G` has no other vertex or edge.

This is the shape the theorem is used in — one always *finds* a `K(3,3)` inside a graph one
already has, never constructs the abstract one — and it is also what makes the drawing
hypothesis land correctly: `Graph.IsDrawing G drawing` is a hypothesis about all of `G`, so
taking `G` larger only strengthens it.

Two economies follow from stating the configuration this way. The nine edge names are
automatically distinct (`Graph.IsK33Config.eq_of_e_eq`): an edge has only two ends, so two
names coinciding would force the index pairs to agree. And no looplessness clause is needed:
`x i ≠ y j` is one of the four fields.

## The indexing is arithmetic in `Fin 3`, so that `decide` can do the bookkeeping

The six-cycle uses the edges `e i i` and `e (i+1) i`; the three remaining edges are
`e s (s+1)` for `s : Fin 3`. Every combinatorial side condition below — that a remaining edge
is not a cycle edge, that the two arcs of the cut cycle cover it and meet only at the cut
points — is a statement about index pairs quantified over `Fin 3`, and is discharged by
`decide`. The edges themselves never have to be compared.

The two arcs into which the ends of the remaining edge `e s (s+1)` cut the six-cycle are named
by their index pairs as well (`Graph.arcAPairs`, `Graph.arcBPairs`); `Graph.arcA` and
`Graph.arcB` are the corresponding edge lists, `rfl`-equal to the mapped pair lists so that
both presentations are available with no conversion lemma.

## Blueprint

* `Graph.IsK33Config` — a copy of the utility graph.
* `Graph.IsK33Config.hexagon_isCycleThrough` — §"Plane graphs and the utility graph": "regard
  `K(3,3)` as the six-cycle `x₁y₁x₂y₂x₃y₃x₁` together with the three remaining edges".
* `Graph.IsK33Config.hexagon_isJordanCurve` — `lem:k33`, "the six-cycle is a polygonal Jordan
  curve". Polygonality plays no part; it is needed only where the *polygonal* Jordan curve
  theorem is applied to the result.
* `Graph.IsK33Config.chord_inter_hexSet`, `Graph.IsK33Config.chord_openArc_eq`,
  `Graph.IsK33Config.chord_openArc_subset_connectedComponentIn` — `lem:k33`, "each remaining
  edge lies wholly on one side": a remaining edge meets the six-cycle in exactly its own two
  ends, so its interior is a connected subset of the complement, hence lies in one component.
  This is also the crosscut hypothesis of `thm:polygonal-crosscut` and
  `cor:alternating-crosscuts`.
* `Graph.IsK33Config.exists_two_chords_same_side` — `lem:k33`, "two of the three lie on the
  same side". The two sides arrive as an arbitrary pair of disjoint open sets covering the
  complement, which is the form `thm:polygonal-jordan` will supply them in.
* `Graph.IsK33Config.chords_alternate` — `lem:k33`, "their endpoints alternate on the
  six-cycle", in the form `cor:alternating-crosscuts` consumes: the ends of one remaining edge
  cut the cycle into two arcs meeting only at those ends, and the two ends of another remaining
  edge lie one interior to each. Every pair of remaining edges is of the form `(s, s+1)`, so
  the single index `s` covers all three pairs.
* `Graph.IsK33Config.chords_disjoint` — the disjointness that `cor:alternating-crosscuts`
  contradicts: two remaining edges have four distinct ends, and distinct edges of a plane graph
  meet only at a shared end.

**How `lem:k33` will close.** Given a plane drawing of a graph with a `K(3,3)` configuration,
make it polygonal (`Graph.polygonal_redrawing`, `lem:polygonal-redrawing`); the six-cycle is
then a polygonal Jordan curve, and `thm:polygonal-jordan` gives the two disjoint open sides
that `exists_two_chords_same_side` wants. It returns two remaining edges on the same side;
`chords_alternate` says their ends alternate, so `cor:alternating-crosscuts` makes them meet,
and `chords_disjoint` says they do not.
-/

open Set Schoenflies unitInterval
open scoped _root_.Graph

namespace Graph

variable {α β : Type*} {G : Graph α β} {x y : Fin 3 → α} {e : Fin 3 → Fin 3 → β}
variable {i j k l s t : Fin 3} {z : α}

/-- A copy of the utility graph `K(3,3)` inside `G`. -/
structure IsK33Config (G : Graph α β) (x y : Fin 3 → α) (e : Fin 3 → Fin 3 → β) : Prop where
  /-- `e i j` joins the `i`-th vertex of one side to the `j`-th vertex of the other. -/
  isLink : ∀ i j, G.IsLink (e i j) (x i) (y j)
  /-- The three vertices of the first side are distinct. -/
  x_injective : Function.Injective x
  /-- The three vertices of the second side are distinct. -/
  y_injective : Function.Injective y
  /-- The two sides are disjoint. -/
  ne : ∀ i j, x i ≠ y j

namespace IsK33Config

theorem x_ne_x (h : IsK33Config G x y e) (hik : i ≠ k) : x i ≠ x k :=
  fun he ↦ hik (h.x_injective he)

theorem y_ne_y (h : IsK33Config G x y e) (hjl : j ≠ l) : y j ≠ y l :=
  fun he ↦ hjl (h.y_injective he)

theorem x_ne_y (h : IsK33Config G x y e) (i j : Fin 3) : x i ≠ y j := h.ne i j

theorem y_ne_x (h : IsK33Config G x y e) (j i : Fin 3) : y j ≠ x i := (h.ne i j).symm

/-- **The nine edges carry nine different names.** This is not an axiom of the configuration:
an edge has only two ends, so two of the nine names being equal would force the two index
pairs to agree. -/
theorem eq_of_e_eq (h : IsK33Config G x y e) (heq : e i j = e k l) : i = k ∧ j = l := by
  have h' : G.IsLink (e i j) (x k) (y l) := by rw [heq]; exact h.isLink k l
  rcases (h.isLink i j).eq_and_eq_or_eq_and_eq h' with ⟨h1, h2⟩ | ⟨h1, -⟩
  · exact ⟨h.x_injective h1, h.y_injective h2⟩
  · exact absurd h1 (h.ne i l)

theorem e_ne (h : IsK33Config G x y e) (hne : ¬ (i = k ∧ j = l)) : e i j ≠ e k l :=
  fun heq ↦ hne (h.eq_of_e_eq heq)

/-- A vertex on one of the nine edges is one of that edge's two ends. -/
theorem inc_elim (h : IsK33Config G x y e) (hz : G.Inc (e i j) z) : z = x i ∨ z = y j :=
  hz.eq_or_eq_of_isLink (h.isLink i j)

/-- **Freshness, in the form the path constructor asks for.** A vertex which is neither the
source of the rest of the walk nor an end of any of its edges is not among the vertices that
rest visits. -/
theorem notMem_walkVertices (h : IsK33Config G x y e) {W : List β} {w : α} (hzw : z ≠ w)
    (hW : ∀ f ∈ W, ∃ i j, f = e i j ∧ z ≠ x i ∧ z ≠ y j) :
    z ∉ G.walkVertices w W := by
  intro hz
  rcases mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, hinc⟩
  · exact hzw rfl
  obtain ⟨i, j, rfl, hxi, hyj⟩ := hW f hf
  rcases h.inc_elim hinc with hh | hh
  exacts [hxi hh, hyj hh]

end IsK33Config

/-! ### The six-cycle

The blueprint reads `K(3,3)` as the six-cycle `x₀y₀x₁y₁x₂y₂x₀` together with the three
remaining edges. The cycle is presented as `Schoenflies/Graph/Cycle.lean` presents one:
through the edge `e 0 0`, with a detour path running the other way round. -/

/-- The index pairs of the six edges of the six-cycle, in the order the cycle is traversed
starting from `e 0 0`. Kept as index pairs, not as edges, because every question about which
edges the cycle uses is then decidable. -/
def hexPairs : List (Fin 3 × Fin 3) := [(0, 0), (0, 2), (2, 2), (2, 1), (1, 1), (1, 0)]

/-- The five edges of the detour of the six-cycle: the path
`x₀ → y₂ → x₂ → y₁ → x₁ → y₀` that returns to the other end of `e 0 0`. -/
def hexDetour (e : Fin 3 → Fin 3 → β) : List β := [e 0 2, e 2 2, e 2 1, e 1 1, e 1 0]

/-- The six edges of the six-cycle. -/
def hexList (e : Fin 3 → Fin 3 → β) : List β := e 0 0 :: hexDetour e

theorem hexList_eq_map (e : Fin 3 → Fin 3 → β) :
    hexList e = hexPairs.map fun p ↦ e p.1 p.2 := rfl

theorem mem_hexList_iff {f : β} : f ∈ hexList e ↔ ∃ p ∈ hexPairs, f = e p.1 p.2 := by
  rw [hexList_eq_map]
  simp only [List.mem_map, eq_comm]

namespace IsK33Config

/-- The detour of the six-cycle is a path. Each freshness clause says that the vertex a step
departs from is none of the six vertices the rest of the detour meets. -/
theorem hexDetour_isPath (h : IsK33Config G x y e) : G.IsPath (x 0) (hexDetour e) (y 0) := by
  have h5 : G.IsPath (x 1) [e 1 0] (y 0) := .single (h.isLink 1 0) (h.x_ne_y 1 0)
  have h4 : G.IsPath (y 1) [e 1 1, e 1 0] (y 0) := by
    refine .cons (h.isLink 1 1).symm h5 (h.notMem_walkVertices (h.y_ne_x 1 1) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl
    exact ⟨1, 0, rfl, h.y_ne_x 1 1, h.y_ne_y (by decide)⟩
  have h3 : G.IsPath (x 2) [e 2 1, e 1 1, e 1 0] (y 0) := by
    refine .cons (h.isLink 2 1) h4 (h.notMem_walkVertices (h.x_ne_y 2 1) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨1, 1, rfl, h.x_ne_x (by decide), h.x_ne_y 2 1⟩
    · exact ⟨1, 0, rfl, h.x_ne_x (by decide), h.x_ne_y 2 0⟩
  have h2 : G.IsPath (y 2) [e 2 2, e 2 1, e 1 1, e 1 0] (y 0) := by
    refine .cons (h.isLink 2 2).symm h3 (h.notMem_walkVertices (h.y_ne_x 2 2) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact ⟨2, 1, rfl, h.y_ne_x 2 2, h.y_ne_y (by decide)⟩
    · exact ⟨1, 1, rfl, h.y_ne_x 2 1, h.y_ne_y (by decide)⟩
    · exact ⟨1, 0, rfl, h.y_ne_x 2 1, h.y_ne_y (by decide)⟩
  refine .cons (h.isLink 0 2) h2 (h.notMem_walkVertices (h.x_ne_y 0 2) ?_)
  rintro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨2, 2, rfl, h.x_ne_x (by decide), h.x_ne_y 0 2⟩
  · exact ⟨2, 1, rfl, h.x_ne_x (by decide), h.x_ne_y 0 1⟩
  · exact ⟨1, 1, rfl, h.x_ne_x (by decide), h.x_ne_y 0 1⟩
  · exact ⟨1, 0, rfl, h.x_ne_x (by decide), h.x_ne_y 0 0⟩

/-- **The six-cycle is a cycle**, presented through the edge `e 0 0`. -/
theorem hexagon_isCycleThrough (h : IsK33Config G x y e) :
    G.IsCycleThrough (e 0 0) (x 0) (y 0) (hexDetour e) := by
  refine ⟨h.isLink 0 0, h.hexDetour_isPath, ?_⟩
  simp only [hexDetour, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h.e_ne (by decide), h.e_ne (by decide), h.e_ne (by decide), h.e_ne (by decide),
    h.e_ne (by decide)⟩

/-! ### The three remaining edges

`e s (s+1)`, for `s : Fin 3`, are the three edges of `K(3,3)` that the six-cycle leaves out. -/

/-- The three remaining edges are not edges of the six-cycle. -/
theorem chord_notMem_hexList (h : IsK33Config G x y e) (s : Fin 3) : e s (s + 1) ∉ hexList e := by
  intro hmem
  obtain ⟨p, hp, heq⟩ := mem_hexList_iff.1 hmem
  have key : ∀ (s : Fin 3) (p : Fin 3 × Fin 3), p ∈ hexPairs → ¬ (s = p.1 ∧ s + 1 = p.2) := by
    decide
  exact key s p hp (h.eq_of_e_eq heq)

/-- Two distinct remaining edges carry distinct names, and share no end. -/
theorem chord_ne (h : IsK33Config G x y e) (hst : s ≠ t) : e s (s + 1) ≠ e t (t + 1) :=
  h.e_ne (fun hc ↦ hst hc.1)

/-- The edges of the six-cycle are edges of the graph. -/
theorem hexList_edge_mem (h : IsK33Config G x y e) {f : β} (hf : f ∈ hexList e) : f ∈ E(G) := by
  obtain ⟨p, -, rfl⟩ := mem_hexList_iff.1 hf
  exact (h.isLink p.1 p.2).edge_mem

end IsK33Config

theorem mem_hexList (e : Fin 3 → Fin 3 → β) {p : Fin 3 × Fin 3} (hp : p ∈ hexPairs) :
    e p.1 p.2 ∈ hexList e :=
  mem_hexList_iff.2 ⟨p, hp, rfl⟩

/-! ### The six-cycle cut at the ends of one remaining edge

The two ends of the remaining edge `e s (s+1)` are `x s` and `y (s+1)`, and they cut the
six-cycle into two paths: `x s → y s → x (s+1) → y (s+1)` and
`x s → y (s+2) → x (s+2) → y (s+1)`. The other two remaining edges each have one end interior
to the first and one end interior to the second — this is the blueprint's "their endpoints
alternate on the six-cycle". -/

/-- Index pairs of the first of the two paths the ends of `e s (s+1)` cut the six-cycle into. -/
def arcAPairs (s : Fin 3) : List (Fin 3 × Fin 3) := [(s, s), (s + 1, s), (s + 1, s + 1)]

/-- Index pairs of the second of the two paths. -/
def arcBPairs (s : Fin 3) : List (Fin 3 × Fin 3) := [(s, s + 2), (s + 2, s + 2), (s + 2, s + 1)]

/-- The edges of the first path. -/
def arcA (e : Fin 3 → Fin 3 → β) (s : Fin 3) : List β := [e s s, e (s + 1) s, e (s + 1) (s + 1)]

/-- The edges of the second path. -/
def arcB (e : Fin 3 → Fin 3 → β) (s : Fin 3) : List β :=
  [e s (s + 2), e (s + 2) (s + 2), e (s + 2) (s + 1)]

theorem arcA_eq_map (e : Fin 3 → Fin 3 → β) (s : Fin 3) :
    arcA e s = (arcAPairs s).map fun p ↦ e p.1 p.2 := rfl

theorem arcB_eq_map (e : Fin 3 → Fin 3 → β) (s : Fin 3) :
    arcB e s = (arcBPairs s).map fun p ↦ e p.1 p.2 := rfl

namespace IsK33Config

/-- The first of the two paths is a path. -/
theorem arcA_isPath (h : IsK33Config G x y e) (s : Fin 3) :
    G.IsPath (x s) (arcA e s) (y (s + 1)) := by
  have hab : s ≠ s + 1 := by revert s; decide
  have p3 : G.IsPath (x (s + 1)) [e (s + 1) (s + 1)] (y (s + 1)) :=
    .single (h.isLink (s + 1) (s + 1)) (h.x_ne_y _ _)
  have p2 : G.IsPath (y s) [e (s + 1) s, e (s + 1) (s + 1)] (y (s + 1)) := by
    refine .cons (h.isLink (s + 1) s).symm p3 (h.notMem_walkVertices (h.y_ne_x _ _) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl
    exact ⟨s + 1, s + 1, rfl, h.y_ne_x _ _, h.y_ne_y hab⟩
  refine .cons (h.isLink s s) p2 (h.notMem_walkVertices (h.x_ne_y _ _) ?_)
  rintro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨s + 1, s, rfl, h.x_ne_x hab, h.x_ne_y _ _⟩
  · exact ⟨s + 1, s + 1, rfl, h.x_ne_x hab, h.x_ne_y _ _⟩

/-- The second of the two paths is a path. -/
theorem arcB_isPath (h : IsK33Config G x y e) (s : Fin 3) :
    G.IsPath (x s) (arcB e s) (y (s + 1)) := by
  have hac : s ≠ s + 2 := by revert s; decide
  have hcb : s + 2 ≠ s + 1 := by revert s; decide
  have q3 : G.IsPath (x (s + 2)) [e (s + 2) (s + 1)] (y (s + 1)) :=
    .single (h.isLink (s + 2) (s + 1)) (h.x_ne_y _ _)
  have q2 : G.IsPath (y (s + 2)) [e (s + 2) (s + 2), e (s + 2) (s + 1)] (y (s + 1)) := by
    refine .cons (h.isLink (s + 2) (s + 2)).symm q3 (h.notMem_walkVertices (h.y_ne_x _ _) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl
    exact ⟨s + 2, s + 1, rfl, h.y_ne_x _ _, h.y_ne_y hcb⟩
  refine .cons (h.isLink s (s + 2)) q2 (h.notMem_walkVertices (h.x_ne_y _ _) ?_)
  rintro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨s + 2, s + 2, rfl, h.x_ne_x hac, h.x_ne_y _ _⟩
  · exact ⟨s + 2, s + 1, rfl, h.x_ne_x hac, h.x_ne_y _ _⟩

end IsK33Config

end Graph

/-! ## The six-cycle drawn in the plane

Everything from here on is about a *drawing* of the configuration. Nothing in this section
uses more geometry than the three clauses of `Graph.IsDrawing`. -/

namespace Graph

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s t : Fin 3}

/-- The point set of the six-cycle of a drawn `K(3,3)`. -/
def hexSet (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) : Set Plane :=
  edgesCover drawing (hexList e)

theorem mem_edgesCover_map_iff {L : List (Fin 3 × Fin 3)} {p : Plane} :
    p ∈ edgesCover drawing (L.map fun q ↦ e q.1 q.2) ↔
      ∃ q ∈ L, p ∈ edgeArc drawing (e q.1 q.2) := by
  constructor
  · intro hp
    obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hf
    exact ⟨q, hq, hpf⟩
  · rintro ⟨q, hq, hpq⟩
    exact mem_edgesCover (List.mem_map_of_mem hq) hpq

theorem mem_hexSet_iff {p : Plane} :
    p ∈ hexSet drawing e ↔ ∃ q ∈ hexPairs, p ∈ edgeArc drawing (e q.1 q.2) := by
  rw [hexSet, hexList_eq_map]; exact mem_edgesCover_map_iff

theorem mem_arcA_iff {p : Plane} :
    p ∈ edgesCover drawing (arcA e s) ↔ ∃ q ∈ arcAPairs s, p ∈ edgeArc drawing (e q.1 q.2) := by
  rw [arcA_eq_map]; exact mem_edgesCover_map_iff

theorem mem_arcB_iff {p : Plane} :
    p ∈ edgesCover drawing (arcB e s) ↔ ∃ q ∈ arcBPairs s, p ∈ edgeArc drawing (e q.1 q.2) := by
  rw [arcB_eq_map]; exact mem_edgesCover_map_iff

namespace IsK33Config

/-- **The six-cycle of a drawn `K(3,3)` is a Jordan curve.** This is the blueprint's "the
six-cycle is a polygonal Jordan curve"; polygonality plays no part in it, and is needed only
where the *polygonal* Jordan curve theorem is applied to the result. -/
theorem hexagon_isJordanCurve (h : IsK33Config G x y e) (hd : IsDrawing G drawing) :
    IsJordanCurve (hexSet drawing e) :=
  hd.cycle_isJordanCurve h.hexagon_isCycleThrough

/-- The `i`-th vertex of the first side lies on the six-cycle. -/
theorem x_mem_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (i : Fin 3) :
    x i ∈ hexSet drawing e := by
  have hp : ∀ i : Fin 3, ((i, i) : Fin 3 × Fin 3) ∈ hexPairs := by decide
  exact mem_edgesCover (mem_hexList e (hp i)) (hd.edge_isArcBetween (h.isLink i i)).left_mem

/-- The `j`-th vertex of the second side lies on the six-cycle. -/
theorem y_mem_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (j : Fin 3) :
    y j ∈ hexSet drawing e := by
  have hp : ∀ j : Fin 3, ((j, j) : Fin 3 × Fin 3) ∈ hexPairs := by decide
  exact mem_edgesCover (mem_hexList e (hp j)) (hd.edge_isArcBetween (h.isLink j j)).right_mem

/-- **Each of the three remaining edges is a crosscut of the six-cycle**: its arc meets the
cycle in exactly its own two ends. -/
theorem chord_inter_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    edgeArc drawing (e s (s + 1)) ∩ hexSet drawing e = {x s, y (s + 1)} := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro p ⟨hpe, hph⟩
    obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hph
    have hne : e s (s + 1) ≠ f := fun hc ↦ h.chord_notMem_hexList s (hc ▸ hf)
    obtain ⟨-, hinc, -⟩ :=
      hd.edge_inter (h.isLink s (s + 1)).edge_mem (h.hexList_edge_mem hf) hne hpe hpf
    exact h.inc_elim hinc
  · rintro p (rfl | rfl)
    · exact ⟨(hd.edge_isArcBetween (h.isLink s (s + 1))).left_mem, h.x_mem_hexSet hd s⟩
    · exact ⟨(hd.edge_isArcBetween (h.isLink s (s + 1))).right_mem, h.y_mem_hexSet hd (s + 1)⟩

/-- The interior of a remaining edge, as the blueprint reads it: its arc without its two
ends. -/
theorem chord_openArc_eq (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    openArc (drawing (e s (s + 1))) = edgeArc drawing (e s (s + 1)) \ {x s, y (s + 1)} := by
  obtain ⟨-, hi, hlink⟩ := hd.edge_param (h.isLink s (s + 1)).edge_mem
  have hpair : ({drawing (e s (s + 1)) 0, drawing (e s (s + 1)) 1} : Set Plane)
      = {x s, y (s + 1)} := by
    rcases hlink.eq_and_eq_or_eq_and_eq (h.isLink s (s + 1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Set.pair_comm]
  rw [openArc_eq_diff hi, hpair]
  rfl

/-- **A remaining edge lies wholly off the six-cycle except at its ends.** -/
theorem chord_openArc_subset_compl (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (s : Fin 3) : openArc (drawing (e s (s + 1))) ⊆ (hexSet drawing e)ᶜ := by
  rw [h.chord_openArc_eq hd s]
  rintro p ⟨hpe, hpn⟩ hph
  exact hpn ((h.chord_inter_hexSet hd s).subset ⟨hpe, hph⟩)

theorem chord_openArc_isPreconnected (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (s : Fin 3) : IsPreconnected (openArc (drawing (e s (s + 1)))) :=
  isPreconnected_Ioo.image _
    ((hd.edge_param (h.isLink s (s + 1)).edge_mem).1.mono Ioo_subset_I)

theorem chord_openArc_nonempty (s : Fin 3) :
    (openArc (drawing (e s (s + 1)))).Nonempty :=
  ⟨drawing (e s (s + 1)) (1 / 2), 1 / 2, by norm_num, rfl⟩

/-- **Each of the three remaining edges lies wholly on one side of the six-cycle**: its
interior, being connected and disjoint from the cycle, lies in a single connected component of
the complement. -/
theorem chord_openArc_subset_connectedComponentIn (h : IsK33Config G x y e)
    (hd : IsDrawing G drawing) (s : Fin 3) {p : Plane}
    (hp : p ∈ openArc (drawing (e s (s + 1)))) :
    openArc (drawing (e s (s + 1))) ⊆ connectedComponentIn (hexSet drawing e)ᶜ p :=
  (h.chord_openArc_isPreconnected hd s).subset_connectedComponentIn hp
    (h.chord_openArc_subset_compl hd s)

/-- **Two distinct remaining edges are disjoint.** Their four ends are distinct, and two
distinct edges of a plane graph meet only at a shared end. -/
theorem chords_disjoint (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (hst : s ≠ t) :
    edgeArc drawing (e s (s + 1)) ∩ edgeArc drawing (e t (t + 1)) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p ⟨hps, hpt⟩ ↦ ?_
  obtain ⟨-, hincs, hinct⟩ := hd.edge_inter (h.isLink s (s + 1)).edge_mem
    (h.isLink t (t + 1)).edge_mem (h.chord_ne hst) hps hpt
  have hne1 : s ≠ t := hst
  have hne2 : s + 1 ≠ t + 1 := fun hc ↦ hst (by simpa using hc)
  rcases h.inc_elim hincs with rfl | rfl <;> rcases h.inc_elim hinct with hh | hh
  · exact (h.x_ne_x hne1) hh
  · exact (h.x_ne_y s (t + 1)) hh
  · exact (h.y_ne_x (s + 1) t) hh
  · exact (h.y_ne_y hne2) hh

/-! ### The two arcs the ends of a remaining edge cut the six-cycle into -/

theorem arcA_isArcBetween (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    IsArcBetween (edgesCover drawing (arcA e s)) (x s) (y (s + 1)) :=
  hd.path_isArcBetween (h.arcA_isPath s) (by simp [arcA])

theorem arcB_isArcBetween (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    IsArcBetween (edgesCover drawing (arcB e s)) (x s) (y (s + 1)) :=
  hd.path_isArcBetween (h.arcB_isPath s) (by simp [arcB])

/-- **The two arcs make up the six-cycle.** -/
theorem arcs_union (s : Fin 3) :
    edgesCover drawing (arcA e s) ∪ edgesCover drawing (arcB e s) = hexSet drawing e := by
  have hA : ∀ s : Fin 3, ∀ q ∈ arcAPairs s, q ∈ hexPairs := by decide
  have hB : ∀ s : Fin 3, ∀ q ∈ arcBPairs s, q ∈ hexPairs := by decide
  have hC : ∀ s : Fin 3, ∀ q ∈ hexPairs, q ∈ arcAPairs s ∨ q ∈ arcBPairs s := by decide
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro p (hp | hp)
    · obtain ⟨q, hq, hpq⟩ := mem_arcA_iff.1 hp
      exact mem_hexSet_iff.2 ⟨q, hA s q hq, hpq⟩
    · obtain ⟨q, hq, hpq⟩ := mem_arcB_iff.1 hp
      exact mem_hexSet_iff.2 ⟨q, hB s q hq, hpq⟩
  · intro p hp
    obtain ⟨q, hq, hpq⟩ := mem_hexSet_iff.1 hp
    rcases hC s q hq with hq' | hq'
    exacts [Or.inl (mem_arcA_iff.2 ⟨q, hq', hpq⟩), Or.inr (mem_arcB_iff.2 ⟨q, hq', hpq⟩)]

/-- **The two arcs meet exactly in the two ends of the remaining edge that cuts the cycle.** -/
theorem arcs_inter (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    edgesCover drawing (arcA e s) ∩ edgesCover drawing (arcB e s) = {x s, y (s + 1)} := by
  have hne : ∀ s : Fin 3, ∀ q ∈ arcAPairs s, ∀ r ∈ arcBPairs s, ¬ (q.1 = r.1 ∧ q.2 = r.2) := by
    decide
  have h1 : ∀ s : Fin 3, ∀ q ∈ arcAPairs s, ∀ r ∈ arcBPairs s, q.1 = r.1 → q.1 = s := by decide
  have h2 : ∀ s : Fin 3, ∀ q ∈ arcAPairs s, ∀ r ∈ arcBPairs s, q.2 = r.2 → q.2 = s + 1 := by
    decide
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro p ⟨hpA, hpB⟩
    obtain ⟨q, hq, hpq⟩ := mem_arcA_iff.1 hpA
    obtain ⟨r, hr, hpr⟩ := mem_arcB_iff.1 hpB
    obtain ⟨-, hincq, hincr⟩ := hd.edge_inter (h.isLink q.1 q.2).edge_mem
      (h.isLink r.1 r.2).edge_mem (h.e_ne (hne s q hq r hr)) hpq hpr
    rcases h.inc_elim hincq with hh | hh <;> rcases h.inc_elim hincr with hh' | hh'
    · exact Or.inl (hh.trans (by rw [h1 s q hq r hr (h.x_injective (hh.symm.trans hh'))]))
    · exact absurd (hh.symm.trans hh') (h.x_ne_y _ _)
    · exact absurd (hh.symm.trans hh') (h.y_ne_x _ _)
    · exact Or.inr (hh.trans (by rw [h2 s q hq r hr (h.y_injective (hh.symm.trans hh'))]))
  · rintro p (rfl | rfl)
    · exact ⟨mem_arcA_iff.2 ⟨(s, s), by simp [arcAPairs],
        (hd.edge_isArcBetween (h.isLink s s)).left_mem⟩,
        mem_arcB_iff.2 ⟨(s, s + 2), by simp [arcBPairs],
          (hd.edge_isArcBetween (h.isLink s (s + 2))).left_mem⟩⟩
    · exact ⟨mem_arcA_iff.2 ⟨(s + 1, s + 1), by simp [arcAPairs],
        (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1))).right_mem⟩,
        mem_arcB_iff.2 ⟨(s + 2, s + 1), by simp [arcBPairs],
          (hd.edge_isArcBetween (h.isLink (s + 2) (s + 1))).right_mem⟩⟩

/-! ### Two of the three remaining edges lie on the same side -/

/-- A remaining edge lies wholly in one of two disjoint open sets covering the complement of
the six-cycle: its interior is connected and misses the cycle. -/
theorem chord_subset_or (h : IsK33Config G x y e) (hd : IsDrawing G drawing) {U V : Set Plane}
    (hUo : IsOpen U) (hVo : IsOpen V) (hUV : Disjoint U V)
    (hcover : (hexSet drawing e)ᶜ ⊆ U ∪ V) (s : Fin 3) :
    openArc (drawing (e s (s + 1))) ⊆ U ∨ openArc (drawing (e s (s + 1))) ⊆ V := by
  have hsub : openArc (drawing (e s (s + 1))) ⊆ U ∪ V :=
    (h.chord_openArc_subset_compl hd s).trans hcover
  obtain ⟨p, hp⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  rcases hsub hp with hpU | hpV
  · exact Or.inl ((h.chord_openArc_isPreconnected hd s).subset_left_of_subset_union
      hUo hVo hUV hsub ⟨p, hp, hpU⟩)
  · refine Or.inr ((h.chord_openArc_isPreconnected hd s).subset_left_of_subset_union
      hVo hUo hUV.symm (hsub.trans (by rw [Set.union_comm])) ⟨p, hp, hpV⟩)

/-- **Two of the three remaining edges lie on the same side of the six-cycle.** The blueprint's
"two of the three lie on the same side": three edges, two sides. The two sides arrive here as
an arbitrary pair of disjoint open sets covering the complement of the cycle, which is the form
the polygonal Jordan curve theorem supplies them in. -/
theorem exists_two_chords_same_side (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    {U V : Set Plane} (hUo : IsOpen U) (hVo : IsOpen V) (hUV : Disjoint U V)
    (hcover : (hexSet drawing e)ᶜ ⊆ U ∪ V) :
    ∃ s t : Fin 3, s ≠ t ∧
      ((openArc (drawing (e s (s + 1))) ⊆ U ∧ openArc (drawing (e t (t + 1))) ⊆ U) ∨
        (openArc (drawing (e s (s + 1))) ⊆ V ∧ openArc (drawing (e t (t + 1))) ⊆ V)) := by
  have key := fun s ↦ h.chord_subset_or hd hUo hVo hUV hcover s
  rcases key 0 with h0 | h0 <;> rcases key 1 with h1 | h1 <;> rcases key 2 with h2 | h2
  exacts [⟨0, 1, by decide, Or.inl ⟨h0, h1⟩⟩, ⟨0, 1, by decide, Or.inl ⟨h0, h1⟩⟩,
    ⟨0, 2, by decide, Or.inl ⟨h0, h2⟩⟩, ⟨1, 2, by decide, Or.inr ⟨h1, h2⟩⟩,
    ⟨1, 2, by decide, Or.inl ⟨h1, h2⟩⟩, ⟨0, 2, by decide, Or.inr ⟨h0, h2⟩⟩,
    ⟨0, 1, by decide, Or.inr ⟨h0, h1⟩⟩, ⟨0, 1, by decide, Or.inr ⟨h0, h1⟩⟩]

end IsK33Config

end Graph
end

section
-- module Solutions.Q146_CD.Graph_Redrawing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Schoenflies.decidableCrosses
attribute [-simp] _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.Plane.coordAcross_param _root_.Schoenflies.Plane.coordAlong_param _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.cover_cons _root_.Schoenflies.cover_nil _root_.Schoenflies.crossings_cons _root_.Schoenflies.crossings_nil _root_.Schoenflies.edgeArc_segmentDrawing _root_.Schoenflies.hgt_self _root_.Schoenflies.orientPiece_interior _root_.Schoenflies.orientPiece_seg _root_.Schoenflies.orientPiece_swap _root_.Schoenflies.overlayGraph_isLink _root_.Schoenflies.overlayGraph_mem_edgeSet _root_.Schoenflies.overlayGraph_vertexSet _root_.Schoenflies.parity_cons _root_.Schoenflies.parity_nil _root_.Schoenflies.pathPieces_cons_cons _root_.Schoenflies.pathPieces_nil _root_.Schoenflies.pathPieces_singleton _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton _root_.Schoenflies.subdivide_cons _root_.Schoenflies.subdivide_nil _root_.Schoenflies.triangle_vertex_one _root_.Schoenflies.triangle_vertex_two _root_.Schoenflies.triangle_vertex_zero
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The polygonal redrawing of a finite plane graph

Bricks B7 and B8 of `lem:polygonal-redrawing`, and the headline theorem: every finite plane
graph is drawn again, on the same abstract graph and the same vertices, with polygonal edges.
Since the vertices of a plane graph *are* plane points and the redrawing leaves them where
they are, the blueprint's "isomorphic plane drawing" is the identity isomorphism, and no
`Graph.IsIsomorphism` is built or needed.

## Three things the design did not have, and this module supplies

**Simple polygonal paths.** `Graph.IsDrawing.edge_param` asks for an *injective*
parametrisation, and brick B6 delivers only a `poly` vertex list, which may cross itself. The
blueprint's Lemma 1.1 makes the path simple "by subdividing at self-intersections and taking a
simple path in the resulting finite graph"; `Schoenflies/PolyPath.lean` deferred that half, and
without it brick B8 cannot discharge the drawing condition at all. `IsArcList` and
`PolyReaches.exists_arcList` supply it, by an induction over the inductive relation rather than
by an overlay graph: at each `step` the new segment is run *backwards* from its far end and
stopped the first time it meets the polygon already built, and the old path is truncated
there. That needs no plane geometry beyond `exists_first_mem_Icc`, and in particular no
connectivity theorem for the overlay graph.

**The contact point is on the frame.** `Graph.IsDrawing.exists_core` states that the core meets
the square about a vertex in exactly one point, but not that this point is on the square's
boundary — and if it were interior the core would not lie in the plane minus the open squares,
which is the carrier brick B5 speaks about, nor would the radial segment from the vertex reach
it. `Plane.supDist_eq_of_inter_eq_singleton` closes the gap by connectedness: an interior
contact point would make the core's trace on the square a nonempty proper clopen piece.

**Radial arithmetic.** That two radials of one square meet only at the centre, and that a
radial meets the plane minus the open squares only at its far end, are both the statement that
the sup distance to the centre is a faithful coordinate along a radius
(`Plane.supDist_lt_of_mem_segment`, `Plane.radial_meet`). These are the "distinct radials in
one square meet only at `v`" and "radials meet the replacement paths only at the designated
boundary points" of brick B8's design, and neither is free.

## Blueprint

Bricks B7 and B8 of `lem:polygonal-redrawing` (H6), and the lemma itself.

* `Plane.supNorm_smul`, `Plane.supDist_add_smul`, `Plane.supDist_lt_of_mem_segment`,
  `Plane.segment_subset_closedSquare`, `Plane.radial_meet` — the radial segments of brick B8.
* `Plane.supDist_eq_of_inter_eq_singleton` — a core's contact point lies on the frame of its
  square; the missing clause of brick B4.
* `lastP`, `poly_snoc`, `IsArcList` — a **simple** polygonal path, in the `u :: t`
  presentation that keeps every statement free of dependent nonemptiness proofs.
* `isArcBetween_poly` — the carrier of a simple polygonal path is an arc between its ends.
* `IsArcList.truncate`, `IsArcList.snoc` — cutting one at any of its points, and extending one
  by a segment that touches it only at its last vertex.
* `PolyReaches.exists_arcList` — **every polygonal path contains a simple one**; the deferred
  half of Lemma 1.1.
* `Graph.polygonal_redrawing` — `lem:polygonal-redrawing`, with bricks B7 and B8 inside its
  proof: the `ε` making the tubes about the cores pairwise disjoint, the component `U e` of
  the core inside its tube, and the assembly of radial, replacement path and radial.
-/

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ### Radial segments in a square

A segment from the centre of a square to a point of its boundary frame leaves the open square
only at its far end, and two such segments in one square meet only at the centre. Those two
facts are the whole of the "radials" half of brick B8, and both are statements about the sup
distance scaling along a segment. -/

/-! ### Simple polygonal paths

`poly vs` is the carrier of a vertex list, and a general vertex list crosses itself. The
drawing condition of a plane graph asks for an *injective* parametrisation, so what brick B8
needs is a vertex list whose carrier is an **arc**. `IsArcList` is exactly the condition that
makes the concatenation of `Schoenflies/Concatenate.lean` apply at every step: consecutive
vertices differ, and each segment meets the rest of the polygon only at the vertex they
share.

The work of this section is `PolyReaches.exists_arcList`: *any* polygonal path inside a set
contains a simple one with the same ends. That is the half of the blueprint's Lemma 1.1 which
`Schoenflies/PolyPath.lean` deferred, and without it nothing downstream can discharge
`Graph.IsDrawing`. The induction is over the inductive relation `PolyReaches`, and the step
takes the *first* point at which the new segment, run backwards from its far end, meets the
polygon already built, truncates there and appends. -/

/-- The last vertex of a nonempty vertex list, with the nonemptiness discharged by the
`cons`. Carrying the list in the form `u :: t` removes every dependent proof argument from
the statements below. -/
def lastP (u : Plane) (t : List Plane) : Plane := (u :: t).getLast (List.cons_ne_nil u t)

@[simp] theorem lastP_nil (u : Plane) : lastP u [] = u := rfl

@[simp] theorem lastP_cons (u v : Plane) (t : List Plane) : lastP u (v :: t) = lastP v t :=
  List.getLast_cons (List.cons_ne_nil v t)

/-- A **simple** polygonal path: consecutive vertices are distinct, and each segment meets the
rest of the polygon exactly in the vertex where they are joined. That is precisely the
hypothesis `Schoenflies.IsArcBetween.concatenate` asks for, one step at a time. -/
def IsArcList : List Plane → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => u ≠ v ∧ segment ℝ u v ∩ poly (v :: rest) = {v} ∧ IsArcList (v :: rest)

@[simp] theorem isArcList_nil : IsArcList [] := trivial

@[simp] theorem isArcList_singleton (v : Plane) : IsArcList [v] := trivial

/-! ### The contact point of a core sits on the frame of its square

`Graph.IsDrawing.exists_core` says the core meets the square about `v` in exactly one point.
That point is on the *frame* of the square and not in its interior, which is what puts the
core in the plane minus the open squares and what makes the radial segment reach the core.
The argument is connectedness, not the parametrisation: were the contact point interior, it
would be a nonempty proper clopen piece of the core. -/

end Schoenflies

/-! ### Bricks B7 and B8, and the redrawing itself -/

open Schoenflies
end

section
-- module Solutions.Q146_CD.Graph_K33Planar
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.ClosedPolygon.carrier_toPre _root_.Schoenflies.ClosedPolygon.rotate_vertex _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.rotate_vertex _root_.Schoenflies.segsOf_nil _root_.Schoenflies.segsOf_singleton
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Lemma 3.10: the utility graph is not planar, and Corollary 3.11 for its subdivisions

`Schoenflies/Graph/K33.lean` built the whole configuration: the six-cycle of a drawn `K(3,3)`
is a Jordan curve, each of the three remaining edges is a crosscut of it, two of the three lie
on the same side, their endpoints alternate, and any two of them are disjoint. This module
wires those five facts to `Schoenflies.alternating_crosscuts` and derives the contradiction; it
then does the blueprint's reduction of `cor:k33-subdivision` to `lem:k33`.

**One hypothesis is assumed and not proved: `Graph.IsHexRealization`. See "The gap" below.**
The remaining results use only the hypotheses in their statements.

## Blueprint

* `Graph.IsHexCrosscut` — the six-cycle, together with one of the three remaining edges, in the
  vocabulary `Schoenflies.IsPolygonalCrosscut` speaks: a `Schoenflies.ClosedPolygon`, its two
  arcs, the crosscut, and a reference point.
* `Graph.IsK33Config.endpoints_subset_arcA`, `…_arcB`, `…exists_reference_point`,
  `…isHexCrosscut` — the four *topological* clauses of `Schoenflies.IsPolygonalCrosscut`,
  discharged from the drawing, so that only the combinatorial realization has to be assumed.
* `Graph.IsHexRealization` — that combinatorial realization, and the one thing assumed here.
* `Graph.IsK33Config.exists_two_chords_same_region` — `lem:k33`, "two of the three lie on the
  same side", with the side named as a region of the complement rather than as one of a pair
  of open sets, which is the form the crosscut corollary consumes.
* `Graph.IsK33Config.false_of_isHexCrosscut` — the contradiction at a *fixed* pair of remaining
  edges: `cor:alternating-crosscuts` makes them meet, `chords_disjoint` says they do not.
* `Graph.IsK33Config.false_of_hexCrosscuts`, `…false_of_hexRealizations` — `lem:k33` for a
  drawing that is already polygonal.
* `Graph.IsK33Config.not_isDrawing` — `lem:k33`: a graph carrying a copy of `K(3,3)` has no
  plane drawing at all. `lem:polygonal-redrawing` reduces the general drawing to a polygonal
  one, which is the only place polygonality is used.
* `Graph.IsArcK33`, `Graph.k33Graph`, `Graph.IsArcK33.arcDrawing`, `…isDrawing`,
  `…isK33Config`, `…false_of_realization` — `cor:k33-subdivision`, first half: nine arcs in the
  plane meeting only where a `K(3,3)` forces them to already *are* a plane drawing of `K(3,3)`,
  on an abstract graph built here for the purpose.
* `Graph.IsK33Subdivision`, `…isArcK33`, `…false_of_realization` — `cor:k33-subdivision`: in a
  plane drawing of a subdivision, the branch paths draw nine such arcs.

## The gap: realizing the six-cycle as a `ClosedPolygon`

Every statement of `Schoenflies/PolygonalJordan.lean`, `Schoenflies/PolygonalCrosscut.lean` and
`Schoenflies/AlternatingCrosscuts.lean` is about a `Schoenflies.ClosedPolygon m` — a cyclic
*vertex list* with `vertex_inj`, `edges_meet` and `corner`. The six-cycle of a polygonally
drawn `K(3,3)` is a polygonal Jordan curve as a **point set**, and nothing in the development
turns a point set into a `ClosedPolygon`: there is no declaration anywhere whose conclusion is
`∃ m (C : ClosedPolygon m), C.carrier = _`. The only closed polygons that exist are the
hand-built `Schoenflies.triangle` and `Schoenflies.unitTriangle`.

`IsHexRealization` is exactly that missing step, stated for the one curve this argument needs
it for and pared down to its combinatorial core: four closed polygons and four equations
identifying their carriers and edge lists with the drawing. No topological side condition
survives in it — the reference point of Theorem 2.8 and the three "meets" clauses are proved
here from the drawing. It is *not proved here*, and every theorem below that mentions it is
therefore requires that realization as a hypothesis.

**Why the realization is allowed to change the drawing.** `IsHexRealization` asks for
`C.arc a k = arcA e s`, which pins the two ends of that arc — the vertices `x s` and
`y (s+1)` — to be *vertices* of `C`. A `Schoenflies.ClosedPolygon` has no straight vertices
(its `corner` field), so this is possible only if the six-cycle actually turns at `x s` and at
`y (s+1)`. A polygonal drawing need not do that: two of the three polygonal edges at a vertex
may leave it in exactly opposite directions, and then no closed polygon with that carrier has
that point as a vertex. A realization must therefore be free to bend the drawing at the six
vertices first, and `Graph.IsK33Config.not_isDrawing` gives it that freedom: it hands the
realization a polygonal drawing and accepts *any* drawing back. This restriction comes from
`Schoenflies.IsPolygonalCrosscut`, not from anything here; the alternative is a crosscut
interface that lets the two cut points be interior to edges of `C`.
-/

open Set Schoenflies unitInterval
open scoped _root_.Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s t : Fin 3} {R : Set Plane}

/-! ### The missing realization, isolated

The six-cycle of a polygonally drawn `K(3,3)`, cut by the remaining edge `e s (s+1)`, presented
in the vocabulary of `Schoenflies.IsPolygonalCrosscut`: a `ClosedPolygon` whose carrier is the
six-cycle, whose two arcs from the cut are the two halves `arcA e s` and `arcB e s`, and whose
crosscut occupies exactly the remaining edge's arc. -/

namespace IsK33Config

/-! ### The alternation, with the two arcs named

`Graph.IsK33Config.chords_alternate` returns the two arcs existentially. The crosscut corollary
has to be handed *those particular sets*, since the realization has to reproduce them, so the
two membership clauses are restated here with the arcs written out. -/

/-- The near end of the next remaining edge is interior to the first arc. -/
theorem x_succ_mem_arcA (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    x (s + 1) ∈ edgesCover drawing (arcA e s) \ ({x s, y (s + 1)} : Set Plane) := by
  have hs1 : ∀ s : Fin 3, s + 1 ≠ s := by decide
  refine ⟨mem_arcA_iff.2 ⟨(s + 1, s), by simp [arcAPairs],
    (hd.edge_isArcBetween (h.isLink (s + 1) s)).left_mem⟩, ?_⟩
  rintro (hc | hc)
  exacts [h.x_ne_x (hs1 s) hc, h.x_ne_y _ _ hc]

/-- The far end of the next remaining edge is interior to the second arc. -/
theorem y_succ_mem_arcB (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    y (s + 1 + 1) ∈ edgesCover drawing (arcB e s) \ ({x s, y (s + 1)} : Set Plane) := by
  have hsucc : ∀ s : Fin 3, s + 1 + 1 = s + 2 := by decide
  have hs2 : ∀ s : Fin 3, s + 2 ≠ s + 1 := by decide
  rw [hsucc s]
  refine ⟨mem_arcB_iff.2 ⟨(s + 2, s + 2), by simp [arcBPairs],
    (hd.edge_isArcBetween (h.isLink (s + 2) (s + 2))).right_mem⟩, ?_⟩
  rintro (hc | hc)
  exacts [h.y_ne_x _ _ hc, h.y_ne_y (hs2 s) hc]

/-! ### Two of the three remaining edges lie in one region -/

/-- A remaining edge's interior lies inside the edge's arc. -/
theorem chord_openArc_subset_edgeArc (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (s : Fin 3) : openArc (drawing (e s (s + 1))) ⊆ edgeArc drawing (e s (s + 1)) := by
  rw [h.chord_openArc_eq hd s]; exact Set.sdiff_subset

/-- **Two of the three remaining edges lie in one and the same region of the complement of the
six-cycle.** This is `Graph.IsK33Config.exists_two_chords_same_side` with the two sides read as
the two regions `Int` and `Ext` of the polygonal Jordan curve theorem, which is the form the
crosscut corollary consumes. -/
theorem exists_two_chords_same_region (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hsep : IsSeparating (hexSet drawing e)) :
    ∃ s t : Fin 3, s ≠ t ∧ ∃ R : Set Plane, IsRegionOf (hexSet drawing e) R ∧
      openArc (drawing (e s (s + 1))) ⊆ R ∧ openArc (drawing (e t (t + 1))) ⊆ R := by
  obtain ⟨s, t, hst, hcase⟩ := h.exists_two_chords_same_side hd hsep.isOpen_inside
    hsep.isOpen_outside disjoint_inside_outside (inside_union_outside _).ge
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨s, t, hst, _, IsRegionOf.inside _, h1, h2⟩
  · exact ⟨s, t, hst, _, IsRegionOf.outside _, h1, h2⟩

/-! ### The topological side conditions of the crosscut, discharged

`Schoenflies.IsPolygonalCrosscut` asks for four things beyond the edge lists: that the crosscut
meets the polygon only in points of each arc, and a reference point off the polygon in the
region the crosscut does not enter. All four are properties of the *drawing*, and are proved
here, so that what has to be assumed from outside is only the combinatorial realization
(`Graph.IsHexRealization`). -/

/-- The two ends of the remaining edge lie on the first arc of the cut. -/
theorem endpoints_subset_arcA (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    ({x s, y (s + 1)} : Set Plane) ⊆ edgesCover drawing (arcA e s) := by
  rintro p (rfl | rfl)
  · exact mem_arcA_iff.2 ⟨(s, s), by simp [arcAPairs],
      (hd.edge_isArcBetween (h.isLink s s)).left_mem⟩
  · exact mem_arcA_iff.2 ⟨(s + 1, s + 1), by simp [arcAPairs],
      (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1))).right_mem⟩

/-- The two ends of the remaining edge lie on the second arc of the cut. -/
theorem endpoints_subset_arcB (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    ({x s, y (s + 1)} : Set Plane) ⊆ edgesCover drawing (arcB e s) := by
  rintro p (rfl | rfl)
  · exact mem_arcB_iff.2 ⟨(s, s + 2), by simp [arcBPairs],
      (hd.edge_isArcBetween (h.isLink s (s + 2))).left_mem⟩
  · exact mem_arcB_iff.2 ⟨(s + 2, s + 1), by simp [arcBPairs],
      (hd.edge_isArcBetween (h.isLink (s + 2) (s + 1))).right_mem⟩

/-- **The reference point of Theorem 2.8, for a remaining edge.** The interior of the remaining
edge lies in one region of the complement of the six-cycle; any point of the *other* region is a
legitimate reference point, and the other region is nonempty because it is a region. -/
theorem exists_reference_point (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hsep : IsSeparating (hexSet drawing e)) (s : Fin 3) :
    ∃ yref : Plane, yref ∉ hexSet drawing e ∧
      Disjoint (edgeArc drawing (e s (s + 1)))
        (connectedComponentIn (hexSet drawing e)ᶜ yref) := by
  obtain ⟨z, hz⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  have hzC : z ∉ hexSet drawing e := h.chord_openArc_subset_compl hd s hz
  -- The region of `z` and the region on the far side of it are the two regions.
  have hpair := hsep.isRegionPair_farRegion hzC
  obtain ⟨yref, hyref⟩ := (hpair.right.isConnected hsep).nonempty
  refine ⟨yref, hpair.right.subset_compl hyref, ?_⟩
  rw [hpair.right.connectedComponentIn_eq hsep hyref, Set.disjoint_left]
  intro p hp hpfar
  by_cases hpin : p ∈ ({x s, y (s + 1)} : Set Plane)
  · refine hpfar.1 ?_
    rcases hpin with rfl | rfl
    exacts [h.x_mem_hexSet hd s, h.y_mem_hexSet hd (s + 1)]
  · refine hpfar.2 (h.chord_openArc_subset_connectedComponentIn hd s hz ?_)
    rw [h.chord_openArc_eq hd s]
    exact ⟨hp, hpin⟩

end IsK33Config

/-! ### What must still be assumed: the combinatorial realization

Everything above is proved. What is not is that the six-cycle, its two arcs, and the two closed
curves the remaining edge forms with them are *closed polygons at all* — that a polygonal Jordan
curve given as a point set carries a cyclic vertex list. `IsHexRealization` says exactly that,
and nothing more: no reference point, no meeting condition, only the four `ClosedPolygon`s and
the four equations identifying their carriers and edge lists with the drawing. -/

/-! ## Corollary 3.11: no subdivision of `K(3,3)` has a plane drawing

The blueprint's proof replaces each branch path of a subdivision by the simple arc it draws and
then treats that arc as a single edge. Both halves are done here, in that order: first the
*abstract* statement that nine arcs meeting only where they must already carry a drawn
`K(3,3)` (`Graph.IsArcK33`), then the reduction of a drawn subdivision to nine such arcs. -/

/-- **Nine arcs in the plane, meeting only where they must.** This is what a plane drawing of a
subdivision of `K(3,3)` leaves once each branch path has been replaced by the arc it draws: six
distinct points, and for each pair `(i, j)` an arc from `x i` to `y j`, with two distinct arcs
meeting only in a point that is an endpoint of both.

Nothing here mentions a graph. The abstract `K(3,3)` that carries these arcs is built below. -/
structure IsArcK33 (x y : Fin 3 → Plane) (P : Fin 3 → Fin 3 → Set Plane) : Prop where
  /-- The `(i, j)`-th arc runs from `x i` to `y j`. -/
  arc : ∀ i j, IsArcBetween (P i j) (x i) (y j)
  /-- The three points of the first side are distinct. -/
  x_injective : Function.Injective x
  /-- The three points of the second side are distinct. -/
  y_injective : Function.Injective y
  /-- The two sides are disjoint. -/
  ne : ∀ i j, x i ≠ y j
  /-- Two distinct arcs meet only in a common endpoint. -/
  meet : ∀ i j k l, (i, j) ≠ (k, l) →
    P i j ∩ P k l ⊆ ({x i, y j} : Set Plane) ∩ ({x k, y l} : Set Plane)

/-- **The abstract `K(3,3)` on six named points of the plane.** Its edges are index pairs, and
`(i, j)` links `x i` to `y j`. The edge set is all of `Fin 3 × Fin 3`, so no membership side
condition ever has to be discharged. -/
def k33Graph (x y : Fin 3 → Plane) : Graph Plane (Fin 3 × Fin 3) where
  vertexSet := Set.range x ∪ Set.range y
  edgeSet := Set.univ
  IsLink p u v := (u = x p.1 ∧ v = y p.2) ∨ (u = y p.2 ∧ v = x p.1)
  isLink_symm := by
    rintro ⟨i, j⟩ -
    constructor
    rintro u v (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    exacts [Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩]
  eq_or_eq_of_isLink_of_isLink := by
    rintro ⟨i, j⟩ u v a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
  edge_mem_iff_exists_isLink := by
    rintro ⟨i, j⟩
    exact ⟨fun _ => ⟨x i, y j, Or.inl ⟨rfl, rfl⟩⟩, fun _ => Set.mem_univ _⟩
  left_mem_of_isLink := by
    rintro ⟨i, j⟩ u v (⟨rfl, -⟩ | ⟨rfl, -⟩)
    exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨j, rfl⟩]

@[simp] theorem k33Graph_vertexSet (x y : Fin 3 → Plane) :
    V(k33Graph x y) = Set.range x ∪ Set.range y := rfl

@[simp] theorem k33Graph_edgeSet (x y : Fin 3 → Plane) :
    E(k33Graph x y) = (Set.univ : Set (Fin 3 × Fin 3)) := rfl

theorem k33Graph_isLink (x y : Fin 3 → Plane) (i j : Fin 3) :
    (k33Graph x y).IsLink (i, j) (x i) (y j) := Or.inl ⟨rfl, rfl⟩

/-- An endpoint of an edge of the abstract `K(3,3)` is incident with it. -/
theorem k33Graph_inc {x y : Fin 3 → Plane} {i j : Fin 3} {p : Plane}
    (hp : p ∈ ({x i, y j} : Set Plane)) : (k33Graph x y).Inc (i, j) p := by
  rcases hp with rfl | rfl
  · exact ⟨y j, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨x i, Or.inr ⟨rfl, rfl⟩⟩

namespace IsArcK33

variable {x y : Fin 3 → Plane} {P : Fin 3 → Fin 3 → Set Plane}

/-- The nine arcs, parametrized: a drawing of `k33Graph`. The parametrizations are the ones the
arcs come with, so the point set of an edge is the arc it was built from
(`IsArcK33.edgeArc_eq`). -/
noncomputable def arcDrawing (h : IsArcK33 x y P) : Fin 3 × Fin 3 → ℝ → Plane :=
  fun p => (h.arc p.1 p.2).choose

theorem edgeArc_eq (h : IsArcK33 x y P) (i j : Fin 3) :
    edgeArc h.arcDrawing (i, j) = P i j := (h.arc i j).choose_spec.2.2.1

theorem arcDrawing_zero (h : IsArcK33 x y P) (i j : Fin 3) : h.arcDrawing (i, j) 0 = x i :=
  (h.arc i j).choose_spec.2.2.2.1

theorem arcDrawing_one (h : IsArcK33 x y P) (i j : Fin 3) : h.arcDrawing (i, j) 1 = y j :=
  (h.arc i j).choose_spec.2.2.2.2

/-- An arc carries none of the six points except its own two ends: a third point `x k` lies on
the arc `P k l` for every `l`, and two distinct arcs meet only in a common end. -/
theorem mem_arc_elim (h : IsArcK33 x y P) {i j : Fin 3} {p : Plane}
    (hpV : p ∈ Set.range x ∪ Set.range y) (hp : p ∈ P i j) :
    p ∈ ({x i, y j} : Set Plane) := by
  have hsucc : ∀ i : Fin 3, i + 1 ≠ i := by decide
  rcases hpV with ⟨k, rfl⟩ | ⟨l, rfl⟩
  · -- `x k` lies on `P k (j+1)`, an arc with a different index pair.
    exact (h.meet i j k (j + 1) (fun hc => hsucc j (congrArg Prod.snd hc).symm)
      ⟨hp, (h.arc k (j + 1)).left_mem⟩).1
  · -- `y l` lies on `P (i+1) l`.
    exact (h.meet i j (i + 1) l (fun hc => hsucc i (congrArg Prod.fst hc).symm)
      ⟨hp, (h.arc (i + 1) l).right_mem⟩).1

/-- **The nine arcs draw the abstract `K(3,3)` in the plane.** -/
theorem isDrawing (h : IsArcK33 x y P) : IsDrawing (k33Graph x y) h.arcDrawing := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, j⟩ -
    obtain ⟨hc, hi, -, -, -⟩ := (h.arc i j).choose_spec
    refine ⟨hc, hi, ?_⟩
    rw [show h.arcDrawing (i, j) 0 = x i from h.arcDrawing_zero i j,
      show h.arcDrawing (i, j) 1 = y j from h.arcDrawing_one i j]
    exact k33Graph_isLink x y i j
  · rintro ⟨i, j⟩ u v w hl hwV hw
    have hmem : w ∈ ({x i, y j} : Set Plane) :=
      h.mem_arc_elim hwV (by rwa [h.edgeArc_eq i j] at hw)
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmem
    · exact hmem.symm
  · rintro ⟨i, j⟩ ⟨k, l⟩ - - hne p hp hq
    rw [h.edgeArc_eq i j] at hp
    rw [h.edgeArc_eq k l] at hq
    obtain ⟨hij, hkl⟩ := h.meet i j k l hne ⟨hp, hq⟩
    refine ⟨?_, k33Graph_inc hij, k33Graph_inc hkl⟩
    rcases hij with rfl | rfl
    exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨j, rfl⟩]

/-- The nine arcs carry a copy of `K(3,3)`, on the graph they draw. -/
theorem isK33Config (h : IsArcK33 x y P) :
    IsK33Config (k33Graph x y) x y (fun i j => (i, j)) where
  isLink := k33Graph_isLink x y
  x_injective := h.x_injective
  y_injective := h.y_injective
  ne := h.ne

end IsArcK33

/-! ### From a drawn subdivision to nine arcs -/

end Graph
end

section
-- module Solutions.Q146_CD.Graph_K33Closed
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun _root_.Schoenflies.PrePolygon.arcPieces_toPre _root_.Schoenflies.PrePolygon.arc_toPre _root_.Schoenflies.PrePolygon.insertLast_vertex _root_.Schoenflies.PrePolygon.pieces_toPre
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Discharging the realization hypothesis of `lem:k33`

`Schoenflies/Graph/K33Planar.lean` proves the nonplanarity of `K(3,3)` from one assumption,
`Graph.IsHexRealization`: that the six-cycle, the two arcs the chord cuts it into, and the two
closed curves the chord forms with them are all presented by cyclic vertex lists.
`Schoenflies/Realization.lean` now supplies the presentations. This module wires the two
together.

## Blueprint

* `Schoenflies.exists_poly_anchored`, `Schoenflies.IsPolygonal.union`,
  `Graph.IsDrawing.isPolygonal_edgesCover` — §1: a polygonal set is the carrier of a vertex list
  running between any two of its points, so two polygonal sets that meet have a polygonal union,
  and a walk of a polygonal plane graph draws a polygonal set.
* `Schoenflies.ClosedPolygon.reverse` — a closed polygon read backwards.
* `Schoenflies.ClosedPolygon.arc_vertex_eq`, `…arcPieces_eq` — **the decomposition of an arc is
  the arc's own**: two closed polygons that share an arc, starting at the same vertex, run
  through the same vertices along it. This is what makes the three presentations below fit
  together into one crosscut.
* `Schoenflies.exists_closedPolygon_arcs_oriented` — the realization of a splitting with the
  first arc's *direction* fixed as well, so that two realizations of one arc can be compared.
* `Graph.IsK33Config.isPolygonal_hexSet`, `…chord_inter_arcA`, `…chord_inter_arcB` — the three
  curves the crosscut is built from, as polygonal Jordan curves.
* `Graph.IsHexGeneric` — the general-position hypothesis that survives: at each of the two cut
  points, the six-cycle and both spliced curves turn.
* `Graph.IsK33Config.isHexRealization` — `Graph.IsHexRealization`, discharged from it. **This is
  the theorem this module exists for.**
* `Graph.Bendable`, `Graph.IsK33Config.false_of_hexGeneric`, `…not_isDrawing_of_bendable`,
  `Graph.IsArcK33.false_of_bendable`, `Graph.IsK33Subdivision.false_of_bendable`,
  `Graph.k33Graph_not_isDrawing` — `lem:k33` and `cor:k33-subdivision` with `IsHexRealization`
  replaced by `IsHexGeneric`.

## What is still assumed, and why — READ THIS BEFORE USING THE THEOREMS BELOW

**Milestone H8 is not closed here.** `Graph.IsHexRealization` is gone, but a strictly smaller
hypothesis has taken its place, and it is not discharged.

`Schoenflies.ClosedPolygon` forbids a vertex at which the curve runs straight through, and
`Schoenflies.ClosedPolygon.isCornerAt_vertex` says that this is not a defect of the proofs:
*every* vertex of *every* realization is a corner of the curve. A crosscut whose ends are cut
points of `C` therefore forces those ends to be corners — of `C`, and of both curves the
crosscut forms with the two arcs. `Graph.IsHexGeneric` says exactly that and nothing more, and
by the two corner theorems it cannot be weakened while the crosscut is presented as a
`Schoenflies.IsPolygonalCrosscut`.

For a drawn `K(3,3)` it is the statement that at each of the six vertices the three edges leave
along three pairwise non-collinear germs. A polygonal drawing need not have that: two of the
three edges at a vertex may leave along exactly opposite rays, which is perfectly compatible
with the drawing condition. The remaining gap is therefore a *bending* lemma — every polygonal
drawing can be redrawn so that no two edges at a vertex are collinear there — and it is
genuinely about changing the drawing, not about presentations. `Graph.Bendable` is that
statement in the shape the theorems below consume; nothing here proves it.
-/

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ## A polygonal set is a vertex list between any two of its points

`Schoenflies.IsPolygonal` is "the carrier of a vertex list", and a vertex list carries a *path*,
so the predicate is not closed under arbitrary finite unions — two disjoint segments are not the
carrier of any one list. It is closed under unions that meet, and the way to see that is to move
the ends of the list: a list can be made to start and end wherever one likes on its own carrier,
by running out and back. -/

/-! ## A closed polygon read backwards

A realization of a splitting names its two arcs *in a direction*, and two realizations of one
arc need not agree on it. Reversing the cyclic order is what reconciles them. -/

namespace ClosedPolygon

variable {m : ℕ}

/-- **The same closed polygon, traversed the other way.** -/
def reverse (P : ClosedPolygon m) : ClosedPolygon m where
  vertex j := P.vertex (-j)
  vertex_inj _ _ h := neg_injective (P.vertex_inj h)
  edges_meet i j hij := by
    have e1 : (-(i + 1) : ZMod (m + 3)) = -i - 1 := by ring
    have e2 : (-(j + 1) : ZMod (m + 3)) = -j - 1 := by ring
    have e3 : (-i - 1 : ZMod (m + 3)) + 1 = -i := by ring
    have e4 : (-j - 1 : ZMod (m + 3)) + 1 = -j := by ring
    have hij' : (-i - 1 : ZMod (m + 3)) ≠ -j - 1 := fun h => hij (by linear_combination -h)
    have h := P.edges_meet (-i - 1) (-j - 1) hij'
    rw [e3, e4] at h
    simp only [e1, e2]
    rw [segment_symm ℝ (P.vertex (-i)) (P.vertex (-i - 1)),
      segment_symm ℝ (P.vertex (-j)) (P.vertex (-j - 1)), Set.pair_comm]
    exact h
  corner i := by
    have e1 : (-(i - 1) : ZMod (m + 3)) = -i + 1 := by ring
    have e2 : (-(i + 1) : ZMod (m + 3)) = -i - 1 := by ring
    simp only [e1, e2]
    rw [Plane.det_comm]
    exact fun h => P.corner (-i) (by linear_combination -h)

@[simp] theorem reverse_vertex (P : ClosedPolygon m) (j : ZMod (m + 3)) :
    P.reverse.vertex j = P.vertex (-j) := rfl

/-- The `t`-th edge of the reversed arc is the `k - 1 - t`-th of the original: the same edges,
listed backwards. -/
theorem reverse_natCast {n k t : ℕ} (ht : t < k) :
    ((k - t - 1 : ℕ) : ZMod n) + (t : ZMod n) + 1 = (k : ZMod n) := by
  have h : (k - t - 1) + t + 1 = k := by omega
  have hc := congrArg (fun j : ℕ => (j : ZMod n)) h
  push_cast at hc
  linear_combination hc

/-! ## The decomposition of an arc is the arc's own

`Graph.IsHexRealization` asks for three closed polygons that agree on the arcs they share. They
are found independently, and nothing so far says they agree — until this: two closed polygons
carrying the same arc, and starting it at the same vertex, run through the same vertices along
it. The proof walks the arc: the first edges of the two are two segments leaving one point along
one ray, so one contains the other, and the shorter one's far end would be a vertex of its own
polygon interior to an edge of the other — which `corner` forbids. -/

/-- Stepping the cyclic index by a positive numeral. -/
theorem natCast_pred_succ {n t : ℕ} (ht : 0 < t) : ((t - 1 : ℕ) : ZMod n) + 1 = (t : ZMod n) := by
  have h : (t - 1) + 1 = t := by omega
  have hc := congrArg (fun j : ℕ => (j : ZMod n)) h
  push_cast at hc
  linear_combination hc

end ClosedPolygon

end Schoenflies

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-! ## What the realization needs from the drawing, and nothing else -/

variable {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β} {s : Fin 3}

namespace IsK33Config

/-- The first half of the six-cycle is polygonal: it is drawn by a path. -/
theorem isPolygonal_arcA (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) (s : Fin 3) :
    IsPolygonal (edgesCover drawing (arcA e s)) :=
  hd.isPolygonal_edgesCover hpoly (h.arcA_isPath s).isWalk (by simp [arcA])

/-- The second half of the six-cycle is polygonal. -/
theorem isPolygonal_arcB (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) (s : Fin 3) :
    IsPolygonal (edgesCover drawing (arcB e s)) :=
  hd.isPolygonal_edgesCover hpoly (h.arcB_isPath s).isWalk (by simp [arcB])

/-- **The six-cycle of a polygonally drawn `K(3,3)` is polygonal**: it is the union of its two
halves, which meet. -/
theorem isPolygonal_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) :
    IsPolygonal (hexSet drawing e) := by
  rw [← arcs_union (drawing := drawing) (e := e) 0]
  exact (h.isPolygonal_arcA hd hpoly 0).union (h.isPolygonal_arcB hd hpoly 0)
    ⟨x 0, (h.arcA_isArcBetween hd 0).left_mem, (h.arcB_isArcBetween hd 0).left_mem⟩

/-- A remaining edge meets the first half of the six-cycle exactly in its own two ends. -/
theorem chord_inter_arcA (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    edgesCover drawing (arcA e s) ∩ edgeArc drawing (e s (s + 1)) = {x s, y (s + 1)} := by
  refine Set.Subset.antisymm (fun z hz => ?_) ?_
  · have hzhex : z ∈ hexSet drawing e := by
      rw [← arcs_union (drawing := drawing) (e := e) s]; exact Or.inl hz.1
    rw [← h.chord_inter_hexSet hd s]
    exact ⟨hz.2, hzhex⟩
  · rintro z (rfl | rfl)
    exacts [⟨(h.arcA_isArcBetween hd s).left_mem,
      (hd.edge_isArcBetween (h.isLink s (s + 1))).left_mem⟩,
      ⟨(h.arcA_isArcBetween hd s).right_mem,
      (hd.edge_isArcBetween (h.isLink s (s + 1))).right_mem⟩]

/-- A remaining edge meets the second half of the six-cycle exactly in its own two ends. -/
theorem chord_inter_arcB (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    edgesCover drawing (arcB e s) ∩ edgeArc drawing (e s (s + 1)) = {x s, y (s + 1)} := by
  refine Set.Subset.antisymm (fun z hz => ?_) ?_
  · have hzhex : z ∈ hexSet drawing e := by
      rw [← arcs_union (drawing := drawing) (e := e) s]; exact Or.inr hz.1
    rw [← h.chord_inter_hexSet hd s]
    exact ⟨hz.2, hzhex⟩
  · rintro z (rfl | rfl)
    exacts [⟨(h.arcB_isArcBetween hd s).left_mem,
      (hd.edge_isArcBetween (h.isLink s (s + 1))).left_mem⟩,
      ⟨(h.arcB_isArcBetween hd s).right_mem,
      (hd.edge_isArcBetween (h.isLink s (s + 1))).right_mem⟩]

/-! ### `lem:k33` and `cor:k33-subdivision`, with the realization gone

What is left as a hypothesis is a *bending* step, and only that: every polygonal drawing can be
redrawn so that no two edges at a vertex leave it along one line. -/

end IsK33Config

end Graph
end

section
-- module Solutions.Q146_CD.Graph_K33Land
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.Graph.pointSet_union _root_.Schoenflies.CellStructure.Realization.edgeSet_graph _root_.Schoenflies.CellStructure.Realization.vertexSet_graph _root_.Schoenflies.CellStructure.SkeletonHomeo.symm_toFun
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# `lem:k33` and `cor:k33-subdivision`, with nothing assumed

`Schoenflies/Graph/K33Planar.lean` proves the nonplanarity of `K(3,3)` from
`Graph.IsHexRealization`; `Schoenflies/Graph/K33Closed.lean` reduces that to `Graph.Bendable` —
"every polygonal drawing can be redrawn so that no two edges leave a vertex along one line". This
module removes the hypothesis altogether. Nothing is bent.

## Where the hypothesis came from, and why it is not needed

`Schoenflies.ClosedPolygon` carries a `corner` field, and
`Schoenflies.ClosedPolygon.isCornerAt_vertex` shows the field is not slack: *every* vertex of
*every* `ClosedPolygon` presentation is a point at which the curve turns. So a crosscut interface
phrased with `ClosedPolygon`s — `Schoenflies.IsPolygonalCrosscut`, and hence
`Schoenflies.alternating_crosscuts` — can only cut the curve at corners, and a drawn `K(3,3)` puts
its branch points wherever it likes.

The blueprint's `cor:alternating-crosscuts` has no such condition: it is stated for a set-level
simple closed polygonal curve and simple polygonal arcs with endpoints anywhere on it. The fix is
to state the crosscut for `Schoenflies.PrePolygon` — `ClosedPolygon` without `corner` — whose
vertices may sit anywhere on the curve. `Schoenflies/PrePolygonSep.lean` already supplies the two
things Theorem 2.8 asks of such a curve: that its carrier separates the plane, and the two values
of the crossing parity. Everything else in the chain is about *edge lists*, and edge lists do not
know about corners.

## The one construction this needed

Three closed polygons enter Theorem 2.8 — the curve `C` and the two curves `Jᵢ` the crosscut
forms with the two arcs — and their **edge lists** must agree: `SameEdges Jᵢ.pieces (Aᵢ ++ K)`.
`Schoenflies/Graph/K33Closed.lean` found three realizations independently and matched them with
`Schoenflies.ClosedPolygon.arcPieces_eq`, whose proof is exactly where `corner` was consumed. For
`PrePolygon` no such matching theorem can exist: two presentations of one arc need not agree.

So the two spliced curves are not found — they are *built*. `Schoenflies.PrePolygon.exists_splice`
lays two chains with common ends end to end and returns a `PrePolygon` whose edge list is their
concatenation, so the three lists agree by construction and nothing has to be matched. The chains
themselves come from `Schoenflies.exists_prePolygon_arcs_oriented`, which needs
`Schoenflies.PrePolygon.insertLast` of `Schoenflies/PrePolygonArc.lean`: a point of the curve that
is not yet a vertex is interior to an edge, and an edge may be cut. That is the inverse of
`Schoenflies.PrePolygon.deleteLast`, and it is what makes "a `PrePolygon` may be presented with
vertices at any prescribed finite set of points of its carrier" a theorem
(`Schoenflies.PrePolygon.exists_prePolygon_vertices`).

## What this module rests on

The `Schoenflies.PrePolygon` arc apparatus — `chain`, `arcPieces`, `arc`, `arc_inter`,
`isArcBetween_arc`, `parity_splitting`, `parity_ne_iff_mem_farRegion`, `insertLast`,
`exists_prePolygon_vertices`, `Schoenflies.exists_prePolygon_split` and the segment-cutting
lemmas — is in `Schoenflies/PrePolygonArc.lean`, shared with `Schoenflies/FaceCyclesLand.lean`.
Only what is peculiar to the crosscut wiring is left here.

## Blueprint

* `Schoenflies.PrePolygon.exists_splice` — two arcs with common ends, laid end to end.
* `Schoenflies.PrePolygon.reverse`, `…reverse_arc`, `…sameEdges_reverse_arcPieces` — the polygon
  traversed the other way, which is what pins the direction of a prescribed arc.
* `Schoenflies.exists_prePolygon_arcs`, `…exists_prePolygon_arcs_oriented` — §1, the realization
  theorem **with the cut points anywhere on the curve**, tracking a prescribed splitting.
  Compare `Schoenflies.exists_closedPolygon_arcs`, which requires the cut points to be corners.
* `Schoenflies.IsPrePolygonalCrosscut` and its API up to
  `…alternating_inter_nonempty_of_same_side` — `thm:polygonal-crosscut` and
  `cor:alternating-crosscuts` in the blueprint's own generality: the split points need not be
  corners.
* `Graph.IsPreHexCrosscut`, `Graph.IsK33Config.isPreHexCrosscut` — the six-cycle of a polygonally
  drawn `K(3,3)`, cut at the two ends of one remaining edge, as such a crosscut. **This is what
  `Graph.IsHexRealization` was assuming, and it is proved here.**
* `Graph.IsK33Config.false_of_isPreHexCrosscut`, `…false_of_polygonal`,
  `Graph.IsK33Config.not_exists_isDrawing` — `lem:k33`.
* `Graph.IsArcK33.elim`, `Graph.IsK33Subdivision.elim` — `cor:k33-subdivision`.
* `Graph.k33Graph_not_exists_isDrawing` — `lem:k33` for the concrete graph.

## A note on names, for the integrator

The direct statements use eliminator-style names because the realization-parametric lemmas are
still in the import closure:

| realization-parametric lemma                      | direct theorem                             |
|---------------------------------------------------|--------------------------------------------|
| `Graph.IsK33Config.not_isDrawing` (K33Planar)      | `Graph.IsK33Config.not_exists_isDrawing`   |
| `Graph.IsK33Config.not_isDrawing_of_bendable`      | `Graph.IsK33Config.not_exists_isDrawing`   |
| `Graph.IsArcK33.false_of_realization`/`_bendable`  | `Graph.IsArcK33.elim`                      |
| `Graph.IsK33Subdivision.false_of_realization`/`…`  | `Graph.IsK33Subdivision.elim`              |
| `Graph.k33Graph_not_isDrawing`                     | `Graph.k33Graph_not_exists_isDrawing`      |

With this module in place `Graph.IsHexRealization`, `Graph.IsHexCrosscut`, `Graph.IsHexGeneric`
and `Graph.Bendable` have no consumers left.
-/

open Bornology Metric Set unitInterval
open scoped Graph

namespace Schoenflies

open Plane

namespace PrePolygon

/-! ## Splicing two chains into a closed polygon

The crosscut of Theorem 2.8 asks for three closed polygons whose *edge lists* fit together, and
independent realizations of three curves do not. The way out is to realize only the curve `C`,
and to build the two spliced curves out of one arc of `C` and one presentation of the crosscut —
so that the three edge lists agree by construction. This is that construction: two chains with
the same pair of ends, meeting only there, laid end to end. -/

/-- **Two arcs with common ends splice into a closed polygon whose edge list is their
concatenation.** `P.arcPieces a k` runs from `p` to `q` and `P'.arcPieces b l` runs from `q` back
to `p`; the two meet only at `p` and `q`. -/
theorem exists_splice {m m' : ℕ} (P : PrePolygon m) (P' : PrePolygon m')
    {a : ZMod (m + 3)} {k : ℕ} {b : ZMod (m' + 3)} {l : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) (hl1 : 1 ≤ l) (hl2 : l ≤ m' + 2)
    (hstart : P'.vertex b = P.vertex (a + (k : ZMod (m + 3))))
    (hend : P'.vertex (b + (l : ZMod (m' + 3))) = P.vertex a)
    (hinter : P.arc a k ∩ P'.arc b l = {P.vertex a, P.vertex (a + (k : ZMod (m + 3)))}) :
    ∃ (n : ℕ) (Q : PrePolygon n), Q.pieces = P.arcPieces a k ++ P'.arcPieces b l := by
  -- The two chains cannot both be a single edge: they would be the same segment.
  have hthree : 3 ≤ k + l := by
    by_contra hcon
    obtain rfl : k = 1 := by omega
    obtain rfl : l = 1 := by omega
    rw [Nat.cast_one] at hstart hinter
    rw [Nat.cast_one] at hend
    have hseg : P'.edge b = P.edge a := by
      rw [edge, edge, hstart, hend, segment_symm]
    rw [P.arc_one a, P'.arc_one b, hseg, Set.inter_self] at hinter
    obtain ⟨z, hz, hz1, hz2⟩ := exists_mem_segment_ne (vertex_ne_succ (P := P) a)
    rcases hinter.subset hz with h | h
    exacts [hz1 h, hz2 h]
  obtain ⟨n, hn⟩ : ∃ n, k + l = n + 3 := ⟨k + l - 3, by omega⟩
  -- Pieces of one arc lie in that arc; that is all the intersection hypothesis is used through.
  have hPedge : ∀ t : ℕ, t < k → P.edge (a + (t : ZMod (m + 3))) ⊆ P.arc a k :=
    fun t ht z hz => mem_arc_iff.2 ⟨t, ht, hz⟩
  have hP'edge : ∀ t : ℕ, t < l → P'.edge (b + (t : ZMod (m' + 3))) ⊆ P'.arc b l :=
    fun t ht z hz => mem_arc_iff.2 ⟨t, ht, hz⟩
  have hcross : ∀ s : ℕ, s < k → ∀ t : ℕ, t < l →
      P.edge (a + (s : ZMod (m + 3))) ∩ P'.edge (b + (t : ZMod (m' + 3)))
        ⊆ ({P.vertex a, P.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
    intro s hs t ht z hz
    rw [← hinter]
    exact ⟨hPedge s hs hz.1, hP'edge t ht hz.2⟩
  -- The spliced vertex list.
  set w : ZMod (n + 3) → Plane := fun j =>
    if j.val < k then P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)))
    else P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))) with hwdef
  have hbound : ∀ j : ZMod (n + 3), j.val < k + l := fun j => by
    have := ZMod.val_lt j; omega
  have hw_lt : ∀ j : ZMod (n + 3), j.val < k →
      w j = P.vertex (a + ((j.val : ℕ) : ZMod (m + 3))) := fun j hj => by
    rw [hwdef]; exact if_pos hj
  have hw_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      w j = P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))) := fun j hj => by
    rw [hwdef]; exact if_neg hj
  have hsucc_lt : ∀ j : ZMod (n + 3), j.val < k →
      w (j + 1) = P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)) + 1) := by
    intro j hj
    have hval : (j + 1).val = j.val + 1 := val_succ_of_lt (m := n) (by omega)
    by_cases hlt : j.val + 1 < k
    · rw [hw_lt (j + 1) (by omega), hval]
      congr 1
      push_cast
      ring
    · have hk' : j.val + 1 = k := by omega
      rw [hw_ge (j + 1) (by omega), hval, hk', Nat.sub_self, Nat.cast_zero, add_zero, hstart]
      congr 1
      rw [← hk']
      push_cast
      ring
  have hsucc_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      w (j + 1) = P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3)) + 1) := by
    intro j hj
    have hjb := hbound j
    by_cases hlt : j.val + 1 < n + 3
    · have hval : (j + 1).val = j.val + 1 := val_succ_of_lt (m := n) (by omega)
      rw [hw_ge (j + 1) (by omega), hval]
      congr 1
      rw [show j.val + 1 - k = (j.val - k) + 1 by omega]
      push_cast
      ring
    · have hval : (j + 1).val = 0 := val_succ_last (m := n) (by omega)
      rw [hw_lt (j + 1) (by omega), hval, Nat.cast_zero, add_zero, ← hend]
      congr 1
      have hc : ((l - 1 : ℕ) : ZMod (m' + 3)) + 1 = ((l : ℕ) : ZMod (m' + 3)) :=
        ClosedPolygon.natCast_pred_succ (by omega)
      rw [show j.val - k = l - 1 by omega, add_assoc, hc]
  -- The edges of the spliced list are the edges of the two arcs.
  have hE_lt : ∀ j : ZMod (n + 3), j.val < k →
      segment ℝ (w j) (w (j + 1)) = P.edge (a + ((j.val : ℕ) : ZMod (m + 3))) := by
    intro j hj
    rw [hw_lt j hj, hsucc_lt j hj, edge]
  have hE_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      segment ℝ (w j) (w (j + 1)) = P'.edge (b + ((j.val - k : ℕ) : ZMod (m' + 3))) := by
    intro j hj
    rw [hw_ge j hj, hsucc_ge j hj, edge]
  have hends_lt : ∀ j : ZMod (n + 3), j.val < k →
      ({w j, w (j + 1)} : Set Plane)
        = {P.vertex (a + ((j.val : ℕ) : ZMod (m + 3))),
           P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)) + 1)} := by
    intro j hj
    rw [hw_lt j hj, hsucc_lt j hj]
  have hends_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      ({w j, w (j + 1)} : Set Plane)
        = {P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))),
           P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3)) + 1)} := by
    intro j hj
    rw [hw_ge j hj, hsucc_ge j hj]
  refine ⟨n, ⟨w, ?_, ?_⟩, ?_⟩
  · -- injectivity
    intro i j hij
    have hib := hbound i
    have hjb := hbound j
    have hcase : ∀ i' j' : ZMod (n + 3), i'.val < k → ¬ j'.val < k → w i' ≠ w j' := by
      intro i' j' hi' hj' he
      rw [hw_lt i' hi', hw_ge j' hj'] at he
      have hval : P.vertex (a + ((i'.val : ℕ) : ZMod (m + 3))) ∈
          ({P.vertex a, P.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
        rw [← hinter]
        exact ⟨hPedge i'.val hi' (left_mem_segment ℝ _ _),
          he ▸ hP'edge (j'.val - k) (by have := hbound j'; omega) (left_mem_segment ℝ _ _)⟩
      rcases hval with hval | hval
      · -- the common point is `p`: on the second arc that forces the last index
        have h0 : i'.val = 0 := by
          have := P.natCast_shift_inj a (show i'.val < m + 3 by omega) (show 0 < m + 3 by omega)
            (by rw [hval, Nat.cast_zero, add_zero])
          omega
        have hlast : P'.vertex (b + ((j'.val - k : ℕ) : ZMod (m' + 3)))
            = P'.vertex (b + ((l : ℕ) : ZMod (m' + 3))) := by rw [hend, ← he, hval]
        have := P'.natCast_shift_inj b (show j'.val - k < m' + 3 by have := hbound j'; omega)
          (show l < m' + 3 by omega) hlast
        have := hbound j'
        omega
      · have := P.natCast_shift_inj a (show i'.val < m + 3 by omega) (show k < m + 3 by omega)
          (by rw [hval])
        omega
    by_cases hli : i.val < k <;> by_cases hlj : j.val < k
    · rw [hw_lt i hli, hw_lt j hlj] at hij
      exact ZMod.val_injective _ (P.natCast_shift_inj a (by omega) (by omega) hij)
    · exact absurd hij (hcase i j hli hlj)
    · exact absurd hij.symm (hcase j i hlj hli)
    · rw [hw_ge i hli, hw_ge j hlj] at hij
      have := P'.natCast_shift_inj b (show i.val - k < m' + 3 by omega)
        (show j.val - k < m' + 3 by omega) hij
      exact ZMod.val_injective _ (by omega)
  · -- simplicity
    intro i j hij
    have hib := hbound i
    have hjb := hbound j
    by_cases hli : i.val < k <;> by_cases hlj : j.val < k
    · rw [hE_lt i hli, hE_lt j hlj, hends_lt i hli]
      refine P.edges_meet _ _ fun he => hij (ZMod.val_injective _ ?_)
      exact P.natCast_shift_inj a (by omega) (by omega) (by rw [he])
    · rw [hE_lt i hli, hE_ge j hlj, hends_lt i hli]
      intro z hz
      have hz' := hcross i.val hli (j.val - k) (by omega) hz
      rcases hz' with rfl | rfl
      exacts [vertex_mem_edge_elim (P := P) (c := a) hz.1,
        vertex_mem_edge_elim (P := P) (c := a + (k : ZMod (m + 3))) hz.1]
    · rw [hE_ge i hli, hE_lt j hlj, hends_ge i hli]
      intro z hz
      have hz' := hcross j.val hlj (i.val - k) (by omega) ⟨hz.2, hz.1⟩
      rcases hz' with rfl | rfl
      · rw [← hend]
        exact vertex_mem_edge_elim (P := P') (c := b + (l : ZMod (m' + 3)))
          (by rw [hend]; exact hz.1)
      · rw [← hstart]
        exact vertex_mem_edge_elim (P := P') (c := b) (by rw [hstart]; exact hz.1)
    · rw [hE_ge i hli, hE_ge j hlj, hends_ge i hli]
      refine P'.edges_meet _ _ fun he => hij (ZMod.val_injective _ ?_)
      have := P'.natCast_shift_inj b (show i.val - k < m' + 3 by omega)
        (show j.val - k < m' + 3 by omega) (by rw [he])
      omega
  · -- the edge list
    have hrange : List.range (n + 3) = List.range k ++ (List.range l).map (k + ·) := by
      rw [← hn]; exact List.range_add
    change ((List.range (n + 3)).map fun j : ℕ =>
        (w ((j : ℕ) : ZMod (n + 3)), w (((j : ℕ) : ZMod (n + 3)) + 1))) = _
    rw [hrange, List.map_append, List.map_map, arcPieces, arcPieces]
    congr 1
    · refine List.map_congr_left fun t ht => ?_
      have htk : t < k := List.mem_range.1 ht
      have hval : ((t : ZMod (n + 3))).val = t := ZMod.val_cast_of_lt (by omega)
      have h1 : ((t : ZMod (n + 3))).val < k := by rw [hval]; exact htk
      rw [hw_lt _ h1, hsucc_lt _ h1, hval]
    · refine List.map_congr_left fun s hs => ?_
      have hsl : s < l := List.mem_range.1 hs
      have hval : (((k + s : ℕ) : ZMod (n + 3))).val = k + s := ZMod.val_cast_of_lt (by omega)
      have h1 : ¬ (((k + s : ℕ) : ZMod (n + 3))).val < k := by rw [hval]; omega
      simp only [Function.comp_apply]
      rw [hw_ge _ h1, hsucc_ge _ h1, hval, show k + s - k = s by omega]

/-! ## The polygon read backwards

Needed only to pin the *direction* in which a realization traverses a prescribed arc; the
`Schoenflies.ClosedPolygon` version is in `Schoenflies/Graph/K33Closed.lean`, and this is the
same construction with the `corner` field dropped. -/

/-- **The same closed polygon, traversed the other way.** -/
def reverse {m : ℕ} (P : PrePolygon m) : PrePolygon m where
  vertex j := P.vertex (-j)
  vertex_inj _ _ h := neg_injective (P.vertex_inj h)
  edges_meet i j hij := by
    have e1 : (-(i + 1) : ZMod (m + 3)) = -i - 1 := by ring
    have e2 : (-(j + 1) : ZMod (m + 3)) = -j - 1 := by ring
    have e3 : (-i - 1 : ZMod (m + 3)) + 1 = -i := by ring
    have e4 : (-j - 1 : ZMod (m + 3)) + 1 = -j := by ring
    have hij' : (-i - 1 : ZMod (m + 3)) ≠ -j - 1 := fun h => hij (by linear_combination -h)
    have h := P.edges_meet (-i - 1) (-j - 1) hij'
    rw [e3, e4] at h
    simp only [e1, e2]
    rw [segment_symm ℝ (P.vertex (-i)) (P.vertex (-i - 1)),
      segment_symm ℝ (P.vertex (-j)) (P.vertex (-j - 1)), Set.pair_comm]
    exact h

@[simp] theorem reverse_vertex {m : ℕ} (P : PrePolygon m) (j : ZMod (m + 3)) :
    P.reverse.vertex j = P.vertex (-j) := rfl

theorem reverse_edge {m : ℕ} (P : PrePolygon m) (j : ZMod (m + 3)) :
    P.reverse.edge j = P.edge (-j - 1) := by
  rw [edge, edge, reverse_vertex, reverse_vertex,
    show (-(j + 1) : ZMod (m + 3)) = -j - 1 by ring,
    show (-j - 1 : ZMod (m + 3)) + 1 = -j by ring]
  exact segment_symm ℝ _ _

@[simp] theorem reverse_carrier {m : ℕ} (P : PrePolygon m) : P.reverse.carrier = P.carrier := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    rw [reverse_edge] at hi
    exact Set.mem_iUnion.2 ⟨_, hi⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    refine Set.mem_iUnion.2 ⟨-i - 1, ?_⟩
    rw [reverse_edge, show (-(-i - 1) - 1 : ZMod (m + 3)) = i by ring]
    exact hi

/-- **Reversing does not move an arc**, it only starts it at the other end. -/
theorem reverse_arc {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.reverse.arc (-a - (k : ZMod (m + 3))) k = P.arc a k := by
  ext z
  rw [mem_arc_iff, mem_arc_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    rw [reverse_edge] at hz
    refine ⟨k - t - 1, by omega, ?_⟩
    rw [show a + ((k - t - 1 : ℕ) : ZMod (m + 3))
        = -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3))) - 1 by
      linear_combination ClosedPolygon.reverse_natCast (n := m + 3) ht]
    exact hz
  · rintro ⟨t, ht, hz⟩
    refine ⟨k - t - 1, by omega, ?_⟩
    rw [reverse_edge, show -(-a - (k : ZMod (m + 3)) + ((k - t - 1 : ℕ) : ZMod (m + 3))) - 1
        = a + (t : ZMod (m + 3)) by
      linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) ht]
    exact hz

/-- **Reversing does not change the edge list either**, up to the order and the naming of each
edge's two ends — which is exactly what `Schoenflies.SameEdges` forgives. -/
theorem sameEdges_reverse_arcPieces {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    SameEdges (P.reverse.arcPieces (-a - (k : ZMod (m + 3))) k) (P.arcPieces a k) := by
  have key : (P.reverse.arcPieces (-a - (k : ZMod (m + 3))) k).map orientPiece
      = ((P.arcPieces a k).map orientPiece).reverse := by
    rw [arcPieces, arcPieces, List.map_map, List.map_map, ← List.map_reverse,
      List.range_eq_range', List.reverse_range', ← List.range_eq_range', List.map_map]
    refine List.map_congr_left fun t ht => ?_
    have htk : t < k := List.mem_range.1 ht
    have he : (0 + k - 1 - t : ℕ) = k - t - 1 := by omega
    simp only [Function.comp_apply, he, reverse_vertex]
    rw [show -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3)))
          = a + ((k - t - 1 : ℕ) : ZMod (m + 3)) + 1 by
        linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) htk,
      show -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3)) + 1)
        = a + ((k - t - 1 : ℕ) : ZMod (m + 3)) by
        linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) htk]
    exact orientPiece_swap (_, _)
  rw [SameEdges, key]
  exact List.reverse_perm _

end PrePolygon

/-! ## The realization theorem, tracking a prescribed splitting

`Schoenflies.exists_prePolygon_split` of `Schoenflies/PrePolygonArc.lean` presents the curve with
the two cut points among its vertices, with no corner condition on them. What remains is to say
*which* arc of that presentation is which of two prescribed arcs, and in which direction the
first is traversed. -/

/-! ## Theorem 2.8 and Corollary 2.9 for a polygon presented with redundant vertices

`Schoenflies.IsPolygonalCrosscut` is stated for `ClosedPolygon`s, and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` that pins the two cut points to be *corners* of the
curve. Nothing in the proof of Theorem 2.8 needs the `corner` field: what it uses of `C`, `J₁`,
`J₂` is that their carriers separate the plane and that their crossing counts are the ones the
edge lists compute. `Schoenflies/PrePolygonSep.lean` supplies both for a `PrePolygon`, so the
whole chain goes through with the cut points anywhere on the curve. -/

variable {m m₁ m₂ : ℕ} {C : PrePolygon m} {J₁ : PrePolygon m₁} {J₂ : PrePolygon m₂}
  {K : List Piece} {a : ZMod (m + 3)} {k : ℕ} {y : Plane}

/-- **The setting of Theorem 2.8, with the cut points unrestricted.** Word for word
`Schoenflies.IsPolygonalCrosscut`, with `PrePolygon` for `ClosedPolygon`. -/
structure IsPrePolygonalCrosscut (C : PrePolygon m) (J₁ : PrePolygon m₁) (J₂ : PrePolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (y : Plane) : Prop where
  /-- The first arc runs forward through at most a full turn. -/
  le : k ≤ m + 3
  /-- `J₁` carries the edges of the first arc together with those of the crosscut. -/
  edges₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K)
  /-- `J₂` carries the edges of the second arc together with those of the crosscut. -/
  edges₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K)
  /-- The crosscut meets the polygon only in points of the first arc … -/
  meets₁ : cover K ∩ C.carrier ⊆ C.arc a k
  /-- … and only in points of the second arc. -/
  meets₂ : cover K ∩ C.carrier ⊆ C.arc (a + k) (m + 3 - k)
  /-- The reference point lies off the polygon … -/
  notMem : y ∉ C.carrier
  /-- … and the crosscut does not enter its region. -/
  avoids : Disjoint (cover K) (connectedComponentIn C.carrierᶜ y)

namespace IsPrePolygonalCrosscut

variable (h : IsPrePolygonalCrosscut C J₁ J₂ K a k y)
include h

/-- **The two arcs may be swapped.** -/
theorem symm : IsPrePolygonalCrosscut C J₂ J₁ K (a + k) (m + 3 - k) y := by
  have hk : k ≤ m + 3 := h.le
  have hnat : m + 3 - (m + 3 - k) = k := by omega
  have hzmod := zmod_add_sub_cancel (k := k) hk a
  refine ⟨by omega, h.edges₂, ?_, h.meets₂, ?_, h.notMem, h.avoids⟩
  · rw [hzmod, hnat]; exact h.edges₁
  · rw [hzmod, hnat]; exact h.meets₁

/-! ### The elementary consequences -/

theorem notMem_cover : y ∉ cover K :=
  fun hy => Set.disjoint_left.1 h.avoids hy (mem_connectedComponentIn h.notMem)

theorem carrier₁ : J₁.carrier = C.arc a k ∪ cover K :=
  PrePolygon.carrier_eq_of_sameEdges h.edges₁

theorem notMem_carrier₁ : y ∉ J₁.carrier :=
  PrePolygon.notMem_carrier_of_sameEdges h.edges₁ h.notMem h.notMem_cover

theorem cover_subset_carrier₁ : cover K ⊆ J₁.carrier := by
  rw [h.carrier₁]; exact Set.subset_union_right

theorem carrier₁_subset : J₁.carrier ⊆ C.carrier ∪ cover K := by
  rw [h.carrier₁]
  exact Set.union_subset_union_left _ (C.arc_subset_carrier a k)

/-- The edges of the crosscut are nondegenerate, because they are edges of `J₁`. -/
theorem nondeg : ∀ Q ∈ K, Q.Nondeg := by
  intro Q hQ
  obtain ⟨R, hR, hRQ⟩ := h.edges₁.symm.exists_mem (List.mem_append_right _ hQ)
  have hRn : (orientPiece R).Nondeg := orientPiece_nondeg (J₁.pieces_nondeg R hR)
  rw [hRQ] at hRn
  rcases orientPiece_eq_or Q with e | e
  · rw [e] at hRn; exact hRn
  · rw [e] at hRn; exact fun hh => hRn hh.symm

/-- A ray direction transverse to every edge of `C` and of the crosscut at once. -/
theorem exists_direction : ∃ u : Plane, Plane.IsDirection u ∧
    (∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) ∧ (∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) := by
  obtain ⟨u, hu, hlev⟩ := exists_direction_hgt_ne (C.pieces ++ K) (by
    intro Q hQ
    rcases List.mem_append.1 hQ with hQ' | hQ'
    · exact C.pieces_nondeg Q hQ'
    · exact h.nondeg Q hQ')
  exact ⟨u, hu, fun Q hQ => hlev Q (List.mem_append_left _ hQ),
    fun Q hQ => hlev Q (List.mem_append_right _ hQ)⟩

/-! ### The two cells -/

theorem regionPairC :
    IsRegionPair C.carrier (farRegion C.carrier y) (connectedComponentIn C.carrierᶜ y) :=
  (C.isSeparating_carrier.isRegionPair_farRegion h.notMem).symm

theorem regionPair₁ :
    IsRegionPair J₁.carrier (connectedComponentIn J₁.carrierᶜ y) (farRegion J₁.carrier y) :=
  J₁.isSeparating_carrier.isRegionPair_farRegion h.notMem_carrier₁

/-- The untouched region of `ℝ² ∖ C` lies in one region of `ℝ² ∖ J₁`, namely the one of `y`. -/
theorem near_subset₁ :
    connectedComponentIn C.carrierᶜ y ⊆ connectedComponentIn J₁.carrierᶜ y := by
  refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
    (mem_connectedComponentIn h.notMem) (fun w hw => ?_)
  have hwC : w ∉ C.carrier := connectedComponentIn_subset _ _ hw
  have hwK : w ∉ cover K := fun hK => Set.disjoint_left.1 h.avoids hK hw
  exact PrePolygon.notMem_carrier_of_sameEdges h.edges₁ hwC hwK

/-- **Lemma 2.6(a), first half**: the cell lies in `Ω ∖ P`. -/
theorem cell_subset₁ : farRegion J₁.carrier y ⊆ farRegion C.carrier y \ cover K :=
  cell_subset_region_diff (P := cover K) C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC h.regionPair₁ h.near_subset₁ h.cover_subset_carrier₁

theorem cell_subset₂ : farRegion J₂.carrier y ⊆ farRegion C.carrier y \ cover K :=
  h.symm.cell_subset₁

/-- **Lemma 2.6(a)**: the cell is a connected component of `Ω ∖ P`. -/
theorem cell_isComponent₁ : ∀ z ∈ farRegion J₁.carrier y,
    connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₁.carrier y :=
  cell_isComponent (P := cover K) C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC h.regionPair₁ h.near_subset₁ h.cover_subset_carrier₁ h.carrier₁_subset

theorem cell_isComponent₂ : ∀ z ∈ farRegion J₂.carrier y,
    connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₂.carrier y :=
  h.symm.cell_isComponent₁

/-- **Lemma 2.6(c)**: the closure of the cell meets the polygon exactly in its arc. -/
theorem closure_cell_inter₁ : closure (farRegion J₁.carrier y) ∩ C.carrier = C.arc a k := by
  rw [closure_cell_inter_curve C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC.right h.regionPair₁ h.near_subset₁, h.carrier₁]
  refine Set.Subset.antisymm ?_ (fun w hw => ⟨Or.inl hw, C.arc_subset_carrier a k hw⟩)
  rintro w ⟨hw | hw, hwC⟩
  · exact hw
  · exact h.meets₁ ⟨hw, hwC⟩

theorem closure_cell_inter₂ :
    closure (farRegion J₂.carrier y) ∩ C.carrier = C.arc (a + k) (m + 3 - k) :=
  h.symm.closure_cell_inter₁

/-! ### Exhaustion: the crossing counts add up -/

/-- **A point off `C ∪ P` is separated from `y` by `C` exactly when it is separated from `y` by
exactly one of `J₁, J₂`.** -/
theorem separates_xor {x : Plane} (hxC : x ∉ C.carrier) (hxK : x ∉ cover K) :
    x ∈ farRegion C.carrier y ↔
      (x ∈ farRegion J₁.carrier y ↔ ¬ x ∈ farRegion J₂.carrier y) := by
  obtain ⟨u, hu, hlevC, hlevK⟩ := h.exists_direction
  have hlev₁ := h.edges₁.hgt_ne (PrePolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hlev₂ := h.edges₂.hgt_ne (PrePolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hxJ₁ := PrePolygon.notMem_carrier_of_sameEdges h.edges₁ hxC hxK
  have hxJ₂ := PrePolygon.notMem_carrier_of_sameEdges h.edges₂ hxC hxK
  rw [← C.parity_ne_iff_mem_farRegion hu hlevC hxC h.notMem,
    ← J₁.parity_ne_iff_mem_farRegion hu hlev₁ hxJ₁ h.notMem_carrier₁,
    ← J₂.parity_ne_iff_mem_farRegion hu hlev₂ hxJ₂ h.symm.notMem_carrier₁]
  have hsx := C.parity_splitting u a h.le h.edges₁ h.edges₂ x
  have hsy := C.parity_splitting u a h.le h.edges₁ h.edges₂ y
  have key : ∀ s₁ s₂ s t₁ t₂ t : ZMod 2, s₁ + s₂ = s → t₁ + t₂ = t →
      (s ≠ t ↔ ((s₁ ≠ t₁) ↔ ¬ (s₂ ≠ t₂))) := by decide
  exact key _ _ _ _ _ _ hsx hsy

/-- **Theorem 2.8, the two cells.** -/
theorem region_eq :
    farRegion C.carrier y \ cover K = farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
  refine Set.Subset.antisymm ?_ (Set.union_subset h.cell_subset₁ h.cell_subset₂)
  rintro w ⟨hwΩ, hwK⟩
  by_cases hw₁ : w ∈ farRegion J₁.carrier y
  · exact Or.inl hw₁
  · refine Or.inr ?_
    by_contra hw₂
    exact hw₁ (((h.separates_xor hwΩ.1 hwK).1 hwΩ).2 hw₂)

/-! ### Corollary 2.9 -/

/-- **The region the crosscut enters is the component of any of its points off `C`.** -/
theorem connectedComponentIn_cover_eq {z : Plane} (hz : z ∈ cover K) (hzC : z ∉ C.carrier) :
    connectedComponentIn C.carrierᶜ z = farRegion C.carrier y :=
  h.regionPairC.left.connectedComponentIn_eq C.isSeparating_carrier
    (diff_subset_farRegion h.avoids ⟨hz, hzC⟩)

/-- **Corollary 2.9, core form.** -/
theorem inter_cover_nonempty {Q : Set Plane} {w₁ w₂ : Plane}
    (hconn : IsPreconnected Q) (hside : Q ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ closure Q) (hw₂ : w₂ ∈ closure Q)
    (hw₁A : w₁ ∈ C.arc a k) (hw₁B : w₁ ∉ C.arc (a + k) (m + 3 - k))
    (hw₂B : w₂ ∈ C.arc (a + k) (m + 3 - k)) (hw₂A : w₂ ∉ C.arc a k) :
    (Q ∩ cover K).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hempty
  have hsub : Q ⊆ farRegion C.carrier y \ cover K :=
    fun z hz => ⟨hside hz, fun hzK => hempty z ⟨hz, hzK⟩⟩
  obtain ⟨z, hz⟩ : Q.Nonempty := by
    by_contra hQ
    rw [Set.not_nonempty_iff_eq_empty] at hQ
    rw [hQ, closure_empty] at hw₁
    simp at hw₁
  have hzcell : z ∈ farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
    rw [← h.region_eq]; exact hsub hz
  rcases hzcell with hz₁ | hz₂
  · have hQ₁ : Q ⊆ farRegion J₁.carrier y := by
      have hcc := hconn.subset_connectedComponentIn hz hsub
      rwa [h.cell_isComponent₁ z hz₁] at hcc
    have hmem : w₂ ∈ closure (farRegion J₁.carrier y) ∩ C.carrier :=
      ⟨closure_mono hQ₁ hw₂, C.arc_subset_carrier _ _ hw₂B⟩
    rw [h.closure_cell_inter₁] at hmem
    exact hw₂A hmem
  · have hQ₂ : Q ⊆ farRegion J₂.carrier y := by
      have hcc := hconn.subset_connectedComponentIn hz hsub
      rwa [h.cell_isComponent₂ z hz₂] at hcc
    have hmem : w₁ ∈ closure (farRegion J₂.carrier y) ∩ C.carrier :=
      ⟨closure_mono hQ₂ hw₁, C.arc_subset_carrier _ _ hw₁A⟩
    rw [h.closure_cell_inter₂] at hmem
    exact hw₁B hmem

/-- **Corollary 2.9 for a second crosscut presented as a simple arc.** -/
theorem arc_inter_cover_nonempty {Q : Set Plane} {w₁ w₂ : Plane}
    (hQ : IsArcBetween Q w₁ w₂) (hside : Q \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁A : w₁ ∈ C.arc a k) (hw₁B : w₁ ∉ C.arc (a + k) (m + 3 - k))
    (hw₂B : w₂ ∈ C.arc (a + k) (m + 3 - k)) (hw₂A : w₂ ∉ C.arc a k) :
    (Q ∩ cover K).Nonempty := by
  obtain ⟨z, hzQ, hzK⟩ := h.inter_cover_nonempty hQ.isPreconnected_diff hside
    hQ.left_mem_closure_diff hQ.right_mem_closure_diff hw₁A hw₁B hw₂B hw₂A
  exact ⟨z, hzQ.1, hzK⟩

/-- **Corollary 2.9 in the shape a plane-graph argument produces it.** -/
theorem alternating_inter_nonempty {A B Q : Set Plane} {p q w₁ w₂ : Plane}
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hQ : IsArcBetween Q w₁ w₂) (hside : Q \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (Q ∩ cover K).Nonempty := by
  refine h.arc_inter_cover_nonempty hQ hside (hA ▸ hw₁.1) ?_ (hB ▸ hw₂.1) ?_
  · rw [hB]; exact fun hmem => hw₁.2 (hAB ▸ Set.mem_inter hw₁.1 hmem)
  · rw [hA]; exact fun hmem => hw₂.2 (hAB ▸ Set.mem_inter hmem hw₂.1)

/-- **Corollary 2.9 with "the same side" read as "the same connected component".** -/
theorem alternating_inter_nonempty_of_same_side {A B Q : Set Plane} {p q w₁ w₂ z : Plane}
    (hz : z ∈ cover K) (hzC : z ∉ C.carrier)
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hQ : IsArcBetween Q w₁ w₂)
    (hside : Q \ {w₁, w₂} ⊆ connectedComponentIn C.carrierᶜ z)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (Q ∩ cover K).Nonempty :=
  h.alternating_inter_nonempty hA hB hAB hQ
    (hside.trans (h.connectedComponentIn_cover_eq hz hzC).subset) hw₁ hw₂

end IsPrePolygonalCrosscut

end Schoenflies

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s : Fin 3} {R : Set Plane}

/-! ## The six-cycle and one remaining edge, as a crosscut

`Graph.IsHexCrosscut` of `Schoenflies/Graph/K33Planar.lean` is the same statement with
`Schoenflies.ClosedPolygon` for `Schoenflies.PrePolygon`; the change is what removes the corner
condition on the two cut points, which is the whole of the remaining gap. -/

/-- **The six-cycle and one remaining edge, realized as a polygonal crosscut**, with the two cut
points wherever the drawing put them. -/
def IsPreHexCrosscut (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) (s : Fin 3) : Prop :=
  ∃ (m m₁ m₂ : ℕ) (C : PrePolygon m) (J₁ : PrePolygon m₁) (J₂ : PrePolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (yref : Plane),
      C.carrier = hexSet drawing e ∧
      C.arc a k = edgesCover drawing (arcA e s) ∧
      C.arc (a + k) (m + 3 - k) = edgesCover drawing (arcB e s) ∧
      cover K = edgeArc drawing (e s (s + 1)) ∧
      IsPrePolygonalCrosscut C J₁ J₂ K a k yref

namespace IsK33Config

/-! ### The contradiction -/

/-- **The two remaining edges indexed by `s` and `s + 1` cannot lie in one region.** Their four
ends alternate around the six-cycle, so `cor:alternating-crosscuts` makes them meet; but distinct
edges of a plane graph meet only at shared vertices, and these two share none. -/
theorem false_of_isPreHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hcross : IsPreHexCrosscut drawing e s) (hsep : IsSeparating (hexSet drawing e))
    (hR : IsRegionOf (hexSet drawing e) R)
    (h1 : openArc (drawing (e s (s + 1))) ⊆ R)
    (h2 : openArc (drawing (e (s + 1) (s + 1 + 1))) ⊆ R) : False := by
  obtain ⟨m, m₁, m₂, C, J₁, J₂, K, a, k, yref, hcar, hA, hB, hK, hcc⟩ := hcross
  obtain ⟨z, hz⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  have hzK : z ∈ cover K := by rw [hK]; exact h.chord_openArc_subset_edgeArc hd s hz
  have hzC : z ∉ C.carrier := by rw [hcar]; exact h.chord_openArc_subset_compl hd s hz
  have hzR : z ∈ R := h1 hz
  have hside : edgeArc drawing (e (s + 1) (s + 1 + 1)) \ ({x (s + 1), y (s + 1 + 1)} : Set Plane)
      ⊆ connectedComponentIn C.carrierᶜ z := by
    rw [hcar, hR.connectedComponentIn_eq hsep hzR, ← h.chord_openArc_eq hd (s + 1)]
    exact h2
  obtain ⟨w, hw₁, hw₂⟩ := hcc.alternating_inter_nonempty_of_same_side hzK hzC hA hB
    (h.arcs_inter hd s) (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1 + 1))) hside
    (h.x_succ_mem_arcA hd s) (h.y_succ_mem_arcB hd s)
  have hs1 : ∀ s : Fin 3, s + 1 ≠ s := by decide
  have hdis := h.chords_disjoint hd (hs1 s)
  rw [Set.eq_empty_iff_forall_notMem] at hdis
  exact hdis w ⟨hw₁, by rwa [hK] at hw₂⟩

end IsK33Config

end Graph
end

section
-- module Solutions.Q146_CD.Graph_Relabel
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Relabelling the edges of a multigraph

Mathlib's `Graph.map` changes vertex names and deliberately leaves edge names fixed.  The ear
construction needs the complementary operation: give the finitely many edges of an ambient path
fresh abstract cell names while retaining every vertex and every incidence.

The relabelling map only has to be injective on the graph's edge set.  Walks, paths, and path
graphs then push forward by mapping their edge lists.
-/

open Set
open Schoenflies
open unitInterval
open scoped _root_.Graph

namespace Graph

variable {α β δ : Type*} {G : Graph α β} {f : β → δ}

/-- Relabel every edge of `G` by a map injective on `E(G)`, without changing its vertices. -/
def relabelEdges (G : Graph α β) (f : β → δ) (hf : InjOn f E(G)) : Graph α δ where
  vertexSet := V(G)
  edgeSet := f '' E(G)
  IsLink d x y := ∃ e ∈ E(G), f e = d ∧ G.IsLink e x y
  isLink_symm := by
    intro d _
    constructor
    intro x y
    rintro ⟨e, he, rfl, hxy⟩
    exact ⟨e, he, rfl, hxy.symm⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro d x y v w ⟨e, he, hfe, hxy⟩ ⟨e', he', hfe', hvw⟩
    have heq : e = e' := hf he he' (hfe.trans hfe'.symm)
    exact hxy.left_eq_or_eq (heq ▸ hvw)
  edge_mem_iff_exists_isLink := by
    intro d
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
      exact ⟨x, y, e, he, rfl, hxy⟩
    · rintro ⟨x, y, e, he, rfl, -⟩
      exact ⟨e, he, rfl⟩
  left_mem_of_isLink := by
    rintro d x y ⟨e, -, -, hxy⟩
    exact hxy.left_mem

@[simp] theorem vertexSet_relabelEdges (G : Graph α β) (f : β → δ) (hf : InjOn f E(G)) :
    V(G.relabelEdges f hf) = V(G) := rfl

@[simp] theorem edgeSet_relabelEdges (G : Graph α β) (f : β → δ) (hf : InjOn f E(G)) :
    E(G.relabelEdges f hf) = f '' E(G) := rfl

@[simp] theorem relabelEdges_isLink (G : Graph α β) (f : β → δ) (hf : InjOn f E(G))
    (d : δ) (x y : α) :
    (G.relabelEdges f hf).IsLink d x y ↔
      ∃ e ∈ E(G), f e = d ∧ G.IsLink e x y :=
  Iff.rfl

/-- An old link survives after its edge receives its new name. -/
theorem IsLink.relabelEdges (hf : InjOn f E(G)) (h : G.IsLink e x y) :
    (G.relabelEdges f hf).IsLink (f e) x y :=
  ⟨e, h.edge_mem, rfl, h⟩

/-- A walk pushes forward along an injective relabelling of its edges. -/
theorem IsWalk.relabelEdges (hf : InjOn f E(G)) (h : G.IsWalk u W v) :
    (G.relabelEdges f hf).IsWalk u (W.map f) v := by
  induction h with
  | nil hx => exact .nil hx
  | cons hl _ ih => exact .cons (hl.relabelEdges hf) ih

/-- Relabelling preserves graph finiteness. -/
theorem Finite.relabelEdges [G.Finite] (hf : InjOn f E(G)) :
    (G.relabelEdges f hf).Finite where
  finite_vertexSet := by
    rw [vertexSet_relabelEdges]
    exact _root_.Graph.finite_vertexSet G
  finite_edgeSet := by
    rw [edgeSet_relabelEdges]
    exact (_root_.Graph.finite_edgeSet G).image f

/-- Relabelling preserves connectedness because every old walk pushes forward. -/
theorem Connected.relabelEdges (h : G.Connected) (hf : InjOn f E(G)) :
    (G.relabelEdges f hf).Connected := by
  constructor
  · simpa using h.nonempty
  · intro u hu v hv
    obtain ⟨W, hW⟩ := h.reaches (by simpa using hu) (by simpa using hv)
    exact ⟨W.map f, hW.relabelEdges hf⟩

/-! ### Relabelling a drawing -/

end Graph
end

section
-- module Solutions.Q146_CD.LocalGrid
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The local source grid, and the missing hypothesis of the anchored square mesh

Two things, and the second is the more important.

## 1. `prop:anchored-square-mesh` clause 5 — which hypothesis repairs it

`docs/ROADMAP.md` records clause 5, *the skeleton of `T` is 2-connected*, as **false** for
`Schoenflies.squareMesh` when the fresh-point set is too small, and names
`Schoenflies.FreshDense` as "the shape the missing hypothesis should take". The first section
of this module checks that, and the answer is **no: `FreshDense` alone does not repair
clause 5.**

* `Schoenflies.freshDense_of_four_sqrt_two_le` — for `4√2 ≤ δ`, `FreshDense fresh δ` holds for
  **every** list `fresh`, the empty one included, because `S` itself has diameter `2√2`. So
  `FreshDense fresh δ` is vacuous at large `δ` and excludes nothing.
* `Schoenflies.freshDense_not_isTwoConnected` — the counterexample made formal: at
  `δ = 4√2` the hypotheses `0 < δ` and `FreshDense [] δ` both hold and
  `squareMesh δ [] anchors` is still not 2-connected.

What does repair it is `FreshDense` **together with a bound on `δ`**:

* `Schoenflies.exists_two_distinct_fresh_of_freshDense` — `FreshDense fresh δ` and `δ < 4`
  force two distinct fresh points. (`4` is not the sharp constant — `4√2` is — but it is the
  one a side of `S`, whose two ends are `2` apart, gives with no work. The blueprint's own
  `δ = ε_n = 2^{-n}` is far below either.)

and two distinct fresh points is exactly the right amount, because *fewer* is always fatal:

* `Schoenflies.not_isTwoConnected_meshGraph_of_fresh_subsingleton` — a mesh whose fresh points
  are not two distinct points is **never** 2-connected. This closes the case
  `SquareMeshFixed.lean` left open in prose: with exactly one fresh point `z` the mesh is
  connected, but `z` is a cut vertex, because the spoke at `z` is the only edge of the mesh
  that changes the sup norm and every other edge preserves it.

So the correct statement of clause 5 carries the hypothesis `∃ z ∈ fresh, ∃ w ∈ fresh, z ≠ w`,
which `FreshDense fresh δ ∧ δ < 4` supplies, and which is necessary as well as sufficient in
the degenerate range.

## 2. `prop:local-grid-attachment` — the grid

The blueprint's proof begins: *"Choose sufficiently fine finite horizontal and vertical
coordinate sets in `W`, with at least two intervals in each direction. Begin with the outer
rectangle of the resulting grid `K` … By `lem:subdivision-ear-preserve`, `K` is 2-connected."*

`Schoenflies.localGrid` is that `K`, as a `def`: the uniform `k × k` grid on the closed square
`W` of centre `p` and radius `s`. `Schoenflies/SquareMeshConnected.lean` and
`Schoenflies/SquareMeshFixed.lean` supply everything combinatorial about a grid, so what is
added here is the *quantitative* clause the proposition needs — every closed grid rectangle has
diameter `< ε` — together with the instantiation of the general grid lemmas at these
coordinates.

The rest of `prop:local-grid-attachment` — the overlay of `K` with the polygonal nonboundary
skeleton of `Γ`, the three cases, and the component-joining loop — is **not** here; see the
report.

## Blueprint

* `prop:anchored-square-mesh`, clause 5 — `freshDense_of_four_sqrt_two_le`,
  `freshDense_not_isTwoConnected`, `exists_two_distinct_fresh_of_freshDense`,
  `not_isTwoConnected_meshGraph_of_fresh_subsingleton`,
  `not_isTwoConnected_squareMesh_of_fresh_subsingleton`.
* `prop:local-grid-attachment`, the grid `K` — `localGrid`, `localGrid_isTwoConnected`,
  `localGrid_subdivide_isTwoConnected`, `localGrid_isDrawing`, `localGrid_outer_cycle`.
* `prop:local-grid-attachment`, clause 3 — `dist_le_of_mem_localGridCell` (the closed grid
  rectangle), `dist_lt_of_avoiding_localGrid` (a connected subset of `W` missing the grid),
  `localGridCount`, `localGridCount_spec`, `localGrid_fine`.
* `lem:union-two-connected` — used through `Graph.IsTwoConnected.union` and
  `Graph.IsTwoConnected.ear`; `Graph.IsTwoConnected.of_le_of_vertexSet_subset` is the
  "spanning 2-connected subgraph" form the assembly needs.
-/

open Metric Set
open scoped Graph

/-! ### A spanning 2-connected subgraph makes the whole graph 2-connected

The form in which every assembly out of `lem:union-two-connected` is finished: a chain of
unions produces *some* graph, and what the consumer wants is 2-connectivity of the graph it
started from. As long as the assembled graph is a subgraph that misses no vertex, the two
coincide — extra edges can only help connectivity. -/

namespace Graph

variable {α β : Type*} {H K : Graph α β}

/-- Connectedness passes up to a graph with the same vertices. -/
theorem Connected.of_spanning_le (hH : H.Connected) (hHK : H ≤ K) (hV : V(K) ⊆ V(H)) :
    K.Connected := by
  obtain ⟨u, hu⟩ := hH.nonempty
  exact Connected.of_hub (hHK.vertexSet_mono hu) fun x hx => (hH.reaches hu (hV hx)).mono hHK

end Graph
end


