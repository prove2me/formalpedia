-- Prove2me | Definitions.Def_KServer_glue2
-- name    : KServer_glue2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T13:00:06.171533+00:00
-- url     : https://prove2.me/theorems/831fa688-30dc-4110-b6fe-7a3c8151cc5f
-- title:
--   Binary and theta gluings of marked metric spaces
-- statement:
--   Elementary gluing constructions for the corrected BCR geometry: the **binary glue** of $A$ at $a$ to $B$ at $b$ (representing the identified point once, with the four-case distance and its triangle inequality); the **three-copy path** $X \to X \to X$ of a marked space, with all pairwise copy distance formulas and $d(\mathrm{start}, \mathrm{stop}) = 3\,d(s,t)$; and the **theta gluing** — two copies of a marked space sharing BOTH marked points, i.e. Bubeck–Coester–Rabani's cycle of six copies with orientation pattern $(+,+,+,-,-,-)$ — via a side-tagged helper distance (direct route, the two around-routes on equal sides, the two seam-routes across sides) whose triangle inequality is verified in all thirty-six route combinations. Within a side the direct route always wins, so each copy embeds isometrically; the separation property holds because the second copy's representatives exclude the shared points.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Section 4 (construction of the spaces), corrected orientation.

import Mathlib

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

/-! ### Binary and double gluings of metric spaces

`glueDist` is the distance on `A ⊕ B` obtained by gluing the marked point
`a : A` to the marked point `b : B` (representing the identified point by
`Sum.inl a`; the representative `Sum.inr b` is kept at distance `0`-free by
never being used — the space is a metric space on the subtype excluding it,
but we work with the pseudometric on the sum and restrict requests away
from `Sum.inr b` instead, or use `GluePoint`).

`doubleDist` is the distance on the both-ends gluing of two copies of one
space `U` with marked points `s ≠ t`: copies `false` and `true` of `U`
share their `s` points and share their `t` points ("theta" gluing). The
second copy's representatives exclude `s` and `t`. -/

variable {A B : Type*} [MetricSpace A] [MetricSpace B]

/-- Points of the gluing of `A` (at `a`) to `B` (at `b`): all of `A`, plus
`B` minus its glue point (which lives on as `Sum.inl a`). -/
abbrev GluePoint (B : Type*) (b : B) : Type _ := {y : B // y ≠ b}

/-- Distance for the gluing of `a : A` with `b : B`. -/
noncomputable def glueDist (a : A) (b : B) :
    A ⊕ GluePoint B b → A ⊕ GluePoint B b → ℝ
  | Sum.inl x, Sum.inl y => dist x y
  | Sum.inl x, Sum.inr y => dist x a + dist b y.1
  | Sum.inr x, Sum.inl y => dist x.1 b + dist a y
  | Sum.inr x, Sum.inr y => dist x.1 y.1

theorem glueDist_self (a : A) (b : B) (p : A ⊕ GluePoint B b) :
    glueDist a b p p = 0 := by
  rcases p with x | x <;> simp [glueDist]

theorem glueDist_comm (a : A) (b : B) (p q : A ⊕ GluePoint B b) :
    glueDist a b p q = glueDist a b q p := by
  rcases p with x | x <;> rcases q with y | y <;>
    simp [glueDist, dist_comm] <;> ring

theorem glueDist_triangle (a : A) (b : B) (p q r : A ⊕ GluePoint B b) :
    glueDist a b p r ≤ glueDist a b p q + glueDist a b q r := by
  rcases p with x | x <;> rcases q with y | y <;> rcases r with z | z <;>
    simp only [glueDist]
  · exact dist_triangle x y z
  · linarith [dist_triangle x y a]
  · linarith [dist_triangle x a z, dist_nonneg (x := b) (y := y.1),
      dist_nonneg (x := y.1) (y := b)]
  · linarith [dist_triangle b y.1 z.1]
  · linarith [dist_triangle a y z]
  · linarith [dist_triangle x.1 b z.1, dist_nonneg (x := a) (y := y),
      dist_nonneg (x := y) (y := a)]
  · linarith [dist_triangle x.1 y.1 b]
  · exact dist_triangle x.1 y.1 z.1

/-! ### The double (theta) gluing -/

variable {U : Type*} [MetricSpace U]

/-- Helper distance on side-tagged points for the both-ends gluing of two
copies of `U` at `s` and at `t`. On equal sides: the direct distance or a
route around through the other copy; on different sides: through one of the
two shared points. Defined on all of `Bool × U` as a pseudometric (the
shared points are represented twice); the metric space restricts the second
copy away from `s` and `t`. -/
noncomputable def thetaDist (s t : U) : Bool → U → Bool → U → ℝ :=
  fun b1 x b2 y =>
    if b1 = b2 then
      min (dist x y)
        (min (dist x s + dist s t + dist t y) (dist x t + dist s t + dist s y))
    else
      min (dist x s + dist s y) (dist x t + dist t y)

theorem thetaDist_self (s t : U) (b : Bool) (x : U) :
    thetaDist s t b x b x = 0 := by
  unfold thetaDist
  rw [if_pos rfl]
  have h2 : (0:ℝ) ≤ dist x s + dist s t + dist t x := by positivity
  have h3 : (0:ℝ) ≤ dist x t + dist s t + dist s x := by positivity
  rw [dist_self x, min_eq_left (le_min h2 h3)]

theorem thetaDist_comm (s t : U) (b1 : Bool) (x : U) (b2 : Bool) (y : U) :
    thetaDist s t b1 x b2 y = thetaDist s t b2 y b1 x := by
  unfold thetaDist
  by_cases h : b1 = b2
  · rw [if_pos h, if_pos h.symm, dist_comm x y]
    rw [dist_comm x s, dist_comm t y, dist_comm x t, dist_comm s y]
    rw [min_comm (dist s x + dist s t + dist y t) (dist t x + dist s t + dist y s)]
    congr 2
    · ring
    · ring
  · rw [if_neg h, if_neg (fun hc => h hc.symm), dist_comm x s, dist_comm s y,
      dist_comm x t, dist_comm t y]
    congr 1
    · ring
    · ring

theorem thetaDist_nonneg (s t : U) (b1 : Bool) (x : U) (b2 : Bool) (y : U) :
    0 ≤ thetaDist s t b1 x b2 y := by
  unfold thetaDist
  split_ifs
  · refine le_min dist_nonneg (le_min (by positivity) (by positivity))
  · exact le_min (by positivity) (by positivity)

/-- The theta triangle inequality, on the full tagged helper. -/
theorem thetaDist_triangle (s t : U) (b1 : Bool) (x : U) (b2 : Bool) (y : U)
    (b3 : Bool) (z : U) :
    thetaDist s t b1 x b3 z ≤ thetaDist s t b1 x b2 y + thetaDist s t b2 y b3 z := by
  have T : ∀ a b c : U, dist a c ≤ dist a b + dist b c := dist_triangle
  have N : ∀ a b : U, (0:ℝ) ≤ dist a b := fun a b => dist_nonneg
  unfold thetaDist
  by_cases h12 : b1 = b2 <;> by_cases h23 : b2 = b3
  · -- same, same, same
    rw [if_pos h12, if_pos h23, if_pos (h12.trans h23)]
    simp only [← min_add_add_right, ← min_add_add_left, le_min_iff]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · exact min_le_of_left_le (T x y z)
    · refine min_le_of_right_le (min_le_of_left_le ?_)
      have := T t y z
      linarith
    · refine min_le_of_right_le (min_le_of_right_le ?_)
      have := T s y z
      linarith
    · refine min_le_of_right_le (min_le_of_left_le ?_)
      have := T x y s
      linarith
    · refine min_le_of_right_le (min_le_of_left_le ?_)
      linarith [N t y, N y s, N s t]
    · refine min_le_of_right_le (min_le_of_left_le ?_)
      have h1 : dist x s ≤ dist x t + dist t s := T x t s
      have h2 : dist t s = dist s t := dist_comm t s
      linarith [N s y, N y s]
    · refine min_le_of_right_le (min_le_of_right_le ?_)
      have := T x y t
      linarith
    · refine min_le_of_right_le (min_le_of_right_le ?_)
      have h1 : dist x t ≤ dist x s + dist s t := T x s t
      linarith [N t y, N y t]
    · refine min_le_of_right_le (min_le_of_right_le ?_)
      linarith [N s y, N y t, N s t]
  · -- same, diff: b1 = b2, b2 ≠ b3, so b1 ≠ b3
    rw [if_pos h12, if_neg h23, if_neg (fun hc => h23 (h12.symm.trans hc))]
    simp only [← min_add_add_right, ← min_add_add_left, le_min_iff]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · refine min_le_of_left_le ?_
      have := T x y s
      linarith
    · refine min_le_of_left_le ?_
      linarith [N s t, N t y, N y s]
    · refine min_le_of_left_le ?_
      have h1 : dist x s ≤ dist x t + dist t s := T x t s
      have h2 : dist t s = dist s t := dist_comm t s
      linarith [N s y, N y s]
    · refine min_le_of_right_le ?_
      have := T x y t
      linarith
    · refine min_le_of_right_le ?_
      have h1 : dist x t ≤ dist x s + dist s t := T x s t
      linarith [N t y, N y t]
    · refine min_le_of_right_le ?_
      linarith [N s t, N s y, N y t]
  · -- diff, same: b1 ≠ b2, b2 = b3, so b1 ≠ b3
    rw [if_neg h12, if_pos h23, if_neg (fun hc => h12 (hc.trans h23.symm))]
    simp only [← min_add_add_right, ← min_add_add_left, le_min_iff]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · refine min_le_of_left_le ?_
      have := T s y z
      linarith [dist_comm s y]
    · refine min_le_of_right_le ?_
      have := T t y z
      linarith [dist_comm t y]
    · refine min_le_of_right_le ?_
      have h1 : dist x t ≤ dist x s + dist s t := T x s t
      linarith [dist_comm s y, N s y, N y s]
    · refine min_le_of_right_le ?_
      linarith [dist_comm t y, N t y, N y s, N s t]
    · refine min_le_of_left_le ?_
      linarith [dist_comm s y, N s y, N y t, N s t]
    · refine min_le_of_left_le ?_
      have h1 : dist x s ≤ dist x t + dist t s := T x t s
      have h2 : dist t s = dist s t := dist_comm t s
      linarith [dist_comm t y, N t y, N y t]
  · -- diff, diff: b1 = b3 (booleans)
    have h13 : b1 = b3 := by
      rcases b1 <;> rcases b2 <;> rcases b3 <;> simp_all
    rw [if_neg h12, if_neg h23, if_pos h13]
    simp only [← min_add_add_right, ← min_add_add_left, le_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · refine min_le_of_left_le ?_
      have := T x s z
      linarith [N s y, N y s]
    · refine min_le_of_right_le (min_le_of_right_le ?_)
      have h1 : dist s t ≤ dist s y + dist y t := T s y t
      linarith [dist_comm s y, dist_comm y t, dist_comm t y, dist_comm y s]
    · refine min_le_of_right_le (min_le_of_left_le ?_)
      have h1 : dist s t ≤ dist s y + dist y t := T s y t
      linarith
    · refine min_le_of_left_le ?_
      have := T x t z
      linarith [N t y, N y t]

/-- The direct route always wins on equal sides. -/
theorem thetaDist_same (s t : U) (b : Bool) (x y : U) :
    thetaDist s t b x b y = dist x y := by
  unfold thetaDist
  rw [if_pos rfl]
  refine min_eq_left (le_min ?_ ?_)
  · calc dist x y ≤ dist x s + dist s y := dist_triangle x s y
      _ ≤ dist x s + (dist s t + dist t y) := by
          have := dist_triangle s t y
          linarith
      _ = dist x s + dist s t + dist t y := by ring
  · calc dist x y ≤ dist x t + dist t y := dist_triangle x t y
      _ ≤ dist x t + (dist t s + dist s y) := by
          have := dist_triangle t s y
          linarith
      _ = dist x t + dist s t + dist s y := by
          rw [dist_comm t s]
          ring

theorem thetaDist_cross (s t : U) (x y : U) {b1 b2 : Bool} (h : b1 ≠ b2) :
    thetaDist s t b1 x b2 y
      = min (dist x s + dist s y) (dist x t + dist t y) := by
  unfold thetaDist
  rw [if_neg h]

/-- Points of the theta gluing: two copies of `U` sharing `s` and `t`; the
second copy's representatives exclude the shared points. -/
abbrev ThetaPoint (U : Type*) (s t : U) : Type _ :=
  U ⊕ {u : U // u ≠ s ∧ u ≠ t}

namespace ThetaPoint

variable (s t : U)

/-- The side tag of a theta point. -/
def side : ThetaPoint U s t → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

/-- The underlying point. -/
def pt : ThetaPoint U s t → U
  | Sum.inl x => x
  | Sum.inr x => x.1

noncomputable def dist' (p q : ThetaPoint U s t) : ℝ :=
  thetaDist s t (side s t p) (pt s t p) (side s t q) (pt s t q)

theorem dist'_self (p : ThetaPoint U s t) : dist' s t p p = 0 :=
  thetaDist_self s t _ _

theorem dist'_comm (p q : ThetaPoint U s t) :
    dist' s t p q = dist' s t q p :=
  thetaDist_comm s t _ _ _ _

theorem dist'_triangle (p q r : ThetaPoint U s t) :
    dist' s t p r ≤ dist' s t p q + dist' s t q r :=
  thetaDist_triangle s t _ _ _ _ _ _

theorem dist'_eq_zero (hst : s ≠ t) (p q : ThetaPoint U s t)
    (h : dist' s t p q = 0) : p = q := by
  rcases p with x | x <;> rcases q with y | y
  · have h1 : dist' s t (Sum.inl x) (Sum.inl y) = dist x y :=
      thetaDist_same s t false x y
    rw [h1] at h
    rw [dist_eq_zero] at h
    rw [h]
  · have h1 : dist' s t (Sum.inl x) (Sum.inr y)
        = min (dist x s + dist s y.1) (dist x t + dist t y.1) :=
      thetaDist_cross s t x y.1 (by simp [side])
    rw [h1] at h
    exfalso
    rcases min_eq_iff.mp h with ⟨h2, -⟩ | ⟨h2, -⟩
    · have h3 : dist s y.1 = 0 := by
        have := dist_nonneg (x := x) (y := s)
        have := dist_nonneg (x := s) (y := y.1)
        linarith
      exact y.2.1 (by rw [dist_eq_zero] at h3; exact h3.symm)
    · have h3 : dist t y.1 = 0 := by
        have := dist_nonneg (x := x) (y := t)
        have := dist_nonneg (x := t) (y := y.1)
        linarith
      exact y.2.2 (by rw [dist_eq_zero] at h3; exact h3.symm)
  · have h1 : dist' s t (Sum.inr x) (Sum.inl y)
        = min (dist x.1 s + dist s y) (dist x.1 t + dist t y) :=
      thetaDist_cross s t x.1 y (by simp [side])
    rw [h1] at h
    exfalso
    rcases min_eq_iff.mp h with ⟨h2, -⟩ | ⟨h2, -⟩
    · have h3 : dist x.1 s = 0 := by
        have := dist_nonneg (x := x.1) (y := s)
        have := dist_nonneg (x := s) (y := y)
        linarith
      exact x.2.1 (by rw [dist_eq_zero] at h3; exact h3)
    · have h3 : dist x.1 t = 0 := by
        have := dist_nonneg (x := x.1) (y := t)
        have := dist_nonneg (x := t) (y := y)
        linarith
      exact x.2.2 (by rw [dist_eq_zero] at h3; exact h3)
  · have h1 : dist' s t (Sum.inr x) (Sum.inr y) = dist x.1 y.1 :=
      thetaDist_same s t true x.1 y.1
    rw [h1] at h
    rw [dist_eq_zero] at h
    rw [show x = y from Subtype.ext h]

/-- The theta gluing as a metric space. -/
noncomputable def metric (hst : s ≠ t) : MetricSpace (ThetaPoint U s t) where
  dist := dist' s t
  dist_self := dist'_self s t
  dist_comm := dist'_comm s t
  dist_triangle p q r := dist'_triangle s t p q r
  eq_of_dist_eq_zero {p q} h := dist'_eq_zero s t hst p q h

end ThetaPoint

/-! ### The binary glue as a metric space, and the three-copy path -/

theorem glueDist_eq_zero {a : A} {b : B} (hb : ∀ y : GluePoint B b, True)
    (p q : A ⊕ GluePoint B b) (h : glueDist a b p q = 0) : p = q := by
  rcases p with x | x <;> rcases q with y | y <;> simp only [glueDist] at h
  · rw [dist_eq_zero] at h
    rw [h]
  · exfalso
    have h1 : dist b y.1 = 0 := by
      have := dist_nonneg (x := x) (y := a)
      have := dist_nonneg (x := b) (y := y.1)
      linarith
    exact y.2 (by rw [dist_eq_zero] at h1; exact h1.symm)
  · exfalso
    have h1 : dist x.1 b = 0 := by
      have := dist_nonneg (x := x.1) (y := b)
      have := dist_nonneg (x := a) (y := y)
      linarith
    exact x.2 (by rw [dist_eq_zero] at h1; exact h1)
  · rw [dist_eq_zero] at h
    rw [show x = y from Subtype.ext h]

/-- The binary gluing (`a : A` identified with `b : B`) as a metric space. -/
noncomputable def glueMetric (a : A) (b : B) :
    MetricSpace (A ⊕ GluePoint B b) where
  dist := glueDist a b
  dist_self := glueDist_self a b
  dist_comm := glueDist_comm a b
  dist_triangle p q r := glueDist_triangle a b p q r
  eq_of_dist_eq_zero {p q} h := glueDist_eq_zero (fun _ => trivial) p q h

/-! ### The three-copy path of a marked space

`chain3` glues three copies of `X` in a row: copy 0's `t` to copy 1's `s`,
copy 1's `t` to copy 2's `s`. Marked points: copy 0's `s` and copy 2's `t`. -/

variable (X : Type*) [MetricSpace X]

/-- Two copies glued: copy 0's `t` = copy 1's `s`. -/
abbrev Chain2Point (s t : X) : Type _ := X ⊕ GluePoint X s

@[reducible] noncomputable def chain2Metric (s t : X) :
    MetricSpace (Chain2Point X s t) := glueMetric t s

/-- Three copies glued in a row. -/
abbrev Chain3Point (s t : X) : Type _ :=
  Chain2Point X s t ⊕ GluePoint X s

@[reducible] noncomputable def chain3Metric (s t : X) (hst : s ≠ t) :
    MetricSpace (Chain3Point X s t) :=
  letI := chain2Metric X s t
  glueMetric (Sum.inr (⟨t, hst.symm⟩ : GluePoint X s)) s

namespace Chain3

variable {X : Type*} [MetricSpace X] (s t : X) (hst : s ≠ t)

/-- The start of the path: copy 0's `s`. -/
def start : Chain3Point X s t := Sum.inl (Sum.inl s)

/-- The end of the path: copy 2's `t`. -/
def stop : Chain3Point X s t := Sum.inr ⟨t, hst.symm⟩

/-- The three copy embeddings. -/
def emb0 (x : X) : Chain3Point X s t := Sum.inl (Sum.inl x)

def emb1 (x : X) (hx : x ≠ s) : Chain3Point X s t := Sum.inl (Sum.inr ⟨x, hx⟩)

def emb2 (x : X) (hx : x ≠ s) : Chain3Point X s t := Sum.inr ⟨x, hx⟩

/-- Distances in the three-copy path. -/
theorem dist_emb0_emb0 (x y : X) :
    letI := chain3Metric X s t hst
    dist (emb0 s t x) (emb0 s t y) = dist x y := rfl

theorem dist_emb0_emb1 (x y : X) (hy : y ≠ s) :
    letI := chain3Metric X s t hst
    dist (emb0 s t x) (emb1 s t y hy) = dist x t + dist s y := rfl

theorem dist_emb1_emb1 (x y : X) (hx : x ≠ s) (hy : y ≠ s) :
    letI := chain3Metric X s t hst
    dist (emb1 s t x hx) (emb1 s t y hy) = dist x y := rfl

theorem dist_emb0_emb2 (x y : X) (hy : y ≠ s) :
    letI := chain3Metric X s t hst
    dist (emb0 s t x) (emb2 s t y hy) = dist x t + dist s t + dist s y := by
  letI := chain2Metric X s t
  show glueDist _ s _ _ = _
  show glueDist t s (Sum.inl x) (Sum.inr ⟨t, hst.symm⟩) + dist s y = _
  unfold glueDist
  ring

theorem dist_emb1_emb2 (x y : X) (hx : x ≠ s) (hy : y ≠ s) :
    letI := chain3Metric X s t hst
    dist (emb1 s t x hx) (emb2 s t y hy) = dist x t + dist s y := by
  letI := chain2Metric X s t
  show glueDist _ s _ _ = _
  show glueDist t s (Sum.inr ⟨x, hx⟩) (Sum.inr ⟨t, hst.symm⟩) + dist s y = _
  unfold glueDist
  rfl

theorem dist_emb2_emb2 (x y : X) (hx : x ≠ s) (hy : y ≠ s) :
    letI := chain3Metric X s t hst
    dist (emb2 s t x hx) (emb2 s t y hy) = dist x y := rfl

/-- The path has length `3 · dist s t`. -/
theorem dist_start_stop :
    letI := chain3Metric X s t hst
    dist (start s t) (stop s t hst) = 3 * dist s t := by
  have h := dist_emb0_emb2 s t hst s t hst.symm
  show (chain3Metric X s t hst).dist (emb0 s t s) (emb2 s t t hst.symm)
    = 3 * dist s t
  rw [show (chain3Metric X s t hst).dist (emb0 s t s) (emb2 s t t hst.symm)
    = dist s t + dist s t + dist s t from h]
  ring

end Chain3

/-! ### The BCR level step: theta of the three-copy path -/

instance {X : Type*} [Fintype X] [DecidableEq X] (b : X) :
    Fintype (GluePoint X b) := by
  unfold GluePoint
  infer_instance

instance {X : Type*} [DecidableEq X] (b : X) :
    DecidableEq (GluePoint X b) := by
  unfold GluePoint
  infer_instance

namespace ThetaChain

variable {X : Type*} [MetricSpace X] (s t : X) (hst : s ≠ t)

/-- One BCR level step: the theta gluing of two three-copy paths of `X`. -/
abbrev Step : Type _ :=
  ThetaPoint (Chain3Point X s t) (Chain3.start s t) (Chain3.stop s t hst)

/-- The three-copy path is nondegenerate. -/
theorem start_ne_stop : Chain3.start s t ≠ Chain3.stop s t hst := by
  unfold Chain3.start Chain3.stop
  simp

@[reducible] noncomputable def stepMetric : MetricSpace (Step s t hst) :=
  letI := chain3Metric X s t hst
  ThetaPoint.metric (Chain3.start s t) (Chain3.stop s t hst)
    (start_ne_stop s t hst)

/-- The new marked points: the shared endpoints of the theta gluing. -/
def stepS : Step s t hst := Sum.inl (Chain3.start s t)

def stepT : Step s t hst := Sum.inl (Chain3.stop s t hst)

theorem stepS_ne_stepT : stepS s t hst ≠ stepT s t hst := by
  unfold stepS stepT
  intro h
  exact start_ne_stop s t hst (Sum.inl_injective h)

/-- The marked points of the step are at distance `3 · dist s t`. -/
theorem dist_stepS_stepT :
    letI := stepMetric s t hst
    dist (stepS s t hst) (stepT s t hst) = 3 * dist s t := by
  letI := chain3Metric X s t hst
  show ThetaPoint.dist' (Chain3.start s t) (Chain3.stop s t hst)
    (Sum.inl (Chain3.start s t)) (Sum.inl (Chain3.stop s t hst)) = _
  unfold ThetaPoint.dist'
  rw [show ThetaPoint.side (Chain3.start s t) (Chain3.stop s t hst)
      (Sum.inl (Chain3.start s t)) = false from rfl,
    show ThetaPoint.side (Chain3.start s t) (Chain3.stop s t hst)
      (Sum.inl (Chain3.stop s t hst)) = false from rfl]
  rw [thetaDist_same]
  show dist (Chain3.start s t) (Chain3.stop s t hst) = 3 * dist s t
  exact Chain3.dist_start_stop s t hst

end ThetaChain


