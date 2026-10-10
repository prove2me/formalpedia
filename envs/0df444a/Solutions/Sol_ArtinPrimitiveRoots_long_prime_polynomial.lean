-- Prove2me | solution 1 for ArtinPrimitiveRoots.long_prime_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T16:37:30.631501+00:00
-- url     : https://prove2.me/submissions/5361e443-f472-4203-9d29-d2b97c97e12d

import Mathlib
import Theorems.Thm_ArtinPrimitiveRoots_dirichlet_L_zero_free_strip

section
/-!
# L31P_Residue: the rectangle residue theorem with a simple pole

A copy of the package's sorry-free modules `Solutions.Artin.SW.Def.Rectangle_defs`,
`...ResidueCalcOnRectangles_defs` and `Solutions.Artin.SW.Thm.*` up to
`ResidueTheoremOnRectangleWithSimplePole_prime` (ported PrimeNumberTheoremAnd material, see the
provenance lines below), renamed into `ArtinPrimitiveRoots.L31PRes` and with `arctan` written
`Real.arctan` so that it compiles under a single `import Mathlib`.
-/

-- ===== Solutions.Artin.SW.Def.Rectangle_defs =====

namespace ArtinPrimitiveRoots.L31PRes
/-! Ported from prove2.me definition bundle `Rectangle_defs` (0a8a3c2f-e233-4739-9f57-3945a05c3db8, by Community (Bot)). -/

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle

end Rectangle

/-- A `RectangleBorder` has corners `z` and `w`. -/
def RectangleBorder (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

end ArtinPrimitiveRoots.L31PRes
-- ===== Solutions.Artin.SW.Def.ResidueCalcOnRectangles_defs =====

namespace ArtinPrimitiveRoots.L31PRes
/-! Ported from prove2.me definition bundle `ResidueCalcOnRectangles_defs` (f82527a4-e4e4-4999-9ab9-d940d8b0546f, by Community (Bot)). -/

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)

/-- A `RectangleIntegral` of a function `f` is one over a rectangle
  determined by `z` and `w` in `ℂ`. -/
noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

/-- A `RectangleIntegral'` of a function `f` is one over a rectangle
  determined by `z` and `w` in `ℂ`, divided by `2 * π * I`. -/
noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • RectangleIntegral f z w

/-- A function is `HolomorphicOn` a set if it is complex
  differentiable on that set. -/
abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s

def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/

-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.

-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.

-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.

end ArtinPrimitiveRoots.L31PRes
-- ===== Solutions.Artin.SW.Thm.HolomorphicOn_vanishesOnRectangle =====

namespace ArtinPrimitiveRoots.L31PRes
/-! Ported from prove2.me: `HolomorphicOn.vanishesOnRectangle` (9545a167-c26e-42b4-a31e-6b0da9ea9f41, statement by Community (Bot)); proof = accepted direct submission 54348a9e-624c-4bbc-9145-0e2421394525 by Community (Bot). -/

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem _root_.ArtinPrimitiveRoots.L31PRes.HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/

-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.

-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.

-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.

end ArtinPrimitiveRoots.L31PRes
-- ===== Solutions.Artin.SW.Thm.IsBigO_to_BddAbove =====

namespace ArtinPrimitiveRoots.L31PRes
/-! Ported from prove2.me: `IsBigO_to_BddAbove` (9679d93e-eb72-4a91-9e81-ff4618976134, statement by Community (Bot)); proof = accepted direct submission 9ffe6794-56f8-4e92-8a26-a32e3b220800 by Community (Bot). -/

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem _root_.ArtinPrimitiveRoots.L31PRes.IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at f_near_p
  obtain ⟨c, hc⟩ := f_near_p
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨U_is_open, p_in_U⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds U_is_open p_in_U
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, mem_diff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, x_not_p⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [x_not_p] using hU x_in_U

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/

-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.

-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.

-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.

end ArtinPrimitiveRoots.L31PRes
-- ===== Solutions.Artin.SW.Thm.existsDifferentiableOn_of_bddAbove =====

namespace ArtinPrimitiveRoots.L31PRes
/-! Ported from prove2.me: `existsDifferentiableOn_of_bddAbove` (dc84894c-d500-4dce-9c12-f004772b9cf6, statement by Community (Bot)); proof = accepted direct submission 5099e0df-cbca-4fc9-9991-1a2549e17f05 by Community (Bot). -/

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem _root_.ArtinPrimitiveRoots.L31PRes.existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/

-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.

-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.

-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.

end ArtinPrimitiveRoots.L31PRes
-- ===== Solutions.Artin.SW.Thm.mapsTo_rectangleBorder_left_im =====

namespace ArtinPrimitiveRoots.L31PRes
/-! Ported from prove2.me: `mapsTo_rectangleBorder_left_im` (e7072fdd-3190-4349-9824-672ed7f6cf10, statement by Community (Bot)); proof = accepted direct submission d3f774b3-f08b-4c42-a2b1-b1dba24da366 by Community (Bot). -/

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem _root_.ArtinPrimitiveRoots.L31PRes.mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

end ArtinPrimitiveRoots.L31PRes
-- ===== Solutions.Artin.SW.Thm.mapsTo_rectangleBorder_left_re =====

namespace ArtinPrimitiveRoots.L31PRes
/-! Ported from prove2.me: `mapsTo_rectangleBorder_left_re` (58a6d1e7-fb5d-479c-b33d-a2cad2193a8d, statement by Community (Bot)); proof = accepted direct submission 01260408-219a-49a4-83e3-215fa93c8dee by Community (Bot). -/

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem _root_.ArtinPrimitiveRoots.L31PRes.mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

end ArtinPrimitiveRoots.L31PRes
-- ===== Solutions.Artin.SW.Thm.mapsTo_rectangleBorder_right_im =====

namespace ArtinPrimitiveRoots.L31PRes
/-! Ported from prove2.me: `mapsTo_rectangleBorder_right_im` (db6b635b-9391-44f3-8b91-1e5a6b9f6e28, statement by Community (Bot)); proof = accepted direct submission 723fc351-35c3-49ac-809f-eda7e8d55d83 by Community (Bot). -/

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem _root_.ArtinPrimitiveRoots.L31PRes.mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

end ArtinPrimitiveRoots.L31PRes
-- ===== Solutions.Artin.SW.Thm.mapsTo_rectangleBorder_right_re =====

namespace ArtinPrimitiveRoots.L31PRes
/-! Ported from prove2.me: `mapsTo_rectangleBorder_right_re` (9bf0ecd2-4d6c-4f13-92c8-b80e5002d20a, statement by Community (Bot)); proof = accepted direct submission 2e11baed-c579-4baf-b664-a206e5e44616 by Community (Bot). -/

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem _root_.ArtinPrimitiveRoots.L31PRes.mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

end ArtinPrimitiveRoots.L31PRes
-- ===== Solutions.Artin.SW.Thm.rectangle_mem_nhds_iff =====

namespace ArtinPrimitiveRoots.L31PRes
/-! Ported from prove2.me: `rectangle_mem_nhds_iff` (6acc033d-4619-41c3-9897-aeffeb433822, statement by Community (Bot)); proof = accepted direct submission 59d17d34-2c35-4e41-82da-0f2b7d4a2a3c by Community (Bot). -/

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem _root_.ArtinPrimitiveRoots.L31PRes.rectangle_mem_nhds_iff {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]

end ArtinPrimitiveRoots.L31PRes
-- ===== Solutions.Artin.SW.Thm.not_mem_rectangleBorder_of_rectangle_mem_nhds =====

namespace ArtinPrimitiveRoots.L31PRes
/-! Ported from prove2.me: `not_mem_rectangleBorder_of_rectangle_mem_nhds` (d2ce0450-2d8e-4253-9421-c254e63992cd, statement by Community (Bot)); proof = accepted sketch submission cfcdf00e-dd69-4098-a362-d468f2bb6b9b by Community (Bot). -/

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem _root_.Set.left_not_mem_uIoo {a b : ℝ} : a ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (left_lt_sup.mp h2) (le_of_not_ge (inf_lt_left.mp h1))

private theorem _root_.Set.right_not_mem_uIoo {a b : ℝ} : b ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (right_lt_sup.mp h2) (le_of_not_ge (inf_lt_right.mp h1))

private theorem _root_.Set.ne_left_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a :=
  fun h ↦ Set.left_not_mem_uIoo (h ▸ hc)

private theorem _root_.Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  fun h ↦ Set.right_not_mem_uIoo (h ▸ hc)

private theorem rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [RectangleBorder, Set.mem_union, not_or]
  exact ⟨⟨⟨fun hc ↦ h.2.2.1 hc.2, fun hc ↦ h.1 hc.1⟩, fun hc ↦ h.2.2.2 hc.2⟩,
    fun hc ↦ h.2.1 hc.1⟩

theorem _root_.ArtinPrimitiveRoots.L31PRes.not_mem_rectangleBorder_of_rectangle_mem_nhds {z w p : ℂ}
    (hp : Rectangle z w ∈ 𝓝 p) :
    p ∉ RectangleBorder z w := by
  refine Set.disjoint_right.mp (rectangleBorder_disjoint_singleton ?_) rfl
  have h1 := rectangle_mem_nhds_iff.mp hp
  exact ⟨Set.ne_left_of_mem_uIoo h1.1, Set.ne_right_of_mem_uIoo h1.1,
    Set.ne_left_of_mem_uIoo h1.2, Set.ne_right_of_mem_uIoo h1.2⟩

end ArtinPrimitiveRoots.L31PRes
-- ===== Solutions.Artin.SW.Thm.rectangleBorder_subset_rectangle =====

namespace ArtinPrimitiveRoots.L31PRes
/-! Ported from prove2.me: `rectangleBorder_subset_rectangle` (27c9e576-b409-45cb-b295-116f3f8a1e5a, statement by Community (Bot)); proof = accepted direct submission b468ed91-03cd-4774-a2ff-4c6133145b93 by Community (Bot). -/

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem _root_.ArtinPrimitiveRoots.L31PRes.rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩

end ArtinPrimitiveRoots.L31PRes
-- ===== Solutions.Artin.SW.Thm.ResidueTheoremOnRectangleWithSimplePole_prime =====

namespace ArtinPrimitiveRoots.L31PRes
/-! Ported from prove2.me: `ResidueTheoremOnRectangleWithSimplePole_prime` (de1ab0a9-354d-4b8c-b836-bb3f087bdb7a, statement by Community (Bot)); proof = accepted sketch submission 3b52f320-4c89-40f8-b5d9-72a8cda7ab1d by Community (Bot). -/

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

private theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral VIntegral
  congrm ?_ - ?_ + I • ?_ - I • ?_
  all_goals refine integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩

private theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]

private theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module

omit [NormedSpace ℂ E] in
theorem _root_.ContinuousOn.rectangleBorder_integrable (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩

omit [NormedSpace ℂ E] in
private theorem _root_.ContinuousOn.rectangleBorderIntegrable (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  ContinuousOn.rectangleBorder_integrable (hf.mono (rectangleBorder_subset_rectangle z w))

omit [NormedSpace ℂ E] in
private theorem _root_.ContinuousOn.rectangleBorderNoPIntegrable
    (hf : ContinuousOn f (Rectangle z w \ {p})) (pNotOnBorder : p ∉ RectangleBorder z w) :
    RectangleBorderIntegrable f z w := by
  refine ContinuousOn.rectangleBorder_integrable (hf.mono (Set.subset_diff.mpr ?_))
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

private theorem HolomorphicOn.rectangleBorderIntegrable'
    (hf : HolomorphicOn f (Rectangle z w \ {p})) (hp : Rectangle z w ∈ nhds p) :
    RectangleBorderIntegrable f z w :=
  hf.continuousOn.rectangleBorderNoPIntegrable (not_mem_rectangleBorder_of_rectangle_mem_nhds hp)

private theorem HolomorphicOn.rectangleBorderIntegrable (hf : HolomorphicOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := hf.continuousOn.rectangleBorderIntegrable

private theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]

private theorem RectangleIntegral.translate' (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  simp_rw [RectangleIntegral', RectangleIntegral.translate]

private theorem _root_.Complex.inv_re_add_im : (x + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [conj_ofReal, normSq] <;> ring

private theorem sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]

private theorem continuous_self_div_sq_add_sq (hy : y ≠ 0) :
    Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _ => sq_add_sq_ne_zero hy)

private theorem integral_self_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1 <;> try with_reducible_and_instances rfl
    first | ring | (norm_num; ring) | field_simp
  have e3 : deriv f = fun x => x / (x ^ 2 + y ^ 2) := funext (fun _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using continuous_self_div_sq_add_sq hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _ => e2.differentiableAt) (e4.intervalIntegrable _ _)

private theorem integral_const_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring

set_option backward.isDefEq.respectTransparency false in
private theorem integral_const_div_self_add_im (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * I) = A * x / (x ^ 2 + y ^ 2) - A * I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [inv_re_add_im]
    ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have e3 : IntervalIntegrable (fun x ↦ A * I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy, integral_const_div_sq_add_sq hy]

private theorem integral_const_div_re_add_self (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * I) = A / I / (y + ↑(-x) * I) := by
    have e1 : x + y * I ≠ 0 := by
      contrapose! hx
      simpa using congr_arg re hx
    have e2 : y + I * ↑(-x) ≠ 0 := by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]

private theorem ResidueTheoremAtOrigin' {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * I * π * c := by
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  rw [integral_const_div_re_add_self h1.ne, integral_const_div_re_add_self h3.ne.symm]
  rw [integral_const_div_self_add_im h2.ne, integral_const_div_self_add_im h4.ne.symm]
  have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg, arctan_neg, ofReal_neg,
    sub_neg_eq_add]
  rw [l1, l3, l4, l6, r1, r3, r4, r6]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
  ring_nf

private theorem ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  simp only [rectangle_mem_nhds_iff, uIoo_of_le zRe_le_wRe, uIoo_of_le zIm_le_wIm,
    mem_reProdIm, mem_Ioo] at pInRectInterior
  rw [RectangleIntegral.translate', RectangleIntegral']
  have : 1 / (2 * ↑π * I) * (2 * I * ↑π * c) = c := by
    field_simp
  rwa [ResidueTheoremAtOrigin']
  all_goals simp [*]

private theorem ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) g (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  have principalPart' : Set.EqOn f (g + (fun s ↦ A / (s - p))) (Rectangle z w \ {p}) :=
    fun s hs => by rw [Pi.add_apply, ← principalPart hs, Pi.sub_apply, sub_add_cancel]
  have : Set.EqOn f (g + (fun s ↦ A / (s - p))) (RectangleBorder z w) :=
    principalPart'.mono <| Set.subset_diff.mpr
      ⟨rectangleBorder_subset_rectangle z w,
        disjoint_singleton_right.mpr
          (not_mem_rectangleBorder_of_rectangle_mem_nhds pInRectInterior)⟩
  rw [RectangleIntegral'_congr this]
  have t1 : RectangleBorderIntegrable g z w :=
    HolomorphicOn.rectangleBorderIntegrable gHolo
  have t2 : HolomorphicOn (fun s ↦ A / (s - p)) (Rectangle z w \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by
          rw [sub_ne_zero]
          exact hx
    · rintro s ⟨_, hs⟩
      exact hs
  have t3 : RectangleBorderIntegrable (fun s ↦ A / (s - p)) z w :=
    HolomorphicOn.rectangleBorderIntegrable' t2 pInRectInterior
  rw [RectangleIntegral', RectangleBorderIntegrable.add t1 t3, smul_add]
  rw [HolomorphicOn.vanishesOnRectangle gHolo (by rfl), smul_zero, zero_add]
  exact ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm pInRectInterior

private theorem BddAbove_on_rectangle_of_bdd_near {z w p : ℂ} {f : ℂ → ℂ}
    (f_cont : ContinuousOn f (Rectangle z w \ {p}))
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    BddAbove (norm ∘ f '' (Rectangle z w \ {p})) := by
  obtain ⟨V, V_in_nhds, V_prop⟩ := IsBigO_to_BddAbove f_near_p
  rw [mem_nhds_iff] at V_in_nhds
  obtain ⟨W, W_subset, W_open, p_in_W⟩ := V_in_nhds
  set U := Rectangle z w
  have : U \ {p} = (U \ W) ∪ ((U ∩ W) \ {p}) := by
    ext x
    simp only [mem_diff, mem_singleton_iff, mem_union, mem_inter_iff]
    constructor
    · intro ⟨xu, x_not_p⟩
      tauto
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩
      · refine ⟨h1, ?_⟩
        intro h
        rw [← h] at p_in_W
        exact h2 p_in_W
      · tauto
  rw [this, image_union]
  apply BddAbove.union
  · apply IsCompact.bddAbove_image
    · apply IsCompact.diff _ W_open
      exact IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
    · apply f_cont.norm.mono
      apply diff_subset_diff_right
      simpa
  · exact V_prop.mono
      (image_mono <| diff_subset_diff_left <| subset_trans inter_subset_right W_subset)

theorem _root_.ArtinPrimitiveRoots.L31PRes.ResidueTheoremOnRectangleWithSimplePole_prime {f : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (fHolo : HolomorphicOn f (Rectangle z w \ {p}))
    (near_p : (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = A := by
  set g := f - (fun s ↦ A / (s - p))
  have gHolo : HolomorphicOn g (Rectangle z w \ {p}) := by
    apply DifferentiableOn.sub fHolo
    intro s hs
    have : s - p ≠ 0 := sub_ne_zero.mpr hs.2
    exact  DifferentiableWithinAt.div (by fun_prop) (by fun_prop) this
  have := BddAbove_on_rectangle_of_bdd_near gHolo.continuousOn near_p
  obtain ⟨h, ⟨hHolo, hEq⟩⟩ := existsDifferentiableOn_of_bddAbove pInRectInterior gHolo this
  exact ResidueTheoremOnRectangleWithSimplePole zRe_le_wRe zIm_le_wIm pInRectInterior hHolo hEq

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/

-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.

-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.

-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.

end ArtinPrimitiveRoots.L31PRes
end

section
/-!
# L31P_Perron: truncated Perron formula and contour-shift bound

Copied (verbatim up to renaming and `private` removal) from the accepted proof
`SWPort.Davenport.perron_of_region_bound` (prove2.me e1f52231, accepted sketch ea5571ed by alya),
module `Solutions/Artin/SW/Thm/Davenport_perron_of_region_bound.lean`, pieces `Sums`, `Kernel`,
`Shift (E)` and `PerronFormula`. The residue theorem it uses is the copy in `L31P_Residue`.
-/

namespace ArtinPrimitiveRoots
namespace L31P

open Finset DirichletCharacter ArtinPrimitiveRoots.L31PRes
open Complex Real Set MeasureTheory intervalIntegral Filter Topology

/-! ### Piece `Sums` -/

/-! ### Helpers for (G1)/(G2) -/

/-- Termwise bound `Λ n / n^σ ≤ (1/δ) n^(-1-δ)` with `δ = (σ-1)/2`. -/
theorem g_term_le {σ : ℝ} (hσ : 1 < σ) (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ
      ≤ (1 / ((σ - 1) / 2)) * (n : ℝ) ^ (-1 - (σ - 1) / 2) := by
  set δ : ℝ := (σ - 1) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, ArithmeticFunction.map_zero, zero_div]
    exact mul_nonneg (by positivity) (Real.zero_rpow_nonneg _)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n :=
    ArithmeticFunction.vonMangoldt_le_log
  have h2 : Real.log n ≤ (n : ℝ) ^ δ / δ := Real.log_le_rpow_div hn'.le hδpos
  have h3 : (n : ℝ) ^ (-1 - δ) = (n : ℝ) ^ δ / (n : ℝ) ^ σ := by
    rw [← Real.rpow_sub hn']
    congr 1
    rw [hδ]; ring
  rw [h3]
  have hpos : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hn' σ
  rw [div_le_iff₀ hpos]
  calc (ArithmeticFunction.vonMangoldt n : ℝ) ≤ (n : ℝ) ^ δ / δ := h1.trans h2
    _ = 1 / δ * ((n : ℝ) ^ δ / (n : ℝ) ^ σ) * (n : ℝ) ^ σ := by
        field_simp

/-- Nonnegativity of the terms. -/
theorem g_term_nonneg {σ : ℝ} (n : ℕ) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ := by
  apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
  exact Real.rpow_nonneg (Nat.cast_nonneg n) σ

/-- (G1) Summability of `Λ n / n^σ` for `σ > 1`. -/
theorem summable_vonMangoldt_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ) := by
  have hs : Summable (fun n : ℕ => (1 / ((σ - 1) / 2)) * (n : ℝ) ^ (-1 - (σ - 1) / 2)) := by
    apply Summable.mul_left
    rw [Real.summable_nat_rpow]
    linarith
  exact Summable.of_nonneg_of_le (fun n => g_term_nonneg n) (fun n => g_term_le hσ n) hs

/-! ### (G2) -/

/-- Partial sums of `n^(-1-δ)` are bounded by `1 + 1/δ`. -/
theorem g_sum_rpow_le {δ : ℝ} (hδ : 0 < δ) (M : ℕ) :
    ∑ i ∈ Finset.range M, (i : ℝ) ^ (-1 - δ) ≤ 1 + 1 / δ := by
  have hδ' : 0 ≤ 1 / δ := by positivity
  have hexp : (-1 - δ) ≠ 0 := by linarith
  rcases M with _ | M
  · simp; positivity
  rcases M with _ | a
  · simp [Real.zero_rpow hexp]; positivity
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.cast_zero, Nat.cast_one, Real.one_rpow, zero_add, Real.zero_rpow hexp, add_zero]
  -- the tail `∑_{i < a} (i+2)^(-1-δ)` is bounded by the integral `∫_1^{1+a} x^(-1-δ)`
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-1 - δ)) (Icc 1 (1 + (a : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hint := hanti.sum_le_integral
  have hI : ∫ x in (1 : ℝ)..(1 + (a : ℝ)), x ^ (-1 - δ)
      = ((1 + (a : ℝ)) ^ (-1 - δ + 1) - (1 : ℝ) ^ (-1 - δ + 1)) / (-1 - δ + 1) := by
    apply integral_rpow
    right
    refine ⟨by linarith, ?_⟩
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have hle : ((1 + (a : ℝ)) ^ (-1 - δ + 1) - (1 : ℝ) ^ (-1 - δ + 1)) / (-1 - δ + 1) ≤ 1 / δ := by
    rw [Real.one_rpow, show (-1 - δ + 1) = -δ by ring]
    have h0 : 0 ≤ (1 + (a : ℝ)) ^ (-δ) := Real.rpow_nonneg (by positivity) _
    rw [div_le_iff_of_neg (by linarith)]
    have : 1 / δ * (-δ) = -1 := by field_simp
    rw [this]
    linarith
  have hsum : ∑ i ∈ Finset.range a, ((i : ℝ) + 1 + 1) ^ (-1 - δ)
      = ∑ i ∈ Finset.range a, (fun x : ℝ => x ^ (-1 - δ)) (1 + ((i + 1 : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only
    congr 1
    push_cast
    ring
  have key : ∑ i ∈ Finset.range a, ((i : ℝ) + 1 + 1) ^ (-1 - δ) ≤ 1 / δ := by
    rw [hsum]
    exact hint.trans (hI ▸ hle)
  push_cast
  linarith

/-- (G2) Explicit bound `∑ Λ n / n^σ ≤ 8 / (σ - 1)^2` for `1 < σ ≤ 3`. -/
theorem tsum_vonMangoldt_div_rpow_le {σ : ℝ} (hσ : 1 < σ) (hσ3 : σ ≤ 3) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ ≤ 8 / (σ - 1) ^ 2 := by
  set δ : ℝ := (σ - 1) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ ≤ 1 := by rw [hδ]; linarith
  apply Real.tsum_le_of_sum_range_le (fun n => g_term_nonneg n)
  intro M
  calc ∑ i ∈ Finset.range M, (ArithmeticFunction.vonMangoldt i : ℝ) / (i : ℝ) ^ σ
      ≤ ∑ i ∈ Finset.range M, (1 / δ) * (i : ℝ) ^ (-1 - δ) :=
        Finset.sum_le_sum (fun i _ => g_term_le hσ i)
    _ = (1 / δ) * ∑ i ∈ Finset.range M, (i : ℝ) ^ (-1 - δ) := by rw [Finset.mul_sum]
    _ ≤ (1 / δ) * (1 + 1 / δ) := by
        apply mul_le_mul_of_nonneg_left (g_sum_rpow_le hδpos M)
        positivity
    _ ≤ (1 / δ) * (2 / δ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [show (2 : ℝ) / δ = 1 / δ + 1 / δ by ring]
        have : 1 ≤ 1 / δ := by
          rw [le_div_iff₀ hδpos]; linarith
        linarith
    _ = 8 / (σ - 1) ^ 2 := by
        rw [hδ]; field_simp; ring

/-! ### (G3) -/

/-- (G3) Elementary: for `x > 0`, `n ≥ 1`, `n ≠ x`: `1/|log (x/n)| ≤ 1/log 2 + 2x/|x - n|`. -/
theorem one_div_abs_log_le {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hxn : (n : ℝ) ≠ x) :
    1 / |Real.log (x / n)| ≤ 1 / Real.log 2 + 2 * x / |x - n| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set y : ℝ := x / n with hy
  have hy0 : 0 < y := div_pos hx hn'
  have hy1 : y ≠ 1 := by
    rw [hy]; intro h
    rw [div_eq_one_iff_eq hn'.ne'] at h
    exact hxn h.symm
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogy : Real.log y ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy0 hy1
  have habs : 0 < |Real.log y| := abs_pos.mpr hlogy
  have hxn' : 0 < |x - n| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hxn))
  have hA : 0 ≤ 2 * x / |x - n| := by positivity
  have hB : 0 ≤ 1 / Real.log 2 := by positivity
  -- helper: from `a ≤ |log y|` with `a > 0` get `1/|log y| ≤ 1/a`
  by_cases h2 : 2 ≤ y
  · have : Real.log 2 ≤ |Real.log y| := by
      rw [abs_of_pos (Real.log_pos (by linarith))]
      exact Real.log_le_log (by norm_num) h2
    calc 1 / |Real.log y| ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hlog2 this
      _ ≤ _ := by linarith
  by_cases h3 : y ≤ 1 / 2
  · have : Real.log 2 ≤ |Real.log y| := by
      have hlt : Real.log y < 0 := Real.log_neg hy0 (by linarith)
      rw [abs_of_neg hlt]
      have := Real.log_le_log hy0 h3
      rw [one_div, Real.log_inv] at this
      linarith
    calc 1 / |Real.log y| ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hlog2 this
      _ ≤ _ := by linarith
  push Not at h2 h3
  -- middle case: `1/2 < y < 2`
  have hkey : |x - n| / (2 * x) ≤ |Real.log y| := by
    have hn2 : (n : ℝ) < 2 * x := by
      rw [hy, lt_div_iff₀ hn'] at h3; linarith
    have hx2 : x < 2 * n := by
      rw [hy, div_lt_iff₀ hn'] at h2; linarith
    rcases lt_or_gt_of_ne hy1 with hlt | hgt
    · -- `y < 1`, i.e. `x < n`
      have hxn2 : x < n := by rw [hy, div_lt_one hn'] at hlt; exact hlt
      have hl : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
      have hneg : Real.log y < 0 := Real.log_neg hy0 hlt
      rw [abs_of_neg hneg, abs_of_neg (by linarith)]
      have : 1 - y = (n - x) / n := by rw [hy]; field_simp
      rw [div_le_iff₀ (by positivity)]
      calc -(x - n) = (n - x) := by ring
        _ ≤ (1 - y) * (2 * x) := by
            rw [this, div_mul_eq_mul_div, le_div_iff₀ hn']
            nlinarith
        _ ≤ -Real.log y * (2 * x) := by nlinarith
    · -- `y > 1`, i.e. `x > n`
      have hxn2 : (n : ℝ) < x := by rw [hy, one_lt_div hn'] at hgt; exact hgt
      have hl : 1 - y⁻¹ ≤ Real.log y := Real.one_sub_inv_le_log_of_pos hy0
      have hpos : 0 < Real.log y := Real.log_pos hgt
      rw [abs_of_pos hpos, abs_of_pos (by linarith)]
      have : 1 - y⁻¹ = (x - n) / x := by rw [hy, inv_div]; field_simp
      rw [div_le_iff₀ (by positivity)]
      calc x - n ≤ (1 - y⁻¹) * (2 * x) := by
            rw [this, div_mul_eq_mul_div, le_div_iff₀ hx]
            nlinarith
        _ ≤ Real.log y * (2 * x) := by nlinarith
  calc 1 / |Real.log y| ≤ 1 / (|x - n| / (2 * x)) :=
        one_div_le_one_div_of_le (by positivity) hkey
    _ = 2 * x / |x - n| := by rw [one_div_div]
    _ ≤ _ := by linarith

/-! ### (G4) -/

/-- Distance of the half-integer `x = N - 1/2` to any natural number is at least `1/2`. -/
theorem g_abs_sub_ge {N : ℕ} {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) (n : ℕ) :
    1 / 2 ≤ |x - n| := by
  rcases lt_or_ge n N with h | h
  · have : (n : ℝ) + 1 ≤ N := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    linarith
  · have : (N : ℝ) ≤ n := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]
    linarith

theorem g_ne_of_half {N : ℕ} {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) (n : ℕ) : (n : ℝ) ≠ x := by
  intro h
  have := g_abs_sub_ge hx n
  rw [h, sub_self, abs_zero] at this
  linarith

/-- (G4) Summability of the Perron error terms, `x = N - 1/2`. -/
theorem summable_perron_error {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : x = (N : ℝ) - 1 / 2)
    {σ₀ : ℝ} (hσ₀ : 1 < σ₀) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ /
      |Real.log (x / n)|) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < x := by rw [hx]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hS := summable_vonMangoldt_div_rpow hσ₀
  have hC : 0 ≤ x ^ σ₀ * (1 / Real.log 2 + 4 * x) := by positivity
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hS.mul_left (x ^ σ₀ * (1 / Real.log 2 + 4 * x)))
  · exact div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (by positivity) _)) (abs_nonneg _)
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have hn1 : 1 ≤ n := hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hG3 := one_div_abs_log_le hx0 hn1 (g_ne_of_half hx n)
      have habs := g_abs_sub_ge hx n
      have h4 : 2 * x / |x - n| ≤ 4 * x := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      have hterm : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ :=
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) _)
      calc (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ / |Real.log (x / n)|
          = (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ * (1 / |Real.log (x / n)|) := by
            ring
        _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ * (1 / Real.log 2 + 4 * x) :=
            mul_le_mul_of_nonneg_left (hG3.trans (by linarith)) hterm
        _ = x ^ σ₀ * (1 / Real.log 2 + 4 * x) *
              ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀) := by
            rw [Real.div_rpow hx0.le hn'.le]; ring

/-! ### (C') -/

theorem g_log_two_ge : 1 / 2 ≤ Real.log 2 := by
  have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at this
  linarith

theorem g_log_two_le : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

/-- The real harmonic number as a `range` sum. -/
theorem g_harmonic_eq (N : ℕ) : (harmonic N : ℝ) = ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) := by
  simp [harmonic, one_div]

/-- Harmonic-type bound: `∑_{n < 2N} 1/|x - n| ≤ 4 (1 + log N)` for `x = N - 1/2`. -/
theorem g_sum_inv_abs_le {N : ℕ} {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) :
    ∑ n ∈ Finset.range (2 * N), 1 / |x - n| ≤ 4 * (1 + Real.log N) := by
  have hH : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
  have h1 : ∑ n ∈ Finset.range N, 1 / |x - n| ≤ 2 * (harmonic N : ℝ) := by
    calc ∑ n ∈ Finset.range N, 1 / |x - n|
        ≤ ∑ n ∈ Finset.range N, 2 * (1 / (((N - 1 - n : ℕ) : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_range] at hn
          have hcast : ((N - 1 - n : ℕ) : ℝ) + 1 = N - n := by
            rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
          rw [hcast]
          have : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
          rw [abs_of_pos (by linarith), div_le_iff₀ (by linarith), mul_one_div,
            div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
          linarith
      _ = ∑ j ∈ Finset.range N, 2 * (1 / ((j : ℝ) + 1)) :=
          Finset.sum_range_reflect (fun j : ℕ => 2 * (1 / ((j : ℝ) + 1))) N
      _ = 2 * (harmonic N : ℝ) := by rw [g_harmonic_eq, Finset.mul_sum]
  have h2 : ∑ n ∈ Finset.range N, 1 / |x - ((N + n : ℕ) : ℝ)| ≤ 2 * (harmonic N : ℝ) := by
    rw [g_harmonic_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have hpos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
    have habs : |x - ((N + n : ℕ) : ℝ)| = n + 1 / 2 := by
      push_cast
      rw [abs_of_neg (by linarith)]
      linarith
    rw [habs, div_le_iff₀ hpos, mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  rw [two_mul, Finset.sum_range_add]
  linarith

/-- The class-B majorant: supported on `x/2 < n < 2x`. -/
private noncomputable def g_hB (N : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  if x / 2 < n ∧ (n : ℝ) < 2 * x then 8 * (1 + Real.log N) * (2 + 2 * x / |x - n|) else 0

theorem g_hB_nonneg {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx0 : 0 < x) (n : ℕ) : 0 ≤ g_hB N x n := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  unfold g_hB
  split_ifs
  · apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  · exact le_rfl

theorem g_hB_supp {N : ℕ} {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) :
    ∀ n ∉ Finset.range (2 * N), g_hB N x n = 0 := by
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  have : (2 * N : ℝ) ≤ n := by exact_mod_cast hn
  unfold g_hB
  rw [if_neg]
  rintro ⟨_, h2⟩
  linarith

theorem g_hB_le {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx0 : 0 < x) (n : ℕ) :
    g_hB N x n ≤ 8 * (1 + Real.log N) * (2 + 2 * x / |x - n|) := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  unfold g_hB
  split_ifs
  · exact le_rfl
  · apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)

/-- The finite class-B sum. -/
theorem g_sum_hB_le {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) :
    ∑ n ∈ Finset.range (2 * N), g_hB N x n ≤ 96 * N * (1 + Real.log N) ^ 2 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < x := by rw [hx]; linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hL : 1 ≤ 1 + Real.log N := by linarith
  have hsig := g_sum_inv_abs_le hx
  calc ∑ n ∈ Finset.range (2 * N), g_hB N x n
      ≤ ∑ n ∈ Finset.range (2 * N), 8 * (1 + Real.log N) * (2 + 2 * x / |x - n|) :=
        Finset.sum_le_sum (fun n _ => g_hB_le hN hx0 n)
    _ = 8 * (1 + Real.log N) * 2 * (2 * N : ℝ)
          + 8 * (1 + Real.log N) * (2 * x) * ∑ n ∈ Finset.range (2 * N), 1 / |x - n| := by
        rw [Finset.mul_sum]
        have : 8 * (1 + Real.log N) * 2 * (2 * N : ℝ)
            = ∑ n ∈ Finset.range (2 * N), 8 * (1 + Real.log N) * 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        rw [this, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ ≤ 8 * (1 + Real.log N) * 2 * (2 * N : ℝ)
          + 8 * (1 + Real.log N) * (2 * x) * (4 * (1 + Real.log N)) := by
        have hc : 0 ≤ 8 * (1 + Real.log N) * (2 * x) :=
          mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
        have := mul_le_mul_of_nonneg_left hsig hc
        linarith
    _ = 32 * N * (1 + Real.log N) + 64 * x * (1 + Real.log N) ^ 2 := by ring
    _ ≤ 32 * N * (1 + Real.log N) ^ 2 + 64 * N * (1 + Real.log N) ^ 2 := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (by linarith)
          nlinarith
        · apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
    _ = 96 * N * (1 + Real.log N) ^ 2 := by ring

/-- Pointwise bound `f n ≤ g n + h n` for the Perron error terms. -/
theorem g_pointwise {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : x = (N : ℝ) - 1 / 2)
    {σ₀ : ℝ} (hσ₀ : 1 < σ₀) (hσ₀3 : σ₀ ≤ 3) (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ / |Real.log (x / n)|
      ≤ 2 * x ^ σ₀ * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀) + g_hB N x n := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < x := by rw [hx]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh0 := g_hB_nonneg hN hx0 n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, ArithmeticFunction.map_zero, zero_mul, zero_div, mul_zero, zero_add]
    exact hh0
  have hn1 : 1 ≤ n := hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hy0 : 0 < x / n := div_pos hx0 hn'
  have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hyσ : 0 ≤ (x / n) ^ σ₀ := Real.rpow_nonneg hy0.le _
  have hterm : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ := mul_nonneg hΛ0 hyσ
  have hgn : 2 * x ^ σ₀ * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)
      = 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀) := by
    rw [Real.div_rpow hx0.le hn'.le]; ring
  rw [hgn]
  have hne : (n : ℝ) ≠ x := g_ne_of_half hx n
  by_cases hB : x / 2 < n ∧ (n : ℝ) < 2 * x
  · -- class B
    have hhn : g_hB N x n = 8 * (1 + Real.log N) * (2 + 2 * x / |x - n|) := by
      unfold g_hB; rw [if_pos hB]
    have hG3 := one_div_abs_log_le hx0 hn1 hne
    have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 1 + Real.log N := by
      calc (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n :=
            ArithmeticFunction.vonMangoldt_le_log
        _ ≤ Real.log (2 * N) := Real.log_le_log hn' (by rw [hx] at hB; linarith [hB.2])
        _ = Real.log 2 + Real.log N := Real.log_mul (by norm_num) (by positivity)
        _ ≤ 1 + Real.log N := by linarith [g_log_two_le]
    have hy2 : (x / n) ^ σ₀ ≤ 8 := by
      calc (x / n) ^ σ₀ ≤ (2 : ℝ) ^ σ₀ :=
            Real.rpow_le_rpow hy0.le (by rw [div_le_iff₀ hn']; linarith [hB.1]) (by linarith)
        _ ≤ (2 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ₀3
        _ = 8 := by
            rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have hl2 : 1 / Real.log 2 ≤ 2 := by
      rw [div_le_iff₀ hlog2]; linarith [g_log_two_ge]
    have hA0 : 0 ≤ 2 * x / |x - n| := by positivity
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ / |Real.log (x / n)|
        = (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ * (1 / |Real.log (x / n)|) := by
          ring
      _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ *
            (1 / Real.log 2 + 2 * x / |x - n|) := mul_le_mul_of_nonneg_left hG3 hterm
      _ ≤ (1 + Real.log N) * 8 * (2 + 2 * x / |x - n|) := by
          apply mul_le_mul (mul_le_mul hΛ hy2 hyσ (by linarith)) (by linarith)
            (add_nonneg (by positivity) hA0) (by positivity)
      _ = g_hB N x n := by rw [hhn]; ring
      _ ≤ 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀) + g_hB N x n := by
          linarith
  · -- class A: `|log (x/n)| ≥ log 2 ≥ 1/2`
    have hhn : g_hB N x n = 0 := by unfold g_hB; rw [if_neg hB]
    have hlog : 1 / 2 ≤ |Real.log (x / n)| := by
      by_cases hn2 : x / 2 < n
      · have h2 : 2 * x ≤ n := by
          by_contra hcon
          exact hB ⟨hn2, by linarith⟩
        have : x / n ≤ 1 / 2 := by rw [div_le_iff₀ hn']; linarith
        have hneg : Real.log (x / n) < 0 := Real.log_neg hy0 (by linarith)
        rw [abs_of_neg hneg]
        have := Real.log_le_log hy0 this
        rw [one_div, Real.log_inv] at this
        linarith [g_log_two_ge]
      · push Not at hn2
        have : 2 ≤ x / n := by rw [le_div_iff₀ hn']; linarith
        rw [abs_of_pos (Real.log_pos (by linarith))]
        calc 1 / 2 ≤ Real.log 2 := g_log_two_ge
          _ ≤ Real.log (x / n) := Real.log_le_log (by norm_num) this
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ / |Real.log (x / n)|
        = (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ * (1 / |Real.log (x / n)|) := by
          ring
      _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ * 2 := by
          apply mul_le_mul_of_nonneg_left _ hterm
          calc 1 / |Real.log (x / n)| ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) hlog
            _ = 2 := by norm_num
      _ = 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀) + g_hB N x n := by
          rw [hhn]; ring

/-- (C') Bound for the Perron error sum, `x = N - 1/2`, `1 < σ₀ ≤ 3`. -/
theorem perron_error_sum_le {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : x = (N : ℝ) - 1 / 2)
    {σ₀ : ℝ} (hσ₀ : 1 < σ₀) (hσ₀3 : σ₀ ≤ 3) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ / |Real.log (x / n)|
      ≤ 10 * x ^ σ₀ * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)
        + 100 * N * (1 + Real.log N) ^ 2 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < x := by rw [hx]; linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hS0 : 0 ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀ :=
    tsum_nonneg (fun n => g_term_nonneg n)
  have hSsum := summable_vonMangoldt_div_rpow hσ₀
  have hf := summable_perron_error hN hx hσ₀
  have hg : Summable (fun n : ℕ =>
      2 * x ^ σ₀ * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)) :=
    hSsum.mul_left _
  have hh : Summable (fun n : ℕ => g_hB N x n) := summable_of_ne_finset_zero (g_hB_supp hx)
  have hxσ : 0 ≤ x ^ σ₀ := Real.rpow_nonneg hx0.le _
  have hNL : 0 ≤ (N : ℝ) * (1 + Real.log N) ^ 2 := by positivity
  calc ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ / |Real.log (x / n)|
      ≤ ∑' n : ℕ, (2 * x ^ σ₀ * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)
          + g_hB N x n) :=
        Summable.tsum_le_tsum (fun n => g_pointwise hN hx hσ₀ hσ₀3 n) hf (hg.add hh)
    _ = ∑' n : ℕ, 2 * x ^ σ₀ * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)
          + ∑' n : ℕ, g_hB N x n := hg.tsum_add hh
    _ = 2 * x ^ σ₀ * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)
          + ∑ n ∈ Finset.range (2 * N), g_hB N x n := by
        rw [tsum_mul_left, tsum_eq_sum (g_hB_supp hx)]
    _ ≤ 2 * x ^ σ₀ * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀)
          + 96 * N * (1 + Real.log N) ^ 2 := by
        linarith [g_sum_hB_le hN hx]
    _ ≤ _ := by nlinarith


/-! ### Piece `Kernel` -/

/-! ### Basic facts about `s ↦ y^s / s` -/

/-- Differentiability of `s ↦ y^s / s` away from `0`. -/
theorem k_differentiableAt {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s / s) s := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hy.ne'))
  exact h1.div differentiableAt_id hs

/-- Pointwise bound on a horizontal line `Im s = t ≠ 0`. -/
theorem k_norm_le {y : ℝ} (hy : 0 < y) {σ t : ℝ} (ht : t ≠ 0) :
    ‖(y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖ ≤ y ^ σ / |t| := by
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  have him : ((σ : ℂ) + t * I).im = t := by simp
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, hre]
  have hpos : 0 < ‖(σ : ℂ) + t * I‖ := by
    rw [norm_pos_iff]
    intro h
    have := congrArg Complex.im h
    simp at this
    exact ht this
  have hle : |t| ≤ ‖(σ : ℂ) + t * I‖ := by
    have := Complex.abs_im_le_norm ((σ : ℂ) + t * I)
    rwa [him] at this
  have hy' : 0 ≤ y ^ σ := (Real.rpow_pos_of_pos hy σ).le
  exact div_le_div_of_nonneg_left hy' (abs_pos.mpr ht) hle

/-- Pointwise bound on a vertical line `Re s = σ ≠ 0`. -/
theorem k_norm_le' {y : ℝ} (hy : 0 < y) {σ t : ℝ} (hσ : σ ≠ 0) :
    ‖(y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖ ≤ y ^ σ / |σ| := by
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, hre]
  have hpos : 0 < ‖(σ : ℂ) + t * I‖ := by
    rw [norm_pos_iff]
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hσ this
  have hle : |σ| ≤ ‖(σ : ℂ) + t * I‖ := by
    have := Complex.abs_re_le_norm ((σ : ℂ) + t * I)
    rwa [hre] at this
  have hy' : 0 ≤ y ^ σ := (Real.rpow_pos_of_pos hy σ).le
  exact div_le_div_of_nonneg_left hy' (abs_pos.mpr hσ) hle

/-- Continuity of `σ ↦ y^σ`. -/
theorem k_continuous_rpow {y : ℝ} (hy : 0 < y) : Continuous (fun σ : ℝ => y ^ σ) :=
  continuous_const.rpow continuous_id (fun _ => Or.inl hy.ne')

/-- The integral of `y^σ`. -/
theorem k_integral_rpow {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (σ₁ σ₂ : ℝ) :
    ∫ σ in σ₁..σ₂, y ^ σ = (y ^ σ₂ - y ^ σ₁) / Real.log y := by
  have hlog : Real.log y ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h | h | h
    · exact hy.ne' h
    · exact hy1 h
    · linarith
  have hderiv : ∀ σ ∈ uIcc σ₁ σ₂,
      HasDerivAt (fun σ : ℝ => y ^ σ / Real.log y) (y ^ σ) σ := by
    intro σ _
    have := ((Real.hasStrictDerivAt_const_rpow hy σ).hasDerivAt).div_const (Real.log y)
    rwa [mul_div_cancel_right₀ _ hlog] at this
  rw [integral_eq_sub_of_hasDerivAt hderiv ((k_continuous_rpow hy).intervalIntegrable _ _)]
  ring

/-- Bound for the horizontal integral of `y^s/s` on `Im s = t ≠ 0`. -/
theorem k_horizontal_le {y : ℝ} (hy : 0 < y) {t : ℝ} (ht : t ≠ 0) {σ₁ σ₂ : ℝ} (h : σ₁ ≤ σ₂) :
    ‖∫ σ in σ₁..σ₂, (y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖
      ≤ (1 / |t|) * ∫ σ in σ₁..σ₂, y ^ σ := by
  have hb : ‖∫ σ in σ₁..σ₂, (y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖
      ≤ ∫ σ in σ₁..σ₂, y ^ σ / |t| := by
    refine intervalIntegral.norm_integral_le_of_norm_le h (Eventually.of_forall ?_) ?_
    · intro σ _
      exact k_norm_le hy ht
    · exact ((k_continuous_rpow hy).div_const _).intervalIntegrable _ _
  refine hb.trans (le_of_eq ?_)
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  ext σ
  ring

/-- Bound for the vertical integral of `y^s/s` on `Re s = σ ≠ 0`. -/
theorem k_vertical_le {y : ℝ} (hy : 0 < y) {σ : ℝ} (hσ : σ ≠ 0) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    ‖∫ t in t₁..t₂, (y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖
      ≤ y ^ σ / |σ| * (t₂ - t₁) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t₁) (b := t₂) (C := y ^ σ / |σ|)
    (f := fun t : ℝ => (y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I))
    (fun t _ => k_norm_le' hy hσ)
  rw [abs_of_nonneg (sub_nonneg.mpr h)] at this
  exact this

/-- Cauchy's theorem on a rectangle with real coordinates. -/
theorem k_cauchy {f : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (H : DifferentiableOn ℂ f (Set.uIcc x₁ x₂ ×ℂ Set.uIcc y₁ y₂)) :
    (∫ x : ℝ in x₁..x₂, f (x + y₁ * I)) - (∫ x : ℝ in x₁..x₂, f (x + y₂ * I)) +
      I • (∫ y : ℝ in y₁..y₂, f (x₂ + y * I)) -
      I • (∫ y : ℝ in y₁..y₂, f (x₁ + y * I)) = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ H

/-- The horizontal edge integrals of `y^s/s` are bounded by `y^a / (|t| * (-log y))`
(`y < 1`, `U ≥ 0`). -/
theorem k_horizontal_lt_one {y a U : ℝ} (hy0 : 0 < y) (hy : y < 1) {t : ℝ} (ht : t ≠ 0)
    (hU : 0 ≤ U) :
    ‖∫ σ in a..a + U, (y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖
      ≤ y ^ a / (-Real.log y) * (1 / |t|) := by
  have hlog : Real.log y < 0 := Real.log_neg hy0 hy
  refine (k_horizontal_le hy0 ht (by linarith)).trans ?_
  rw [k_integral_rpow hy0 hy.ne a (a + U)]
  have h1 : 0 ≤ y ^ (a + U) := (Real.rpow_pos_of_pos hy0 _).le
  have h2 : (y ^ (a + U) - y ^ a) / Real.log y ≤ y ^ a / (-Real.log y) := by
    rw [show (y ^ (a + U) - y ^ a) / Real.log y = (y ^ a - y ^ (a + U)) / (-Real.log y) by
      rw [div_neg, ← neg_div, neg_sub]]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  calc (1 / |t|) * ((y ^ (a + U) - y ^ a) / Real.log y)
      ≤ (1 / |t|) * (y ^ a / (-Real.log y)) := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = y ^ a / (-Real.log y) * (1 / |t|) := by ring

/-- The horizontal edge integrals of `y^s/s` are bounded by `y^a / (|t| * log y)`
(`y > 1`, `U ≥ 0`). -/
theorem k_horizontal_gt_one {y a U : ℝ} (hy : 1 < y) {t : ℝ} (ht : t ≠ 0)
    (hU : 0 ≤ U) :
    ‖∫ σ in a - U..a, (y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖
      ≤ y ^ a / Real.log y * (1 / |t|) := by
  have hy0 : 0 < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  refine (k_horizontal_le hy0 ht (by linarith)).trans ?_
  rw [k_integral_rpow hy0 hy.ne' (a - U) a]
  have h1 : 0 ≤ y ^ (a - U) := (Real.rpow_pos_of_pos hy0 _).le
  have h2 : (y ^ a - y ^ (a - U)) / Real.log y ≤ y ^ a / Real.log y := by
    apply div_le_div_of_nonneg_right _ hlog.le
    linarith
  calc (1 / |t|) * ((y ^ a - y ^ (a - U)) / Real.log y)
      ≤ (1 / |t|) * (y ^ a / Real.log y) := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = y ^ a / Real.log y * (1 / |t|) := by ring

/-- Norm of the constant `1 / (2π)`. -/
theorem k_norm_two_pi : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
  have : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- (K2), one rectangle: the bound with the right-edge error term. -/
theorem k_lt_one_step {y a t₁ t₂ U : ℝ} (hy0 : 0 < y) (hy : y < 1) (ha : 0 < a)
    (ht₁ : t₁ < 0) (ht₂ : 0 < t₂) (hU : 0 < U) :
    ‖∫ t in t₁..t₂, (y : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I)‖
      ≤ y ^ a / (-Real.log y) * (1 / (-t₁) + 1 / t₂) + y ^ (a + U) / (a + U) * (t₂ - t₁) := by
  set f : ℂ → ℂ := fun s => (y : ℂ) ^ s / s with hf
  have hdiff : DifferentiableOn ℂ f (Set.uIcc a (a + U) ×ℂ Set.uIcc t₁ t₂) := by
    intro s hs
    apply (k_differentiableAt hy0 _).differentiableWithinAt
    intro h0
    rw [Complex.mem_reProdIm, h0, Set.uIcc_of_le (by linarith)] at hs
    have := hs.1
    simp at this
    linarith
  have hc := k_cauchy hdiff
  rw [sub_eq_zero] at hc
  have hnorm : ‖∫ t in t₁..t₂, f (a + t * I)‖ = ‖I • ∫ t in t₁..t₂, f (a + t * I)‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  have hB := k_horizontal_lt_one (a := a) (U := U) hy0 hy ht₁.ne hU.le
  have hT := k_horizontal_lt_one (a := a) (U := U) hy0 hy ht₂.ne' hU.le
  have hR := k_vertical_le hy0 (σ := a + U) (by linarith) (t₁ := t₁) (t₂ := t₂) (by linarith)
  rw [abs_of_neg ht₁] at hB
  rw [abs_of_pos ht₂] at hT
  rw [abs_of_pos (by linarith)] at hR
  calc ‖∫ t in t₁..t₂, f (a + t * I)‖
      = ‖(∫ x : ℝ in a..a + U, f (x + t₁ * I)) - (∫ x : ℝ in a..a + U, f (x + t₂ * I)) +
          I • (∫ t : ℝ in t₁..t₂, f ((a + U : ℝ) + t * I))‖ := by rw [hnorm, ← hc]
    _ ≤ ‖∫ x : ℝ in a..a + U, f (x + t₁ * I)‖ + ‖∫ x : ℝ in a..a + U, f (x + t₂ * I)‖ +
          ‖∫ t : ℝ in t₁..t₂, f ((a + U : ℝ) + t * I)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul (I : ℂ), Complex.norm_I, one_mul]
        have := norm_sub_le (∫ x : ℝ in a..a + U, f (x + t₁ * I)) (∫ x : ℝ in a..a + U, f (x + t₂ * I))
        linarith
    _ ≤ y ^ a / (-Real.log y) * (1 / (-t₁)) + y ^ a / (-Real.log y) * (1 / t₂) +
          y ^ (a + U) / (a + U) * (t₂ - t₁) := by
        gcongr
    _ = _ := by ring

/-- (K2) `0 < y < 1`: the truncated integral of `y^s/s` is small. -/
theorem kernel_lt_one {y a t₁ t₂ : ℝ} (hy0 : 0 < y) (hy : y < 1) (ha : 0 < a)
    (ht₁ : t₁ < 0) (ht₂ : 0 < t₂) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in t₁..t₂, (y : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I))‖
      ≤ y ^ a / (2 * π * (-Real.log y)) * (1 / (-t₁) + 1 / t₂) := by
  set C : ℝ := y ^ a / (-Real.log y) * (1 / (-t₁) + 1 / t₂) with hC
  have key : ‖∫ t in t₁..t₂, (y : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I)‖ ≤ C := by
    have hlim : Tendsto (fun U : ℝ => C + y ^ a * (t₂ - t₁) / (a + U)) atTop (𝓝 (C + 0)) := by
      apply Tendsto.const_add
      exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left atTop a tendsto_id)
    rw [add_zero] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop 0] with U hU
    refine (k_lt_one_step hy0 hy ha ht₁ ht₂ hU).trans ?_
    rw [hC]
    gcongr
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hy0 hy.le (by linarith))
      (by linarith)
  rw [norm_mul, k_norm_two_pi]
  calc 1 / (2 * π) * ‖∫ t in t₁..t₂, (y : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I)‖
      ≤ 1 / (2 * π) * C := by gcongr
    _ = _ := by rw [hC]; ring

/-- The `O(1)` condition at the simple pole `0` of `y^s / s` with residue `1`. -/
theorem k_near_zero {y : ℝ} (hy : 0 < y) :
    ((fun s : ℂ => (y : ℂ) ^ s / s) - fun s => (1 : ℂ) / (s - 0)) =O[𝓝[≠] 0] (1 : ℂ → ℂ) := by
  have hd : HasDerivAt (fun s : ℂ => (y : ℂ) ^ s) ((y : ℂ) ^ (0 : ℂ) * Complex.log y) 0 :=
    (Complex.hasStrictDerivAt_const_cpow (Or.inl (by exact_mod_cast hy.ne'))).hasDerivAt
  have hO := hd.isBigO_sub
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨c, hc⟩ := hO
  rw [Asymptotics.isBigO_iff]
  refine ⟨c, ?_⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hc] with s hs hs0
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hs0
  simp only [Pi.sub_apply, sub_zero, Pi.one_apply, norm_one, mul_one]
  rw [Complex.cpow_zero, sub_zero] at hs
  rw [div_sub_div_same, norm_div, div_le_iff₀ (norm_pos_iff.mpr hs0)]
  exact hs

/-- (K1), one rectangle: the bound with the left-edge error term. -/
theorem k_gt_one_step {y a t₁ t₂ U : ℝ} (hy : 1 < y) (ha : 0 < a)
    (ht₁ : t₁ < 0) (ht₂ : 0 < t₂) (hU : a < U) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in t₁..t₂, (y : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I)) - 1‖
      ≤ 1 / (2 * π) * (y ^ a / Real.log y * (1 / (-t₁) + 1 / t₂)
          + y ^ (a - U) * (U - a)⁻¹ * (t₂ - t₁)) := by
  have hy0 : 0 < y := by linarith
  have hres := ResidueTheoremOnRectangleWithSimplePole_prime (f := fun s : ℂ => (y : ℂ) ^ s / s)
    (z := ⟨a - U, t₁⟩) (w := ⟨a, t₂⟩) (p := 0) (A := 1) (by show a - U ≤ a; linarith)
    (by show t₁ ≤ t₂; linarith) ?_ ?_ (k_near_zero hy0)
  rotate_left
  · show Set.uIcc (a - U) a ×ℂ Set.uIcc t₁ t₂ ∈ 𝓝 0
    have hopen : IsOpen (Set.Ioo (a - U) a ×ℂ Set.Ioo t₁ t₂) := isOpen_Ioo.reProdIm isOpen_Ioo
    refine mem_of_superset (hopen.mem_nhds ?_) ?_
    · rw [Complex.mem_reProdIm]
      simp only [Complex.zero_re, Complex.zero_im, Set.mem_Ioo]
      exact ⟨⟨by linarith, ha⟩, ht₁, ht₂⟩
    · intro s hs
      rw [Complex.mem_reProdIm] at hs ⊢
      rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
      exact ⟨Ioo_subset_Icc_self hs.1, Ioo_subset_Icc_self hs.2⟩
  · intro s hs
    apply (k_differentiableAt hy0 _).differentiableWithinAt
    intro h0
    exact hs.2 (by simp [h0])
  simp only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, smul_eq_mul] at hres
  set B := ∫ x : ℝ in a - U..a, (y : ℂ) ^ ((x : ℂ) + t₁ * I) / ((x : ℂ) + t₁ * I) with hB
  set T := ∫ x : ℝ in a - U..a, (y : ℂ) ^ ((x : ℂ) + t₂ * I) / ((x : ℂ) + t₂ * I) with hT
  set F := ∫ t : ℝ in t₁..t₂, (y : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I) with hF
  set L := ∫ t : ℝ in t₁..t₂, (y : ℂ) ^ (((a - U : ℝ) : ℂ) + t * I) / (((a - U : ℝ) : ℂ) + t * I)
    with hL
  have hne : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [one_div, inv_mul_eq_iff_eq_mul₀ hne, mul_one] at hres
  have h3 : F = 2 * π + I * B - I * T + L := by
    linear_combination (-I) * hres + (F - L - 2 * π) * Complex.I_mul_I
  have h4 : (1 / (2 * π) : ℂ) * F - 1 = (1 / (2 * π) : ℂ) * (I * B - I * T + L) := by
    rw [h3]
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  rw [h4, norm_mul, k_norm_two_pi]
  have hBle := k_horizontal_gt_one (a := a) (U := U) hy ht₁.ne (by linarith)
  have hTle := k_horizontal_gt_one (a := a) (U := U) hy ht₂.ne' (by linarith)
  have hLle := k_vertical_le hy0 (σ := a - U) (by linarith) (t₁ := t₁) (t₂ := t₂) (by linarith)
  rw [abs_of_neg ht₁] at hBle
  rw [abs_of_pos ht₂] at hTle
  rw [abs_of_neg (by linarith), neg_sub] at hLle
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖I * B - I * T + L‖ ≤ ‖I * B‖ + ‖I * T‖ + ‖L‖ := by
        refine (norm_add_le _ _).trans ?_
        have := norm_sub_le (I * B) (I * T)
        linarith
    _ = ‖B‖ + ‖T‖ + ‖L‖ := by rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
    _ ≤ y ^ a / Real.log y * (1 / (-t₁)) + y ^ a / Real.log y * (1 / t₂)
          + y ^ (a - U) / (U - a) * (t₂ - t₁) := by
        gcongr
    _ = _ := by ring

/-- (K1) `y > 1`: the truncated integral of `y^s/s` over `Re s = a > 0`, `Im s ∈ [t₁, t₂]`
with `t₁ < 0 < t₂`, is `1` up to the horizontal-segment error. -/
theorem kernel_gt_one {y a t₁ t₂ : ℝ} (hy : 1 < y) (ha : 0 < a) (ht₁ : t₁ < 0) (ht₂ : 0 < t₂) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in t₁..t₂, (y : ℂ) ^ ((a : ℂ) + t * I) / ((a : ℂ) + t * I)) - 1‖
      ≤ y ^ a / (2 * π * Real.log y) * (1 / (-t₁) + 1 / t₂) := by
  set C : ℝ := y ^ a / Real.log y * (1 / (-t₁) + 1 / t₂) with hC
  have h1 : Tendsto (fun U : ℝ => y ^ (a - U)) atTop (𝓝 0) := by
    have := (tendsto_rpow_atBot_of_base_gt_one y hy).comp
      (tendsto_atBot_add_const_left atTop a tendsto_neg_atTop_atBot)
    refine this.congr fun U => ?_
    simp [Function.comp, sub_eq_add_neg]
  have h2 : Tendsto (fun U : ℝ => (U - a)⁻¹) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (-a) tendsto_id)
    refine this.congr fun U => ?_
    simp [Function.comp, sub_eq_add_neg]
  have hlim : Tendsto (fun U : ℝ => 1 / (2 * π) * (C + y ^ (a - U) * (U - a)⁻¹ * (t₂ - t₁)))
      atTop (𝓝 (1 / (2 * π) * (C + 0 * 0 * (t₂ - t₁)))) :=
    ((h1.mul h2).mul_const _).const_add C |>.const_mul _
  simp only [zero_mul, add_zero] at hlim
  have key := ge_of_tendsto hlim ((eventually_gt_atTop a).mono fun U hU =>
    k_gt_one_step hy ha ht₁ ht₂ hU)
  refine key.trans (le_of_eq ?_)
  rw [hC]
  ring


/-! ### Piece `Shift` -/

/-! ## (A) Absorption -/
/-! ## (E) Contour shift -/

lemma e_cont_max {σ₁ : ℝ} (hσ₁ : 0 < σ₁) : Continuous (fun t : ℝ => 1 / max σ₁ |t|) := by
  apply Continuous.div continuous_const (continuous_const.max continuous_abs)
  intro t; exact (lt_max_of_lt_left hσ₁).ne'

/-- `∫_{-T}^{T} dt / max σ₁ |t| = 2 + 2 log (T/σ₁)`. -/
lemma e_integral_max {σ₁ T : ℝ} (hσ₁ : 0 < σ₁) (hσ₁T : σ₁ ≤ T) :
    ∫ t in (-T)..T, 1 / max σ₁ |t| = 2 + 2 * Real.log (T / σ₁) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => 1 / max σ₁ |t|) volume a b :=
    fun a b => (e_cont_max hσ₁).intervalIntegrable a b
  have h1 : ∫ t in (-T)..(-σ₁), 1 / max σ₁ |t| = Real.log (T / σ₁) := by
    have : ∫ t in (-T)..(-σ₁), 1 / max σ₁ |t| = ∫ t in (-T)..(-σ₁), (fun t : ℝ => t⁻¹) (-t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      simp only
      rw [abs_of_neg (by linarith [ht.2]), max_eq_right (by linarith [ht.2]), one_div]
    rw [this, intervalIntegral.integral_comp_neg, neg_neg, neg_neg,
      integral_inv_of_pos hσ₁ (by linarith)]
  have h2 : ∫ t in (-σ₁)..σ₁, 1 / max σ₁ |t| = 2 := by
    have : ∫ t in (-σ₁)..σ₁, 1 / max σ₁ |t| = ∫ t in (-σ₁)..σ₁, (1 / σ₁) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      simp only
      rw [max_eq_left (abs_le.mpr ⟨ht.1, ht.2⟩)]
    rw [this, intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  have h3 : ∫ t in σ₁..T, 1 / max σ₁ |t| = Real.log (T / σ₁) := by
    have : ∫ t in σ₁..T, 1 / max σ₁ |t| = ∫ t in σ₁..T, t⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hσ₁T] at ht
      simp only
      rw [abs_of_pos (by linarith [ht.1]), max_eq_right ht.1, one_div]
    rw [this, integral_inv_of_pos hσ₁ (by linarith)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-T) (-σ₁)) (hint (-σ₁) T),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (-σ₁) σ₁) (hint σ₁ T), h1, h2, h3]
  ring

lemma e_norm_term {H : ℂ → ℂ} {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖H s * (x : ℂ) ^ s / s‖ = ‖H s‖ * x ^ s.re / ‖s‖ := by
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]

/-- Horizontal edge bound. -/
lemma e_horiz {H : ℂ → ℂ} {σ₁ σ₀ T x B : ℝ} (hσ : σ₁ ≤ σ₀) (hT : 1 ≤ T)
    (hx : 1 ≤ x) (hB : 0 ≤ B)
    (hHB : ∀ z ∈ Icc σ₁ σ₀ ×ℂ Icc (-T) T, ‖H z‖ ≤ B) {t : ℝ} (ht : |t| = T) :
    ‖∫ σ in σ₁..σ₀, H ((σ : ℂ) + t * I) * (x : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖
      ≤ B * x ^ σ₀ / T * (σ₀ - σ₁) := by
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := by linarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ₁) (b := σ₀)
    (C := B * x ^ σ₀ / T)
    (f := fun σ : ℝ => H ((σ : ℂ) + t * I) * (x : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)) ?_
  · rwa [abs_of_nonneg (by linarith)] at this
  · intro σ hσ'
    rw [Set.uIoc_of_le hσ] at hσ'
    have hσI : σ ∈ Icc σ₁ σ₀ := ⟨hσ'.1.le, hσ'.2⟩
    have htI : t ∈ Icc (-T) T := abs_le.mp ht.le
    have hmem : (σ : ℂ) + t * I ∈ Icc σ₁ σ₀ ×ℂ Icc (-T) T := by
      rw [Complex.mem_reProdIm]
      simpa using ⟨hσI, htI⟩
    have hnorm : T ≤ ‖(σ : ℂ) + t * I‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + t * I)
      simpa [ht] using this
    rw [e_norm_term hx0]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      add_zero]
    have hxσ : x ^ σ ≤ x ^ σ₀ := Real.rpow_le_rpow_of_exponent_le hx hσI.2
    exact div_le_div₀ (by positivity) (mul_le_mul (hHB _ hmem) hxσ (by positivity) hB) hT0 hnorm

/-- Left edge bound. -/
lemma e_left {H : ℂ → ℂ} {σ₁ σ₀ T x B : ℝ} (hσ₁ : 0 < σ₁) (hσ : σ₁ ≤ σ₀) (hT : 1 ≤ T)
    (hx : 1 ≤ x) (hB : 0 ≤ B) (hσ₁T : σ₁ ≤ T)
    (hHB : ∀ z ∈ Icc σ₁ σ₀ ×ℂ Icc (-T) T, ‖H z‖ ≤ B) :
    ‖∫ t in (-T)..T, H ((σ₁ : ℂ) + t * I) * (x : ℂ) ^ ((σ₁ : ℂ) + t * I) / ((σ₁ : ℂ) + t * I)‖
      ≤ B * x ^ σ₁ * (2 + 2 * Real.log (T / σ₁)) := by
  have hx0 : 0 < x := by linarith
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := -T) (b := T)
    (by linarith)
    (g := fun t : ℝ => B * x ^ σ₁ * (1 / max σ₁ |t|))
    (f := fun t : ℝ => H ((σ₁ : ℂ) + t * I) * (x : ℂ) ^ ((σ₁ : ℂ) + t * I) / ((σ₁ : ℂ) + t * I))
    ?_ ?_
  · rw [intervalIntegral.integral_const_mul, e_integral_max hσ₁ hσ₁T] at hbound
    exact hbound
  · refine Filter.Eventually.of_forall fun t ht => ?_
    have htI : t ∈ Icc (-T) T := ⟨ht.1.le, ht.2⟩
    have hmem : (σ₁ : ℂ) + t * I ∈ Icc σ₁ σ₀ ×ℂ Icc (-T) T := by
      rw [Complex.mem_reProdIm]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
        add_zero, add_im, zero_add, mul_im]
      exact ⟨⟨le_refl σ₁, hσ⟩, htI⟩
    have hnorm : max σ₁ |t| ≤ ‖(σ₁ : ℂ) + t * I‖ := by
      refine max_le ?_ ?_
      · have := Complex.abs_re_le_norm ((σ₁ : ℂ) + t * I)
        simpa [abs_of_pos hσ₁] using this
      · have := Complex.abs_im_le_norm ((σ₁ : ℂ) + t * I)
        simpa using this
    rw [e_norm_term hx0]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      add_zero]
    rw [mul_one_div]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (hHB _ hmem) (by positivity))
      (lt_max_of_lt_left hσ₁) hnorm
  · exact (continuous_const.mul (e_cont_max hσ₁)).intervalIntegrable _ _

theorem shift_bound {H : ℂ → ℂ} {σ₁ σ₀ T x B : ℝ} (hσ₁ : 0 < σ₁) (hσ₁1 : σ₁ ≤ 1)
    (hσ : σ₁ ≤ σ₀) (hT : 1 ≤ T) (hx : 1 ≤ x) (hB : 0 ≤ B)
    (hH : DifferentiableOn ℂ H (Icc σ₁ σ₀ ×ℂ Icc (-T) T))
    (hHB : ∀ z ∈ Icc σ₁ σ₀ ×ℂ Icc (-T) T, ‖H z‖ ≤ B) :
    ‖(1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
        H ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)‖
      ≤ B / (2 * π) * (x ^ σ₁ * (2 + 2 * Real.log (T / σ₁)) + 2 * (σ₀ - σ₁) * x ^ σ₀ / T) := by
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := by linarith
  have hσ₁T : σ₁ ≤ T := hσ₁1.trans hT
  have hdiff : DifferentiableOn ℂ (fun s : ℂ => H s * (x : ℂ) ^ s / s)
      (Icc σ₁ σ₀ ×ℂ Icc (-T) T) := by
    apply DifferentiableOn.div
      (hH.mul (differentiableOn_id.const_cpow (Or.inl (by exact_mod_cast hx0.ne'))))
      differentiableOn_id
    intro s hs h0
    simp only [id] at h0
    rw [Complex.mem_reProdIm, h0] at hs
    simp only [zero_re, zero_im, Set.mem_Icc] at hs
    linarith [hs.1.1]
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun s : ℂ => H s * (x : ℂ) ^ s / s) ⟨σ₁, -T⟩ ⟨σ₀, T⟩ (by
      dsimp only
      rw [Set.uIcc_of_le hσ, Set.uIcc_of_le (by linarith)]
      exact hdiff)
  dsimp only at hc
  rw [smul_eq_mul, smul_eq_mul] at hc
  set V₀ := ∫ t in (-T)..T,
    H ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I) with hV₀
  set V₁ := ∫ t in (-T)..T,
    H ((σ₁ : ℂ) + t * I) * (x : ℂ) ^ ((σ₁ : ℂ) + t * I) / ((σ₁ : ℂ) + t * I) with hV₁
  set bot := ∫ σ in σ₁..σ₀,
    H ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) * (x : ℂ) ^ ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)
      / ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) with hbot
  set top := ∫ σ in σ₁..σ₀,
    H ((σ : ℂ) + (T : ℂ) * I) * (x : ℂ) ^ ((σ : ℂ) + (T : ℂ) * I)
      / ((σ : ℂ) + (T : ℂ) * I) with htop
  have hV : I * V₀ = I * V₁ - bot + top := by linear_combination hc
  have hV0 : ‖V₀‖ ≤ ‖V₁‖ + ‖bot‖ + ‖top‖ := by
    have h1 : ‖V₀‖ = ‖I * V₀‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    rw [h1, hV]
    calc ‖I * V₁ - bot + top‖ ≤ ‖I * V₁ - bot‖ + ‖top‖ := norm_add_le _ _
      _ ≤ ‖I * V₁‖ + ‖bot‖ + ‖top‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖V₁‖ + ‖bot‖ + ‖top‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hleft := e_left hσ₁ hσ hT hx hB hσ₁T hHB
  have hbot' := e_horiz hσ hT hx hB hHB (t := -T) (by rw [abs_neg, abs_of_pos hT0])
  have htop' := e_horiz hσ hT hx hB hHB (t := T) (abs_of_pos hT0)
  have hnorm : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    have : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [norm_mul, hnorm]
  have hfinal : ‖V₀‖ ≤ B * (x ^ σ₁ * (2 + 2 * Real.log (T / σ₁))
      + 2 * (σ₀ - σ₁) * x ^ σ₀ / T) := by
    calc ‖V₀‖ ≤ ‖V₁‖ + ‖bot‖ + ‖top‖ := hV0
      _ ≤ B * x ^ σ₁ * (2 + 2 * Real.log (T / σ₁)) + B * x ^ σ₀ / T * (σ₀ - σ₁)
          + B * x ^ σ₀ / T * (σ₀ - σ₁) := add_le_add (add_le_add hleft hbot') htop'
      _ = _ := by ring
  calc 1 / (2 * π) * ‖V₀‖
      ≤ 1 / (2 * π) * (B * (x ^ σ₁ * (2 + 2 * Real.log (T / σ₁))
          + 2 * (σ₀ - σ₁) * x ^ σ₀ / T)) := by gcongr
    _ = _ := by ring


/-! ### Piece `PerronFormula` -/

/-! ### Elementary facts about `s t = σ₀ + t I` -/

lemma c_s_re (σ₀ t : ℝ) : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp

lemma c_s_ne_zero {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (t : ℝ) : (σ₀ : ℂ) + t * I ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  simp at h'
  linarith

lemma c_le_norm_s {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (t : ℝ) : σ₀ ≤ ‖(σ₀ : ℂ) + t * I‖ := by
  have h := Complex.abs_re_le_norm ((σ₀ : ℂ) + t * I)
  rwa [c_s_re, abs_of_pos hσ₀] at h

/-! ### Summability of the Dirichlet series -/

lemma c_norm_term_le {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (σ₀ t : ℝ) (n : ℕ) :
    ‖LSeries.term a ((σ₀ : ℂ) + t * I) n‖
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀ := by
  rw [LSeries.norm_term_eq, c_s_re]
  split_ifs with hn
  · subst hn
    simp
  · gcongr
    exact ha n

lemma c_summable {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    {σ₀ : ℝ} (hσ₀ : 1 < σ₀) (t : ℝ) : LSeriesSummable a ((σ₀ : ℂ) + t * I) :=
  Summable.of_norm_bounded (summable_vonMangoldt_div_rpow hσ₀) (c_norm_term_le ha σ₀ t)

lemma c_norm_F_le {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    {x σ₀ : ℝ} (hx : 0 < x) (hσ₀ : 0 < σ₀) (t : ℝ) (n : ℕ) :
    ‖LSeries.term a ((σ₀ : ℂ) + t * I) n * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)‖
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀ * x ^ σ₀ / σ₀ := by
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, c_s_re]
  have h1 := c_norm_term_le ha σ₀ t n
  have h2 := c_le_norm_s hσ₀ t
  have h3 : 0 ≤ x ^ σ₀ := Real.rpow_nonneg hx.le _
  have h4 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀ :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  exact div_le_div₀ (mul_nonneg h4 h3) (mul_le_mul_of_nonneg_right h1 h3) hσ₀ h2

lemma c_continuous_F (a : ℕ → ℂ) {x σ₀ : ℝ} (hx : 0 < x) (hσ₀ : 0 < σ₀) (n : ℕ) :
    Continuous fun t : ℝ =>
      LSeries.term a ((σ₀ : ℂ) + t * I) n * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I) := by
  have hs : Continuous fun t : ℝ => (σ₀ : ℂ) + t * I := by fun_prop
  have hx' : Continuous fun t : ℝ => (x : ℂ) ^ ((σ₀ : ℂ) + t * I) :=
    hs.const_cpow (Or.inl (by exact_mod_cast hx.ne'))
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, zero_mul, zero_div]
    exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hn' : Continuous fun t : ℝ => (n : ℂ) ^ ((σ₀ : ℂ) + t * I) :=
      hs.const_cpow (Or.inl hn0)
    refine ((continuous_const.div hn' ?_).mul hx').div hs (c_s_ne_zero hσ₀)
    intro t
    rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero (c_s_ne_zero hσ₀ t)]
    exact hn0

/-! ### Termwise evaluation -/

lemma c_div_cpow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (s : ℂ) :
    ((x / n : ℝ) : ℂ) ^ s = (x : ℂ) ^ s / (n : ℂ) ^ s := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx hn0,
    Complex.ofReal_inv, Complex.ofReal_natCast, Complex.inv_cpow, div_eq_mul_inv]
  rw [Complex.natCast_arg]
  exact Real.pi_pos.ne

lemma c_integral_term (a : ℕ → ℂ) {x σ₀ T : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) :
    (∫ t in (-T)..T, LSeries.term a ((σ₀ : ℂ) + t * I) n * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) /
        ((σ₀ : ℂ) + t * I))
      = a n * ∫ t in (-T)..T, ((x / n : ℝ) : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  rw [LSeries.term_of_ne_zero hn, c_div_cpow hx n]
  ring

/-! ### The per-term bound -/

lemma c_term_bound {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) {σ₀ : ℝ} (hσ₀ : 1 < σ₀)
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
        LSeries.term a ((σ₀ : ℂ) + t * I) n * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))
      - (if n < N then a n else 0)‖
      ≤ 1 / (π * T) * ((ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ /
          |Real.log (x / n)|) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < x := by rw [hx]; linarith
  have hσ₀' : 0 < σ₀ := by linarith
  have hπ : 0 < π := Real.pi_pos
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  rcases eq_or_ne n 0 with rfl | hn
  · -- the `n = 0` term
    have ha0 : a 0 = 0 := by
      have h := ha 0
      simp at h
      exact h
    simp [ha0]
  · rw [c_integral_term a hx0.le hn]
    have hy0 : 0 < x / n := div_pos hx0 (by positivity)
    have hyσ : 0 ≤ (x / n) ^ σ₀ := Real.rpow_nonneg hy0.le _
    by_cases hnN : n < N
    · -- `n < N`, so `y = x / n > 1`
      rw [if_pos hnN]
      have hn1 : (n : ℝ) + 1 ≤ N := by exact_mod_cast hnN
      have hy : 1 < x / n := by
        rw [lt_div_iff₀ (by positivity), hx]; linarith
      have hK := kernel_gt_one hy hσ₀' (neg_neg_of_pos hT) hT
      have hlog : 0 < Real.log (x / n) := Real.log_pos hy
      have heq : (1 / (2 * π) : ℂ) * (a n * ∫ t in (-T)..T,
          ((x / n : ℝ) : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)) - a n
          = a n * ((1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
          ((x / n : ℝ) : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)) - 1) := by ring
      rw [heq, norm_mul]
      calc ‖a n‖ * ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
              ((x / n : ℝ) : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)) - 1‖
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
              ((x / n) ^ σ₀ / (2 * π * Real.log (x / n)) * (1 / (- -T) + 1 / T)) :=
            mul_le_mul (ha n) hK (norm_nonneg _) hΛ
        _ = 1 / (π * T) * ((ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ /
              |Real.log (x / n)|) := by
            rw [abs_of_pos hlog, neg_neg]
            field_simp
            ring
    · -- `n ≥ N`, so `y = x / n < 1`
      rw [if_neg hnN, sub_zero]
      have hn1 : (N : ℝ) ≤ n := by exact_mod_cast Nat.le_of_not_lt hnN
      have hy : x / n < 1 := by
        rw [div_lt_iff₀ (by positivity), hx]; linarith
      have hK := kernel_lt_one hy0 hy hσ₀' (neg_neg_of_pos hT) hT
      have hlog : Real.log (x / n) < 0 := Real.log_neg hy0 hy
      rw [mul_left_comm, norm_mul]
      calc ‖a n‖ * ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
              ((x / n : ℝ) : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))‖
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
              ((x / n) ^ σ₀ / (2 * π * (-Real.log (x / n))) * (1 / (- -T) + 1 / T)) :=
            mul_le_mul (ha n) hK (norm_nonneg _) hΛ
        _ = 1 / (π * T) * ((ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ /
              |Real.log (x / n)|) := by
            rw [abs_of_neg hlog, neg_neg]
            have : 0 < -Real.log (x / n) := by linarith
            field_simp
            ring

/-! ### The truncated Perron formula -/

theorem perron_truncated {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : x = (N : ℝ) - 1 / 2) {σ₀ : ℝ} (hσ₀ : 1 < σ₀)
    {T : ℝ} (hT : 0 < T) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
        LSeries a ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))
      - ∑ n ∈ Finset.range N, a n‖
      ≤ 1 / (π * T) * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ /
          |Real.log (x / n)| := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < x := by rw [hx]; linarith
  have hσ₀' : 0 < σ₀ := by linarith
  -- Step 1: interchange sum and integral
  have hDCT : HasSum
      (fun n : ℕ => ∫ t in (-T)..T,
        LSeries.term a ((σ₀ : ℂ) + t * I) n * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))
      (∫ t in (-T)..T,
        LSeries a ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ₀ * x ^ σ₀ / σ₀)
    · intro n
      exact (c_continuous_F a hx0 hσ₀' n).aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall (fun t _ => c_norm_F_le ha hx0 hσ₀' t n)
    · exact Filter.Eventually.of_forall
        (fun t _ => ((summable_vonMangoldt_div_rpow hσ₀).mul_right _).div_const _)
    · exact _root_.intervalIntegrable_const
    · exact Filter.Eventually.of_forall
        (fun t _ => ((c_summable ha hσ₀ t).hasSum.mul_right _).div_const _)
  -- Step 2: the sequences
  set u : ℕ → ℂ := fun n => (1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
    LSeries.term a ((σ₀ : ℂ) + t * I) n * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)
    with hu_def
  set v : ℕ → ℂ := fun n => if n < N then a n else 0 with hv_def
  set w : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (x / n) ^ σ₀ /
    |Real.log (x / n)| with hw_def
  have hbound : ∀ n, ‖u n - v n‖ ≤ 1 / (π * T) * w n :=
    fun n => c_term_bound ha hN hx hσ₀ hT n
  have hw : Summable (fun n => 1 / (π * T) * w n) :=
    (summable_perron_error hN hx hσ₀).mul_left _
  have hnorm : Summable (fun n => ‖u n - v n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hw
  have hu : Summable u := hDCT.summable.mul_left _
  have hv : Summable v := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    rw [Finset.mem_range] at hn
    simp [hv_def, hn]
  have h1 : (1 / (2 * π) : ℂ) * (∫ t in (-T)..T,
      LSeries a ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))
      = ∑' n, u n := by
    rw [← hDCT.tsum_eq, hu_def, tsum_mul_left]
  have h2 : ∑ n ∈ Finset.range N, a n = ∑' n, v n := by
    rw [tsum_eq_sum (s := Finset.range N)]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_range] at hn
      simp [hv_def, hn]
    · intro n hn
      rw [Finset.mem_range] at hn
      simp [hv_def, hn]
  rw [h1, h2, ← hu.tsum_sub hv]
  calc ‖∑' n, (u n - v n)‖
      ≤ ∑' n, ‖u n - v n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, 1 / (π * T) * w n := hnorm.tsum_le_tsum hbound hw
    _ = 1 / (π * T) * ∑' n, w n := tsum_mul_left


end L31P
end ArtinPrimitiveRoots
end

section
/-!
# L31P_Psi: a ψ-type bound for `Σ_{n<M} Λ(n) χ(n) n^{it}` from a log-derivative bound

Truncated Perron formula at `y = M - 1/2`, `σ₀ = 1 + 1/λ`, height `H`, then the contour shift to
`Re s = σ₁` (`shift_bound`), assuming `L(·, χ)` has no zero and `‖L′/L‖ ≤ B` on the shifted
rectangle `[σ₁, σ₀] × [-H, H] - it`.
-/

namespace ArtinPrimitiveRoots
namespace L31P

open Complex Real Set MeasureTheory intervalIntegral Filter Topology

/-- The twisted von Mangoldt coefficients `Λ(n) χ(n) n^{it}`. -/
noncomputable def tw {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * χ n * (n : ℂ) ^ (I * t)

theorem tw_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) :
    ‖tw χ t n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [tw]
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold tw
  rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  have h1 : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ = ArithmeticFunction.vonMangoldt n := by
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rw [h1]
  have h2 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  simp only [mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
    Real.rpow_zero, mul_one]
  calc ArithmeticFunction.vonMangoldt n * ‖χ n‖
      ≤ ArithmeticFunction.vonMangoldt n * 1 :=
        mul_le_mul_of_nonneg_left h2 ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := mul_one _

theorem LSeries_tw {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (tw χ t) s =
      -deriv (DirichletCharacter.LFunction χ) (s - I * t) /
        DirichletCharacter.LFunction χ (s - I * t) := by
  have hs' : 1 < (s - I * t).re := by simpa using hs
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs',
    DirichletCharacter.LFunction_eq_LSeries χ hs',
    ← DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs']
  unfold LSeries
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_sub _ _ hn']
  have h1 : (n : ℂ) ^ s ≠ 0 := (Complex.cpow_ne_zero_iff_of_exponent_ne_zero
    (by intro h; rw [h] at hs; simp at hs; linarith)).mpr hn'
  have h2 : (n : ℂ) ^ (I * t) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hn']; exact Complex.exp_ne_zero _
  simp only [tw, Pi.mul_apply]
  field_simp

theorem psi_tw_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) {M : ℕ} (hM : 2 ≤ M)
    {lam σ₁ H B : ℝ} (hlam : 1 ≤ lam) (hσ₁ : 0 < σ₁) (hσ₁1 : σ₁ ≤ 1) (hH : 1 ≤ H) (hB : 0 ≤ B)
    (hnz : ∀ z ∈ Icc σ₁ (1 + 1 / lam) ×ℂ Icc (-H) H,
      z - I * t ≠ 1 ∧ DirichletCharacter.LFunction χ (z - I * t) ≠ 0)
    (hbd : ∀ z ∈ Icc σ₁ (1 + 1 / lam) ×ℂ Icc (-H) H,
      ‖deriv (DirichletCharacter.LFunction χ) (z - I * t) /
        DirichletCharacter.LFunction χ (z - I * t)‖ ≤ B) :
    ‖∑ n ∈ Finset.range M, tw χ t n‖ ≤
      B / (2 * π) * (((M : ℝ) - 1 / 2) ^ σ₁ * (2 + 2 * Real.log (H / σ₁))
          + 2 * (1 + 1 / lam - σ₁) * ((M : ℝ) - 1 / 2) ^ (1 + 1 / lam) / H)
        + 1 / (π * H) * (10 * ((M : ℝ) - 1 / 2) ^ (1 + 1 / lam) * (8 * lam ^ 2)
          + 100 * M * (1 + Real.log M) ^ 2) := by
  set σ₀ : ℝ := 1 + 1 / lam with hσ₀def
  set y : ℝ := (M : ℝ) - 1 / 2 with hydef
  have hlam0 : 0 < lam := by linarith
  have hσ₀ : 1 < σ₀ := by rw [hσ₀def]; have : 0 < 1 / lam := by positivity
                          linarith
  have hσ₀3 : σ₀ ≤ 3 := by
    rw [hσ₀def]; have : 1 / lam ≤ 1 := by rw [div_le_one hlam0]; exact hlam
    linarith
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hy1 : 1 ≤ y := by rw [hydef]; linarith
  set F : ℂ → ℂ := fun z => -deriv (DirichletCharacter.LFunction χ) (z - I * t) /
    DirichletCharacter.LFunction χ (z - I * t) with hFdef
  -- analyticity of `L(·, χ)` off `1`
  have hLdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {w : ℂ | w ≠ 1} :=
    fun w hw => (DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hw)).differentiableWithinAt
  have hLan : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {w : ℂ | w ≠ 1} :=
    hLdiff.analyticOnNhd isOpen_ne
  have hdLan : AnalyticOnNhd ℂ (deriv (DirichletCharacter.LFunction χ)) {w : ℂ | w ≠ 1} :=
    hLan.deriv
  have hdiff : DifferentiableOn ℂ F (Icc σ₁ σ₀ ×ℂ Icc (-H) H) := by
    intro z hz
    obtain ⟨hw, hL0⟩ := hnz z hz
    have hsub : DifferentiableAt ℂ (fun z : ℂ => z - I * t) z := by fun_prop
    have h1 : DifferentiableAt ℂ (fun z => deriv (DirichletCharacter.LFunction χ) (z - I * t)) z :=
      show DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction χ) ∘ fun z => z - I * t) z from
        (hdLan _ hw).differentiableAt.comp z hsub
    have h2 : DifferentiableAt ℂ (fun z => DirichletCharacter.LFunction χ (z - I * t)) z :=
      show DifferentiableAt ℂ (DirichletCharacter.LFunction χ ∘ fun z => z - I * t) z from
        (DirichletCharacter.differentiableAt_LFunction χ _ (Or.inl hw)).comp z hsub
    exact (h1.neg.div h2 hL0).differentiableWithinAt
  have hFB : ∀ z ∈ Icc σ₁ σ₀ ×ℂ Icc (-H) H, ‖F z‖ ≤ B := by
    intro z hz
    simp only [hFdef, neg_div, norm_neg]
    exact hbd z hz
  have hshift := shift_bound (H := F) hσ₁ hσ₁1 (by linarith) hH hy1 hB hdiff hFB
  have hP := perron_truncated (tw_norm_le χ t) hM hydef hσ₀ (by linarith : (0 : ℝ) < H)
  have hE := perron_error_sum_le hM hydef hσ₀ hσ₀3
  have hS := tsum_vonMangoldt_div_rpow_le hσ₀ hσ₀3
  have hS' : 8 / (σ₀ - 1) ^ 2 = 8 * lam ^ 2 := by
    rw [hσ₀def]; field_simp; ring
  rw [hS'] at hS
  have hint_eq : (∫ u in (-H)..H, LSeries (tw χ t) ((σ₀ : ℂ) + u * I) *
        (y : ℂ) ^ ((σ₀ : ℂ) + u * I) / ((σ₀ : ℂ) + u * I)) =
      ∫ u in (-H)..H, F ((σ₀ : ℂ) + u * I) * (y : ℂ) ^ ((σ₀ : ℂ) + u * I) /
        ((σ₀ : ℂ) + u * I) := by
    congr 1
    funext u
    rw [LSeries_tw χ t (by simpa using hσ₀)]
  rw [hint_eq] at hP
  set Iv : ℂ := (1 / (2 * π) : ℂ) * ∫ u in (-H)..H, F ((σ₀ : ℂ) + u * I) *
    (y : ℂ) ^ ((σ₀ : ℂ) + u * I) / ((σ₀ : ℂ) + u * I) with hIv
  have hy0 : 0 ≤ y := by linarith
  have hyσ : 0 ≤ y ^ σ₀ := Real.rpow_nonneg hy0 _
  have hπH : 0 ≤ 1 / (π * H) := by have := Real.pi_pos; positivity
  have herr : 1 / (π * H) * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (y / n) ^ σ₀ /
      |Real.log (y / n)| ≤ 1 / (π * H) * (10 * y ^ σ₀ * (8 * lam ^ 2)
        + 100 * M * (1 + Real.log M) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hπH
    refine hE.trans ?_
    gcongr
  calc ‖∑ n ∈ Finset.range M, tw χ t n‖
      = ‖Iv - (Iv - ∑ n ∈ Finset.range M, tw χ t n)‖ := by ring_nf
    _ ≤ ‖Iv‖ + ‖Iv - ∑ n ∈ Finset.range M, tw χ t n‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hshift (hP.trans herr)

end L31P
end ArtinPrimitiveRoots
end

section
/-!
# L31P_Small: the ψ-type sum is `≤ y L^{-A} / 12`

Specialisation of `psi_tw_bound` to `λ = L`, `σ₁ = 1 - cT²/(2L)` (`T = log L`), `H = L^{A+3}`,
`B = K L`, with the numerical side conditions as hypotheses.
-/

namespace ArtinPrimitiveRoots
namespace L31P

open Complex Real Set

theorem psi_small {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) {M : ℕ} (hM : 2 ≤ M)
    {L c K A : ℝ} (hL : 38400 ≤ L) (hc : 0 < c) (hK : 0 ≤ K) (hA : 0 < A)
    (hδ : c * Real.log L ^ 2 / (2 * L) ≤ 1 / 2)
    (hyL : Real.log ((M : ℝ) - 1 / 2) ≤ L)
    (hy1 : ((M : ℝ) - 1 / 2) ^ (-(c * Real.log L ^ 2 / (2 * L))) ≤ L ^ (-(A + 3)))
    (hK1 : 48 * K * (5 + (A + 3) * Real.log L) ≤ L ^ 2)
    (hnz : ∀ z ∈ Icc (1 - c * Real.log L ^ 2 / (2 * L)) (1 + 1 / L) ×ℂ
        Icc (-(L ^ (A + 3))) (L ^ (A + 3)),
      z - I * t ≠ 1 ∧ DirichletCharacter.LFunction χ (z - I * t) ≠ 0)
    (hbd : ∀ z ∈ Icc (1 - c * Real.log L ^ 2 / (2 * L)) (1 + 1 / L) ×ℂ
        Icc (-(L ^ (A + 3))) (L ^ (A + 3)),
      ‖deriv (DirichletCharacter.LFunction χ) (z - I * t) /
        DirichletCharacter.LFunction χ (z - I * t)‖ ≤ K * L) :
    ‖∑ n ∈ Finset.range M, tw χ t n‖ ≤ ((M : ℝ) - 1 / 2) * L ^ (-A) / 12 := by
  set δ : ℝ := c * Real.log L ^ 2 / (2 * L) with hδdef
  set H : ℝ := L ^ (A + 3) with hHdef
  set y : ℝ := (M : ℝ) - 1 / 2 with hydef
  set P : ℝ := L ^ A with hPdef
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  have hP0 : 0 < P := Real.rpow_pos_of_pos hL0 A
  have hP1 : 1 ≤ P := Real.one_le_rpow hL1 hA.le
  have hHP : H = P * L ^ 3 := by
    rw [hHdef, hPdef, Real.rpow_add hL0, Real.rpow_ofNat]
  have hH1 : 1 ≤ H := by rw [hHP]; exact one_le_mul_of_one_le_of_one_le hP1 (one_le_pow₀ hL1)
  have hnegA3 : L ^ (-(A + 3)) = 1 / (P * L ^ 3) := by
    rw [Real.rpow_neg hL0.le, ← hHdef, hHP, one_div]
  have hnegA : L ^ (-A) = 1 / P := by rw [Real.rpow_neg hL0.le, one_div]
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hy0 : 0 < y := by rw [hydef]; linarith
  have hy32 : 3 / 2 ≤ y := by rw [hydef]; linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  -- `y ^ σ₀ ≤ 3 y`
  have hyσ₀ : y ^ (1 + 1 / L) ≤ 3 * y := by
    rw [Real.rpow_add hy0, Real.rpow_one]
    have h1 : y ^ (1 / L) ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos hy0]
      apply Real.exp_le_exp.mpr
      rw [mul_one_div, div_le_one hL0]
      exact hyL
    have h2 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    calc y * y ^ (1 / L) ≤ y * 3 := mul_le_mul_of_nonneg_left (h1.trans h2) hy0.le
      _ = 3 * y := by ring
  -- `y ^ σ₁ ≤ y / (P L³)`
  have hyσ₁ : y ^ (1 - δ) ≤ y / (P * L ^ 3) := by
    rw [sub_eq_add_neg, Real.rpow_add hy0, Real.rpow_one]
    calc y * y ^ (-δ) ≤ y * L ^ (-(A + 3)) := mul_le_mul_of_nonneg_left hy1 hy0.le
      _ = y / (P * L ^ 3) := by rw [hnegA3]; ring
  -- `log (H / σ₁) ≤ 1 + (A + 3) log L`
  have hσ₁ : 1 / 2 ≤ 1 - δ := by linarith
  have hlogH : Real.log (H / (1 - δ)) ≤ 1 + (A + 3) * Real.log L := by
    have h1 : H / (1 - δ) ≤ 2 * H := by
      rw [div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hσ₁ (by positivity : (0 : ℝ) ≤ 2 * H)
      linarith
    have h2 : Real.log (H / (1 - δ)) ≤ Real.log (2 * H) :=
      Real.log_le_log (by apply div_pos <;> linarith) h1
    rw [Real.log_mul (by norm_num) (by linarith), hHdef, Real.log_rpow hL0] at h2
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have hlogH0 : 0 ≤ Real.log (H / (1 - δ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith)]; linarith
  -- `log M ≤ 1 + L`
  have hlogM : Real.log M ≤ 1 + L := by
    have h1 : (M : ℝ) ≤ 2 * y := by rw [hydef]; linarith
    have h2 : Real.log M ≤ Real.log (2 * y) := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) hy0.ne'] at h2
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  -- pieces
  have e1 : y ^ (1 - δ) * (2 + 2 * Real.log (H / (1 - δ))) ≤
      y / (P * L ^ 3) * (4 + 2 * (A + 3) * Real.log L) := by
    apply mul_le_mul hyσ₁ (by linarith) (by linarith) (by positivity)
  have e2 : 2 * (1 + 1 / L - (1 - δ)) * y ^ (1 + 1 / L) / H ≤ 6 * y / (P * L ^ 3) := by
    have h1 : 1 + 1 / L - (1 - δ) ≤ 1 := by
      have : 1 / L ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
      linarith
    have h0 : 0 ≤ 1 + 1 / L - (1 - δ) := by
      have : 0 ≤ 1 / L := by positivity
      linarith
    have hyσ0 : 0 ≤ y ^ (1 + 1 / L) := Real.rpow_nonneg hy0.le _
    have hnum : 2 * (1 + 1 / L - (1 - δ)) * y ^ (1 + 1 / L) ≤ 6 * y := by
      have := mul_le_mul h1 hyσ₀ hyσ0 zero_le_one
      linarith
    rw [hHP]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have e3 : 10 * y ^ (1 + 1 / L) * (8 * L ^ 2) + 100 * (M : ℝ) * (1 + Real.log M) ^ 2 ≤
      1040 * y * L ^ 2 := by
    have h1 : (1 + Real.log M) ^ 2 ≤ (2 * L) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : (M : ℝ) ≤ 2 * y := by rw [hydef]; linarith
    have h3 : 10 * y ^ (1 + 1 / L) * (8 * L ^ 2) ≤ 10 * (3 * y) * (8 * L ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyσ₀ (by norm_num)) (by positivity)
    have h4 : 100 * (M : ℝ) * (1 + Real.log M) ^ 2 ≤ 100 * (2 * y) * (2 * L) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) h1 (by positivity) (by positivity)
    have h5 : 10 * (3 * y) * (8 * L ^ 2) + 100 * (2 * y) * (2 * L) ^ 2 = 1040 * y * L ^ 2 := by
      ring
    linarith
  have hKL : 0 ≤ K * L / (2 * π) := by positivity
  have hπ : 3 < π := Real.pi_gt_three
  have hπH : 0 ≤ 1 / (π * H) := by positivity
  have step1 : K * L / (2 * π) * (y ^ (1 - δ) * (2 + 2 * Real.log (H / (1 - δ))) +
      2 * (1 + 1 / L - (1 - δ)) * y ^ (1 + 1 / L) / H) ≤
      y / P * (K * (5 + (A + 3) * Real.log L) / (π * L ^ 2)) := by
    calc _ ≤ K * L / (2 * π) * (y / (P * L ^ 3) * (4 + 2 * (A + 3) * Real.log L) +
          6 * y / (P * L ^ 3)) := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hKL
      _ = _ := by field_simp; ring
  have step2 : 1 / (π * H) * (10 * y ^ (1 + 1 / L) * (8 * L ^ 2) +
      100 * (M : ℝ) * (1 + Real.log M) ^ 2) ≤ y / P * (1040 / (π * L)) := by
    calc _ ≤ 1 / (π * H) * (1040 * y * L ^ 2) := mul_le_mul_of_nonneg_left e3 hπH
      _ = _ := by rw [hHP]; field_simp
  have f1 : K * (5 + (A + 3) * Real.log L) / (π * L ^ 2) ≤ 1 / 48 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h1 : L ^ 2 ≤ π * L ^ 2 := le_mul_of_one_le_left (by positivity) (by linarith)
    linarith
  have f2 : 1040 / (π * L) ≤ 1 / 36 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h1 : L ≤ π * L := le_mul_of_one_le_left hL0.le (by linarith)
    linarith
  have hyP : 0 ≤ y / P := by positivity
  have hfin : y / P * (1 / 48) + y / P * (1 / 36) ≤ y * L ^ (-A) / 12 := by
    rw [hnegA]
    have : y / P * (1 / 48) + y / P * (1 / 36) = y / P * (7 / 144) := by ring
    rw [this]
    have : y * (1 / P) / 12 = y / P * (12 / 144) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by norm_num) hyP
  have hmain := psi_tw_bound χ t hM (lam := L) (σ₁ := 1 - δ) (H := H) (B := K * L) hL1
    (by linarith) (by linarith) hH1 (by positivity) hnz hbd
  calc ‖∑ n ∈ Finset.range M, tw χ t n‖ ≤ _ := hmain
    _ ≤ y / P * (K * (5 + (A + 3) * Real.log L) / (π * L ^ 2)) +
        y / P * (1040 / (π * L)) := add_le_add step1 step2
    _ ≤ y / P * (1 / 48) + y / P * (1 / 36) := by gcongr
    _ ≤ y * L ^ (-A) / 12 := hfin

end L31P
end ArtinPrimitiveRoots
end

section
/-!
# L31P_Window: from the ψ-type bound to the prime sum over a window `[a, b]`

Prime powers are removed with Mathlib's `ψ - θ ≤ 2 √x log x`, and the weight `1/(n log n)` by
summation by parts (`Finset.sum_range_by_parts`).
-/

namespace ArtinPrimitiveRoots
namespace L31P

open Complex Real Set Finset

/-- Summation by parts against a nonnegative nonincreasing weight. -/
theorem abel_bound (c : ℕ → ℂ) (f : ℕ → ℝ) (k : ℕ) (E : ℝ)
    (hf : ∀ i, f (i + 1) ≤ f i) (hf0 : ∀ i, 0 ≤ f i)
    (hE : ∀ j ≤ k, ‖∑ i ∈ range j, c i‖ ≤ E) :
    ‖∑ i ∈ range k, f i • c i‖ ≤ E * f 0 := by
  rw [Finset.sum_range_by_parts]
  have h1 : ‖f (k - 1) • ∑ i ∈ range k, c i‖ ≤ f (k - 1) * E := by
    rw [norm_smul, Real.norm_of_nonneg (hf0 _)]
    exact mul_le_mul_of_nonneg_left (hE k le_rfl) (hf0 _)
  have h2 : ‖∑ i ∈ range (k - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), c j‖ ≤
      ∑ i ∈ range (k - 1), (f i - f (i + 1)) * E := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hf i))]
    apply mul_le_mul_of_nonneg_left (hE _ ?_) (sub_nonneg.mpr (hf i))
    have := Finset.mem_range.mp hi
    omega
  have h3 : ∑ i ∈ range (k - 1), (f i - f (i + 1)) * E = (f 0 - f (k - 1)) * E := by
    rw [← Finset.sum_mul, Finset.sum_range_sub']
  calc _ ≤ ‖f (k - 1) • ∑ i ∈ range k, c i‖ +
        ‖∑ i ∈ range (k - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), c j‖ := norm_sub_le _ _
    _ ≤ f (k - 1) * E + (f 0 - f (k - 1)) * E := by rw [← h3]; exact add_le_add h1 h2
    _ = E * f 0 := by ring

/-- Removing prime powers: `‖Σ_{n<m} tw − Σ_{p<m} tw‖ ≤ ψ(m) − θ(m) ≤ 2 √m log m`. -/
theorem tw_sub_prime_le {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ‖∑ n ∈ range m, tw χ t n - ∑ n ∈ range m, (if n.Prime then tw χ t n else 0)‖ ≤
      2 * √(m : ℝ) * Real.log m := by
  set g : ℕ → ℝ := fun n => if ¬ n.Prime then (ArithmeticFunction.vonMangoldt n : ℝ) else 0
    with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    simp only [hg]
    by_cases hp : n.Prime <;> simp [hp, ArithmeticFunction.vonMangoldt_nonneg]
  have h1 : ‖∑ n ∈ range m, tw χ t n - ∑ n ∈ range m, (if n.Prime then tw χ t n else 0)‖ ≤
      ∑ n ∈ range m, g n := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    simp only [hg]
    split_ifs with hp
    · simp
    · simpa using tw_norm_le χ t n
  have h2 : ∑ n ∈ range m, g n = ∑ n ∈ (range m).erase 0, g n :=
    (Finset.sum_erase _ (by simp [hg, Nat.not_prime_zero])).symm
  have h3 : ∑ n ∈ (range m).erase 0, g n ≤ ∑ n ∈ Ioc 0 m, g n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [Finset.mem_erase, Finset.mem_range] at hn
      rw [Finset.mem_Ioc]
      omega
    · intro n _ _; exact hg0 n
  have h4 : ∑ n ∈ Ioc 0 m, g n = Chebyshev.psi m - Chebyshev.theta m := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
  have h5 := Chebyshev.psi_sub_theta_le (x := (m : ℝ)) (by exact_mod_cast hm)
  linarith

/-- The prime sum over a window `[a, b]` with `a ≥ max 3 N`, from a bound on the twisted
von Mangoldt partial sums at every `m ∈ [a, b + 1]`. -/
theorem prime_window_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) {N ε : ℝ} (hN : 0 < N)
    {a b : ℕ} (ha3 : 3 ≤ a) (hNa : N ≤ a) (hab : a ≤ b)
    (hΨ : ∀ m : ℕ, a ≤ m → m ≤ b + 1 →
      ‖∑ n ∈ range m, tw χ t n‖ + 2 * √(m : ℝ) * Real.log m ≤ N * ε / 2) :
    ‖∑ n ∈ Icc a b, (if n.Prime then χ n * (n : ℂ) ^ (-1 + I * t) else 0)‖ ≤ ε := by
  set cP : ℕ → ℂ := fun n => if n.Prime then tw χ t n else 0 with hcP
  set w : ℕ → ℝ := fun n => 1 / (n * Real.log n) with hw
  -- bound for prime partial sums
  have hP : ∀ m : ℕ, a ≤ m → m ≤ b + 1 → ‖∑ n ∈ range m, cP n‖ ≤ N * ε / 2 := by
    intro m h1 h2
    have hm : 1 ≤ m := by omega
    have := tw_sub_prime_le χ t hm
    have h3 := hΨ m h1 h2
    have h4 : ‖∑ n ∈ range m, cP n‖ ≤ ‖∑ n ∈ range m, tw χ t n‖ +
        ‖∑ n ∈ range m, tw χ t n - ∑ n ∈ range m, cP n‖ := by
      have := norm_sub_le (∑ n ∈ range m, tw χ t n)
        (∑ n ∈ range m, tw χ t n - ∑ n ∈ range m, cP n)
      simpa using this
    linarith
  have hε : 0 ≤ ε := by
    have h := hΨ a le_rfl (by omega)
    have h1 : 0 ≤ ‖∑ n ∈ range a, tw χ t n‖ + 2 * √(a : ℝ) * Real.log a := by
      have : 0 ≤ Real.log a := Real.log_natCast_nonneg a
      positivity
    by_contra hneg
    push Not at hneg
    have : N * ε / 2 < 0 := by
      have := mul_neg_of_pos_of_neg hN hneg
      linarith
    linarith
  -- rewrite the sum
  have hterm : ∀ n : ℕ, 3 ≤ n →
      (if n.Prime then χ n * (n : ℂ) ^ (-1 + I * t) else 0) = w n • cP n := by
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have : n ≠ 0 := by omega
      exact_mod_cast this
    have hlog : Real.log n ≠ 0 := by
      have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      exact (Real.log_pos this).ne'
    simp only [hcP, hw]
    split_ifs with hp
    · rw [Complex.real_smul, tw, ArithmeticFunction.vonMangoldt_apply_prime hp,
        Complex.cpow_add _ _ hn0, Complex.cpow_neg_one]
      push_cast
      have hlogC : Complex.log n ≠ 0 := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
        exact_mod_cast hlog
      field_simp
    · simp
  have hsum : ∑ n ∈ Icc a b, (if n.Prime then χ n * (n : ℂ) ^ (-1 + I * t) else 0) =
      ∑ i ∈ range (b + 1 - a), w (a + i) • cP (a + i) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact hterm (a + i) (by omega)
  rw [hsum]
  have hab := abel_bound (fun i => cP (a + i)) (fun i => w (a + i)) (b + 1 - a) (N * ε)
    (fun i => by
      simp only [hw]
      have h3 : (3 : ℝ) ≤ (a + i : ℕ) := by exact_mod_cast (show 3 ≤ a + i by omega)
      have hpos : 0 < ((a + i : ℕ) : ℝ) * Real.log (a + i : ℕ) :=
        mul_pos (by linarith) (Real.log_pos (by linarith))
      apply one_div_le_one_div_of_le hpos
      rw [show a + (i + 1) = (a + i) + 1 by ring, Nat.cast_add_one]
      apply mul_le_mul (by linarith) (Real.log_le_log (by linarith) (by linarith))
        (Real.log_nonneg (by linarith)) (by linarith))
    (fun i => by
      simp only [hw]
      exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)))
    (fun j hj => by
      have e : ∑ i ∈ range j, cP (a + i) =
          ∑ n ∈ range (a + j), cP n - ∑ n ∈ range a, cP n := by
        rw [Finset.sum_range_add]; ring
      rw [e]
      have h1 := hP (a + j) (by omega) (by omega)
      have h2 := hP a le_rfl (by omega)
      calc _ ≤ ‖∑ n ∈ range (a + j), cP n‖ + ‖∑ n ∈ range a, cP n‖ := norm_sub_le _ _
        _ ≤ N * ε / 2 + N * ε / 2 := add_le_add h1 h2
        _ = N * ε := by ring)
  refine hab.trans ?_
  simp only [add_zero, hw]
  have ha3' : (3 : ℝ) ≤ a := by exact_mod_cast ha3
  have hlog1 : 1 ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hden : N ≤ (a : ℝ) * Real.log a := by
    have := mul_le_mul_of_nonneg_left hlog1 (by linarith : (0 : ℝ) ≤ a)
    linarith
  rw [mul_one_div, div_le_iff₀ (mul_pos (by linarith) (by linarith))]
  calc N * ε ≤ ((a : ℝ) * Real.log a) * ε := mul_le_mul_of_nonneg_right hden hε
    _ = ε * (a * Real.log a) := by ring

end L31P
end ArtinPrimitiveRoots
end

section
/-!
# L31P_Main: `long_prime_polynomial` from `dirichlet_L_zero_free_strip`

`B₀ = A + 4`, `K = 1`. The asymptotic side conditions are collected in `eventually_conds`;
`window_reduction` turns the interval `J` into a window `[a, b]` of integers; `main_step` checks
the hypotheses of `psi_small` and `prime_window_bound`.
-/

namespace ArtinPrimitiveRoots
namespace L31P

open Real Filter Topology

theorem eventually_conds (τ η A c K₁ x₀ : ℝ) (hτ : 0 < τ) (hη : η < 1) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, x₀ ≤ x ∧ 0 < x ∧ 38400 ≤ log x ∧ 48 * K₁ * (8 + A) ≤ log x ∧
      c * log (log x) ^ 2 ≤ log x ∧ 4 * (A + 3) / (c * τ) ≤ log (log x) ∧
      2 ≤ (1 - η) * log x ∧ 5 ≤ τ * log x ∧ log x ^ (A + 3) ≤ x ∧
      1536 * (log x ^ A) ^ 2 * log x ^ 2 ≤ x ^ τ := by
  have hL := tendsto_log_atTop
  have c5 : ∀ᶠ L : ℝ in atTop, c * log L ^ 2 ≤ L := by
    have h := tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    have h' : ∀ᶠ L : ℝ in atTop, log L ^ 2 / (1 * L + 0) < 1 / c :=
      (tendsto_order.1 h).2 _ (by positivity)
    filter_upwards [h', eventually_gt_atTop 0] with L hL1 hL0
    rw [one_mul, add_zero, div_lt_iff₀ hL0] at hL1
    have := mul_lt_mul_of_pos_left hL1 hc
    rw [show c * (1 / c * L) = L by field_simp] at this
    linarith
  have c6 : ∀ᶠ L : ℝ in atTop, 4 * (A + 3) / (c * τ) ≤ log L :=
    hL.eventually (eventually_ge_atTop _)
  have c9 : ∀ᶠ L : ℝ in atTop, L ^ (A + 3) ≤ exp L := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A + 3) 1 one_pos
    filter_upwards [(tendsto_order.1 h).2 1 one_pos] with L hL1
    rw [neg_mul, one_mul, Real.exp_neg, ← div_eq_mul_inv, div_lt_one (exp_pos L)] at hL1
    exact hL1.le
  have c10 : ∀ᶠ L : ℝ in atTop, 1536 * (L ^ A) ^ 2 * L ^ 2 ≤ exp (τ * L) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * A + 2) τ hτ
    filter_upwards [(tendsto_order.1 h).2 (1 / 1536) (by norm_num), eventually_gt_atTop 0]
      with L hL1 hL0
    have e : L ^ (2 * A + 2) = (L ^ A) ^ 2 * L ^ 2 := by
      rw [Real.rpow_add hL0, show 2 * A = A * 2 by ring, Real.rpow_mul hL0.le, Real.rpow_two,
        Real.rpow_two]
    rw [e, neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (exp_pos _)] at hL1
    linarith
  filter_upwards [eventually_ge_atTop x₀, eventually_gt_atTop 0,
    hL.eventually (eventually_ge_atTop 38400), hL.eventually (eventually_ge_atTop (48 * K₁ * (8 + A))),
    hL.eventually c5, hL.eventually c6, hL.eventually (eventually_ge_atTop (2 / (1 - η))),
    hL.eventually (eventually_ge_atTop (5 / τ)), hL.eventually c9, hL.eventually c10]
    with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by linarith)] at h7; linarith
  · rw [div_le_iff₀ hτ] at h8; linarith
  · rw [Real.exp_log h2] at h9; exact h9
  · rw [Real.rpow_def_of_pos h2, mul_comm (log x) τ]; exact h10

open Classical in
theorem window_reduction (J : Set ℝ) (hJ : J.OrdConnected) (Nmax : ℕ) (f : ℕ → ℂ) :
    (∑ p ∈ (Finset.range (Nmax + 1)).filter Nat.Prime, (if (p : ℝ) ∈ J then f p else 0)) = 0 ∨
    ∃ a b : ℕ, a ≤ b ∧ (a : ℝ) ∈ J ∧ (b : ℝ) ∈ J ∧ b ≤ Nmax ∧
      (∑ p ∈ (Finset.range (Nmax + 1)).filter Nat.Prime, (if (p : ℝ) ∈ J then f p else 0)) =
        ∑ n ∈ Finset.Icc a b, (if n.Prime then f n else 0) := by
  set S := (Finset.range (Nmax + 1)).filter (fun n : ℕ => (n : ℝ) ∈ J) with hS
  have hsum : (∑ p ∈ (Finset.range (Nmax + 1)).filter Nat.Prime,
      (if (p : ℝ) ∈ J then f p else 0)) = ∑ n ∈ S, (if n.Prime then f n else 0) := by
    rw [hS, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h1 : n.Prime <;> by_cases h2 : (n : ℝ) ∈ J <;> simp [h1, h2]
  rcases S.eq_empty_or_nonempty with hE | hne
  · left; rw [hsum, hE, Finset.sum_empty]
  · right
    have ha := Finset.mem_filter.mp (S.min'_mem hne)
    have hb := Finset.mem_filter.mp (S.max'_mem hne)
    rw [Finset.mem_range] at ha hb
    refine ⟨S.min' hne, S.max' hne, S.min'_le_max' hne, ha.2, hb.2, by omega, ?_⟩
    rw [hsum]
    congr 1
    ext n
    constructor
    · intro hn
      rw [Finset.mem_Icc]
      exact ⟨S.min'_le n hn, S.le_max' n hn⟩
    · intro hn
      rw [Finset.mem_Icc] at hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      exact hJ.out ha.2 hb.2 ⟨by exact_mod_cast hn.1, by exact_mod_cast hn.2⟩

open Complex in
/-- The rectangle `[1 - δ, 1 + 1/L] × [-H, H]`, shifted by `-it`, lies at heights
`2 ≤ |Im| ≤ x³/2`. -/
theorem rect_heights {x H t : ℝ} (hx : 3 ≤ x) (hHx : H ≤ x) (ht1 : H + 2 ≤ |t|)
    (ht2 : |t| ≤ x ^ 2) {z : ℂ} (hz : |z.im| ≤ H) :
    (z - I * t).re = z.re ∧ 2 ≤ |(z - I * t).im| ∧ |(z - I * t).im| ≤ x ^ 3 / 2 := by
  have hre : (z - I * t).re = z.re := by simp
  have him : (z - I * t).im = z.im - t := by simp
  refine ⟨hre, ?_, ?_⟩
  · rw [him, abs_sub_comm]
    have := abs_sub_abs_le_abs_sub t z.im
    linarith
  · rw [him]
    have h1 := abs_sub z.im t
    have h2 : x + x ^ 2 ≤ x ^ 3 / 2 := by
      have e1 : 3 * x ^ 2 ≤ x * x ^ 2 := mul_le_mul_of_nonneg_right hx (by positivity)
      have e2 : 3 * x ≤ x * x := mul_le_mul_of_nonneg_right hx (by linarith)
      have e3 : x ^ 3 = x * x ^ 2 := by ring
      have e4 : x ^ 2 = x * x := by ring
      linarith
    linarith

open Classical in
theorem main_step {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {τ η A c K x N t : ℝ}
    (J : Set ℝ) (hc : 0 < c) (hA : 0 < A)
    (hxpos : 0 < x) (hL1 : 38400 ≤ log x) (hL2 : 48 * max K 0 * (8 + A) ≤ log x)
    (hL3 : c * log (log x) ^ 2 ≤ log x) (hL4 : 4 * (A + 3) / (c * τ) ≤ log (log x))
    (hL5 : 2 ≤ (1 - η) * log x) (hL6 : 5 ≤ τ * log x) (hL7 : log x ^ (A + 3) ≤ x)
    (hL8 : 1536 * (log x ^ A) ^ 2 * log x ^ 2 ≤ x ^ τ) (hτ : 0 < τ)
    (hN1 : x ^ τ / 2 ≤ N) (hN2 : N ≤ x ^ η) (ht1 : log x ^ (A + 4) ≤ |t|) (ht2 : |t| ≤ x ^ 2)
    (hJ : J.OrdConnected) (hJN : J ⊆ Set.Icc N (2 * N))
    (hnz0 : ∀ s : ℂ, 1 - c * log (log x) ^ 2 / log x ≤ s.re → 1 ≤ |s.im| → |s.im| ≤ x ^ 3 →
      DirichletCharacter.LFunction χ s ≠ 0)
    (hbd0 : ∀ s : ℂ, 1 - c * log (log x) ^ 2 / (2 * log x) ≤ s.re → s.re ≤ 1 + 1 / log x →
      2 ≤ |s.im| → |s.im| ≤ x ^ 3 / 2 →
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
        K * log x) :
    ‖∑ p ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter Nat.Prime,
        (if (p : ℝ) ∈ J then χ (p : ZMod q) * (p : ℂ) ^ (-1 + Complex.I * t) else 0)‖ ≤
      log x ^ (-A) := by
  set L := log x with hLdef
  set T := log L with hTdef
  set δ : ℝ := c * T ^ 2 / (2 * L) with hδdef
  set P : ℝ := L ^ A with hPdef
  set H : ℝ := L ^ (A + 3) with hHdef
  have hL0 : 0 < L := by linarith
  have hL1' : 1 ≤ L := by linarith
  have hT0 : 0 ≤ T := Real.log_nonneg hL1'
  have hTL : T ≤ L := Real.log_le_self hL0.le
  have hP0 : 0 < P := Real.rpow_pos_of_pos hL0 A
  have hnegA : L ^ (-A) = 1 / P := by rw [Real.rpow_neg hL0.le, one_div]
  have hH1 : 1 ≤ H := Real.one_le_rpow hL1' (by linarith)
  have hHt : H + 2 ≤ |t| := by
    have e : L ^ (A + 4) = H * L := by
      rw [hHdef, show A + 4 = (A + 3) + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
    rw [e] at ht1
    have := mul_le_mul_of_nonneg_left (show (3 : ℝ) ≤ L by linarith) (by linarith : (0 : ℝ) ≤ H)
    linarith
  have hxexp : x = exp L := (Real.exp_log hxpos).symm
  have hx3 : 3 ≤ x := by rw [hxexp]; have := Real.add_one_le_exp L; linarith
  have hxτ : x ^ τ = exp (τ * L) := by rw [Real.rpow_def_of_pos hxpos, mul_comm]
  have hxτ6 : 6 ≤ x ^ τ := by rw [hxτ]; have := Real.add_one_le_exp (τ * L); linarith
  have hN0 : 0 < N := by linarith
  have hxη : 3 * x ^ η ≤ x := by
    have h1 : x ^ η * x ^ (1 - η) = x := by
      rw [← Real.rpow_add hxpos]; simp
    have h2 : 3 ≤ x ^ (1 - η) := by
      rw [Real.rpow_def_of_pos hxpos]
      have := Real.add_one_le_exp (L * (1 - η))
      have e : L * (1 - η) = (1 - η) * L := mul_comm _ _
      linarith
    have h3 : 0 ≤ x ^ η := Real.rpow_nonneg hxpos.le _
    have := mul_le_mul_of_nonneg_left h2 h3
    linarith
  have h3N : 3 * N ≤ x := by linarith
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  have hδ : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_iff₀ (by positivity)]; linarith
  have hδ2 : 1 - c * T ^ 2 / L ≤ 1 - δ := by
    have : δ ≤ c * T ^ 2 / L := by
      rw [hδdef]
      exact div_le_div_of_nonneg_left (by positivity) hL0 (by linarith)
    linarith
  -- the window
  rcases window_reduction J hJ ⌊2 * N⌋₊
      (fun p => χ (p : ZMod q) * (p : ℂ) ^ (-1 + Complex.I * t)) with h0 | ⟨a, b, hab, haJ, hbJ,
        hbN, heq⟩
  · rw [h0, norm_zero]; exact Real.rpow_nonneg hL0.le _
  rw [heq]
  have haN : N ≤ a := (hJN haJ).1
  have hbN2 : (b : ℝ) ≤ 2 * N := (hJN hbJ).2
  have ha3 : 3 ≤ a := by exact_mod_cast (show (3 : ℝ) ≤ a by linarith)
  rw [hnegA]
  apply prime_window_bound χ t hN0 ha3 haN hab
  intro m ham hmb
  have hm_lo : N ≤ (m : ℝ) := le_trans haN (by exact_mod_cast ham)
  have hm_hi : (m : ℝ) ≤ 2 * N + 1 := by
    have : (m : ℝ) ≤ b + 1 := by exact_mod_cast hmb
    linarith
  have hM2 : 2 ≤ m := by exact_mod_cast (show (2 : ℝ) ≤ m by linarith)
  set y : ℝ := (m : ℝ) - 1 / 2 with hydef
  have hy0 : 0 < y := by rw [hydef]; linarith
  have hy_hi : y ≤ x := by rw [hydef]; linarith
  have hy_lo : x ^ τ / 4 ≤ y := by rw [hydef]; linarith
  have hyL : Real.log y ≤ L := Real.log_le_log hy0 hy_hi
  have hlogy : τ * L / 2 ≤ Real.log y := by
    have h1 : Real.log (x ^ τ / 4) ≤ Real.log y := Real.log_le_log (by positivity) hy_lo
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hxpos] at h1
    have h4 : Real.log 4 < 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [this]; have := Real.log_two_lt_d9; linarith
    linarith
  have hy1 : y ^ (-δ) ≤ L ^ (-(A + 3)) := by
    rw [Real.rpow_def_of_pos hy0, Real.rpow_def_of_pos hL0]
    apply Real.exp_le_exp.mpr
    have h1 : 4 * (A + 3) ≤ c * τ * T := by
      rw [div_le_iff₀ (by positivity)] at hL4; linarith
    have h2 : 4 * (A + 3) * T ≤ c * τ * T * T := mul_le_mul_of_nonneg_right h1 hT0
    have h3 : δ * (τ * L / 2) ≤ δ * Real.log y := mul_le_mul_of_nonneg_left hlogy hδ0
    have h4 : δ * (τ * L / 2) = c * τ * T * T / 4 := by rw [hδdef]; field_simp; ring
    have h5 : (A + 3) * T ≤ δ * Real.log y := by linarith
    have h6 : Real.log y * -δ = -(δ * Real.log y) := by ring
    have h7 : T * -(A + 3) = -((A + 3) * T) := by ring
    rw [h6, h7]
    linarith
  have hK1 : 48 * max K 0 * (5 + (A + 3) * T) ≤ L ^ 2 := by
    have hK0 : 0 ≤ max K 0 := le_max_right _ _
    have h1 : 5 + (A + 3) * T ≤ (8 + A) * L := by
      have := mul_le_mul_of_nonneg_left hTL (by linarith : (0 : ℝ) ≤ A + 3)
      linarith
    have h2 : 48 * max K 0 * (5 + (A + 3) * T) ≤ 48 * max K 0 * ((8 + A) * L) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 48 * max K 0 * (8 + A) * L ≤ L * L := mul_le_mul_of_nonneg_right hL2 hL0.le
    have e : L ^ 2 = L * L := sq L
    linarith
  have hrect : ∀ z ∈ Set.Icc (1 - δ) (1 + 1 / L) ×ℂ Set.Icc (-H) H,
      (z - Complex.I * t).re = z.re ∧ 2 ≤ |(z - Complex.I * t).im| ∧
        |(z - Complex.I * t).im| ≤ x ^ 3 / 2 ∧ 1 - δ ≤ z.re ∧ z.re ≤ 1 + 1 / L := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := hz
    obtain ⟨e1, e2, e3⟩ := rect_heights hx3 hL7 hHt ht2 (abs_le.mpr ⟨hi1, hi2⟩)
    exact ⟨e1, e2, e3, hr1, hr2⟩
  have hpsi := psi_small χ t hM2 (L := L) (c := c) (K := max K 0) (A := A) hL1 hc
    (le_max_right _ _) hA hδ hyL hy1 hK1
    (fun z hz => by
      obtain ⟨e1, e2, e3, e4, _⟩ := hrect z hz
      have hx3' : 0 ≤ x ^ 3 := by positivity
      refine ⟨?_, hnz0 _ (by rw [e1]; linarith) (by linarith) (by linarith)⟩
      intro h1
      have : (z - Complex.I * t).im = 0 := by rw [h1]; simp
      rw [this, abs_zero] at e2
      linarith)
    (fun z hz => by
      obtain ⟨e1, e2, e3, e4, e5⟩ := hrect z hz
      refine (hbd0 _ (by rw [e1]; exact e4) (by rw [e1]; exact e5) e2 e3).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hL0.le)
  rw [hnegA] at hpsi
  -- the prime-power term
  have hlogm0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hlogm : Real.log m ≤ L := Real.log_le_log (by positivity) (by linarith)
  have hsq : (2 * √(m : ℝ) * Real.log m) ^ 2 = 4 * m * Real.log m ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  have hNP : 768 * P ^ 2 * L ^ 2 ≤ N := by linarith
  have hpp : 2 * √(m : ℝ) * Real.log m ≤ N * (1 / P) / 4 := by
    have h1 : 4 * (m : ℝ) * Real.log m ^ 2 ≤ 4 * (3 * N) * L ^ 2 :=
      mul_le_mul (by linarith) (pow_le_pow_left₀ hlogm0 hlogm 2) (by positivity) (by positivity)
    have h2 : 4 * (3 * N) * L ^ 2 ≤ (N * (1 / P) / 4) ^ 2 := by
      have e : (N * (1 / P) / 4) ^ 2 = N * N / (16 * P ^ 2) := by field_simp; ring
      rw [e, le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hNP hN0.le
      have h0 : 0 ≤ N * P ^ 2 * L ^ 2 := by positivity
      linarith
    have h3 : 0 ≤ N * (1 / P) / 4 := by positivity
    exact (pow_le_pow_iff_left₀ (by positivity) h3 two_ne_zero).mp (by rw [hsq]; linarith)
  have hyN : y * (1 / P) / 12 ≤ N * (1 / P) / 4 := by
    have : y ≤ 3 * N := by rw [hydef]; linarith
    have h1 : 0 ≤ 1 / P := by positivity
    have := mul_le_mul_of_nonneg_right this h1
    linarith
  rw [← hydef] at hpsi
  linarith

end L31P

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
open Classical in
theorem solution (τ η C A : ℝ) (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1)
    (hC : 0 < C) (hA : 0 < A) :
    ∃ B₀ K x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ N : ℝ, x ^ τ / 2 ≤ N → N ≤ x ^ η →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ log x ^ C → ∀ χ : DirichletCharacter ℂ q,
      ∀ t : ℝ, log x ^ B₀ ≤ |t| → |t| ≤ x ^ 2 →
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc N (2 * N) →
        ‖∑ p ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter Nat.Prime,
            (if (p : ℝ) ∈ J then χ (p : ZMod q) * (p : ℂ) ^ (-1 + Complex.I * t) else 0)‖ ≤
          K * log x ^ (-A) := by
  obtain ⟨c, K, x₀, hc, hZ⟩ := dirichlet_L_zero_free_strip C hC
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    (L31P.eventually_conds τ η A c (max K 0) x₀ hτ hη hc)
  refine ⟨A + 4, 1, x₁, ?_⟩
  intro x hx N hN1 hN2 q hq hqC χ t ht1 ht2 J hJ hJN
  obtain ⟨hx0, hxpos, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hL8⟩ := hx₁ x hx
  have : NeZero q := ⟨hq.ne'⟩
  obtain ⟨hnz0, hbd0⟩ := hZ x hx0 q hqC χ
  rw [one_mul]
  exact L31P.main_step χ J hc hA hxpos hL1 hL2 hL3 hL4 hL5 hL6 hL7 hL8 hτ hN1 hN2 ht1 ht2
    hJ hJN hnz0 hbd0
end
