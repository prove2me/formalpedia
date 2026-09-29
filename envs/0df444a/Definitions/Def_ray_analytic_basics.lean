-- Prove2me | Definitions.Def_ray_analytic_basics
-- name    : ray_analytic_basics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T20:51:40.346895+00:00
-- url     : https://prove2.me/theorems/ddbfb0ea-7f29-476d-8ddb-5e6378a824e6
-- title:
--   ray (1/12): basic definitions and analytic-function lemmas
-- statement:
--   Foundational definitions and lemmas used throughout the ray development. It contains the order of vanishing $\operatorname{orderAt} f\,c$ and leading coefficient of an analytic function, and absolutely convergent infinite products (`HasProdOn`, `ProdExists`, `tprodOn`). It has manifold notions: analyticity on a neighbourhood of a set (`ContMDiffOnNhd`), critical and precritical points, and nontrivial (locally nonconstant) analytic maps. It has the structures `SuperAt`, `SuperNear` and `Super`, which describe a holomorphic family $f_c$ with a monic superattracting fixed point of order $d \ge 2$, and the local Böttcher product `bottcherNear`. It also collects elementary real and complex bounds, facts about multilinear maps and topology, and basic lemmas on analytic functions of one variable.
--
--   This file is part 1 of 12 of a verbatim flattening of Geoffrey Irving's Lean 4 formalization *ray* (https://github.com/girving/ray, Apache License 2.0). Together the 12 files prove that the Mandelbrot set is connected. Each original ray module is wrapped in its own `section`, and module-system keywords are removed. A few mechanical edits avoid clashes with the full Mathlib import and avoid syntax extensions: a duplicated private definition is dropped, `ContinuousOn.partialSups` is renamed to `ContinuousOn.rayPartialSups`, `Finset.antidiagonal` is written as `Finset.HasAntidiagonal.antidiagonal`, the `bound_destruct` attribute macro is inlined, and the notation `𝕊` is replaced by `(OnePoint ℂ)`. The files are split only because of the compile-time limit. Declaration names are ray's own.
-- source:
--   Geoffrey Irving, ray: The Mandelbrot set is connected (Lean 4 formalization), https://github.com/girving/ray (Apache License 2.0), commit of 2026-08-16; module list in the file header. Mathematical background: A. Douady and J. H. Hubbard, Itération des polynômes quadratiques complexes, C. R. Acad. Sci. Paris 294 (1982); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Section 9 and Appendix; Carleson–Gamelin, Complex Dynamics, Ch. VIII.

import Mathlib

/-!
# ray (1/12): basic definitions and analytic-function lemmas

Part 1 of 12 of a flattened copy of Geoffrey Irving's Lean 4 formalization *ray*
(https://github.com/girving/ray, Apache License 2.0, Copyright Geoffrey Irving), which proves that
the Mandelbrot set is connected. Each original module is wrapped in its own `section`;
module-system keywords are removed, and a few names are adjusted to avoid clashes with Mathlib.

Original modules in this file:
* `Ray.Analytic.Defs`
* `Ray.Manifold.Defs`
* `Ray.Misc.Defs`
* `Ray.Dynamics.Defs`
* `Ray.Misc.Bound`
* `Ray.Misc.Finset`
* `Ray.Misc.Bounds`
* `Ray.Misc.Multilinear`
* `Ray.Misc.Topology`
* `Ray.Analytic.Analytic`
-/

-- ===== Ray.Analytic.Defs =====
section Ray_Ray_Analytic_Defs
/-!
## Analytic definitions, allowing minimal public imports
-/

open Classical
open Set
noncomputable section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Order definitions
-/

/-- The order of a zero at a point.
    We define this in terms of the function alone so that expressions involving order can
    depend only on `f`. -/
def orderAt (f : 𝕜 → E) (c : 𝕜) : ℕ :=
  if p : AnalyticAt 𝕜 f c then (choose p).order else 0

/-- The leading nonzero coefficient of `f`'s power series -/
def leadingCoeff (f : 𝕜 → E) (c : 𝕜) : E :=
  ((Function.swap dslope c)^[orderAt f c]) f c

/-- The power series of `(z - c) • f z` -/
def FormalMultilinearSeries.unshift' (p : FormalMultilinearSeries 𝕜 𝕜 E) (c : E) :
    FormalMultilinearSeries 𝕜 𝕜 E :=
  ((ContinuousLinearMap.smulRightL 𝕜 𝕜 E (ContinuousLinearMap.id 𝕜 𝕜)).compFormalMultilinearSeries
        p).unshift c

/-- The power series of `(z - c)^n • f z` -/
def FormalMultilinearSeries.unshiftIter (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) :=
  (fun p ↦ FormalMultilinearSeries.unshift' p (0 : E))^[n] p

/-!
## Product definitions
-/

/-- For all z, `Πₙ f n z` converges absolutely to `g z` (analogous to `HasSumOn`) -/
def HasProdOn (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (s : Set ℂ) :=
  ∀ z, z ∈ s → HasProd (fun n ↦ f n z) (g z)

/-- The product of `f` converges absolutely to something (analogous to `Summable`) -/
def ProdExists (f : ℕ → ℂ) : Prop :=
  ∃ g, HasProd f g

/-- The limit of an infinite product if it exists, or `0` -/
noncomputable def tprodOn (f : ℕ → ℂ → ℂ) := fun z ↦ tprod fun n ↦ f n z

/-- The limit of a parameterized infinite product if it exists, or `0` -/
def ProdExistsOn (f : ℕ → ℂ → ℂ) (s : Set ℂ) :=
  ∀ z, z ∈ s → ProdExists fun n ↦ f n z

/-- If a product has a particular limit, it has some limit -/
theorem HasProd.prodExists {f : ℕ → ℂ} {g : ℂ} (h : HasProd f g) : ProdExists f :=
  ⟨g, h⟩

/-- `tprodOn` is the product on `s` if it exists on `s` -/
theorem HasProdOn.tprodOn_eq {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {s : Set ℂ} :
    HasProdOn f g s → ∀ z, z ∈ s → tprodOn f z = g z := fun h z zs ↦ (h z zs).tprod_eq

end
end Ray_Ray_Analytic_Defs

-- ===== Ray.Manifold.Defs =====
section Ray_Ray_Manifold_Defs
/-!
## Manifold definitions, allowing minimal public imports
-/

open scoped ContDiff Manifold Topology
noncomputable section

/-!
## General manifolds
-/

variable {𝕜 E A F B M N : Type} [NontriviallyNormedField 𝕜]

/-- Analyticity in a neighborhood of a set (the manifold analogue of `AnalyticOnNhd`) -/
def ContMDiffOnNhd {𝕜 E A F B M N : Type} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace A M] [ChartedSpace B N] (I : ModelWithCorners 𝕜 E A) (J : ModelWithCorners 𝕜 F B)
    (f : M → N) (s : Set M) : Prop := ∀ x ∈ s, ContMDiffAt I J ω f x

/-- A typeclass for trivial manifolds where `extChartAt` is the identity.
    In this case, `extChartAt I : E → E`, but the intermediate space `H` might be different.
    This is necessary to handle product spaces, where the intermediate space may be `ModelProd`. -/
class ExtChartEqRefl [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace A]
    (I : ModelWithCorners 𝕜 E A) [ChartedSpace A E] : Prop where
  eq_refl : ∀ x, extChartAt I x = PartialEquiv.refl E

/-- `extChartAt I x = refl` given [ExtChartEqRefl] -/
theorem extChartAt_eq_refl [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace A]
    [ChartedSpace A E] {I : ModelWithCorners 𝕜 E A} [e : ExtChartEqRefl I] (x : E) :
    extChartAt I x = PartialEquiv.refl E :=
  e.eq_refl x

/-- `extChartAt = refl` for `I = modelWithCornersSelf 𝕜 E` -/
instance extChartEqReflSelf [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    ExtChartEqRefl (modelWithCornersSelf 𝕜 E) := ⟨by
  simp only [extChartAt, OpenPartialHomeomorph.extend, chartAt_self_eq,
    OpenPartialHomeomorph.refl_partialEquiv, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl, forall_const]⟩

/-- `extChartAt = refl` extends to products -/
instance extChartEqReflProd [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace A]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace B] [ChartedSpace A E]
    [ChartedSpace B F] {I : ModelWithCorners 𝕜 E A} [ExtChartEqRefl I] {J : ModelWithCorners 𝕜 F B}
    [ExtChartEqRefl J] : ExtChartEqRefl (I.prod J) :=
  ⟨fun x ↦ by simp_rw [extChartAt_prod, extChartAt_eq_refl, PartialEquiv.refl_prod_refl]⟩

/-!
## One dimension
-/

variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]

/-- Abbreviation for `𝓘(ℂ,ℂ) = modelWithCornersSelf ℂ ℂ` -/
abbrev OneDimension.I := modelWithCornersSelf ℂ ℂ

/-- Abbreviation for `𝓘(ℂ,ℂ).prod 𝓘(ℂ,ℂ)` -/
abbrev OneDimension.II := I.prod I

open OneDimension

/-- A critical point is where the derivative of `f` vanishes -/
def Critical (f : S → T) (z : S) :=
  mfderiv I I f z = 0

/-- A precritical point is an iterated preimage of a critical point -/
def Precritical (f : S → S) (z : S) :=
  ∃ n, Critical f (f^[n] z)

/-!
## Nontrivial analyticity
-/

/-- A nontrivial analytic function is one which is not locally constant -/
structure NontrivialAnalyticOn (f : ℂ → ℂ) (s : Set ℂ) : Prop where
  analyticOn : AnalyticOnNhd ℂ f s
  nonconst : ∀ x, x ∈ s → ∃ᶠ y in 𝓝 x, f y ≠ f x

/-- A analytic function that is nonconstant near a point -/
structure NontrivialMAnalyticAt (f : S → T) (z : S) : Prop where
  mAnalyticAt : ContMDiffAt I I ω f z
  nonconst : ∃ᶠ w in 𝓝 z, f w ≠ f z

/-- `f` is nontrivial analytic everyone in `s` -/
def NontrivialMAnalyticOn (f : S → T) (s : Set S) : Prop :=
  ∀ z, z ∈ s → NontrivialMAnalyticAt f z

end
end Ray_Ray_Manifold_Defs

-- ===== Ray.Misc.Defs =====
section Ray_Ray_Misc_Defs
/-!
## Shared defs, to minimise public imports
-/

open scoped Real
noncomputable section

/-- A `Finset ℕ` with only large elements -/
def Late (N : Finset ℕ) (m : ℕ) :=
  ∀ n, n ∈ N → n ≥ m

/-- Lipschitz coefficient for `pow1p_small_general` -/
def psg (r s : ℝ) : ℝ :=
  rexp (r * s / (1 - r)) / (1 - r)

/-- `max b (log x)` -/
def maxLog (b x : ℝ) : ℝ :=
  (max b.exp x).log

end
end Ray_Ray_Misc_Defs

-- ===== Ray.Dynamics.Defs =====
section Ray_Ray_Dynamics_Defs
/-!
## Dynamics definitions, allowing minimal public imports
-/

open Classical
open Filter (Tendsto atTop)
open Function (uncurry)
open OneDimension
open Set
open scoped ContDiff Topology
noncomputable section

/-
## Flat space definitions
-/

/-- `f` has a monic, superattracting fixed point of order `d ≥ 2` at the origin.
    This is a simplified version of `SuperNear` with no smallest requirements. -/
structure SuperAt (f : ℂ → ℂ) (d : ℕ) : Prop where
  d2 : 2 ≤ d
  fa0 : AnalyticAt ℂ f 0
  fd : orderAt f 0 = d
  fc : leadingCoeff f 0 = 1

/-- `f` has a monic, superattracting fixed point of order `d ≥ 2` at the origin.
    We impose some smallness requirements to make bounds easier later. -/
structure SuperNear (f : ℂ → ℂ) (d : ℕ) (t : Set ℂ) (a b : ℝ) :
    Prop extends SuperAt f d where
  o : IsOpen t
  t0 : (0 : ℂ) ∈ t
  t2 : ∀ {z}, z ∈ t → ‖z‖ ≤ a
  fa : AnalyticOnNhd ℂ f t
  ft : MapsTo f t t
  gs' : ∀ {z : ℂ}, z ≠ 0 → z ∈ t → ‖f z / z ^ d - 1‖ ≤ b
  a1 : a < 1
  b0 : 0 ≤ b
  b1 : b < 1
  c1' : a * (1 + b) < 1

/-- `SuperAt` everywhere on a parameter set `u`, at `z = 0` -/
structure SuperAtC (f : ℂ → ℂ → ℂ) (d : ℕ) (u : Set ℂ) : Prop where
  o : IsOpen u
  s : ∀ {c}, c ∈ u → SuperAt (f c) d
  fa : ∀ {c}, c ∈ u → AnalyticAt ℂ (uncurry f) (c, 0)

/-- `SuperNear` everywhere on a parameter set -/
structure SuperNearC (f : ℂ → ℂ → ℂ) (d : ℕ) (u : Set ℂ) (t : Set (ℂ × ℂ)) (a b : ℝ) :
    Prop where
  o : IsOpen t
  tc : ∀ {p : ℂ × ℂ}, p ∈ t → p.1 ∈ u
  s : ∀ {c}, c ∈ u → SuperNear (f c) d {z | (c, z) ∈ t} a b
  fa : AnalyticOnNhd ℂ (uncurry f) t

/-- `g` such that `f z = z^d * g z` -/
def g (f : ℂ → ℂ) (d : ℕ) : ℂ → ℂ := fun z ↦ if z = 0 then 1 else f z / z ^ d

/-- Terms in our infinite product -/
def term (f : ℂ → ℂ) (d n : ℕ) (z : ℂ) :=
  g f d (f^[n] z) ^ (1 / (d ^ (n + 1) : ℕ) : ℂ)

/-- With `term` in hand, we can define Böttcher coordinates -/
def bottcherNear (f : ℂ → ℂ) (d : ℕ) (z : ℂ) :=
  z * tprod fun n ↦ term f d n z

-- Scale factors for bounds
section Scale
variable {f : ℂ → ℂ} {d : ℕ} {t : Set ℂ} {a b : ℝ}
def SuperNear.c (_ : SuperNear f d t a b) := a * (1 + b)
def SuperNear.kt (_ : SuperNear f d t a b) : ℝ := psg b 2⁻¹ * b / 2
def SuperNear.k (s : SuperNear f d t a b) : ℝ := Real.exp (2 * s.kt)
end Scale

/-!
## Manifold definitions
-/

variable {S : Type} [TopologicalSpace S]
variable {f : ℂ → S → S} {a : S} {d : ℕ}

/-- `f` as `ℂ → ℂ → ℂ` in charts, with the attractor at `0` -/
def fl {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] (f : ℂ → S → S) (a : S) :
    ℂ → ℂ → ℂ :=
  fun c ↦
  (fun z ↦ z - extChartAt I a a) ∘
    (extChartAt I a ∘ f c ∘ (extChartAt I a).symm) ∘ fun z ↦ z + extChartAt I a a

variable [CompactSpace S] [ChartedSpace ℂ S] [IsManifold I ω S]

/-- `z` tends to `a` under `f`-iteration -/
def Attracts (f : S → S) (z a : S) :=
  Tendsto (fun n ↦ f^[n] z) atTop (𝓝 a)

/-- `f c` has a monic superattracting fixpoint at `a`, for all `c` -/
structure Super {S : Type} [TopologicalSpace S] [CompactSpace S] [ChartedSpace ℂ S]
    [IsManifold I ω S] (f : ℂ → S → S) (d : ℕ) (a : S) : Prop where
  d2 : 2 ≤ d
  fa : ContMDiff II I ω (uncurry f)
  f0 : ∀ c, f c a = a
  fd : ∀ c, orderAt (fl f a c) 0 = d
  fc : ∀ c, leadingCoeff (fl f a c) 0 = 1

/-- Potential is everywhere continuous only using an additional assumption.  The most general
    assumption is that the set of preimages is closed, but for the Mandelbrot set we have the
    simpler case that `a` is the only preimage of `a`. -/
class OnePreimage (s : Super f d a) : Prop where
  eq_a : ∀ c z, f c z = a → z = a

/-- The basin of points that attract to `a` -/
def Super.basin (_ : Super f d a) : Set (ℂ × S) :=
  {p : ℂ × S | Tendsto (fun n ↦ (f p.1)^[n] p.2) atTop (𝓝 a)}

/-- `s.fl` is `fl` with a few arguments filled in -/
def Super.fl (_ : Super f d a) := _root_.fl f a

/-- `bottcherNear` on the manifold -/
def Super.bottcherNear (s : Super f d a) (c : ℂ) (z : S) : ℂ :=
  _root_.bottcherNear (s.fl c) d (extChartAt I a z - extChartAt I a a)

/-- `s.bottcherNear`, uncurried -/
def Super.bottcherNearp (s : Super f d a) : ℂ × S → ℂ :=
  uncurry s.bottcherNear

/-- `s.bottcherNear` after some iterations of `f` -/
def Super.bottcherNearIter (s : Super f d a) (n : ℕ) : ℂ → S → ℂ := fun c z ↦
  s.bottcherNear c ((f c)^[n] z)

/-!
## Potentials and postcritical potentials
-/

/-- `s.potential c z` measures how quickly `z` attracts to `a` under `f c`. -/
def Super.potential (s : Super f d a) (c : ℂ) (z : S) : ℝ :=
  if h : (c, z) ∈ s.basin ∧
    ∃ p : ℝ, 0 ≤ p ∧ ∀ᶠ n in atTop, ‖s.bottcherNear c ((f c)^[n] z)‖ = p ^ d ^ n
  then choose h.2 else 1

/-- The set of potentials of non-`a` critical points of `f c`, with 1 included.
    For compact `S` 1 is automatically a critical value, but we don't want to show this here. -/
def Super.ps (s : Super f d a) (c : ℂ) : Set ℝ :=
  {p | p = 1 ∨ p ≠ 0 ∧ ∃ z, s.potential c z = p ∧ Critical (f c) z}

/-- The critical potential: the least potential of any non-`a` critical point of `f c` -/
def Super.p (s : Super f d a) (c : ℂ) : ℝ :=
  sInf (s.ps c)

/-- `z : S` is postcritical if its potential is smaller than any critical point (except for `a`) -/
def Postcritical (s : Super f d a) (c : ℂ) (z : S) : Prop :=
  s.potential c z < s.p c

/-- The set of postcritical points -/
def Super.post (s : Super f d a) : Set (ℂ × S) :=
  {p : ℂ × S | Postcritical s p.1 p.2}

/-- The domain on which `s.ray` is well behaved: `{(c,z) | s.potential c z < s.p c}`. -/
def Super.ext (s : Super f d a) : Set (ℂ × ℂ) :=
  {y : ℂ × ℂ | ‖y.2‖ < s.p y.1}

end
end Ray_Ray_Dynamics_Defs

-- ===== Ray.Misc.Bound =====
section Ray_Ray_Misc_Bound
/-!
## Register some bound lemmas
-/

variable {α G₀ : Type*}

attribute [bound] norm_add_le mul_lt_of_lt_one_left Complex.normSq_nonneg norm_inner_le_norm
  Units.norm_pos Real.cosh_pos norm_sub_norm_le neg_le_self Finset.norm_prod_le Real.one_le_exp
  Real.toNNReal_le_toNNReal mul_le_of_le_one_left sub_le_self sub_lt_self Finset.prod_nonneg
  pow_le_of_le_one mul_lt_of_lt_one_right Real.lt_sqrt_of_sq_lt Real.le_sqrt_of_sq_le
  le_mul_of_one_le_left Real.sqrt_nonneg abs_norm_sub_norm_le

@[bound] alias ⟨_, Bound.neg_pos⟩ := neg_pos

@[bound] alias ⟨_, Bound.ennreal_coe_pos⟩ := ENNReal.coe_pos

@[bound] alias ⟨_, Bound.sq_lt_one₀⟩ := sq_lt_one_iff₀

@[bound] alias ⟨_, Bound.sq_le_one₀⟩ := sq_le_one_iff₀

-- These are declared as `private alias` in Mathlib, but they need to be public aliases
@[bound] alias ⟨_, Bound.ofReal_pos_of_pos⟩ := ENNReal.ofReal_pos
@[bound] alias ⟨_, Bound.one_lt_exp_of_pos⟩ := Real.one_lt_exp_iff

@[bound] lemma Bound.lt_mul_of_one_lt_left [MulOneClass α] [Zero α] {a b : α} [Preorder α]
    [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) (b1 : 1 < b) : a < b * a :=
  (lt_mul_iff_one_lt_left a0).mpr b1

@[bound] lemma Bound.one_le_div₀ [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀]
    {a b : G₀} (hb : 0 < b) (ba : b ≤ a) : 1 ≤ a / b :=
  (_root_.one_le_div₀ hb).mpr ba

@[bound] lemma Bound.nat_cast_le [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α]
    [ZeroLEOneClass α] [CharZero α] {m n : ℕ} (h : m ≤ n) : (m : α) ≤ n :=
  Nat.cast_le.mpr h

@[bound] lemma Bound.one_le_rpow {x y : ℝ} (h : 1 ≤ x ∧ 0 ≤ y ∨ 0 < x ∧ x ≤ 1 ∧ y ≤ 0) :
    1 ≤ x ^ y := by
  rcases h with ⟨a,b⟩ | ⟨a,b,c⟩
  · exact Real.one_le_rpow a b
  · exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos a b c

@[bound] lemma Bound.div_nonpos {x y : ℝ} (h : 0 ≤ x ∧ y ≤ 0 ∨ x ≤ 0 ∧ 0 ≤ y) :
    x / y ≤ 0 := by
  rcases h with ⟨a,b⟩ | ⟨a,b⟩
  · exact div_nonpos_of_nonneg_of_nonpos a b
  · exact div_nonpos_of_nonpos_of_nonneg a b

@[bound] lemma Bound.div_neg {x y : ℝ} (h : 0 < x ∧ y < 0 ∨ x < 0 ∧ 0 < y) : x / y < 0 := by
  rcases h with ⟨a,b⟩ | ⟨a,b⟩
  · exact div_neg_of_pos_of_neg a b
  · exact div_neg_of_neg_of_pos a b

@[bound] lemma Bound.add_pos {x y : ℝ} (h : 0 ≤ x ∧ 0 < y ∨ 0 < x ∧ 0 ≤ y) : 0 < x + y := by
  rcases h with ⟨a,b⟩ | ⟨a,b⟩
  · exact add_pos_of_nonneg_of_pos a b
  · exact add_pos_of_pos_of_nonneg a b


-- Unpack membership in intervals
section Intervals
open Set
variable {α : Type} [Preorder α] {a b x : α}
@[aesop safe destruct (rule_sets := [Bound])] public alias ⟨Bound.mem_Icc, _⟩ := Set.mem_Icc
@[aesop safe destruct (rule_sets := [Bound])] public alias ⟨Bound.mem_Ico, _⟩ := Set.mem_Ico
@[aesop safe destruct (rule_sets := [Bound])] public alias ⟨Bound.mem_Ioc, _⟩ := Set.mem_Ioc
@[aesop safe destruct (rule_sets := [Bound])] public alias ⟨Bound.mem_Ioo, _⟩ := Set.mem_Ioo
@[aesop safe destruct (rule_sets := [Bound])] public alias ⟨Bound.mem_Ici, _⟩ := Set.mem_Ici
@[aesop safe destruct (rule_sets := [Bound])] public alias ⟨Bound.mem_Iic, _⟩ := Set.mem_Iic
@[aesop safe destruct (rule_sets := [Bound])] public alias ⟨Bound.mem_Iio, _⟩ := Set.mem_Iio
@[aesop safe destruct (rule_sets := [Bound])] public alias ⟨Bound.mem_Ioi, _⟩ := Set.mem_Ioi
end Intervals

end Ray_Ray_Misc_Bound

-- ===== Ray.Misc.Finset =====
section Ray_Ray_Misc_Finset
/-!
## `Finset ℕ` machinery for use in sums and products
-/

open Filter (atTop)
open Stream' (cons)
open scoped Topology Stream

variable {G : Type} [NormedAddCommGroup G]
variable {H : Type} [CommMonoid H]

/-- Insert `0` into a `Finset ℕ`, adding `1` to existing elements -/
def push (N : Finset ℕ) :=
  insert 0 (Finset.image (fun n ↦ n + 1) N)

/-- Subtract `1` from everything in a `Finset ℕ`, discarding `0`.
    This is the left inverse of push. -/
def pop (N : Finset ℕ) :=
  Finset.image (fun n ↦ n - 1) (Finset.erase N 0)

/-- `push` almost cancels `pop` -/
theorem push_pop {N : Finset ℕ} : push (pop N) = insert 0 N := by
  rw [push, pop]; apply Finset.ext; simp
  intro n; by_cases n0 : n = 0; · rw [n0]; simp
  simp_rw [or_iff_right n0]
  constructor
  · intro h; rcases h with ⟨x, ⟨x0, xN⟩, xn⟩
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr x0)] at xn
    rwa [←xn]
  · intro h; exists n; use ⟨n0,h⟩
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr n0)

/-- `push` is monotone -/
theorem push_le_push {A B : Finset ℕ} : push A ≤ push B ↔ A ≤ B := by
  rw [push, push]
  constructor
  · intro AB; rw [Finset.subset_iff] at AB ⊢; intro x xA
    have h : x + 1 ∈ insert 0 (Finset.image (fun n : ℕ ↦ n + 1) A) := by simpa
    specialize AB h; simp at AB; assumption
  · intro AB; apply Finset.insert_subset_insert; apply Finset.image_mono; assumption

/-- `push` and sums interact nicely, `Stream'.get` version to keep terms type-correct
    at low transparency -/
theorem push_sum_get {X : Type} [AddCommGroup X] {a : X} {g : Stream' X} {N : Finset ℕ} :
    a + N.sum g.get = (push N).sum (cons a g).get := by
  rw [push, Finset.sum_insert (by simp), Finset.sum_image (fun x _ y _ h ↦ by omega)]
  rfl

/-- `push` and sums interact nicely -/
theorem push_sum {X : Type} [AddCommGroup X] {a : X} {f : ℕ → X} {N : Finset ℕ} :
    a + N.sum f = (push N).sum (cons a f) :=
  push_sum_get

/-- `push` and products interact nicely, `Stream'.get` version to keep terms type-correct
    at low transparency -/
theorem push_prod_get {a : H} {g : Stream' H} {N : Finset ℕ} :
    a * N.prod g.get = (push N).prod (cons a g).get := by
  rw [push, Finset.prod_insert (by simp), Finset.prod_image (fun x _ y _ h ↦ by omega)]
  rfl

/-- `push` and products interact nicely -/
theorem push_prod {a : H} {f : ℕ → H} {N : Finset ℕ} :
    a * N.prod f = (push N).prod (cons a f) :=
  push_prod_get

/-- The range of `push` is `Finset`s containing 0 -/
theorem push_range : Set.range push = {N : Finset ℕ | 0 ∈ N} := by
  rw [Set.range]; apply Set.ext; simp; intro N; constructor
  · intro h; rcases h with ⟨M, H⟩; rw [push] at H; rw [← H]; exact Finset.mem_insert_self 0 _
  · intro N0; exists pop N; rw [push_pop]; exact Finset.insert_eq_of_mem N0

theorem push_comap_atTop : Filter.comap push atTop = atTop := by
  apply Filter.comap_embedding_atTop
  exact @push_le_push
  intro N; exists pop N; rw [push_pop]; simp

/-- `f ∘ push` converges `atTop` iff `f` does -/
theorem tendsto_comp_push {A : Type} {f : Finset ℕ → A} {l : Filter A} :
    Filter.Tendsto (f ∘ push) atTop l ↔ Filter.Tendsto f atTop l := by
  nth_rw 1 [← push_comap_atTop]; apply Filter.tendsto_comap'_iff
  rw [push_range]
  have h : {N : Finset ℕ | 0 ∈ N} = {N : Finset ℕ | {0} ≤ N} := by simp
  rw [h]; exact Filter.mem_atTop _

/-- Triangle inequality for finset sums -/
theorem finset_norm_sum_le (N : Finset ℕ) (f : ℕ → G) :
    ‖N.sum fun n ↦ f n‖ ≤ N.sum fun n ↦ ‖f n‖ := by
  induction' N using Finset.induction with n N Nn h; · simp
  · rw [Finset.sum_insert Nn]
    rw [Finset.sum_insert Nn]
    trans ‖f n‖ + ‖N.sum fun n ↦ f n‖
    · apply norm_add_le
    · apply add_le_add_right; assumption

theorem subset_union_sdiff (A B : Finset ℕ) : B ⊆ A ∪ B \ A := by
  rw [Finset.subset_iff]; intro x Bx
  rw [Finset.mem_union, Finset.mem_sdiff]
  by_cases Ax : x ∈ A
  · left; exact Ax
  · right; exact ⟨Bx, Ax⟩

end Ray_Ray_Misc_Finset

-- ===== Ray.Misc.Bounds =====
section Ray_Ray_Misc_Bounds
/-!
## Assorted bound lemmas
-/

open Classical
open Complex (exp log I slitPlane)
open Filter (atTop)
open scoped Real NNReal Topology symmDiff

variable {α : Type}
variable {M : Type} [AddCommMonoid M]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {G : Type} [NormedAddCommGroup G]

lemma late_iff_disjoint_range {m : ℕ} {A : Finset ℕ} :
    Late A m ↔ Disjoint A (Finset.range m) := by
  simp only [Late, ge_iff_le, Finset.disjoint_iff_ne, Finset.mem_range, ne_eq]; constructor
  · intro h n na b bm; linarith [h _ na]
  · intro h n na; specialize h n na n; simpa [not_true, imp_false, not_lt] using h

lemma sdiff_late {m : ℕ} {B : Finset ℕ} (A : Finset ℕ) :
    B ≥ Finset.range m → Late (A \ B) m := by
  intro Bm n nAB
  rw [Finset.mem_sdiff] at nAB
  by_contra h; simp only [not_le] at h
  have nr := Finset.mem_range.mpr h
  have nB := Finset.mem_of_subset Bm nr
  exact nAB.2 nB

/-- Summing a subset of a geometric series is ≤ the series sum -/
theorem partial_geometric_bound {a : ℝ} (N : Finset ℕ) (a0 : 0 ≤ a) (a1 : a < 1) :
    N.sum (fun n ↦ a^n) ≤ (1 - a)⁻¹ :=
  haveI pos : ∀ n, n ∉ N → 0 ≤ a^n := by intro n _; bound
  sum_le_hasSum N pos (hasSum_geometric_of_lt_one a0 a1)

theorem partial_scaled_geometric_bound {a : ℝ} (c : ℝ≥0) (N : Finset ℕ) (a0 : 0 ≤ a)
    (a1 : a < 1) : N.sum (fun n ↦ (c:ℝ) * a^n) ≤ c * (1 - a)⁻¹ := by
  rw [←Finset.mul_sum]
  bound [partial_geometric_bound N a0 a1]

/-- Summing a late part of a series is equivalent to summing a shifted series -/
theorem late_series_sum {m : ℕ} {N : Finset ℕ} (h : Late N m) (f : ℕ → ℝ) :
    N.sum f = (N.image (fun n ↦ n - m)).sum (fun n ↦ f (n + m)) := by
  set Ns := Finset.image (fun n ↦ n - m) N
  have NNs : N = Finset.image (fun n ↦ n + m) Ns := by
    apply Finset.ext; intro k
    rw [Finset.image_image, Finset.mem_image]
    simp
    apply Iff.intro
    · intro kN; exists k; apply And.intro
      assumption; exact Nat.sub_add_cancel (h k kN)
    · intro ha; rcases ha with ⟨a, aN, ak⟩
      rw [Nat.sub_add_cancel (h a aN)] at ak
      rw [← ak]; assumption
  rw [NNs]; apply Finset.sum_image
  intro a _ b _; exact Nat.add_right_cancel

/-- late_series_sum, but forgetting the image set -/
theorem late_series_sum' {m : ℕ} {N : Finset ℕ} (h : Late N m) (f : ℕ → ℝ) :
    ∃ M : Finset ℕ, N.sum f = M.sum (fun n ↦ f (n + m)) := by
  exists Finset.image (fun n ↦ n - m) N
  exact late_series_sum h f

theorem late_geometric_bound {m : ℕ} {a : ℝ} {N : Finset ℕ} (h : Late N m) (a0 : 0 ≤ a)
    (a1 : a < 1) : N.sum (fun n ↦ a^n) ≤ a^m * (1 - a)⁻¹ := by
  rcases late_series_sum' h (fun n ↦ a^n) with ⟨M,L⟩
  rw [L]; clear L
  have pa : (fun n ↦ a^(n + m)) = (fun n ↦ a^n * a^m) := by apply funext; intro n; rw [pow_add]
  calc
    M.sum (fun n ↦ a^(n + m)) = M.sum (fun n ↦ a^n * a^m) := by rw [ pa ]
    _ = M.sum (fun n ↦ a^n) * a^m := (Finset.sum_mul _ _ _).symm
    _ ≤ (1 - a)⁻¹ * a^m := by bound [partial_geometric_bound M a0 a1]
    _ = a^m * (1 - a)⁻¹ := by ring

theorem finset_partition (A B : Finset ℕ) : A = A \ B ∪ A ∩ B := by
  apply Finset.ext
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
  intro x; constructor
  · intro a
    by_cases b : x ∈ B
    · right; use a,b
    · left; use a,b
  · intro h
    cases' h with m m
    repeat exact m.1

theorem finset_sum_partition (A B : Finset ℕ) (f : ℕ → M) :
    A.sum f = (A \ B).sum f + (A ∩ B).sum f := by
  have ha : A = A \ B ∪ A ∩ B := finset_partition A B
  nth_rw 1 [ha]
  exact Finset.sum_union (Finset.disjoint_sdiff_inter A B)

theorem sdiff_sdiff_disjoint (A B : Finset ℕ) : Disjoint (A \ B) (B \ A) :=
  Finset.disjoint_of_subset_right Finset.sdiff_subset Finset.sdiff_disjoint

theorem symmDiff_union (A B : Finset ℕ) : A ∆ B = A \ B ∪ B \ A := by
  rw [symmDiff_def, Finset.sup_eq_union]

theorem symmDiff_bound (A B : Finset ℕ) (f : ℕ → G) :
    dist (A.sum f) (B.sum f) ≤ (A ∆ B).sum (fun n ↦ ‖f n‖) := by
  rw [finset_sum_partition A B f, finset_sum_partition B A f, Finset.inter_comm B A]
  rw [dist_add_right ((A \ B).sum f) ((B \ A).sum f) ((A ∩ B).sum f)]
  rw [dist_eq_norm]
  trans (A \ B).sum (fun n ↦ ‖f n‖) + (B \ A).sum (fun n ↦ ‖f n‖)
  · have ha := finset_norm_sum_le (A \ B) f
    have hb := finset_norm_sum_le (B \ A) f
    calc ‖(A \ B).sum f - (B \ A).sum f‖
      _ ≤ ‖(A \ B).sum f‖ + ‖(B \ A).sum f‖ := by bound
      _ ≤ (A \ B).sum (fun n ↦ ‖f n‖) + (B \ A).sum (fun n ↦ ‖f n‖) := by bound
  · apply le_of_eq
    rw [←Finset.sum_union (sdiff_sdiff_disjoint A B), symmDiff_union]

/-- Symmetric differences of sets containing ranges are late -/
theorem symmDiff_late {A B : Finset ℕ} {m : ℕ} (ha : A ≥ Finset.range m)
    (hb : B ≥ Finset.range m) : Late (A ∆ B) m := by
  intro n ab
  rw [symmDiff_def, Finset.sup_eq_union, Finset.mem_union] at ab
  by_contra h; simp at h
  cases' ab with a b
  · rw [Finset.mem_sdiff] at a
    have h := Finset.mem_of_subset hb (Finset.mem_range.mpr h)
    exact a.2 h
  · rw [Finset.mem_sdiff] at b
    have h := Finset.mem_of_subset ha (Finset.mem_range.mpr h)
    exact b.2 h

/-- `a - z` has similar absolute value to `a` for small `z` -/
theorem sub_near (a z : ℂ) : |‖a - z‖ - ‖a‖| ≤ ‖z‖ := by
  rw [abs_le]; constructor
  · simp only [neg_le_sub_iff_le_add]
    exact norm_le_norm_sub_add a z
  · calc
      ‖a - z‖ - ‖a‖ ≤ ‖a‖ + ‖z‖ - ‖a‖ := by bound
      _ = ‖z‖ := by simp only [add_sub_cancel_left]

theorem add_near (a z : ℂ) : |‖a + z‖ - ‖a‖| ≤ ‖z‖ := by
  have h := sub_near a (-z)
  simp only [sub_neg_eq_add, norm_neg] at h
  assumption

theorem mem_slitPlane_of_near_one' {z : ℂ} (z1 : ‖z - 1‖ ≤ 1) (z0 : z ≠ 0) : z ∈ slitPlane := by
  rw [← sq_le_sq₀ (by bound) (by norm_num)] at z1
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re, ← pow_two,
    Complex.sub_im, Complex.one_im, sub_zero, one_pow] at z1
  by_cases i0 : z.im ≠ 0
  · right
    exact i0
  · simp only [ne_eq, Decidable.not_not] at i0
    left
    contrapose z0
    simp [i0, abs_sub_le_iff, Complex.ext_iff] at z0 z1 ⊢
    grind

theorem mem_slitPlane_of_near_one {z : ℂ} (z1 : ‖z - 1‖ < 1) : z ∈ slitPlane := by
  by_cases z0 : z = 0
  · simp [z0] at z1
  · exact mem_slitPlane_of_near_one' z1.le z0

theorem near_one_avoids_zero {z : ℂ} : ‖z - 1‖ < 1 → z ≠ 0 := by
  intro h; exact Complex.slitPlane_ne_zero (mem_slitPlane_of_near_one h)

theorem derivWithin.cid {z : ℂ} {s : Set ℂ} (o : IsOpen s) (zs : z ∈ s) :
    derivWithin (fun z ↦ z) s z = 1 :=
  derivWithin_id z s (IsOpen.uniqueDiffWithinAt o zs)

theorem derivWithin.clog {f : ℂ → ℂ} {z : ℂ} {s : Set ℂ} (o : IsOpen s) (zs : z ∈ s)
    (hf : DifferentiableWithinAt ℂ f s z) (hx : (f z).re > 0 ∨ (f z).im ≠ 0) :
    derivWithin (fun z ↦ Complex.log (f z)) s z = derivWithin f s z / f z := by
  have hz := DifferentiableWithinAt.hasDerivWithinAt hf
  have h := HasDerivWithinAt.clog hz hx
  have u := o.uniqueDiffWithinAt (𝕜 := ℂ) zs
  rw [HasDerivWithinAt.derivWithin h u]

theorem weak_log1p_small {z : ℂ} {r : ℝ} (r1 : r < 1) (h : ‖z‖ < r) :
    ‖log (1 + z)‖ ≤ 1/(1 - r) * ‖z‖ := by
  by_cases rp : r ≤ 0
  · have a0 : ‖z‖ < 0 := lt_of_lt_of_le h rp
    have a0' : ‖z‖ ≥ 0 := by bound
    exfalso
    linarith [a0, a0']
  · simp only [not_le] at rp
    have L : ‖log (1 + z) - log 1‖ ≤ 1/(1 - r) * ‖1 + z - 1‖ := by
      generalize hs : Metric.ball (1:ℂ) r = s
      have o : IsOpen s := by rw [← hs]; exact Metric.isOpen_ball
      have s1z : 1 + z ∈ s := by simp [← hs]; assumption
      have s1 : (1:ℂ) ∈ s := by simp [← hs]; assumption
      have sp : ∀ w : ℂ, w ∈ s → w.re > 0 ∨ w.im ≠ 0 := by
        intro w ws
        apply mem_slitPlane_of_near_one
        simp only [Metric.mem_ball, Complex.dist_eq, ← hs] at ws
        calc ‖w - 1‖ < r := by assumption
          _ < 1 := r1
      have sa : ∀ w : ℂ, w ∈ s → ‖w‖ ≥ 1 - r := by
        intro w ws
        simp only [Metric.mem_ball, Complex.dist_eq, ← hs] at ws
        calc ‖w‖ = ‖1 + (w - 1)‖ := by ring_nf
          _ ≥ ‖(1 : ℂ)‖ - ‖w - 1‖ := by bound
          _ ≥ ‖(1 : ℂ)‖ - r := by bound
          _ = 1 - r := by rw [norm_one]
      refine Convex.norm_image_sub_le_of_norm_derivWithin_le ?_ ?_ ?_ s1 s1z
      · exact DifferentiableOn.clog differentiableOn_id sp
      · intro w ws
        rw [derivWithin.clog o ws, derivWithin.cid o ws]
        simp only [one_div, norm_inv]
        rw [inv_le_comm₀]
        have aw := sa w ws; simp at aw; field_simp; linarith
        have aw := sa w ws; linarith; norm_num; assumption
        exact differentiableWithinAt_id
        exact sp w ws
      · rw [← hs]; exact convex_ball _ _
    simp only [Complex.log_one, sub_zero, one_div, add_sub_cancel_left] at L
    simpa only [one_div, ge_iff_le]

theorem le_of_forall_small_le_add {a b t : ℝ} (tp : 0 < t)
    (h : ∀ e, 0 < e → e < t → a ≤ b + e) : a ≤ b := by
  apply le_of_forall_pos_lt_add
  intro e ep
  by_cases et : e ≥ t
  · specialize h (t/2) (by bound) (by bound)
    calc a ≤ b + t/2 := h
      _ ≤ b + e/2 := by bound
      _ < b + e := by bound
  · simp only [ge_iff_le, not_le] at et
    calc a ≤ b + e/2 := h (e/2) (by bound) (by linarith)
      _ < b + e := by bound

theorem one_over_one_sub_le {x : ℝ} : 0 ≤ x → x ≤ 1/2 → 1/(1 - x) ≤ 1 + 2*x := by
  intro xp xh
  have x1 : 1 - x > 0 := by linarith
  rw [div_le_iff₀ x1]
  calc (1 + 2*x) * (1 - x) = 1 + x * (1 - 2*x) := by ring
    _ ≥ 1 + x * (1 - 2 * (1/2)) := by bound
    _ = 1 := by ring

theorem Metric.continuous_near {f : ℂ → ℂ} {z : ℂ} {r : ℝ} (fc : ContinuousAt f z) (rp : 0 < r)
    : ∀ e, 0 < e → ∃ s, 0 < s ∧ s ≤ r ∧ ∀ {w} , ‖w - z‖ < s → ‖f w - f z‖ < e := by
  intro e ep
  rcases Metric.continuousAt_iff.mp fc e ep with ⟨s,sp,sc⟩
  simp_rw [ Complex.dist_eq ] at sc
  by_cases sr : s ≤ r; exists s
  simp only [not_le] at sr
  exists r
  refine ⟨rp, by bound, ?_⟩
  intro w wr
  refine @sc w ?_
  trans r; assumption; assumption

theorem slightly_smaller {z : ℂ} (nz : z ≠ 0) {r : ℝ} (rp : 0 < r) :
    ∃ w, ‖w - z‖ < r ∧ ‖w‖ < ‖z‖ := by
  by_cases rz : ‖z‖ < r
  · use 0
    simp only [zero_sub, norm_neg, rz, norm_zero, norm_pos_iff, ne_eq, nz, not_false_eq_true,
      and_self]
  simp only [not_lt] at rz
  have azp : 0 < ‖z‖ := norm_pos_iff.mpr nz
  generalize ha : 1 - r/2/‖z‖ = a
  have a0 : 0 ≤ a := by rw [←ha, sub_nonneg, div_le_one azp]; exact _root_.trans (by bound) rz
  have a1 : a < 1 := by rw [←ha, sub_lt_self_iff]; positivity
  generalize hw : ↑a * z = w
  use w; constructor
  · rw [ ←hw, ← ha]
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div]
    rw [mul_sub_right_distrib]
    simp only [one_mul, Complex.ofReal_ofNat, sub_sub_cancel_left, norm_neg, Complex.norm_mul,
      Complex.norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos rp, Complex.norm_ofNat,
      div_mul (r / 2), div_one, half_lt_self_iff, div_self azp.ne', abs_norm, rp]
  · simp only [← hw, Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg a0]
    exact mul_lt_of_lt_one_left azp a1

/-- There are smaller values nearby any z ≠ 0 -/
theorem frequently_smaller {z : ℂ} (z0 : z ≠ 0) : ∃ᶠ w : ℂ in 𝓝 z, ‖w‖ < ‖z‖ := by
  simp only [Filter.Frequently, Metric.eventually_nhds_iff, not_exists, not_forall, not_not,
    Complex.dist_eq, not_and]
  intro r rp; rcases slightly_smaller z0 rp with ⟨w, b, lt⟩; use w, b, lt

theorem weak_to_strong_small {f : ℂ → ℂ} {z : ℂ} {r c : ℝ} (rp : 0 < r) (cp : 0 < c)
    (zr : ‖z‖ ≤ r) (fc : ContinuousAt f z) (h : ∀ z : ℂ, ‖z‖ < r → ‖f z‖ ≤ c * ‖z‖) :
    ‖f z‖ ≤ c * ‖z‖ := by
  by_cases nz : z = 0; · refine h z ?_; rw [nz]; simpa
  apply le_of_forall_small_le_add zero_lt_one
  intro e ep _
  rcases Metric.continuous_near fc rp e ep with ⟨s,sp,_,sc⟩
  rcases slightly_smaller nz sp with ⟨w,wz,awz⟩
  have wr : ‖w‖ < r := lt_of_lt_of_le awz zr
  calc ‖f z‖ = ‖f w - (f w - f z)‖ := by ring_nf
    _ ≤ ‖f w‖ + ‖f w - f z‖ := by bound
    _ ≤ c * ‖w‖ + e := by bound [h w wr, sc wz]
    _ ≤ c * ‖z‖ + e := by bound

theorem log1p_small' {z : ℂ} {r : ℝ} (r1 : r < 1) (zr : ‖z‖ ≤ r) :
    ‖log (1 + z)‖ ≤ 1 / (1 - r) * ‖z‖ := by
  by_cases r0 : r ≤ 0
  · have z0 := le_antisymm (le_trans zr r0) (norm_nonneg z)
    simp only [norm_eq_zero] at z0
    simp only [z0, add_zero, Complex.log_one, norm_zero, one_div, mul_zero, le_refl]
  simp only [not_le] at r0
  have fc : ContinuousAt (fun z ↦ log (1 + z)) z := by
    apply ContinuousAt.clog; apply ContinuousAt.add; exact continuousAt_const; exact continuousAt_id
    refine mem_slitPlane_of_near_one ?_
    simp only [add_sub_cancel_left, lt_of_le_of_lt zr r1]
  apply weak_to_strong_small r0 (by bound) zr fc
  intro w wr
  exact @weak_log1p_small w r (by bound) wr

theorem log1p_small {z : ℂ} (zs : ‖z‖ ≤ 1/2) : ‖log (1 + z)‖ ≤ 2 * ‖z‖ :=
  le_trans (log1p_small' (by norm_num) zs) (le_of_eq (by norm_num))

/-- `log (1+x)` is small for small `x` -/
theorem Real.log1p_small' {x r : ℝ} (r1 : r < 1) (xr : |x| ≤ r) :
    |Real.log (1 + x)| ≤ 1 / (1-r) * |x| := by
  set z := (x : ℂ)
  have zx : ‖z‖ = |x| := by simp only [Complex.norm_real, norm_eq_abs, z]
  simp only [← Complex.log_ofReal_re, ← zx] at xr ⊢
  refine _root_.trans (_root_.trans (Complex.abs_re_le_norm _) ?_) (_root_.log1p_small' r1 xr)
  simp only [Complex.ofReal_add, Complex.ofReal_one, le_refl, z]

/-- `log (1+x)` is small for small `x` -/
theorem Real.log1p_small {x : ℝ} (xr : |x| ≤ 1/2) : |Real.log (1 + x)| ≤ 2 * |x| :=
  le_trans (Real.log1p_small' (by norm_num) xr) (le_of_eq (by norm_num))

/-- `log z` is small for `z ≈ 1` -/
theorem log_small {z : ℂ} (zs : ‖z - 1‖ ≤ 1 / 2) : ‖log z‖ ≤ 2 * ‖z - 1‖ := by
  generalize zw : z - 1 = z1; have wz : z = 1 + z1 := by rw [← zw]; ring
  rw [wz]; refine log1p_small ?_; rw [← zw]; assumption

theorem weak_exp_small' {z : ℂ} {r : ℝ} (zr : ‖z‖ < r) (r1 : r ≤ 1) :
    ‖exp z - 1‖ ≤ (1 + r) * ‖z‖ := by
  have r0 : 0 ≤ r := le_trans (norm_nonneg _) zr.le
  have L := Complex.locally_lipschitz_exp r0 r1 0 z (by simpa only [sub_zero])
  simpa only [Complex.exp_zero, norm_one, mul_one, sub_zero] using L

theorem weak_exp_small {z : ℂ} (h : ‖z‖ < 1) : ‖exp z - 1‖ ≤ 2 * ‖z‖ := by
  have L := weak_exp_small' h (by norm_num)
  norm_num at L
  exact L

/-- `exp z ≈ 1` for `z ≈ 0` -/
theorem exp_small' {z : ℂ} {r : ℝ} (zs : ‖z‖ ≤ r) (r1 : r ≤ 1) : ‖exp z - 1‖ ≤ (1 + r) * ‖z‖ := by
  by_cases z0 : z = 0
  · simp [z0]
  have r0 : 0 < r := lt_of_lt_of_le (norm_pos_iff.mpr z0) zs
  have cp : 0 < 1 + r := by linarith
  have fc : ContinuousAt (fun z ↦ exp z - 1) z := by
    apply ContinuousAt.sub; apply ContinuousAt.cexp
    exact continuousAt_id; exact continuousAt_const
  apply weak_to_strong_small r0 cp zs fc
  intro w wr
  exact weak_exp_small' wr r1

/-- `exp z ≈ 1` for `z ≈ 0` -/
theorem exp_small {z : ℂ} (zs : ‖z‖ ≤ 1) : ‖exp z - 1‖ ≤ 2 * ‖z‖ := by
  have s := exp_small' zs (by norm_num)
  norm_num at s
  exact s

/-- `exp_small'`, but for any ball -/
lemma exp_small_general {z : ℂ} {r : ℝ} (zs : ‖z‖ ≤ r) : ‖exp z - 1‖ ≤ Real.exp r * ‖z‖ := by
  have b := Complex.norm_exp_sub_sum_le_norm_mul_exp z 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    ne_eq, one_ne_zero, not_false_eq_true, div_self, pow_one, mul_comm ‖z‖] at b
  exact le_trans b (by bound)

@[bound] lemma psg_nonzero {r s : ℝ} (r1 : r ≤ 1) : 0 ≤ psg r s := by
  unfold psg
  bound

theorem pow1p_small_general {z w : ℂ} {r s : ℝ} (zr : ‖z‖ ≤ r) (ws : ‖w‖ ≤ s) (r1 : r < 1)  :
    ‖(1 + z) ^ w - 1‖ ≤ psg r s * ‖z‖ * ‖w‖ := by
  by_cases z0 : z = 0
  · simp [z0]
  have r0 : 0 < r := lt_of_lt_of_le (norm_pos_iff.mpr z0) zr
  have s0 : 0 ≤ s := le_trans (norm_nonneg _) ws
  have z1 : 1 + z ≠ 0 := by
    rw [← norm_pos_iff]
    calc ‖1 + z‖ ≥ ‖(1 : ℂ)‖ - ‖z‖ := by bound
      _ ≥ ‖(1 : ℂ)‖ - r := by bound
      _ > 0 := by simp only [norm_one, sub_pos, r1]
  rw [Complex.cpow_def_of_ne_zero z1]
  have ls := log1p_small' r1 zr
  have eas : ‖log (1 + z) * w‖ ≤ r * s / (1 - r) := by
    rw [Complex.norm_mul]
    calc ‖log (1 + z)‖ * ‖w‖ ≤ 1 / (1 - r) * ‖z‖ * s := by bound
      _ ≤ 1 / (1 - r) * r * s := by bound
      _ = _ := by ring
  have es := exp_small_general eas
  rw [Complex.norm_mul, ← mul_assoc] at es
  refine le_trans es ?_
  grw [ls]
  simp only [psg]
  apply le_of_eq
  grind

theorem pow1p_small' {z w : ℂ} {r s : ℝ} (zr : ‖z‖ ≤ r) (ws : ‖w‖ ≤ s) (r1 : r < 1)
    (rs1 : r * s ≤ 1 - r) :
    ‖(1 + z) ^ w - 1‖ ≤ (1 - r + r * s) / (1 - r) ^ 2 * ‖z‖ * ‖w‖ := by
  by_cases z0 : z = 0
  · simp [z0]
  have r0 : 0 < r := lt_of_lt_of_le (norm_pos_iff.mpr z0) zr
  have s0 : 0 ≤ s := le_trans (norm_nonneg _) ws
  have z1 : 1 + z ≠ 0 := by
    rw [← norm_pos_iff]
    calc ‖1 + z‖ ≥ ‖(1 : ℂ)‖ - ‖z‖ := by bound
      _ ≥ ‖(1 : ℂ)‖ - r := by bound
      _ > 0 := by simp only [norm_one, sub_pos, r1]
  rw [Complex.cpow_def_of_ne_zero z1]
  have ls := log1p_small' r1 zr
  have eas : ‖log (1 + z) * w‖ ≤ r * s / (1 - r) := by
    rw [Complex.norm_mul]
    calc ‖log (1 + z)‖ * ‖w‖ ≤ 1 / (1 - r) * ‖z‖ * s := by bound
      _ ≤ 1 / (1 - r) * r * s := by bound
      _ = _ := by ring
  have es := exp_small' eas (by rw [div_le_iff₀ (by bound)]; linarith)
  rw [Complex.norm_mul, ← mul_assoc] at es
  refine le_trans es ?_
  grw [ls]
  · apply le_of_eq
    grind
  · bound

theorem pow1p_small {z w : ℂ} (zs : ‖z‖ ≤ 1/2) (ws : ‖w‖ ≤ 1) :
    ‖(1 + z) ^ w - 1‖ ≤ 4 * ‖z‖ * ‖w‖ := by
  have L := pow1p_small' zs ws (by norm_num) (by bound)
  norm_num at L
  exact L

/-- `‖z^w - 1‖ = O(‖z - 1‖ * ‖w‖)` for `z ≈ 1`, `w` small -/
theorem pow_small' {z w : ℂ} {r s : ℝ} (zr : ‖z - 1‖ ≤ r) (ws : ‖w‖ ≤ s) (r1 : r < 1)
    (rs1 : r * s ≤ 1 - r) :
    ‖z ^ w - 1‖ ≤ (1 - r + r * s) / (1 - r) ^ 2 * ‖z - 1‖ * ‖w‖ := by
  generalize zw : z - 1 = z1
  have wz : z = 1 + z1 := by rw [← zw]; ring
  exact wz ▸ pow1p_small' (by rwa [← zw]) ws r1 rs1

/-- `‖z^w - 1‖ = O(‖z - 1‖ * ‖w‖)` for `z ≈ 1`, `w` small -/
theorem pow_small_general {z w : ℂ} {r s : ℝ} (zr : ‖z - 1‖ ≤ r) (ws : ‖w‖ ≤ s) (r1 : r < 1) :
    ‖z ^ w - 1‖ ≤ psg r s * ‖z - 1‖ * ‖w‖ := by
  generalize zw : z - 1 = z1
  have wz : z = 1 + z1 := by rw [← zw]; ring
  exact wz ▸ pow1p_small_general (by rwa [← zw]) ws r1

/-- `‖z^w - 1‖ ≤ 4 * ‖z - 1‖ * ‖w‖` for `z ≈ 1`, `w` small -/
theorem pow_small {z w : ℂ} (zs : ‖z - 1‖ ≤ 1 / 2) (ws : ‖w‖ ≤ 1) :
    ‖z ^ w - 1‖ ≤ 4 * ‖z - 1‖ * ‖w‖ := by
  generalize zw : z - 1 = z1
  have wz : z = 1 + z1 := by rw [← zw]; ring
  exact wz ▸ pow1p_small (by rwa [← zw]) ws

/-- `a + b ≠ 0` from `abs b < abs a` -/
theorem add_ne_zero_of_abs_lt {a b : ℂ} (h : ‖b‖ < ‖a‖) : a + b ≠ 0 := by
  have e : a + b = a - -b := by abel
  rw [e, sub_ne_zero]
  contrapose h
  simp only [h, not_lt, norm_neg, le_refl]

/-- `e < 3` -/
theorem Real.exp_one_lt_3 : Real.exp 1 < 3 :=
  _root_.trans Real.exp_one_lt_d9 (by norm_num)

theorem log_add (a b : ℝ) (a0 : 0 < a) (ab0 : 0 < a + b) :
    Real.log (a + b) = Real.log a + Real.log (1 + b/a) := by
  have d0 : 0 < 1 + b/a := by field_simp [a0.ne']; bound
  rw [←Real.log_mul a0.ne' d0.ne', left_distrib, mul_one, mul_div_cancel₀ _ a0.ne']

/-- `log (abs (a + b)) = log (abs a) + log (abs (1 + b/a))` -/
theorem log_abs_add (a b : ℂ) (a0 : a ≠ 0) (ab0 : a + b ≠ 0) :
    Real.log (‖a + b‖) = Real.log (‖a‖) + Real.log (‖1 + b/a‖) := by
  have d0 : 1 + b/a ≠ 0 := by field_simp [a0, ab0]; exact div_ne_zero ab0 a0
  have a0' : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr a0
  have d0' : ‖1 + b / a‖ ≠ 0 := norm_ne_zero_iff.mpr d0
  rw [←Real.log_mul a0' d0', ← Complex.norm_mul, left_distrib, mul_one, mul_div_cancel₀ _ a0]

/-- `e^(1/4) ≤ 4/3` -/
theorem Real.exp_forth_lt_four_thirds : Real.exp (1/4) < 4/3 := by
  rw [←Real.exp_one_rpow, one_div, ←@Real.pow_rpow_inv_natCast (4/3) 4 (by norm_num) (by norm_num)]
  refine Real.rpow_lt_rpow (Real.exp_pos _).le ?_ (by norm_num)
  exact _root_.trans Real.exp_one_lt_d9 (by norm_num)

/-- Bound `abs (product - 1)` in terms of `abs (sum)` -/
theorem dist_prod_one_le_abs_sum {f : ℕ → ℂ} {s : Finset ℕ} {c : ℝ}
    (le : s.sum (fun n ↦ ‖f n - 1‖) ≤ c) (c1 : c ≤ 1/2) : ‖s.prod f - 1‖ ≤ 4 * c := by
  set g := fun n ↦ Complex.log (f n)
  have b : ∀ n, n ∈ s → ‖f n - 1‖ ≤ c := by
    intro n m; refine _root_.trans ?_ le
    exact Finset.single_le_sum (f := fun n ↦ ‖f n - 1‖) (fun _ _ ↦ norm_nonneg _) m
  have f0 : ∀ n, n ∈ s → f n ≠ 0 := by
    intro n m; specialize b n m; contrapose b
    simp only [b, not_le]; norm_num; linarith
  have sg : ‖s.sum g‖ ≤ 2 * c := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun n m ↦ log_small (le_trans (b n m) c1))) ?_
    rw [← Finset.mul_sum]; bound
  have e : s.prod f = Complex.exp (s.sum g) := by
    rw [Complex.exp_sum]; apply Finset.prod_congr rfl
    intro n m; rw [Complex.exp_log (f0 n m)]
  rw [e]; exact _root_.trans (exp_small (by linarith)) (by linarith)

/-- If `z, w` are close, then `0 < (z⁻¹ * w).re` -/
lemma re_mul_inv_pos_of_close {z w : ℂ} (wz : ‖w - z‖ < ‖z‖) : 0 < (z⁻¹ * w).re := by
  have z0 : z ≠ 0 := norm_ne_zero_iff.mp (lt_of_le_of_lt (by bound) wz).ne'
  have h : ‖z⁻¹ * w - 1‖ < 1 := by
    nth_rw 1 [← inv_mul_cancel₀ z0]
    simp only [← mul_sub, norm_mul, norm_inv]
    simp only [← div_eq_inv_mul]
    bound [norm_pos_iff.mpr z0]
  generalize z⁻¹ * w = x at h
  rw [norm_sub_rev] at h
  simpa only [Complex.sub_re, Complex.one_re, sub_lt_self_iff] using
    lt_of_le_of_lt (Complex.re_le_norm _) h

end Ray_Ray_Misc_Bounds

-- ===== Ray.Misc.Multilinear =====
section Ray_Ray_Misc_Multilinear
/-!
## Continuous multilinear map constructors

We define continuous multilinear maps for

1. `fstCmmap` for `fst`
2. `sndCmmap` for `snd`
3. `smulCmmap` for two continuous multilinear maps `smul`'ed together
4. Products of monomials: `termCmmap` for `x^a * y^b`
5. `conjCLM` for `conj` (this is one a continuous linear map)
6. `cmmapApplyCmap`, a continuous linear map that evaluates a continuous multilinear map at a point
-/

open scoped ComplexConjugate
noncomputable section

variable {n : ℕ}
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {ι : Type}
variable {R A B E : Type} [Semiring R]

theorem ContinuousMultilinearMap.toFun_eq_coe {R A B : Type} [Semiring R] [AddCommMonoid A]
    [Module R A] [TopologicalSpace A] [AddCommMonoid B] [Module R B] [TopologicalSpace B]
    (f : ContinuousMultilinearMap R (fun _ : Fin n ↦ A) B) : f.toFun = ⇑f := by
  rw [MultilinearMap.toFun_eq_coe]; simp

/-- `fst` as a `ContinuousMultilinearMap` -/
def fstCmmap (R : Type) (A B : Type) [Semiring R] [AddCommMonoid A] [Module R A]
    [TopologicalSpace A] [AddCommMonoid B] [Module R B] [TopologicalSpace B] :
    ContinuousMultilinearMap R (fun _ : Fin 1 ↦ A × B) A :=
  ContinuousMultilinearMap.ofSubsingleton R (A × B) A (0 : Fin 1) (ContinuousLinearMap.fst R A B)

/-- `snd` as a `ContinuousMultilinearMap` -/
def sndCmmap (R : Type) (A B : Type) [Semiring R] [AddCommMonoid A] [Module R A]
    [TopologicalSpace A] [AddCommMonoid B] [Module R B] [TopologicalSpace B] :
    ContinuousMultilinearMap R (fun _ : Fin 1 ↦ A × B) B :=
  ContinuousMultilinearMap.ofSubsingleton R (A × B) B (0 : Fin 1) (ContinuousLinearMap.snd R A B)

theorem fstCmmap_apply [AddCommMonoid A] [Module R A] [TopologicalSpace A] [AddCommMonoid B]
    [Module R B] [TopologicalSpace B] (a : A) (b : B) : (fstCmmap R A B fun _ ↦ (a, b)) = a := by
  simp only [fstCmmap, ContinuousMultilinearMap.ofSubsingleton_apply_apply,
    ContinuousLinearMap.coe_fst']

theorem sndCmmap_apply [AddCommMonoid A] [Module R A] [TopologicalSpace A] [AddCommMonoid B]
    [Module R B] [TopologicalSpace B] (a : A) (b : B) : (sndCmmap R A B fun _ ↦ (a, b)) = b := by
  simp only [sndCmmap, ContinuousMultilinearMap.ofSubsingleton_apply_apply,
    ContinuousLinearMap.coe_snd']

theorem fstCmmap_norm [NormedRing A] [NormedAlgebra 𝕜 A] [NormOneClass A] [NormedRing B]
    [NormedAlgebra 𝕜 B] [NormOneClass B] : ‖fstCmmap 𝕜 A B‖ = 1 := by
  apply le_antisymm
  · refine (fstCmmap 𝕜 A B).opNorm_le_bound (M := 1) (by norm_num) ?_
    intro z; simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, one_mul]
    have e : z = (fun _ ↦ ((z 0).1, (z 0).2)) := by apply funext; intro i; rw [Fin.eq_zero i]
    rw [e]
    rw [fstCmmap_apply]; simp; exact norm_fst_le (z 0)
  · have lo := (fstCmmap 𝕜 A B).unit_le_opNorm (m := fun _ ↦ (1, 1)) ?_
    rw [fstCmmap_apply, norm_one] at lo; assumption
    rw [pi_norm_le_iff_of_nonneg]; intro i; simp only [Prod.norm_def, norm_one]
    repeat norm_num

theorem sndCmmap_norm [NormedRing A] [NormedAlgebra 𝕜 A] [NormOneClass A] [NormedRing B]
    [NormedAlgebra 𝕜 B] [NormOneClass B] : ‖sndCmmap 𝕜 A B‖ = 1 := by
  apply le_antisymm
  · apply (sndCmmap 𝕜 A B).opNorm_le_bound (M := 1) (by norm_num)
    intro z; simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, one_mul]
    have e : z = (fun _ ↦ ((z 0).1, (z 0).2)) := by apply funext; intro i; rw [Fin.eq_zero i]
    rw [e]
    rw [sndCmmap_apply]; simp; exact norm_snd_le (z 0)
  · have lo := (sndCmmap 𝕜 A B).unit_le_opNorm (m := fun _ ↦ (1, 1)) ?_
    rw [sndCmmap_apply, norm_one] at lo; assumption
    rw [pi_norm_le_iff_of_nonneg]; intro i; simp only [Prod.norm_def, norm_one]
    repeat norm_num

-- Lemmas for `smulCmmap`
theorem update_0_0 (z : Fin (n + 1) → A) (x : A) :
    Function.update (fun _ : Fin 1 ↦ z 0) 0 x = (fun _ : Fin 1 ↦ x) := by
  apply funext; intro i
  have i0 : i = 0 := by simp only [eq_iff_true_of_subsingleton]
  rw [i0]; simp only [Function.update_self]

theorem update_0_succ (d : DecidableEq (Fin (n + 1))) (f : Fin (n + 1) → A) (x : A) (i : Fin n) :
    @Function.update _ _ d f 0 x i.succ = f i.succ := by
  rw [Function.update_apply]; simp only [ite_eq_right_iff]
  have i0 := Fin.succ_ne_zero i
  intro h; exfalso; exact i0 h

theorem update_nz_0 (d : DecidableEq (Fin (n + 1))) (f : Fin (n + 1) → A) {x : A} {i : Fin (n + 1)}
    (i0 : i ≠ 0) : @Function.update _ _ d f i x 0 = f 0 := by rw [Function.update_of_ne i0.symm]

theorem update_nz_succ (d : DecidableEq (Fin (n + 1))) (f : Fin (n + 1) → A) (x : A)
    {i : Fin (n + 1)} (i0 : i ≠ 0) :
    (fun j : Fin n ↦ @Function.update _ _ d f i x j.succ) =
      Function.update (fun j : Fin n ↦ f j.succ) (i.pred i0) x := by
  apply funext; intro k
  by_cases ki : k.succ = i
  · have ki' : k = i.pred i0 := by simp_rw [← ki, Fin.pred_succ]
    rw [ki, ki']; rw [Function.update_self]; rw [Function.update_self]
  · rw [Function.update_of_ne ki]
    rw [Function.update_of_ne _]
    by_contra h
    simp only [h, Fin.succ_pred, not_true_eq_false] at ki

/-- Raw cons of two continuous multilinear maps -/
def smulCmmapFn [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] [NormedAddCommGroup B]
    [NormedSpace 𝕜 B] (x : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) 𝕜)
    (xs : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) B) : (∀ _ : Fin (n + 1), A) → B :=
  fun z ↦ (x.toFun (fun _ ↦ z 0)) • xs.toFun (fun i ↦ z i.succ)

/-- `smulCmmapFn` is multiadditive -/
theorem smul_cmmap_add [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] [NormedAddCommGroup B]
    [NormedSpace 𝕜 B] (x : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) 𝕜)
    (xs : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) B) :
    ∀ (d : DecidableEq (Fin (n + 1))) (z : ∀ _ : Fin (n + 1), A) (i : Fin (n + 1)) (u v : A),
      smulCmmapFn x xs (@Function.update _ _ d z i (u + v)) =
        smulCmmapFn x xs (@Function.update _ _ d z i u) +
          smulCmmapFn x xs (@Function.update _ _ d z i v) := by
  intro d z i u v
  by_cases i0 : i = 0
  · rw [i0]
    have uv := x.map_update_add (fun _ ↦ z 0) 0 u v
    simp only [update_0_0 z _] at uv
    simp only [Function.update_self, MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe,
      uv, add_smul, smulCmmapFn, update_0_succ]
  · simp only [smul_add, update_nz_0 d z i0, MultilinearMap.toFun_eq_coe,
    ContinuousMultilinearMap.coe_coe, update_nz_succ d z _ i0, MultilinearMap.map_update_add,
    smul_add, smulCmmapFn]

/-- `smulCmmapFn` commutes with scalars -/
theorem smul_cmmap_smul [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] [NormedAddCommGroup B]
    [NormedSpace 𝕜 B] (x : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) 𝕜)
    (xs : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) B) :
    ∀ (d : DecidableEq (Fin (n + 1))) (z : ∀ _ : Fin (n + 1), A) (i : Fin (n + 1)) (s : 𝕜) (u : A),
      smulCmmapFn x xs (@Function.update _ _ d z i (s • u)) =
        s • smulCmmapFn x xs (@Function.update _ _ d z i u) := by
  intro d z i s u
  rw [smulCmmapFn]
  by_cases i0 : i = 0
  · rw [i0]
    have su := x.map_update_smul (fun _ ↦ z 0) 0 s u
    rw [update_0_0 z _, update_0_0 z _] at su
    simp only [Function.update_self, MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe,
      su, smul_eq_mul, update_0_succ d z _ _, smulCmmapFn, ← smul_assoc]
  · have su := xs.map_update_smul (fun j ↦ z j.succ) (i.pred i0) s u
    simp only [MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe, update_nz_0 d z i0,
      update_nz_succ d z _ i0, su, smul_comm _ s, smulCmmapFn]

/-- `smulCmmapFn` is continuous -/
theorem smul_cmmap_cont [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] [NormedAddCommGroup B]
    [NormedSpace 𝕜 B] (x : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) 𝕜)
    (xs : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) B) : Continuous (smulCmmapFn x xs) := by
  apply Continuous.smul; repeat continuity

/-- Cons two `ContinuousMultilinearMap`s together, combining values via `•` -/
def smulCmmap (𝕜 A B : Type) [NontriviallyNormedField 𝕜] [AddCommMonoid A] [Module 𝕜 A]
    [TopologicalSpace A] [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    (x : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) 𝕜)
    (xs : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) B) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) B where
  toFun := smulCmmapFn x xs
  map_update_add' := smul_cmmap_add x xs _
  map_update_smul' := smul_cmmap_smul x xs _
  cont := smul_cmmap_cont x xs

theorem smulCmmap_apply [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] [NormedAddCommGroup B]
    [NormedSpace 𝕜 B] (x : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) 𝕜)
    (xs : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) B) (z : ∀ _ : Fin (n + 1), A) :
    smulCmmap _ _ _ x xs z = (x fun _ ↦ z 0) • xs fun i ↦ z i.succ := by
  rw [smulCmmap, ←ContinuousMultilinearMap.toFun_eq_coe]; simp only; rfl

theorem smulCmmap_norm [NormedAddCommGroup A] [NormedSpace 𝕜 A] [NormedAddCommGroup B]
    [NormedSpace 𝕜 B] (x : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) 𝕜)
    (xs : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) B) :
    ‖smulCmmap 𝕜 A B x xs‖ ≤ ‖x‖ * ‖xs‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound; bound
  intro z; rw [smulCmmap_apply]
  have xb := ContinuousMultilinearMap.le_opNorm x fun _ : Fin 1 ↦ z 0
  have xsb := ContinuousMultilinearMap.le_opNorm xs fun i : Fin n ↦ z i.succ
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_const, Finset.card_singleton,
    pow_one] at xb xsb
  have e0 := Fin.prod_cons ‖z 0‖ fun i : Fin n ↦ ‖z i.succ‖
  have e1 : ‖z 0‖ = (fun i : Fin (n + 1) ↦ ‖z i‖) 0 := rfl
  have e2 : (fun i : Fin n ↦ ‖z i.succ‖) = Fin.tail fun i : Fin (n + 1) ↦ ‖z i‖ := rfl
  nth_rw 1 [e1] at e0; nth_rw 1 [e2] at e0; rw [Fin.cons_self_tail (fun i ↦ ‖z i‖)] at e0
  calc ‖(x fun _ : Fin 1 ↦ z 0) • xs fun i : Fin n ↦ z i.succ‖
    _ ≤ ‖x‖ * ‖z 0‖ * (‖xs‖ * Finset.univ.prod fun i : Fin n ↦ ‖z i.succ‖) := by
      rw [norm_smul]; bound
    _ = ‖x‖ * ‖xs‖ * (‖z 0‖ * Finset.univ.prod fun i : Fin n ↦ ‖z i.succ‖) := by ring
    _ = ‖x‖ * ‖xs‖ * Finset.univ.prod fun i : Fin (n + 1) ↦ ‖z i‖ := by rw [←e0]

/-- A term of the general `n`-linear map on `𝕜 × 1𝕜,
    equal to `z0^k * z1^(n-k)` when applied to `fun _ ↦ (z0,z1)` -/
noncomputable def termCmmap (𝕜 : Type) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] : ∀ n : ℕ, ℕ → E → ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ 𝕜 × 𝕜) E
  | 0 => fun _ x ↦ ContinuousMultilinearMap.constOfIsEmpty _ _ x
  | n + 1 => fun k x ↦
    smulCmmap _ _ _ (if n < k then fstCmmap 𝕜 𝕜 𝕜 else sndCmmap 𝕜 𝕜 𝕜) (termCmmap 𝕜 n k x)

theorem termCmmap_apply [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SMulCommClass 𝕜 𝕜 E]
    [IsScalarTower 𝕜 𝕜 E] (n k : ℕ) (a b : 𝕜) (x : E) :
    (termCmmap 𝕜 n k x fun _ ↦ (a, b)) = a ^ min k n • b ^ (n - k) • x := by
  induction' n with n h
  · simp only [termCmmap, ContinuousMultilinearMap.constOfIsEmpty_apply, min_zero, pow_zero,
    zero_tsub, one_smul]
  · rw [termCmmap, smulCmmap_apply, h]
    by_cases nk : n < k
    · have nsk : n.succ ≤ k := Nat.succ_le_iff.mpr nk
      simp only [nk, if_true, fstCmmap_apply, min_eq_right nk.le, min_eq_right nsk,
        Nat.sub_eq_zero_of_le nk.le, Nat.sub_eq_zero_of_le nsk, pow_zero, one_smul, smul_smul,
        pow_succ']
    · simp [nk]; simp at nk
      rw [sndCmmap_apply]
      have nsk : k ≤ n.succ := Nat.le_succ_of_le nk
      rw [min_eq_left nk, min_eq_left nsk]
      rw [smul_comm b _, ← smul_assoc b _ _, smul_eq_mul, ← pow_succ', ← Nat.sub_add_comm nk]

theorem termCmmap_norm (𝕜 : Type) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (n k : ℕ) (x : E) : ‖termCmmap 𝕜 n k x‖ ≤ ‖x‖ := by
  induction' n with n nh
  · simp only [termCmmap, le_refl, ContinuousMultilinearMap.norm_constOfIsEmpty]
  · rw [termCmmap]; simp only
    generalize ht : termCmmap 𝕜 n k x = t; rw [ht] at nh
    have tn := smulCmmap_norm (if n < k then fstCmmap 𝕜 𝕜 𝕜 else sndCmmap 𝕜 𝕜 𝕜) t
    by_cases nk : n < k
    · simp [nk] at tn ⊢; rw [fstCmmap_norm] at tn; simp at tn; exact _root_.trans tn nh
    · simp [nk] at tn ⊢; rw [sndCmmap_norm] at tn; simp at tn; exact _root_.trans tn nh

/-- `conj` as a `ContinuousLinearMap`. This is `starₗᵢ ℂ`, but with a simpler type. -/
def conjCLM : ℂ →L[ℝ] ℂ where
  toFun z := conj z
  map_add' := by simp only [map_add, forall_const]
  map_smul' := by simp only [Complex.real_smul, map_mul, RingHom.id_apply, Complex.conj_ofReal,
    implies_true]

theorem conjCLM_apply (z : ℂ) : conjCLM z = conj z := by rfl

/-- The continuous linear map that evaluates a continuous multilinear map at a point -/
def cmmapApplyCmap (𝕜 : Type) {I : Type} (A : I → Type) (B : Type) [Fintype I]
    [NontriviallyNormedField 𝕜] [∀ i, NormedAddCommGroup (A i)] [∀ i, NormedSpace 𝕜 (A i)]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B] (x : ∀ i, A i) : ContinuousMultilinearMap 𝕜 A B →L[𝕜] B
    where
  toFun f := f x
  map_add' := by simp
  map_smul' := by simp
  cont := by simp [continuous_eval_const]

@[simp] theorem cmmapApplyCmap_apply {I : Type} (A : I → Type) (B : Type) [Fintype I]
    [∀ i, NormedAddCommGroup (A i)] [∀ i, NormedSpace 𝕜 (A i)]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B] (x : ∀ i, A i) (f : ContinuousMultilinearMap 𝕜 A B) :
    cmmapApplyCmap 𝕜 A B x f = f x := by rfl

/-- Prove `A x = 0` by `x = 0` for a continuous linear map `A` -/
lemma ContinuousLinearMap.apply_eq_zero_of_eq_zero {𝕜 X Y : Type} [NormedField 𝕜]
    [TopologicalSpace X] [NormedAddCommGroup X] [Module 𝕜 X] [NormedAddCommGroup Y] [Module 𝕜 Y]
    (f : X →L[𝕜] Y) {x : X} (h : x = 0) : f x = 0 := by
  rw [h, ContinuousLinearMap.map_zero]

/-- `.smulRight` is nonzero if it's inputs are -/
lemma ContinuousLinearMap.smulRight_ne_zero {R A B : Type} [Ring R] [TopologicalSpace A]
    [AddCommMonoid A] [TopologicalSpace R] [Module R A] [TopologicalSpace B] [AddCommMonoid B]
    [Module R B] [ContinuousSMul R B] [NoZeroSMulDivisors R B] {c : A →L[R] R} {f : B}
    (c0 : c ≠ 0) (f0 : f ≠ 0) :
    c.smulRight f ≠ 0 := by
  rcases ContinuousLinearMap.exists_ne_zero c0 with ⟨x,cx⟩
  simp only [Ne, ContinuousLinearMap.ext_iff, not_forall, _root_.zero_apply,
    ContinuousLinearMap.smulRight_apply]
  exact ⟨x, fun h ↦ (eq_zero_or_eq_zero_of_smul_eq_zero h).elim cx f0⟩

/-- `1 ≠ 0`, `ContinuousLinearMap` case -/
lemma ContinuousLinearMap.one_ne_zero {R A : Type} [Ring R] [TopologicalSpace A]
    [AddCommMonoid A] [Module R A] [Nontrivial A] : (1 : A →L[R] A) ≠ 0 := by
  simp only [Ne, ContinuousLinearMap.ext_iff, not_forall, _root_.zero_apply,
    _root_.one_apply_eq_self]
  apply exists_ne

/-- `mkPiRing` is continuous -/
lemma ContinuousMultilinearMap.continuous_mkPiRing {𝕜 ι E : Type} [NontriviallyNormedField 𝕜]
    [Fintype ι] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
    Continuous (fun z : E ↦ ContinuousMultilinearMap.mkPiRing 𝕜 ι z) := by
  rw [Metric.continuous_iff]
  intro x e e0
  refine ⟨e / 2, by bound, fun y xy ↦ ?_⟩
  simp only [dist_eq_norm] at xy
  refine lt_of_le_of_lt (b := e / 2) ?_ (by bound)
  rw [dist_eq_norm, ContinuousMultilinearMap.opNorm_le_iff (by bound)]
  intro m
  simp only [_root_.sub_apply, ContinuousMultilinearMap.mkPiRing_apply,
    ← smul_sub]
  refine le_trans (norm_smul_le _ _) ?_
  rw [mul_comm]
  bound

/-!
### Conjugate a `ContinuousMultilinearMap` with complex `conj`
-/

/-- Conjugate a `ContinuousMultilinearMap` with complex `conj` -/
def ContinuousMultilinearMap.conj_conj [Fintype ι]
    (m : ContinuousMultilinearMap ℂ (fun _ : ι ↦ ℂ) ℂ) :
    ContinuousMultilinearMap ℂ (fun _ : ι ↦ ℂ) ℂ where
  toFun := fun z ↦ conj (m fun i ↦ conj (z i))
  map_update_add' g a x y := by
    simp only [← map_add, Function.apply_update (fun _ z ↦ conj z) (g := g), ← m.map_update_add]
  map_update_smul' g a s y := by
    simp only [smul_eq_mul, Function.apply_update (fun _ z ↦ conj z) (g := g), map_mul]
    simp only [← smul_eq_mul, m.map_update_smul]
    simp only [smul_eq_mul, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  cont := by continuity

@[simp] lemma ContinuousMultilinearMap.conj_conj_apply [Fintype ι]
    (m : ContinuousMultilinearMap ℂ (fun _ : ι ↦ ℂ) ℂ) (x : ι → ℂ) :
    m.conj_conj x = conj (m fun i ↦ conj (x i)) := by rfl

end
end Ray_Ray_Misc_Multilinear

-- ===== Ray.Misc.Topology =====
section Ray_Ray_Misc_Topology
/-!
## Various topology lemmas
-/

open Classical
open Metric (ball closedBall sphere mem_sphere mem_ball)
open Filter
open OrderDual (ofDual toDual)
open Set
open scoped Real NNReal Topology Filter ENNReal
noncomputable section

/-- Uniform cauchy sequences on compact sets are uniformly bounded -/
theorem UniformCauchySeqOn.bounded {X Y : Type} [TopologicalSpace X] [NormedAddCommGroup Y]
    {f : ℕ → X → Y} {s : Set X} (u : UniformCauchySeqOn f atTop s) (fc : ∀ n, ContinuousOn (f n) s)
    (sc : IsCompact s) : ∃ b : ℝ, 0 ≤ b ∧ ∀ n x, x ∈ s → ‖f n x‖ ≤ b := by
  generalize hc : (fun n ↦ Classical.choose ((sc.bddAbove_image (fc n).norm).exists_ge 0)) = c
  have cs : ∀ n, 0 ≤ c n ∧ ∀ x, x ∈ s → ‖f n x‖ ≤ c n := fun n ↦ by
    simpa only [← hc, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] using
      Classical.choose_spec ((sc.bddAbove_image (fc n).norm).exists_ge 0)
  rw [Metric.uniformCauchySeqOn_iff] at u
  rcases u 1 (by norm_num) with ⟨N, H⟩; clear u
  generalize hbs : Finset.image c (Finset.range (N + 1)) = bs
  have c0 : c 0 ∈ bs := by simp [← hbs]; exists 0; simp
  generalize hb : 1 + bs.max' ⟨_, c0⟩ = b
  exists b; constructor
  · rw [← hb]; exact add_nonneg (by norm_num) (_root_.trans (cs 0).1 (Finset.le_max' _ _ c0))
  · intro n x xs
    by_cases nN : n ≤ N
    · have cn : c n ∈ bs := by simp [← hbs]; exists n
      exact _root_.trans ((cs n).2 x xs) (_root_.trans (Finset.le_max' _ _ cn)
        (by simp only [le_add_iff_nonneg_left, zero_le_one, ← hb]))
    · simp at nN
      specialize H N le_rfl n nN.le x xs
      have cN : c N ∈ bs := by simp [← hbs]; exists N
      have bN := _root_.trans ((cs N).2 x xs) (Finset.le_max' _ _ cN)
      rw [dist_eq_norm] at H
      calc ‖f n x‖ = ‖f N x - (f N x - f n x)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖f N x‖ + ‖f N x - f n x‖ := norm_sub_le _ _
        _ ≤ bs.max' _ + 1 := add_le_add bN H.le
        _ = 1 + bs.max' ⟨_, c0⟩ := by rw [add_comm]
        _ = b := by simp only [hb]

/-- `{b | (a,b) ∈ s}` is open if `s` is open -/
theorem IsOpen.snd_preimage {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {s : Set (A × B)} (o : IsOpen s) (a : A) : IsOpen {b | (a, b) ∈ s} :=
  o.preimage (Continuous.prodMk_right a)

/-- `{b | (a,b) ∈ s}` is closed if `s` is closed -/
theorem IsClosed.snd_preimage {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {s : Set (A × B)} (c : IsClosed s) (a : A) : IsClosed {b | (a, b) ∈ s} :=
  c.preimage (Continuous.prodMk_right a)

/-- Tendsto commutes with ⁻¹ away from zero -/
theorem tendsto_inv_iff_tendsto {A B : Type} [NontriviallyNormedField B]
    {l : Filter A} {f : A → B} {a : B} (a0 : a ≠ 0) :
    Tendsto (fun x ↦ (f x)⁻¹) l (𝓝 a⁻¹) ↔ Tendsto f l (𝓝 a) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.inv₀ a0⟩
  have h := h.inv₀ (inv_ne_zero a0)
  field_simp [a0] at h; exact h

/-- If `f x ∈ s` for `s ∈ 𝓝 (f x)` and `f` continuous at `z`, `∈` holds locally -/
theorem ContinuousAt.eventually_mem_nhd {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} {x : A} (fc : ContinuousAt f x) {s : Set B} (m : s ∈ 𝓝 (f x)) :
    ∀ᶠ y in 𝓝 x, f y ∈ s :=
  (eventually_mem_nhds_iff.2 (fc m)).mono fun _x hx ↦ mem_preimage.1 (mem_of_mem_nhds hx)

/-- The reverse direction of `IsClosed.Icc_subset_of_forall_mem_nhdsWithin` -/
theorem IsClosed.Icc_subset_of_forall_mem_nhds_within' {X : Type}
    [ConditionallyCompleteLinearOrder X] [TopologicalSpace X] [OrderTopology X] [DenselyOrdered X]
    {a b : X} {s : Set X} (sc : IsClosed (s ∩ Icc a b)) (sb : b ∈ s)
    (so : ∀ x, x ∈ s ∩ Ioc a b → s ∈ 𝓝[Iio x] x) : Icc a b ⊆ s := by
  generalize hs' : ofDual ⁻¹' s = s'
  have rev : Icc (toDual b) (toDual a) ⊆ s' := by
    apply IsClosed.Icc_subset_of_forall_mem_nhdsWithin
    · have e : s' ∩ Icc (toDual b) (toDual a) = ofDual ⁻¹' (s ∩ Icc a b) := by
        apply Set.ext; intro x; simp only [Set.Icc_toDual, Set.preimage_inter, ← hs']
      rw [e]; exact IsClosed.preimage continuous_ofDual sc
    · simp only [Set.mem_preimage, OrderDual.ofDual_toDual, sb, ← hs']
    · intro x m
      simp only [Set.mem_inter_iff, Set.mem_Ico, OrderDual.toDual_le, OrderDual.lt_toDual] at m
      simp only [mem_nhdsWithin_iff_eventually, eventually_nhds_iff, Set.mem_inter_iff,
        Set.mem_Ioc, ← hs'] at so m ⊢
      rcases so (ofDual x) ⟨m.1, m.2.2, m.2.1⟩ with ⟨n, h, o, nx⟩
      use ofDual ⁻¹' n
      refine ⟨?_, o.preimage continuous_ofDual, mem_preimage.mpr nx⟩
      intro y m xy; simp only [Set.mem_Ioi] at xy; simp only [Set.mem_preimage]
      simp only [Set.mem_Iio] at h
      exact h _ m xy
  intro x m; simp only [Set.mem_Icc] at m; specialize @rev (toDual x)
  simp only [Set.Icc_toDual, Set.mem_preimage, Set.mem_Icc, and_imp, OrderDual.ofDual_toDual,
    ← hs'] at rev
  exact rev m.1 m.2

lemma IsPreconnected.sUnion_of_pairwise_exists_isPreconnected {X : Type*} [TopologicalSpace X]
    {S : Set (Set X)} (hSc : ∀ s ∈ S, IsPreconnected s)
    (h : S.Pairwise fun s t ↦ s.Nonempty → t.Nonempty →
      ∃ u, u ⊆ ⋃₀ S ∧ (s ∩ u).Nonempty ∧ (u ∩ t).Nonempty ∧ IsPreconnected u) :
    IsPreconnected (⋃₀ S) := by
  refine isPreconnected_of_forall_pair fun x hx y hy ↦ ?_
  rcases mem_sUnion.1 hx with ⟨s, hs, hxs⟩
  rcases mem_sUnion.1 hy with ⟨t, ht, hyt⟩
  rcases eq_or_ne s t with rfl | hst
  · exact ⟨s, subset_sUnion_of_mem hs, hxs, hyt, hSc s hs⟩
  · rcases h hs ht hst ⟨x, hxs⟩ ⟨y, hyt⟩ with ⟨u, huS, hsu, hut, hu⟩
    refine ⟨s ∪ u ∪ t, ?_, ?_, ?_, ?_⟩
    · simp [*, subset_sUnion_of_mem]
    · simp [*]
    · simp [*]
    · refine ((hSc s hs).union' hsu hu).union' (hut.mono ?_) (hSc t ht)
      exact inter_subset_inter_left _ subset_union_right

lemma IsPreconnected.iUnion_of_pairwise_exists_isPreconnected {ι X : Type*} [TopologicalSpace X]
    {s : ι → Set X} (hsc : ∀ i, IsPreconnected (s i))
    (h : Pairwise fun i j ↦ (s i).Nonempty → (s j).Nonempty →
      ∃ u, u ⊆ ⋃ i, s i ∧ (s i ∩ u).Nonempty ∧ (u ∩ s j).Nonempty ∧ IsPreconnected u) :
    IsPreconnected (⋃ i, s i) := by
  apply IsPreconnected.sUnion_of_pairwise_exists_isPreconnected (forall_mem_range.2 hsc)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
  exact h (ne_of_apply_ne s hij)

/-- Open preconnected sets form a basis for `𝓝ˢ t` in any locally connected space,
    if `t` is preconnected -/
theorem local_preconnected_nhdsSet {X : Type} [TopologicalSpace X]
    [lc : LocallyConnectedSpace X] {s t : Set X} (tc : IsPreconnected t) (st : s ∈ 𝓝ˢ t) :
    ∃ c, IsOpen c ∧ t ⊆ c ∧ c ⊆ s ∧ IsPreconnected c := by
  rw [← subset_interior_iff_mem_nhdsSet] at st
  have hsub : t ⊆ ⋃ x : t, connectedComponentIn (interior s) x := fun x hx ↦
    mem_iUnion.2 ⟨⟨x, hx⟩, mem_connectedComponentIn (st hx)⟩
  refine ⟨_, isOpen_iUnion fun _ ↦ isOpen_interior.connectedComponentIn, hsub,
    iUnion_subset fun x ↦ ?_, ?_⟩
  · exact (connectedComponentIn_subset _ _).trans interior_subset
  · apply IsPreconnected.iUnion_of_pairwise_exists_isPreconnected
    · exact fun _ ↦ isPreconnected_connectedComponentIn
    · exact fun x y _ _ _ ↦ ⟨t, hsub, ⟨x, mem_connectedComponentIn (st x.2), x.2⟩,
        ⟨y, y.2, mem_connectedComponentIn (st y.2)⟩, tc⟩

/-- Open connected sets form a basis for `𝓝ˢ t` in any locally connected space,
    if `t` is connected -/
theorem local_connected_nhdsSet {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {s t : Set X} (tc : IsConnected t) (st : s ∈ 𝓝ˢ t) :
    ∃ c, IsOpen c ∧ t ⊆ c ∧ c ⊆ s ∧ IsConnected c :=
  let ⟨c, hco, htc, hcs, hc⟩ := local_preconnected_nhdsSet tc.2 st
  ⟨c, hco, htc, hcs, tc.1.mono htc, hc⟩

open Filter in
/-- `p` and `q` occur frequently along two filters iff `p ∧ q` occurs frequently in the product
    filter -/
theorem Prod.frequently {A B : Type} {f : Filter A} {g : Filter B} {p : A → Prop}
    {q : B → Prop} :
    (∃ᶠ x : A × B in f ×ˢ g, p x.1 ∧ q x.2) ↔ (∃ᶠ a in f, p a) ∧ ∃ᶠ b in g, q b := by
  simp only [frequently_iff_neBot, ← prod_neBot, ← prod_inf_prod, prod_principal_principal]
  rfl

/-- The product of `MapClusterPt` and `Tendsto` is `MapClusterPt` -/
theorem MapClusterPt.prod {A B C : Type} [TopologicalSpace B] [TopologicalSpace C]
    {f : A → B} {g : A → C} {a : Filter A} {b : B} {c : C}
    (fa : MapClusterPt b a f) (ga : Tendsto g a (𝓝 c)) :
    MapClusterPt (b, c) a fun x ↦ (f x, g x) := by
  rw [mapClusterPt_iff_frequently] at fa ⊢; intro s n
  rcases mem_nhds_prod_iff.mp n with ⟨u, un, v, vn, sub⟩
  apply (fa _ un).mp
  apply (Filter.tendsto_iff_forall_eventually_mem.mp ga v vn).mp
  exact .of_forall fun x gv fu ↦ sub (mk_mem_prod fu gv)

/-- If we converge to `g`, we're eventually greater than anything less than `g` -/
theorem Filter.Tendsto.exists_lt {X : Type} [LinearOrder X] [TopologicalSpace X]
    [OrderClosedTopology X] {f : ℕ → X} {g : X} (tend : Tendsto f atTop (𝓝 g)) :
    ∀ {x}, x < g → ∃ n, x < f n := fun hx ↦
  (tend.eventually (eventually_gt_nhds hx)).exists

/-- `≠ → eventual ≠` -/
theorem Ne.eventually_ne {X : Type} [TopologicalSpace X] [T2Space X] {x y : X} (h : x ≠ y) :
    ∀ᶠ q : X × X in 𝓝 (x, y), q.1 ≠ q.2 :=
  (isOpen_ne_fun continuous_fst continuous_snd).mem_nhds h

/-- The `⊥` filter has no cluster_pts -/
lemma ClusterPt.bot {X : Type} [TopologicalSpace X] {x : X} : ¬ClusterPt x ⊥ := fun h ↦
  (h.neBot.mono inf_le_right).ne rfl

/-- Version of `nhdsWithin_eq_iff_eventuallyEq` that doesn't misuse eventual equality -/
lemma nhdsWithin_eq_iff_eventuallyEq' {X : Type} [TopologicalSpace X] {s t : Set X} {x : X} :
    𝓝[s] x = 𝓝[t] x ↔ (· ∈ s) =ᶠ[𝓝 x] (· ∈ t) :=
  nhdsWithin_eq_iff_eventuallyEq

/-- `ContinuousWithinAt` depends only locally on the set -/
lemma ContinuousWithinAt.congr_set'' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s t : Set X} {x : X} (fc : ContinuousWithinAt f s x)
    (hst : (· ∈ s) =ᶠ[𝓝 x] (· ∈ t)) : ContinuousWithinAt f t x := by
  simpa only [ContinuousWithinAt, nhdsWithin_eq_iff_eventuallyEq'.mpr hst] using fc

/-- Turn eventual equality into an intersection into eventual equality w.r.t. `𝓝[s] x` -/
lemma eventuallyEq_inter {X : Type} [TopologicalSpace X] {s t u : Set X} {x : X} :
    (· ∈ t ∩ s) =ᶠ[𝓝 x] (· ∈ u ∩ s) ↔ (· ∈ t) =ᶠ[𝓝[s] x] (· ∈ u) := by
  rw [Filter.EventuallyEq, eventuallyEq_nhdsWithin_iff]
  simp only [mem_inter_iff, eq_iff_iff, and_congr_left_iff]

/-- Given a closed ball in an open set, we can expand the ball to a larger open ball -/
lemma exists_ball_superset {X : Type} [MetricSpace X] [ProperSpace X] {s : Set X} {x : X}
    {r : ℝ} (sub : closedBall x r ⊆ s) (o : IsOpen s) : ∃ t, r < t ∧ ball x t ⊆ s := by
  by_cases n : closedBall x (r + 1) \ s = ∅
  · simp only [sdiff_eq_empty] at n
    exact ⟨r + 1, by linarith, subset_trans Metric.ball_subset_closedBall n⟩
  simp only [← nonempty_iff_ne_empty] at n
  have c : IsCompact (closedBall x (r + 1) \ s) := (isCompact_closedBall x (r + 1)).diff o
  have d : Continuous fun y ↦ dist x y := continuous_const.dist continuous_id
  obtain ⟨y, ⟨yr, ys⟩, h⟩ := c.exists_isMinOn n d.continuousOn
  refine ⟨dist x y, ?_, ?_⟩
  · contrapose ys
    simp only [not_lt] at ys ⊢
    apply sub
    simpa only [Metric.mem_closedBall, dist_comm]
  · intro z m
    by_contra zs
    simp only [isMinOn_iff, Set.mem_sdiff, Metric.mem_closedBall, dist_comm, and_imp,
      mem_ball] at h m yr
    specialize h z (le_trans m.le yr) zs
    linarith

/-- Eventually in terms of radii -/
lemma eventually_nhdsGT_zero_ball_iff_nhds {X : Type} [MetricSpace X] {c : X} {p : X → Prop} :
    (∀ᶠ r in 𝓝[>] 0, ∀ x ∈ ball c r, p x) ↔ ∀ᶠ x in 𝓝 c, p x := by
  simp only [(nhdsGT_basis (0 : ℝ)).eventually_iff, Metric.nhds_basis_ball.eventually_iff]
  constructor
  · intro ⟨r,r0,h⟩
    exact ⟨r/2, by bound, fun x m ↦ @h (r/2) (by simpa) _ m⟩
  · intro ⟨r,r0,h⟩
    refine ⟨r, by bound, fun s sr x m ↦ @h _ ?_⟩
    simp only [Metric.mem_ball, mem_Ioo] at m sr ⊢
    linarith

/-- Eventually in terms of radii and closed balls -/
lemma eventually_nhdsGT_zero_closedBall_iff_nhds {X : Type} [MetricSpace X] {c : X} {p : X → Prop} :
    (∀ᶠ r in 𝓝[>] 0, ∀ x ∈ closedBall c r, p x) ↔ ∀ᶠ x in 𝓝 c, p x := by
  simp only [(nhdsGT_basis (0 : ℝ)).eventually_iff, Metric.nhds_basis_closedBall.eventually_iff]
  constructor
  · intro ⟨r,r0,h⟩
    exact ⟨r/2, by bound, fun x m ↦ @h (r/2) (by simpa) _ m⟩
  · intro ⟨r,r0,h⟩
    refine ⟨r, by bound, fun s sr x m ↦ @h _ ?_⟩
    simp only [Metric.mem_closedBall, mem_Ioo] at m sr ⊢
    linarith

/-- Eventually in terms of radii and spheres -/
lemma eventually_nhdsGT_zero_sphere_of_nhds {X : Type} [MetricSpace X] {c : X} {p : X → Prop}
    (h : ∀ᶠ x in 𝓝 c, p x) : (∀ᶠ r in 𝓝[>] 0, ∀ x ∈ sphere c r, p x) := by
  simp only [(nhdsGT_basis (0 : ℝ)).eventually_iff,
    Metric.nhds_basis_closedBall.eventually_iff] at h ⊢
  obtain ⟨r,r0,h⟩ := h
  refine ⟨r, by bound, fun s sr x m ↦ @h _ ?_⟩
  simp only [Metric.mem_sphere, mem_Ioo, Metric.mem_closedBall] at m sr ⊢
  rw [← m] at sr
  exact sr.2.le

/-- Flip `atTop` to `𝓝[>] 0` -/
lemma eventually_atTop_iff_nhdsGT_zero {p : ℝ → Prop} :
    (∀ᶠ r in atTop, p r) ↔ ∀ᶠ r in 𝓝[>] 0, p r⁻¹ := by
  simp only [Filter.eventually_atTop, (nhdsGT_basis (0 : ℝ)).eventually_iff]
  constructor
  · intro ⟨r,h⟩
    refine ⟨(max 1 r)⁻¹, by bound, fun s m ↦ h _ ?_⟩
    rw [mem_Ioo, lt_inv_comm₀, max_lt_iff] at m
    all_goals bound
  · intro ⟨r,r0,h⟩
    refine ⟨2 * r⁻¹, fun s m ↦ ?_⟩
    refine inv_inv s ▸ @h s⁻¹ ?_
    simp only [mem_Ioo, inv_pos]
    have s0 : 0 < s := lt_of_lt_of_le (by bound) m
    refine ⟨s0, ?_⟩
    rw [inv_lt_comm₀ s0 r0]
    exact lt_of_lt_of_le (lt_mul_of_one_lt_left (by bound) (by norm_num)) m

/-- Pull an `∃` out of an `∃ᶠ` via Skolemization -/
lemma frequently_skolem {X Y : Type} [TopologicalSpace X] [n : Nonempty Y] {p : X → Y → Prop}
    (f : Filter X) : (∃ᶠ x in f, ∃ y, p x y) ↔ ∃ s : X → Y, ∃ᶠ x in f, p x (s x) := by
  constructor
  · intro h
    set s : X → Y := fun x ↦ if q : ∃ y, p x y then Classical.choose q else Classical.choice n
    use s
    refine h.mp (.of_forall fun x e ↦ ?_)
    simp only [e, ↓reduceDIte, choose_spec, s]
  · intro ⟨s,h⟩
    refine h.mp (.of_forall fun x e ↦ ?_)
    use s x

lemma ENNReal.continuousAt_toNNReal {x : ℝ≥0∞} (h : x ≠ ⊤) :
    ContinuousAt (fun x ↦ x.toNNReal) x := by
  apply ENNReal.continuousOn_toNNReal.continuousAt
  apply ENNReal.isOpen_ne_top.mem_nhds
  simpa only [ne_eq, Set.mem_ofPred_eq]

end
end Ray_Ray_Misc_Topology

-- ===== Ray.Analytic.Analytic =====
section Ray_Ray_Analytic_Analytic
/-!
## Facts about analytic functions (general field case)
-/

open Classical
open Filter (atTop)
open Function (curry uncurry)
open Metric (ball closedBall sphere isOpen_ball)
open Set (univ)
open scoped ContDiff Real NNReal ENNReal Topology
noncomputable section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Drop 'Within' from `AnalyticWithinAt` if we have a neighborhood -/
lemma AnalyticWithinAt.analyticAt {f : E → F} {s : Set E} {x : E}
    (fa : AnalyticWithinAt 𝕜 f s x) (xs : s ∈ 𝓝 x) : AnalyticAt 𝕜 f x := by
  obtain ⟨p, r, fp⟩ := fa
  obtain ⟨e, e0, es⟩ := Metric.mem_nhds_iff.mp xs
  refine ⟨p, min r (.ofReal e),
    {r_le := by simp [fp.r_le], r_pos := by simp [fp.r_pos, e0], hasSum := fun {y} yr ↦ ?_}⟩
  simp only [Metric.mem_eball, edist_zero_right, lt_inf_iff] at yr
  obtain ⟨yr, ye⟩ := yr
  simp only [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff e0] at ye
  exact fp.hasSum (.inr (es (by simp [ye]))) (by simp [yr])

/-- Extract `AnalyticAt` from `ContDiffOn 𝕜 ω` if we have a neighborhood -/
lemma ContDiffOn.analyticAt {f : E → F} {s : Set E} (fa : ContDiffOn 𝕜 ω f s) {x : E}
    (xs : s ∈ 𝓝 x) : AnalyticAt 𝕜 f x :=
  (fa x (mem_of_mem_nhds xs)).analyticWithinAt.analyticAt xs

/-- Extract `AnalyticOnNhd` from `ContDiffOn 𝕜 ω` if we're open -/
lemma ContDiffOn.analyticOnNhd {f : E → F} {s : Set E} (fa : ContDiffOn 𝕜 ω f s)
    (os : IsOpen s) : AnalyticOnNhd 𝕜 f s :=
  fun x xs ↦ (fa x xs).analyticWithinAt.analyticAt (os.mem_nhds xs)

lemma AnalyticAt.dslope {f : 𝕜 → E} {c x : 𝕜} (fa : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (dslope f c) x := by
  by_cases e : x = c
  · obtain ⟨p,fp⟩ := fa
    simp only [← e]
    exact ⟨_, fp.has_fpower_series_dslope_fslope⟩
  · rw [analyticAt_congr (dslope_eventuallyEq_slope_of_ne _ e)]
    apply AnalyticAt.smul
    · exact AnalyticAt.inv (by fun_prop) (by simpa only [ne_eq, sub_eq_zero])
    · simp only [vsub_eq_sub]
      exact fa.sub analyticAt_const

/-- Power series coefficients in terms of iterated derivatives -/
lemma HasFPowerSeriesAt.coeff_eq_iteratedDeriv_div [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 → 𝕜}
    {p : FormalMultilinearSeries 𝕜 𝕜 𝕜} {c : 𝕜} (fp : HasFPowerSeriesAt f p c) (n : ℕ) :
    p.coeff n = iteratedDeriv n f c / n.factorial := by
  simp only [fp.eq_formalMultilinearSeries (AnalyticAt.hasFPowerSeriesAt ⟨_, fp⟩),
    FormalMultilinearSeries.coeff_ofScalars]

/-- `orderAt` is unique, since power series are -/
theorem HasFPowerSeriesAt.orderAt_unique {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E}
    {c : 𝕜} (fp : HasFPowerSeriesAt f p c) : orderAt f c = p.order := by
  have fa : AnalyticAt 𝕜 f c := ⟨p, fp⟩
  simp only [orderAt, fa, dif_pos]
  have s := choose_spec fa
  generalize hq : choose fa = q
  simp_rw [hq] at s
  rw [fp.eq_formalMultilinearSeries s]

/-- `orderAt` is zero for nonzeros -/
theorem orderAt_eq_zero {f : 𝕜 → E} {c : 𝕜} (f0 : f c ≠ 0) : orderAt f c = 0 := by
  by_cases fp : AnalyticAt 𝕜 f c
  · rcases fp with ⟨p, fp⟩; rw [fp.orderAt_unique]; rw [← fp.coeff_zero 1] at f0
    rw [FormalMultilinearSeries.order_eq_zero_iff']; right
    contrapose f0
    simp only [f0, _root_.zero_apply]
  · simp [orderAt, fp]

/-- `orderAt = 0` means either `f = 0` or `f c ≠ 0` -/
theorem orderAt_eq_zero_iff {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c) :
    orderAt f c = 0 ↔ f =ᶠ[𝓝 c] 0 ∨ f c ≠ 0 := by
  rcases fa with ⟨p, fp⟩
  simp only [fp.orderAt_unique, ←fp.coeff_zero fun _ ↦ 0,
    FormalMultilinearSeries.order_eq_zero_iff']
  rw [←@norm_ne_zero_iff _ _ (p 0 fun _ ↦ 0), ContinuousMultilinearMap.fin0_apply_norm,
    norm_ne_zero_iff]
  apply or_congr_left'; intro _; exact fp.locally_zero_iff.symm

/-- `orderAt = 1 → deriv ≠ 0` -/
theorem deriv_ne_zero_of_orderAt_eq_one {f : 𝕜 → E} {c : 𝕜} (o : orderAt f c = 1) :
    deriv f c ≠ 0 := by
  by_cases fa : AnalyticAt 𝕜 f c
  · rcases fa with ⟨p, fp⟩
    rw [fp.orderAt_unique] at o
    have o0 : p.order ≠ 0 := by rw [o]; exact one_ne_zero
    have p0 := FormalMultilinearSeries.apply_order_ne_zero' o0
    rw [o] at p0
    simpa only [fp.deriv, FormalMultilinearSeries.apply_eq_pow_smul_coeff, one_pow, one_smul,
      FormalMultilinearSeries.coeff_eq_zero, Ne]
  · simp only [orderAt, fa] at o; rw [dif_neg] at o; norm_num at o; exact not_false

/-- `leadingCoeff` for nonzeros -/
theorem leadingCoeff_of_ne_zero {f : 𝕜 → E} {c : 𝕜} (f0 : f c ≠ 0) :
    leadingCoeff f c = f c := by
  simp only [leadingCoeff, orderAt_eq_zero f0, Function.iterate_zero_apply]

/-- `f` is approximated by its leading monomial -/
theorem AnalyticAt.leading_approx {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c) :
    (fun z ↦ f z - (z - c) ^ orderAt f c • leadingCoeff f c) =o[𝓝 c] fun z ↦
      (z - c) ^ orderAt f c := by
  rcases fa with ⟨p, fp⟩
  generalize ha : leadingCoeff f c = a
  generalize hd : orderAt f c = d
  have ha' : (Function.swap _root_.dslope c)^[d] f c = a := by rw [← ha, ← hd, leadingCoeff]
  have e := fp.eq_pow_order_mul_iterate_dslope
  simp_rw [← fp.orderAt_unique, hd] at e
  apply Asymptotics.IsLittleO.of_isBigOWith; intro k kp
  rw [Asymptotics.isBigOWith_iff]
  have dc : ContinuousAt ((Function.swap _root_.dslope c)^[d] f) c :=
    (fp.has_fpower_series_iterate_dslope_fslope d).analyticAt.continuousAt
  rcases Metric.continuousAt_iff.mp dc k kp with ⟨r, rp, rh⟩
  rw [ha'] at rh
  generalize hg : (Function.swap _root_.dslope c)^[d] f = g; rw [hg] at rh
  rw [Metric.eventually_nhds_iff]; use r, rp; intro y yr; rw [e y, hg]
  specialize rh yr; rw [dist_eq_norm] at rh
  calc ‖(y - c) ^ d • g y - (y - c) ^ d • a‖
    _ = ‖(y - c) ^ d‖ * ‖g y - a‖ := by rw [←smul_sub, norm_smul]
    _ ≤ ‖(y - c) ^ d‖ * k := mul_le_mul_of_nonneg_left rh.le (norm_nonneg _)
    _ = k * ‖(y - c) ^ d‖ := by rw [mul_comm]

/-- `orderAt > 0` means `f` has a zero -/
theorem AnalyticAt.zero_of_order_pos {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c)
    (p : 0 < orderAt f c) : f c = 0 := by
  have a := (Asymptotics.isBigOWith_iff.mp (fa.leading_approx.forall_isBigOWith zero_lt_one)).self_of_nhds
  simp only [(pow_eq_zero_iff (Nat.pos_iff_ne_zero.mp p)).mpr, sub_self, zero_smul, sub_zero,
    norm_zero, MulZeroClass.mul_zero, norm_le_zero_iff] at a
  exact a


@[simp]
lemma FormalMultilinearSeries.unshift_coeff_zero (p : FormalMultilinearSeries 𝕜 𝕜 E) (c : E) :
    (p.unshift' c).coeff 0 = c := by
  simp only [FormalMultilinearSeries.coeff, FormalMultilinearSeries.unshift',
    FormalMultilinearSeries.unshift, continuousMultilinearCurryFin0_symm_apply,
    ContinuousMultilinearMap.uncurry0_apply]

@[simp]
lemma FormalMultilinearSeries.unshift_coeff_succ (p : FormalMultilinearSeries 𝕜 𝕜 E) (c : E)
    (n : ℕ) : (p.unshift' c).coeff (n + 1) = p.coeff n := by
  simp only [FormalMultilinearSeries.coeff, FormalMultilinearSeries.unshift',
    FormalMultilinearSeries.unshift, ContinuousLinearMap.compFormalMultilinearSeries_apply]
  simp [ContinuousLinearMap.smulRightL, Finset.univ, Fintype.elems, Fin.init]


lemma FormalMultilinearSeries.unshiftIter_coeff (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ)
    (i : ℕ) : (p.unshiftIter n).coeff i = if i < n then 0 else p.coeff (i - n) := by
  revert i; induction' n with n h
  · simp only [FormalMultilinearSeries.unshiftIter, Function.iterate_zero, id_eq, not_lt_zero,
    tsub_zero, if_false, forall_const]
  · simp_rw [FormalMultilinearSeries.unshiftIter] at h
    simp only [FormalMultilinearSeries.unshiftIter, Function.iterate_succ', Function.comp]
    generalize hq : (fun p : FormalMultilinearSeries 𝕜 𝕜 E ↦ p.unshift' 0)^[n] p = q
    rw [hq] at h; clear hq
    intro i; induction' i with i _
    · simp only [FormalMultilinearSeries.unshift_coeff_zero, Nat.succ_pos', if_true]
    · simp only [Nat.succ_lt_succ_iff, h i, FormalMultilinearSeries.unshift_coeff_succ,
        Nat.succ_sub_succ_eq_sub]

/-- `unshift'` respects norm -/
lemma FormalMultilinearSeries.unshift_norm' (p : FormalMultilinearSeries 𝕜 𝕜 E) (c : E) (n : ℕ) :
    ‖p.unshift' c (n + 1)‖ = ‖p n‖ := by
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef,
    FormalMultilinearSeries.unshift_coeff_succ]

/-- `unshift'` respects radius -/
lemma FormalMultilinearSeries.unshift_radius' (p : FormalMultilinearSeries 𝕜 𝕜 E) {c : E} :
    (p.unshift' c).radius = p.radius := by
  simp_rw [FormalMultilinearSeries.radius]
  apply le_antisymm
  · refine iSup₂_le ?_; intro r k; refine iSup_le ?_; intro h
    refine le_trans ?_ (le_iSup₂ r (k * ↑r⁻¹))
    have h := fun n ↦ mul_le_mul_of_nonneg_right (h (n + 1)) (NNReal.coe_nonneg r⁻¹)
    by_cases r0 : r = 0; · simp only [r0, ENNReal.coe_zero, ENNReal.iSup_zero, le_zero_iff]
    simp only [pow_succ, ←mul_assoc _ _ (r:ℝ), mul_assoc _ (r:ℝ) _,
      mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr r0), NNReal.coe_inv, mul_one, p.unshift_norm'] at h
    simp only [NNReal.coe_inv]
    convert le_iSup _ h; rfl
  · refine iSup₂_le ?_; intro r k; refine iSup_le ?_; intro h
    refine le_trans ?_ (le_iSup₂ r (max ‖c‖ (k * ↑r)))
    have h' : ∀ n, ‖p.unshift' c n‖ * (r:ℝ)^n ≤ max ‖c‖ (k * ↑r) := by
      intro n; induction' n with n _
      · simp only [FormalMultilinearSeries.unshift_coeff_zero,
          FormalMultilinearSeries.norm_apply_eq_norm_coef, pow_zero, mul_one, le_max_iff, le_refl,
          true_or]
      · simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef] at h
        simp only [FormalMultilinearSeries.unshift_coeff_succ, pow_succ, ← mul_assoc,
          FormalMultilinearSeries.norm_apply_eq_norm_coef, le_max_iff]
        right; exact mul_le_mul_of_nonneg_right (h n) (NNReal.coe_nonneg _)
    convert le_iSup _ h'; rfl

/-- The power series of `(z - c) • f z` is the unshifted power series -/
theorem HasFPowerSeriesOnBall.unshift' {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {c : 𝕜}
    {r : ENNReal} (fp : HasFPowerSeriesOnBall f p c r) :
    HasFPowerSeriesOnBall (fun z ↦ (z - c) • f z) (p.unshift' 0) c r :=
  { r_le := le_trans fp.r_le (ge_of_eq p.unshift_radius')
    r_pos := fp.r_pos
    hasSum := by
      intro y yr; simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, add_sub_cancel_left]
      generalize hs : (fun n ↦ y ^ n • (p.unshift' 0).coeff n) = s
      have s0 : y • f (c + y) = y • f (c + y) + (Finset.range 1).sum s := by
        simp only [← hs, p.unshift_coeff_zero, Finset.range_one, Finset.sum_singleton, smul_zero,
          add_zero]
      rw [s0, ← hasSum_nat_add_iff, ← hs]
      simp only [p.unshift_coeff_succ, pow_succ', ← smul_smul]; apply HasSum.const_smul
      have h := fp.hasSum yr; simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff] at h
      exact h }

theorem HasFPowerSeriesAt.unshift {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {c : 𝕜}
    (fp : HasFPowerSeriesAt f p c) :
    HasFPowerSeriesAt (fun z ↦ (z - c) • f z) (p.unshift' 0) c := by
  rcases fp with ⟨r, fa⟩; use r; exact fa.unshift'

theorem HasFPowerSeriesAt.unshiftIter {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {c : 𝕜}
    {n : ℕ} (fp : HasFPowerSeriesAt f p c) :
    HasFPowerSeriesAt (fun z ↦ (z - c) ^ n • f z) (p.unshiftIter n) c := by
  induction' n with n h; · simp only [pow_zero, one_smul]; exact fp
  · simp only [pow_succ', ← smul_smul, FormalMultilinearSeries.unshiftIter, Function.iterate_succ',
      Function.comp]
    exact h.unshift

/-- Power series terms are zero iff their coeffs are zero -/
theorem FormalMultilinearSeries.ne_zero_iff_coeff_ne_zero (p : FormalMultilinearSeries 𝕜 𝕜 E)
    {n : ℕ} : p n ≠ 0 ↔ p.coeff n ≠ 0 := by
  constructor
  · intro h; contrapose h; exact coeff_eq_zero.mp h
  · intro h; contrapose h; exact coeff_eq_zero.mpr h

/-- The order of `(z - n)^n • f z` is `n` greater than `f`'s -/
theorem AnalyticAt.monomial_mul_orderAt {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c)
    (fnz : ∃ᶠ z in 𝓝 c, f z ≠ 0) (n : ℕ) :
    orderAt (fun z ↦ (z - c) ^ n • f z) c = n + orderAt f c := by
  rcases fa with ⟨p, fp⟩
  have pnz : p ≠ 0 := by
    contrapose fnz
    simpa only [HasFPowerSeriesAt.locally_zero_iff fp, Filter.not_frequently, not_not]
  have pe : ∃ i, p i ≠ 0 := by contrapose! pnz; exact FormalMultilinearSeries.ext pnz
  have pne : ∃ i, (p.unshiftIter n) i ≠ 0 := by
    rcases pe with ⟨i, pi⟩; use n + i
    simp only [FormalMultilinearSeries.ne_zero_iff_coeff_ne_zero] at pi ⊢
    simpa only [p.unshiftIter_coeff, add_lt_iff_neg_left, add_tsub_cancel_left]
  have fq : HasFPowerSeriesAt (fun z ↦ (z - c) ^ n • f z) (p.unshiftIter n) c := fp.unshiftIter
  rw [fp.orderAt_unique, fq.orderAt_unique]
  rw [FormalMultilinearSeries.order_eq_find pe, FormalMultilinearSeries.order_eq_find pne]
  rw [Nat.find_eq_iff]; constructor
  · have s := Nat.find_spec pe
    simp only [← p.coeff_eq_zero, Ne] at s
    simp only [p.unshiftIter_coeff, ← FormalMultilinearSeries.coeff_eq_zero, s, Ne,
      add_lt_iff_neg_left, not_lt_zero, add_tsub_cancel_left, if_false, not_false_iff]
  · intro m mp; simp [← FormalMultilinearSeries.coeff_eq_zero, p.unshiftIter_coeff]; intro mn
    generalize ha : m - n = a; have hm : m = n + a := by rw [← ha, add_comm, Nat.sub_add_cancel mn]
    simp only [hm, add_lt_add_iff_left, Nat.lt_find_iff, not_not] at mp
    specialize mp a (le_refl _); rwa [FormalMultilinearSeries.coeff_eq_zero]

/-- The leading coefficient of `(z - n)^n • f z` is the same as `f`'s -/
theorem AnalyticAt.monomial_mul_leadingCoeff {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c)
    (fnz : ∃ᶠ z in 𝓝 c, f z ≠ 0) (n : ℕ) :
    leadingCoeff (fun z ↦ (z - c) ^ n • f z) c = leadingCoeff f c := by
  simp [leadingCoeff, fa.monomial_mul_orderAt fnz n]; generalize orderAt f c = a
  induction' n with n h
  · simp only [zero_add, pow_zero, one_smul]
  · simp [pow_succ', ← smul_smul, Nat.succ_add]
    generalize hg : (fun z ↦ (z - c) ^ n • f z) = g
    have hg' : ∀ z, (z - c) ^ n • f z = g z := by
      rw [←hg]; simp only [forall_const]
    simp_rw [hg'] at h ⊢
    have e : (Function.swap _root_.dslope c fun z ↦ (z - c) • g z) = g := by
      simp only [Function.swap, dslope_sub_smul, Function.update_eq_self_iff]
      rw [deriv_fun_smul]
      simp only [sub_self, zero_smul, deriv_fun_sub, differentiableAt_fun_id,
        differentiableAt_const, deriv_id'', deriv_const', sub_zero, one_smul, zero_add]
      exact differentiableAt_id.sub (differentiableAt_const _)
      rw [←hg]
      exact ((differentiableAt_id.sub (differentiableAt_const _)).pow _).smul fa.differentiableAt
    rw [e, h]

/-- `deriv` in the second variable is analytic -/
theorem AnalyticAt.deriv2 [CompleteSpace 𝕜] {f : E → 𝕜 → 𝕜} {c : E × 𝕜}
    (fa : AnalyticAt 𝕜 (uncurry f) c) :
    AnalyticAt 𝕜 (fun x : E × 𝕜 ↦ _root_.deriv (f x.1) x.2) c := by
  set p : (E × 𝕜 →L[𝕜] 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.apply 𝕜 𝕜 (0, 1)
  have e : ∀ᶠ x : E × 𝕜 in 𝓝 c, _root_.deriv (f x.1) x.2 = p (_root_.fderiv 𝕜 (uncurry f) x) := by
    refine fa.eventually_analyticAt.mp (.of_forall ?_)
    intro ⟨x, y⟩ fa; simp only [← fderiv_apply_one_eq_deriv]
    have e : f x = uncurry f ∘ fun y ↦ (x, y) := rfl
    rw [e]; rw [fderiv_comp]
    have pd : _root_.fderiv 𝕜 (fun y : 𝕜 ↦ (x, y)) y = ContinuousLinearMap.inr 𝕜 E 𝕜 := by
      apply HasFDerivAt.fderiv; apply hasFDerivAt_prodMk_right
    rw [pd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.apply_apply]
    · exact fa.differentiableAt
    · exact (differentiableAt_const _).prodMk differentiableAt_id
  rw [analyticAt_congr e]
  exact (p.analyticAt _).comp fa.fderiv

/-- Scaling commutes with power series -/
theorem HasFPowerSeriesAt.const_fun_smul {f : 𝕜 → E} {c a : 𝕜} {p : FormalMultilinearSeries 𝕜 𝕜 E}
    (fp : HasFPowerSeriesAt f p c) : HasFPowerSeriesAt (fun z ↦ a • f z) (fun n ↦ a • p n) c := by
  show HasFPowerSeriesAt (fun z ↦ a • f z) (a • p) c
  rw [hasFPowerSeriesAt_iff] at fp ⊢; refine fp.mp (.of_forall fun z h ↦ ?_)
  simp only [FormalMultilinearSeries.coeff, FormalMultilinearSeries.smul_apply,
    _root_.smul_apply, smul_comm _ a]
  exact h.const_smul a

/-- Nonzero scaling does not change analyticitiy -/
theorem analyticAt_iff_const_smul {f : 𝕜 → E} {c a : 𝕜} (a0 : a ≠ 0) :
    AnalyticAt 𝕜 (fun z ↦ a • f z) c ↔ AnalyticAt 𝕜 f c := by
  constructor
  · intro ⟨p, fp⟩
    have e : f = fun z ↦ a⁻¹ • a • f z := by
      funext; simp only [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ a0, one_smul]
    rw [e]; exact ⟨_, fp.const_smul⟩
  · intro ⟨p, fp⟩; exact ⟨_, fp.const_smul⟩

/-- Nonzero scaling does not change `orderAt` -/
theorem orderAt_const_smul {f : 𝕜 → E} {c a : 𝕜} (a0 : a ≠ 0) :
    orderAt (fun z ↦ a • f z) c = orderAt f c := by
  by_cases fa : AnalyticAt 𝕜 f c
  · rcases fa with ⟨p, fp⟩
    have e : ∀ n, a • p n ≠ 0 ↔ p n ≠ 0 := fun n ↦ by
      simp only [a0, Ne, smul_eq_zero, false_or]
    simp only [fp.orderAt_unique, fp.const_fun_smul.orderAt_unique,
      FormalMultilinearSeries.order, e]
  · have ga := fa; rw [← analyticAt_iff_const_smul a0] at ga
    simp only [orderAt, fa, ga]; rw [dif_neg, dif_neg]
    exact not_false; exact not_false

/-- The leading coefficient of zero is zero -/
theorem leadingCoeff.zero {c : 𝕜} : leadingCoeff (fun _ : 𝕜 ↦ (0 : E)) c = 0 := by
  simp only [leadingCoeff]
  generalize hn : orderAt (fun _ : 𝕜 ↦ (0 : E)) c = n; clear hn
  induction' n with n h; simp only [Function.iterate_zero_apply]
  simp only [Function.iterate_succ_apply]; convert h
  simp only [Function.swap, dslope, deriv_const]
  simp only [slope_fun_def, vsub_eq_sub, sub_zero, smul_zero, Function.update_apply]
  split_ifs; rfl; rfl

/-- `leadingCoeff` has linear scaling -/
theorem leadingCoeff_const_smul {f : 𝕜 → E} {c a : 𝕜} :
    leadingCoeff (fun z ↦ a • f z) c = a • leadingCoeff f c := by
  by_cases a0 : a = 0; simp only [a0, zero_smul, leadingCoeff.zero]
  simp only [leadingCoeff, orderAt_const_smul a0]
  generalize hn : orderAt f c = n; clear hn
  have e : ((Function.swap dslope c)^[n] fun z : 𝕜 ↦ a • f z) =
      a • (Function.swap dslope c)^[n] f := by
    induction' n with n h; funext; simp only [Function.iterate_zero_apply, Pi.smul_apply]
    generalize hg : (Function.swap dslope c)^[n] f = g
    simp only [Function.iterate_succ_apply', h, hg]
    funext x; simp only [Function.swap]
    by_cases cx : x = c
    · simp only [cx, dslope_same, Pi.smul_apply, Pi.smul_def, deriv_fun_const_smul_field]
    · simp only [dslope_of_ne _ cx, Pi.smul_apply, slope, vsub_eq_sub, ← smul_sub, smul_comm _ a]
  simp only [e, Pi.smul_apply]

/-- `leadingCoeff` is nonzero for nonzero order -/
theorem leadingCoeff_ne_zero {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c)
    (o0 : orderAt f c ≠ 0) : leadingCoeff f c ≠ 0 := by
  rcases fa with ⟨p, fp⟩
  simp only [fp.orderAt_unique, leadingCoeff] at o0 ⊢
  exact fp.iterate_dslope_fslope_ne_zero (FormalMultilinearSeries.ne_zero_of_order_ne_zero o0)

end
end Ray_Ray_Analytic_Analytic


