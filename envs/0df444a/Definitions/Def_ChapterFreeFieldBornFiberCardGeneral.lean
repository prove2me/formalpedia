-- Prove2me | Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
-- name    : ChapterFreeFieldBornFiberCardGeneral
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-11T20:56:10.802989+00:00
-- url     : https://prove2.me/theorems/da569450-0289-4a96-8a27-8e91a5c449d7
-- title:
--   ChapterFreeFieldBornFiberCardGeneral

import Theorems.Thm_BookProof_ChapterFreeFieldBornSignFiber_bornMap_eq_iff_signFlip

import Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornMap_bornSection

import Theorems.Thm_BookProof_ChapterFreeFieldBornSignGauge_bornMap_signFlip
import Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornSection_apply


import Theorems.Thm_BookProof_ChapterFreeFieldBornSignGauge_signFlip_mem_sphere

import Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornSection_mem_sphere

import Definitions.Def_ChapterFreeFieldBornFiberCard
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornSectionBij
import Definitions.Def_ChapterFreeFieldBornSignFiber
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# the general Born fiber has exactly `2^(#positive coords)` points

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"* — the Introduction's statement (`book.tex` ~line 805) that the
wave-function is *one possible parametrization* of a probability distribution,
together with the free-field construction of §5 (`book.tex` ~line 1706).

Wave 150 (`ChapterFreeFieldBornFiberCard`) counted the Born fiber over a
*strictly positive* distribution: exactly `2ⁿ` wave functions, one per
coordinate-wise sign choice.  This wave records the **general** count valid for
*every* probability distribution `p`, including ones with vanishing
coordinates: the Born fiber `bornMapSphere ⁻¹' {p}` has exactly
`2^(#{k | p k > 0})` points.  The point is that at a vanishing coordinate
`p_k = 0` the square-root section already has `√(p_k) = 0`, so flipping its sign
does nothing — the sign gauge acts freely *only* on the positive support, and
the fiber is a full orbit of the sign group restricted to that support.

## Main results

* `posSupport` — the Finset of strictly-positive coordinates of `p`.
* `sBool` / `fiberPoint` — the `±1` sign vector and wave function attached to a
  boolean sign choice on the positive support.
* `bornFiberEquivGeneral` — an equivalence
  `(↥(posSupport p) → Bool) ≃ ↥(bornMapSphere n ⁻¹' {p})`.
* **headline** `bornFiber_card_general` —
  `Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ (posSupport p).card`.

Everything is intended to be `sorry`-free and axiom-clean.
-/

open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignFiber BookProof.ChapterFreeFieldBornSectionBij
open BookProof.ChapterFreeFieldBornQuotient BookProof.ChapterFreeFieldBornFiberCard

namespace BookProof.ChapterFreeFieldBornFiberCardGeneral

variable {n : ℕ}

/-- The positive support of `p`: the coordinates that are strictly positive. -/
noncomputable def posSupport (p : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun k => 0 < p k)

@[simp] theorem mem_posSupport {p : Fin n → ℝ} {k : Fin n} :
    k ∈ posSupport p ↔ 0 < p k := by simp [posSupport]

/-- The `±1` sign vector determined by a boolean choice on the positive support
(and the default `+1` off the support). -/
noncomputable def sBool (p : Fin n → ℝ) (b : ↥(posSupport p) → Bool) : Fin n → ℝ :=
  fun k => if h : k ∈ posSupport p then (if b ⟨k, h⟩ then 1 else -1) else 1

theorem sBool_pm (p : Fin n → ℝ) (b : ↥(posSupport p) → Bool) (k : Fin n) :
    sBool p b k = 1 ∨ sBool p b k = -1 := by
  unfold sBool; split_ifs <;> simp

/-- The wave function realizing the sign choice `b` over the distribution `p`. -/
noncomputable def fiberPoint (p : Fin n → ℝ) (b : ↥(posSupport p) → Bool) :
    EuclideanSpace ℝ (Fin n) :=
  signFlip (sBool p b) (bornSection p)

/-- Each `fiberPoint` lies on the unit sphere. -/
theorem fiberPoint_mem_sphere {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n))
    (b : ↥(posSupport p) → Bool) :
    fiberPoint p b ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  signFlip_mem_sphere (sBool_pm p b) (bornSection_mem_sphere hp)

/-- Each `fiberPoint` maps to `p` under the Born map. -/
theorem bornMap_fiberPoint {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n))
    (b : ↥(posSupport p) → Bool) :
    bornMap (fiberPoint p b) = p := by
  unfold fiberPoint
  rw [bornMap_signFlip (sBool_pm p b), bornMap_bornSection hp]

/-
On the positive support the sign group acts *freely*: distinct sign choices
give distinct wave functions.  (At a vanishing coordinate the square-root section
is already `0`, so only the support carries sign information.)
-/
theorem fiberPoint_injective (p : Fin n → ℝ) :
    Function.Injective (fiberPoint p) := by
  intro b b' h; simp_all [ fiberPoint, signFlip, bornSection ] ;
  simp_all [ funext_iff, sBool ];
  grind

/-
Membership in the general Born fiber is exactly being some `fiberPoint`.
-/
theorem mem_fiber_iff_general {p : ↥(stdSimplex ℝ (Fin n))}
    (x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    x ∈ bornMapSphere n ⁻¹' {p} ↔
      ∃ b : ↥(posSupport (p : Fin n → ℝ)) → Bool, fiberPoint (p : Fin n → ℝ) b = x := by
  constructor;
  · intro hx
    obtain ⟨s, hs⟩ : ∃ s : Fin n → ℝ, (∀ k, s k = 1 ∨ s k = -1) ∧
        x.val = signFlip s (bornSection p.val) := by
      convert bornMap_eq_iff_signFlip ( bornSection p.val ) x.val |>.1 _;
      convert congr_arg Subtype.val hx using 1
      · rfl
      · exact bornMap_bornSection p.2
    use fun k => decide (s k.val = 1);
    ext k;
    by_cases hk : k ∈ posSupport p.val <;>
      simp_all only [Set.mem_preimage, Set.mem_singleton_iff, mem_posSupport, fiberPoint,
          signFlip_apply, bornSection_apply, not_lt];
    · cases hs.1 k <;> simp_all only [sBool, mem_posSupport, decide_true, ↓reduceIte, dite_eq_ite,
        ite_self, one_mul, decide_eq_true_eq, ite_mul, neg_mul];
      · rfl;
      · norm_num [ hk ];
        exact if_pos hk;
    · rw [ show p k = 0 by exact le_antisymm hk ( p.2.1 k ) ] ; norm_num;
      exact Or.inr <| Real.sqrt_eq_zero_of_nonpos hk;
  · rintro ⟨ b, hb ⟩;
    convert bornMap_fiberPoint p.2 b;
    constructor <;> intro h <;> simp_all only [Set.mem_preimage, Set.mem_singleton_iff,
        Subtype.ext_iff];
    · convert bornMap_fiberPoint p.2 b;
    · convert h using 1;
      exact hb ▸ rfl

/-- The equivalence between sign choices on the positive support and the general
Born fiber. -/
noncomputable def bornFiberEquivGeneral {p : ↥(stdSimplex ℝ (Fin n))} :
    (↥(posSupport (p : Fin n → ℝ)) → Bool) ≃ ↥(bornMapSphere n ⁻¹' {p}) :=
  Equiv.ofBijective
    (fun b => ⟨⟨fiberPoint (p : Fin n → ℝ) b, fiberPoint_mem_sphere p.property b⟩,
        (mem_fiber_iff_general _).2 ⟨b, rfl⟩⟩)
    ⟨by
        intro b b' h
        exact fiberPoint_injective (p : Fin n → ℝ)
          (congrArg (fun z => (z : ↥(bornMapSphere n ⁻¹' {p})).1.1) h),
      by
        intro z
        obtain ⟨b, hb⟩ := (mem_fiber_iff_general z.1).1 z.2
        exact ⟨b, Subtype.ext (Subtype.ext hb)⟩⟩

/-
**Headline.** For *every* probability distribution `p`, the Born fiber
consists of exactly `2^(#positive coordinates)` wave functions.  This is the
general form of `bornFiber_card`: the `{±1}ⁿ` sign gauge acts freely on the
positive support (and trivially at vanishing coordinates), so each fiber is a
full orbit of the sign group restricted to that support.
-/
theorem bornFiber_card_general {p : ↥(stdSimplex ℝ (Fin n))} :
    Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ (posSupport (p : Fin n → ℝ)).card := by
  convert Nat.card_congr ( bornFiberEquivGeneral.symm ) using 1
  rw [ Nat.card_eq_fintype_card, Fintype.card_pi ]
  norm_num

end BookProof.ChapterFreeFieldBornFiberCardGeneral


