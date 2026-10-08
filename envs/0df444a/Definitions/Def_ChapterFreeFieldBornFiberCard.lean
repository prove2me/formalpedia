-- Prove2me | Definitions.Def_ChapterFreeFieldBornFiberCard
-- name    : ChapterFreeFieldBornFiberCard
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T10:46:40.135562+00:00
-- url     : https://prove2.me/theorems/24b42695-273e-4bef-8592-543456fbf6f0
-- title:
--   ChapterFreeFieldBornFiberCard

import Theorems.Thm_BookProof_ChapterFreeFieldBornSignFiber_bornMap_eq_iff_signFlip

import Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornMap_bornSection

import Theorems.Thm_BookProof_ChapterFreeFieldBornSignGauge_bornMap_signFlip


import Theorems.Thm_BookProof_ChapterFreeFieldBornSignGauge_signFlip_mem_sphere

import Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornSection_mem_sphere

import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornSignFiber
import Definitions.Def_ChapterFreeFieldBornSectionBij
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# the interior Born fiber has exactly `2ⁿ` points

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"* — the Introduction's statement (`book.tex` ~line 805) that the
wave-function is *one possible parametrization* of a probability distribution,
together with the free-field construction of §5 (`book.tex` ~line 1706).

Previous waves on this thread showed the Born map `x ↦ (x_k)²` is a continuous
surjection of the unit sphere onto the probability simplex, pinned down its
gauge redundancy as *exactly* the diagonal `{±1}ⁿ` sign group
(`bornMap_eq_iff_signFlip`), and showed it restricts to a homeomorphism on the
nonnegative orthant.

This wave records the **quantitative** version of the gauge statement: over a
probability distribution `p` all of whose coordinates are strictly positive, the
Born fiber `bornMapSphere ⁻¹' {p}` consists of **exactly `2ⁿ` wave functions** —
one for each coordinate-wise choice of sign — because on the strictly-positive
locus the sign group acts *freely*.

## Main results

* `signVec` — the `±1` sign vector attached to a boolean choice `b : Fin n → Bool`.
* `bornFiberPoint` — the wave function `signFlip (signVec b) (bornSection p)`.
* `bornFiberEquiv` — an equivalence `(Fin n → Bool) ≃ ↥(bornMapSphere n ⁻¹' {p})`.
* **headline** `bornFiber_card` — `Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ n`.

Everything is intended to be `sorry`-free and axiom-clean.
-/

open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignFiber BookProof.ChapterFreeFieldBornSectionBij
open BookProof.ChapterFreeFieldBornQuotient

namespace BookProof.ChapterFreeFieldBornFiberCard

variable {n : ℕ}

/-- The `±1` sign vector determined by a boolean choice: `true ↦ 1`, `false ↦ -1`. -/
def signVec (b : Fin n → Bool) : Fin n → ℝ := fun k => if b k then 1 else -1

theorem signVec_pm (b : Fin n → Bool) (k : Fin n) :
    signVec b k = 1 ∨ signVec b k = -1 := by
  unfold signVec; split_ifs <;> simp

/-- The boolean vector reading off the sign of a `±1` vector `s`. -/
noncomputable def signBool (s : Fin n → ℝ) : Fin n → Bool := fun k => decide (s k = 1)

/-- On a genuine `±1` vector, `signVec ∘ signBool` is the identity. -/
theorem signVec_signBool {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1) :
    signVec (signBool s) = s := by
  funext k
  rcases hs k with h | h <;> simp [signVec, signBool, h] ; norm_num

/-- The wave function realizing the sign choice `b` over the distribution `p`:
sign-flip the canonical square-root section by `signVec b`. -/
noncomputable def bornFiberPoint (p : Fin n → ℝ) (b : Fin n → Bool) :
    EuclideanSpace ℝ (Fin n) :=
  signFlip (signVec b) (bornSection p)

/-- Each `bornFiberPoint` lies on the unit sphere. -/
theorem bornFiberPoint_mem_sphere {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n))
    (b : Fin n → Bool) :
    bornFiberPoint p b ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  signFlip_mem_sphere (signVec_pm b) (bornSection_mem_sphere hp)

/-- Each `bornFiberPoint` maps to `p` under the Born map. -/
theorem bornMap_bornFiberPoint {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n))
    (b : Fin n → Bool) :
    bornMap (bornFiberPoint p b) = p := by
  unfold bornFiberPoint
  rw [bornMap_signFlip (signVec_pm b), bornMap_bornSection hp]

/-
On the strictly-positive locus the sign group acts *freely*: distinct sign
choices give distinct wave functions.
-/
theorem bornFiberPoint_injective {p : Fin n → ℝ} (hp : ∀ k, 0 < p k) :
    Function.Injective (bornFiberPoint p) := by
  intro b b' h;
  ext k;
  unfold bornFiberPoint at h;
  replace h := congr_arg ( fun x => x k ) h ; simp_all [ signVec, bornSection ];
  grind

/-
Membership in the interior Born fiber is exactly being some `bornFiberPoint`.
-/
theorem mem_fiber_iff {p : ↥(stdSimplex ℝ (Fin n))}
    (x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    x ∈ bornMapSphere n ⁻¹' {p} ↔
      ∃ b : Fin n → Bool, bornFiberPoint (p : Fin n → ℝ) b = x := by
  constructor <;> intro h;
  · have := bornMap_eq_iff_signFlip ( bornSection p.val ) x.val |>.1 ?_;
    · obtain ⟨ s, hs₁, hs₂ ⟩ := this; use fun k => decide ( s k = 1 )
      simp_all only [Set.mem_preimage, Set.mem_singleton_iff, bornFiberPoint]
      congr! 1;
      exact signVec_signBool hs₁;
    · convert congr_arg Subtype.val h using 1 <;> try rfl
      all_goals first
        | exact (bornMap_bornSection p.2).symm
        | exact bornMap_bornSection p.2
  · obtain ⟨ b, hb ⟩ := h;
    convert bornMap_bornFiberPoint p.property b using 1;
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff];
    convert Iff.rfl;
    exact hb ▸ rfl

/-
The equivalence between sign choices and the interior Born fiber.
-/
noncomputable def bornFiberEquiv {p : ↥(stdSimplex ℝ (Fin n))}
    (hp : ∀ k, 0 < (p : Fin n → ℝ) k) :
    (Fin n → Bool) ≃ ↥(bornMapSphere n ⁻¹' {p}) :=
  Equiv.ofBijective
    (fun b => ⟨⟨bornFiberPoint (p : Fin n → ℝ) b, bornFiberPoint_mem_sphere p.property b⟩,
        (mem_fiber_iff _).2 ⟨b, rfl⟩⟩)
    ⟨by
        intro b b' h
        exact bornFiberPoint_injective hp
          (congrArg (fun z => (z : ↥(bornMapSphere n ⁻¹' {p})).1.1) h),
      by
        intro z
        obtain ⟨b, hb⟩ := (mem_fiber_iff z.1).1 z.2
        exact ⟨b, Subtype.ext (Subtype.ext hb)⟩⟩

/-
**Headline.** Over a strictly-positive probability distribution `p`, the Born
fiber consists of exactly `2ⁿ` wave functions — one for each coordinate-wise
sign choice.  This is the quantitative form of `bornMap_eq_iff_signFlip`: on the
strictly-positive locus the `{±1}ⁿ` sign gauge acts freely, so each fiber is a
full orbit of size `2ⁿ`.
-/


end BookProof.ChapterFreeFieldBornFiberCard


