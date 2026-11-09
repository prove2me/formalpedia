-- Prove2me | Definitions.Def_SignRankMargin_OREquality_SignRank
-- name    : SignRankMargin_OREquality_SignRank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:41:11.97237+00:00
-- url     : https://prove2.me/theorems/3aa7e220-577e-4f53-ba1c-e7b6e3df656c
-- title:
--   Strict real realizations and minimum sign-rank
-- statement:
--   Let $F:X\times Y\to\{0,1\}$ be a Boolean matrix on finite row and column sets. A real matrix $H$ strictly realizes $F$ if $H(x,y)>0$ at every one-entry and $H(x,y)<0$ at every zero-entry. Define
--
--   $$
--   \operatorname{signRank}(F)=\min\{\operatorname{rank}_{\mathbb R}H:H\text{ strictly realizes }F\}.
--   $$
--
--   The minimum ranges over all real matrices of the same size. The canonical matrix with entries $1$ where $F=1$ and $-1$ where $F=0$ is always feasible; it supplies the existence proof for the natural-number minimum, without restricting that minimum to this witness. Zero is never a permitted realization entry.
--
--   This definition is the shared rank notion for both the upper and lower bounds and all four milestones.
--
--   **Formalization Note** Boolean `true` means one. The implementation takes the least attained ordinary real matrix rank using `Nat.find`. Empty index sets are allowed by the definition, in which case the minimum is zero; all geometric results below require both sets nonempty.
-- source:
--   Gabriel Hart, Kaave Hosseini, STOC 2027 submission #728 (October 2026), Section 2, p. 7

import Mathlib

namespace SignRankMargin.OREquality

/-- Strict entrywise realization: true is positive, false is negative; zero never realizes. -/
def StrictRealizes {X Y : Type*} (F : Matrix X Y Bool) (H : Matrix X Y ℝ) : Prop :=
  ∀ x y, if F x y then 0 < H x y else H x y < 0

/-- The canonical ±1 realization, providing a feasible real matrix for every Boolean matrix. -/
def canonicalRealization {X Y : Type*} (F : Matrix X Y Bool) : Matrix X Y ℝ :=
  fun x y => if F x y then 1 else -1

/-- Minimum ordinary real rank over ALL strict real realizations (§2, p.7).
The existence proof uses only the canonical ±1 realization; no rank bound is built in. -/
noncomputable def signRank {X Y : Type*} [Fintype X] [Fintype Y]
    (F : Matrix X Y Bool) : ℕ := by
  classical
  have h : StrictRealizes F (canonicalRealization F) := by
    intro x y
    cases hF : F x y <;> norm_num [canonicalRealization, hF]
  exact Nat.find (show ∃ r : ℕ, ∃ H : Matrix X Y ℝ,
    StrictRealizes F H ∧ H.rank = r from
    ⟨(canonicalRealization F).rank, canonicalRealization F, h, rfl⟩)

end SignRankMargin.OREquality


