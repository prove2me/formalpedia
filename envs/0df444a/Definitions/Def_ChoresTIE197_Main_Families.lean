-- Prove2me | Definitions.Def_ChoresTIE197_Main_Families
-- name    : ChoresTIE197_Main_Families
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T02:18:55.434061+00:00
-- url     : https://prove2.me/theorems/998aac03-6c0e-4fc1-8e38-9b3cd4f784da
-- title:
--   Uniform procedure families and the headline zero-type wrapper
-- statement:
--   Total family interfaces expose the same procedures to the uniform complexity predicates. Inapplicable dimensions return empty subsets or zero weights and are excluded by the relevant source domains. These values supply no correctness conclusion.
--
--   For positive profiles, the headline construction selects Mechanism 3 for two agents, Mechanism 2 with $k=\lfloor(n-1)/2\rfloor$ for $3\le n\le65$, and the large-agent procedure thereafter. On every profile with an identically zero reported row it instead assigns all chores to the first such agent in public order. Empty chore sets are included. The wrapper is not claimed equal-marginal.
--
--   The purpose is to make the extension beyond the paper's internal positive-MMS convention explicit. The headline theorem still asserts one mechanism for all reports and unilateral deviations; the zero-branch comparisons are recorded in the verification module and moderation notes.
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Result 1 and §4.6, with p.7 zero-type convention, printed p.3, PDF p.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Computation
import Definitions.Def_ChoresTIE197_Main_TwoAgent
import Definitions.Def_ChoresTIE197_Main_Nomination
import Definitions.Def_ChoresTIE197_Main_Large

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

/-- Total interfaces for uniform complexity quantifiers. Inapplicable dimensions
are excluded by the domain in each theorem, not used as a source special case. -/
def commonFamily (m : ℕ) (c : Profile 2 m) : Finset (Fin m) :=
  if h : 0 < m then letI : NeZero m := ⟨Nat.ne_of_gt h⟩; commonPartition c else ∅

def distinctFamily (m : ℕ) (c : Profile 2 m) : Finset (Fin m) :=
  if h : 0 < m then letI : NeZero m := ⟨Nat.ne_of_gt h⟩; distinctPartition c else ∅

def twoFamily (n m _k : ℕ) (c : Profile n m) (A : Allocation n m) : ℝ≥0∞ :=
  if h : n = 2 then by
    subst n
    exact if hm : 0 < m then
      letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
      mechanism3 c A
    else 0
  else 0

def nominationFamily (n m k : ℕ) (c : Profile n m) (A : Allocation n m) : ℝ≥0∞ :=
  if h : 0 < n then letI : NeZero n := ⟨Nat.ne_of_gt h⟩; mechanism2 k c A else 0

def largeFamily (n m _k : ℕ) (c : Profile n m) (A : Allocation n m) : ℝ≥0∞ :=
  if h : 0 < n then letI : NeZero n := ⟨Nat.ne_of_gt h⟩; mechanism4 c A else 0

def headlineCore {n m : ℕ} [NeZero n] : Mechanism n m :=
  if h : n = 2 then by
    subst n
    exact if hm : 0 < m then
      letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
      mechanism3
    else fun _ => PMF.pure (fun _ => 0)
  else if n ≤ 65 then mechanism2 ((n-1)/2) else mechanism4

/-- Public first zero reporter, or the appropriate n-dependent positive branch. -/
def headline {n m : ℕ} [NeZero n] : Mechanism n m := zeroWrap headlineCore

end ChoresTIE197.Main


