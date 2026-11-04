-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
-- name    : Submission_ThreeSum_LightTernaryRowSelector
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:15.399909+00:00
-- url     : https://prove2.me/theorems/6f7f61b9-1228-4871-98fe-370674e11677
-- title:
--   Light Ternary Row Selector
-- statement:
--   Definitions and structural lemmas for Light Ternary Row Selector, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRowSelector.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
namespace ThreeSum.LightTernaryRowSelector
open Light
def Good (flag f₀ f₁ f₂ : ℕ → ℤ) (d₀ d₁ d₂ t₀ t₁ t₂ : ℕ) (i : ℕ) : Prop :=
  flag i ≠ 0 ∧ f₀ i*d₀ ≤ t₀ ∧ f₁ i*d₁ ≤ t₁ ∧ f₂ i*d₂ ≤ t₂
instance (flag f₀ f₁ f₂ : ℕ → ℤ) (d₀ d₁ d₂ t₀ t₁ t₂ i : ℕ) :
    Decidable (Good flag f₀ f₁ f₂ d₀ d₁ d₂ t₀ t₁ t₂ i) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
def pick (good : ℕ → Prop) [DecidablePred good] : ℕ → ℕ
  | 0 => 0
  | n+1 => if good n then n+1 else pick good n
def scanBody : Stmt :=
  .ite (M (v 0 +' v 11) =' k 0) .skip (
    .ite (v 8 <' M (v 1 +' v 11) *' v 5) .skip (
      .ite (v 9 <' M (v 2 +' v 11) *' v 6) .skip (
        .ite (v 10 <' M (v 3 +' v 11) *' v 7) .skip (.set 12 (v 11 +' k 1)))))
def body : Stmt := .set 12 (k 0) ;; .for 11 (v 4) scanBody ;; .set 0 (v 12)
def time (n : ℕ) : ℕ := 160*n+40
def word (n U d₀ d₁ d₂ t₀ t₁ t₂ : ℕ) : ℕ :=
  U*(d₀+d₁+d₂+1)+t₀+t₁+t₂+d₀+d₁+d₂+n+2
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body]
end ThreeSum.LightTernaryRowSelector


