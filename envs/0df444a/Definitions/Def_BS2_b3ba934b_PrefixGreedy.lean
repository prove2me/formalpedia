-- Prove2me | Definitions.Def_BS2_b3ba934b_PrefixGreedy
-- name    : BS2_b3ba934b_PrefixGreedy
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:24:25.507753+00:00
-- url     : https://prove2.me/theorems/003faa6e-8eb1-4d40-9022-3335d6fcf349
-- title:
--   Sensitivity separation: PrefixGreedy (complete source module)
-- statement:
--   Complete Lean source module `PrefixGreedy` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/PrefixGreedy.lean; original SHA-256 522d37d6d27d7b7feb95f651b197fb6e18e92c2dc4a065f3b52b2586a514d33d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact greedy allocation for the simultaneous negative-candidate prefix caps.
The hypotheses concern actual counts and decreasing costs.  No transfer
inequality is assumed. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundGreedy

theorem weighted_two_prefix (n₀ n₁ g₀ g₁ a₀ a₁ : ℕ)
    (h₀ : n₀ ≤ g₀) (h₁ : n₀+n₁ ≤ g₀+g₁) (ha : a₁ ≤ a₀) :
    n₀*a₀+n₁*a₁ ≤ g₀*a₀+g₁*a₁ := by
  let d := a₀-a₁
  have hd : a₀ = d+a₁ := (Nat.sub_add_cancel ha).symm
  rw [hd]
  calc
    n₀*(d+a₁)+n₁*a₁ = n₀*d+(n₀+n₁)*a₁ := by ring
    _ ≤ g₀*d+(g₀+g₁)*a₁ := Nat.add_le_add
      (Nat.mul_le_mul_right d h₀) (Nat.mul_le_mul_right a₁ h₁)
    _ = g₀*(d+a₁)+g₁*a₁ := by ring

theorem weighted_three_prefix (n₀ n₁ n₂ g₀ g₁ g₂ a₀ a₁ a₂ : ℕ)
    (h₀ : n₀ ≤ g₀) (h₁ : n₀+n₁ ≤ g₀+g₁)
    (h₂ : n₀+n₁+n₂ ≤ g₀+g₁+g₂)
    (ha₀ : a₁ ≤ a₀) (ha₁ : a₂ ≤ a₁) :
    n₀*a₀+n₁*a₁+n₂*a₂ ≤ g₀*a₀+g₁*a₁+g₂*a₂ := by
  let d₀ := a₀-a₁
  let d₁ := a₁-a₂
  have e₀ : a₀ = d₀+a₁ := (Nat.sub_add_cancel ha₀).symm
  have e₁ : a₁ = d₁+a₂ := (Nat.sub_add_cancel ha₁).symm
  rw [e₀,e₁]
  calc
    _ = n₀*d₀+(n₀+n₁)*d₁+(n₀+n₁+n₂)*a₂ := by ring
    _ ≤ g₀*d₀+(g₀+g₁)*d₁+(g₀+g₁+g₂)*a₂ :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right d₀ h₀)
        (Nat.mul_le_mul_right d₁ h₁)) (Nat.mul_le_mul_right a₂ h₂)
    _ = _ := by ring

theorem weighted_four_prefix
    (n₀ n₁ n₂ n₃ g₀ g₁ g₂ g₃ a₀ a₁ a₂ a₃ : ℕ)
    (h₀ : n₀ ≤ g₀) (h₁ : n₀+n₁ ≤ g₀+g₁)
    (h₂ : n₀+n₁+n₂ ≤ g₀+g₁+g₂)
    (h₃ : n₀+n₁+n₂+n₃ ≤ g₀+g₁+g₂+g₃)
    (ha₀ : a₁ ≤ a₀) (ha₁ : a₂ ≤ a₁) (ha₂ : a₃ ≤ a₂) :
    n₀*a₀+n₁*a₁+n₂*a₂+n₃*a₃ ≤ g₀*a₀+g₁*a₁+g₂*a₂+g₃*a₃ := by
  let d₀ := a₀-a₁
  let d₁ := a₁-a₂
  let d₂ := a₂-a₃
  have e₀ : a₀ = d₀+a₁ := (Nat.sub_add_cancel ha₀).symm
  have e₁ : a₁ = d₁+a₂ := (Nat.sub_add_cancel ha₁).symm
  have e₂ : a₂ = d₂+a₃ := (Nat.sub_add_cancel ha₂).symm
  rw [e₀,e₁,e₂]
  calc
    _ = n₀*d₀+(n₀+n₁)*d₁+(n₀+n₁+n₂)*d₂+(n₀+n₁+n₂+n₃)*a₃ := by ring
    _ ≤ g₀*d₀+(g₀+g₁)*d₁+(g₀+g₁+g₂)*d₂+(g₀+g₁+g₂+g₃)*a₃ :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_right d₀ h₀) (Nat.mul_le_mul_right d₁ h₁))
        (Nat.mul_le_mul_right d₂ h₂)) (Nat.mul_le_mul_right a₃ h₃)
    _ = _ := by ring

/-- The two-level fill used at q=1 after removing the positive prefix. -/
theorem greedy_two (n₀ n₁ c₀ c₁ a₀ a₁ : ℕ)
    (h₀ : n₀ ≤ c₀) (h₁ : n₀+n₁ ≤ c₁) (ha : a₁ ≤ a₀) :
    n₀*a₀+n₁*a₁ ≤ min c₀ c₁*a₀+(c₁-min c₀ c₁)*a₁ := by
  apply weighted_two_prefix
  · exact le_min h₀ (by omega)
  · have hh := Nat.sub_add_cancel (min_le_right c₀ c₁)
    omega
  · exact ha

/-- The three-level fill used at q=2.  Suffix minima make every
    simultaneous prefix constraint hold, even if the original caps fall. -/
theorem greedy_three (n₀ n₁ n₂ c₀ c₁ c₂ a₀ a₁ a₂ : ℕ)
    (h₀ : n₀ ≤ c₀) (h₁ : n₀+n₁ ≤ c₁) (h₂ : n₀+n₁+n₂ ≤ c₂)
    (ha₀ : a₁ ≤ a₀) (ha₁ : a₂ ≤ a₁) :
    let g₀ := min c₀ (min c₁ c₂)
    let g₁ := min c₁ c₂-g₀
    let g₂ := c₂-(g₀+g₁)
    n₀*a₀+n₁*a₁+n₂*a₂ ≤ g₀*a₀+g₁*a₁+g₂*a₂ := by
  dsimp only
  apply weighted_three_prefix
  · exact le_min h₀ (le_min (by omega) (by omega))
  · have hh := Nat.sub_add_cancel (min_le_right c₀ (min c₁ c₂))
    have hx : n₀+n₁ ≤ min c₁ c₂ := le_min h₁ (by omega)
    omega
  · have hh := Nat.sub_add_cancel (min_le_right c₀ (min c₁ c₂))
    have hl := min_le_right c₁ c₂
    omega
  · exact ha₀
  · exact ha₁

/-- The q=3 negative allocation uses the same argument with four tiers. -/
theorem greedy_four (n₀ n₁ n₂ n₃ c₀ c₁ c₂ c₃ a₀ a₁ a₂ a₃ : ℕ)
    (h₀ : n₀ ≤ c₀) (h₁ : n₀+n₁ ≤ c₁)
    (h₂ : n₀+n₁+n₂ ≤ c₂) (h₃ : n₀+n₁+n₂+n₃ ≤ c₃)
    (ha₀ : a₁ ≤ a₀) (ha₁ : a₂ ≤ a₁) (ha₂ : a₃ ≤ a₂) :
    let g₀ := min c₀ (min c₁ (min c₂ c₃))
    let g₁ := min c₁ (min c₂ c₃)-g₀
    let g₂ := min c₂ c₃-(g₀+g₁)
    let g₃ := c₃-(g₀+g₁+g₂)
    n₀*a₀+n₁*a₁+n₂*a₂+n₃*a₃ ≤ g₀*a₀+g₁*a₁+g₂*a₂+g₃*a₃ := by
  dsimp only
  have hm₀ := min_le_right c₀ (min c₁ (min c₂ c₃))
  have hm₁ := min_le_right c₁ (min c₂ c₃)
  have hm₂ := min_le_right c₂ c₃
  have he₀ := Nat.sub_add_cancel hm₀
  have he₁ := Nat.sub_add_cancel hm₁
  apply weighted_four_prefix
  · exact le_min h₀ (le_min (by omega) (le_min (by omega) (by omega)))
  · have hx : n₀+n₁ ≤ min c₁ (min c₂ c₃) :=
      le_min h₁ (le_min (by omega) (by omega))
    omega
  · have hx : n₀+n₁+n₂ ≤ min c₂ c₃ := le_min h₂ (by omega)
    omega
  · omega
  · exact ha₀
  · exact ha₁
  · exact ha₂

/-- Actual positive and negative prefix counts justify subtraction of
    the fixed positive contribution before running the greedy fill. -/
theorem remove_positive_prefix (negative positive cap : ℕ)
    (h : negative+positive ≤ cap) : negative ≤ cap-positive := by omega

/-- A nonnegative head increment can be charged once per incoming arc,
    even when several arcs hit one head. -/
theorem repeated_increment_safe (base increment count : ℕ) (hc : 1 ≤ count) :
    base+increment ≤ base+count*increment :=
  Nat.add_le_add_left (by simpa using Nat.mul_le_mul_right increment hc) base

end ThreeBoundGreedy

#print axioms ThreeBoundGreedy.greedy_three
#print axioms ThreeBoundGreedy.greedy_four


