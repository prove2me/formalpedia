-- Prove2me | Definitions.Def_DedekindZeta_MellinPrinciple
-- name    : DedekindZeta_MellinPrinciple
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:45:02.469297+00:00
-- url     : https://prove2.me/theorems/1f469bff-33cb-4a00-b692-8ba24c6041d9
-- title:
--   Mellin Principle
-- statement:
--   Definitions and structural lemmas for Mellin Principle, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/MellinPrinciple.lean

import Mathlib
set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
namespace DedekindZeta.MellinPrinciple
noncomputable def reducedMellin (f : ℝ → ℂ) (a₀ : ℂ) (s : ℂ) : ℂ :=
  mellin (fun y => f y - a₀) s
structure IsMellinPair (f g : ℝ → ℂ) (a₀ b₀ C : ℂ) (k c α : ℝ) : Prop where
  /-- `f` is continuous on `ℝ_+^*`. The integrals only ever use `f` on `Ioi 0`,
  so this records exactly the part of the domain used by the integrals. -/
  hf_cont : ContinuousOn f (Set.Ioi (0 : ℝ))
  /-- `g` is continuous on `ℝ_+^*`. -/
  hg_cont : ContinuousOn g (Set.Ioi (0 : ℝ))
  /-- `k > 0` is the weight in the inversion law. -/
  hk : 0 < k
  /-- decay rate `c > 0`. -/
  hc : 0 < c
  /-- decay exponent `α > 0`. -/
  hα : 0 < α
  /-- `C ≠ 0` is the inversion constant. -/
  hC : C ≠ 0
  /-- `f(y) = a₀ + O(e^{-c y^α})` as `y → ∞`. -/
  hf_decay : (fun y : ℝ => f y - a₀) =O[atTop] (fun y : ℝ => Real.exp (-c * y ^ α))
  /-- `g(y) = b₀ + O(e^{-c y^α})` as `y → ∞`. -/
  hg_decay : (fun y : ℝ => g y - b₀) =O[atTop] (fun y : ℝ => Real.exp (-c * y ^ α))
  /-- the inversion law `f(1/y) = C · y^k · g(y)` for `y > 0`. -/
  hfe : ∀ y : ℝ, 0 < y → f (1 / y) = C * ((y ^ k : ℝ) : ℂ) * g y
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}
noncomputable def mellinTail (f g : ℝ → ℂ) (a₀ b₀ C : ℂ) (k : ℝ) (s : ℂ) : ℂ :=
  ∫ y in Ioi (1 : ℝ),
    ((f y - a₀) * (y : ℂ) ^ (s - 1)
      + C * (g y - b₀) * (y : ℂ) ^ ((k : ℂ) - s - 1))
noncomputable def mellinContinuation (f g : ℝ → ℂ) (a₀ b₀ C : ℂ) (k : ℝ) (s : ℂ) :
    ℂ :=
  -a₀ / s + C * b₀ / (s - (k : ℂ)) + mellinTail f g a₀ b₀ C k s
end DedekindZeta.MellinPrinciple


