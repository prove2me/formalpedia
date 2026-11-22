-- Prove2me | Definitions.Def_Formalism_LogFactorialBounds_LocalFactorSplitDv
-- name    : Formalism_LogFactorialBounds_LocalFactorSplitDv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:59.096851+00:00
-- url     : https://prove2.me/theorems/b312f928-c910-4d13-99df-ff3361020925
-- title:
--   Local Factor Split Dv
-- statement:
--   Definitions and structural lemmas for Local Factor Split Dv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialBounds/LocalFactorSplitDv.lean

import Definitions.Def_Formalism_LogFactorialBounds_LocalFactorSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LogFactorialBounds
open Finset Real
def LocalFactorTameDv : Prop :=
  ∀ (q : ℝ), 1 < q → ∀ (r t j : ℕ), 1 ≤ j → ∀ L : ℝ,
    (q ^ (r * j * t) * qE q 1 (r + j * t) / (qE q 1 r * qE q 1 (j * t))) *
        (qE q (t + 1) (r + j * t))⁻¹ *
        (q ^ (-((j * t * r : ℕ) : ℤ)) * qE q 1 r * L / (qE q (t + 1) (j * t))⁻¹) =
      L
def LocalFactorSplitDv : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    let q : ℝ := Fintype.card F
    ((Nat.card (GL (Fin a ⊕ Fin t) F) : ℝ) /
        (Nat.card (blockUpper (F := F) a t (J' : Set (GL (Fin a) F))) : ℝ)) *
      ((Nat.card J' : ℝ) * q ^ (-((a * a : ℕ) : ℤ)) * q ^ (-((a * t : ℕ) : ℤ))) =
    qE q (t + 1) (a + t)
def laguerre (n α : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * ((n + α).choose (n - k) : ℝ) * x ^ k / (k.factorial : ℝ)
def LaguerreCoeffBound : Prop :=
  ∀ (i j D : ℕ), i ≤ j → j ≤ D → ∀ s : ℝ, 0 ≤ s →
    Real.exp (-(s ^ 2) / 2) * Real.sqrt ((i.factorial : ℝ) / (j.factorial : ℝ)) * s ^ (j - i) *
        |laguerre i (j - i) (s ^ 2)| ≤
      Real.exp (-(s ^ 2) / 2) * (2 * (1 + s ^ 2)) ^ D
def ExpPowAbsorb : Prop :=
  ∀ R P : ℝ, 0 < R → 0 < P →
    Real.exp (-(π * R)) * R ^ P ≤ Real.exp (-((π - 1) * R)) * P ^ P
def PrimeSetLogSum : Prop :=
  ∀ B : ℕ, 2 ≤ B → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ B →
    ∑ p ∈ P, Real.log p / ((p : ℝ) - 1) ≤ 10 * Real.log B
end Formalism.LogFactorialBounds


