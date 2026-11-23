-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionWeights
-- name    : Formalism_EllipticTorsion_EllipticTorsionWeights
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:11.849801+00:00
-- url     : https://prove2.me/theorems/31fe15ff-f663-4853-ada4-64ec7052a201
-- title:
--   Elliptic Torsion Weights
-- statement:
--   Definitions and structural lemmas for Elliptic Torsion Weights, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionWeights.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL
open Formalism.G
def EllipticTorsionWeights : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    0 < ‖(p : K)‖ → ‖(p : K)‖ < 1 →
    ∀ (F : FormalGroup (unitBall K)) (l E g : PowerSeries K) (ζ : K),
      IsLog (FK F) l → constantCoeff E = 0 → E.subst l = X → l.subst E = X →
      (∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ ‖(p : K)‖ ^ (-((n : ℝ) - 1) / ((p : ℝ) ^ 2 - 1))) →
      ζ ^ (p ^ 2 - 1) = 1 → (∀ m : ℕ, ¬ (p ^ 2 - 1) ∣ m → ‖ζ ^ m - 1‖ = 1) →
      IsHom (FK F) (FK F) (ζ • X) →
      constantCoeff g = 0 →
      IntegralMv (g.subst (FK F).toPowerSeries - atX g - atY g) →
      IntegralPS (g.subst (ζ • X : PowerSeries K) - ζ ^ p • g) →
      ‖coeff 1 g‖ ≤ 1 →
      ∀ n : ℕ,
        ‖coeff n (g.subst E)‖ ≤ ‖(p : K)‖ ^ (-(n : ℝ) / ((p : ℝ) ^ 2 - 1)) ∨
        (∃ j : ℕ, Odd j ∧ n = p ^ j ∧
          ‖coeff n (g.subst E)‖ ≤ ‖(p : K)‖ ^ (-1 - (n : ℝ) / ((p : ℝ) ^ 2 - 1)))
def FrobExpand : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (p : ℕ), p.Prime → ‖(p : K)‖ < 1 →
    ∀ (m j : ℕ) (a b : Fin m → K), (∀ e, ‖a e‖ ≤ 1) → (∀ e, ‖a e ^ (p ^ j) - b e‖ ≤ ‖(p : K)‖) →
      ∀ α : Fin m →₀ ℕ,
        ‖MvPolynomial.coeff α
            ((∑ e, MvPolynomial.C (a e) * MvPolynomial.X e) ^ (p ^ j)
              - (∑ e, MvPolynomial.C (b e) * MvPolynomial.X e ^ (p ^ j)))‖ ≤ ‖(p : K)‖
end Formalism.ELL


