-- Prove2me | Definitions.Def_Formalism_IncomingBounds_LevelTail
-- name    : Formalism_IncomingBounds_LevelTail
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:27.617864+00:00
-- url     : https://prove2.me/theorems/cdcd5027-8534-4451-91a8-34a74cec225e
-- title:
--   Level Tail
-- statement:
--   Definitions and structural lemmas for Level Tail, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/LevelTail.lean

import Definitions.Def_Formalism_IncomingBounds_IncomingBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.IncomingBounds
def chSol (d : ℕ) (l h : ℝ) (p : ZMod d → ℝ) (a : ZMod d) : ℝ :=
  ∑' k : ℕ, (h - p (a + ((k + 1 : ℕ) : ZMod d))) / l ^ (k + 1)
def CHRecursion : Prop :=
  ∀ (d : ℕ) [NeZero d] (l : ℝ), 1 < l → ∀ (h : ℝ) (p x : ZMod d → ℝ),
    (∀ a : ZMod d, x a + (h - p a) = l * x (a - 1)) ↔ ∀ a : ZMod d, x a = chSol d l h p a
def CHValue : Prop :=
  ∀ (d : ℕ) [NeZero d] (l : ℕ), 2 ≤ l → 2 ≤ d → Even d →
    ∀ (r j j' rh : ℕ), rh ≤ j' → j + j' ≤ r →
      (∀ a : ZMod d, Even a.val →
        chSol d l ((r : ℝ) - rh) (fun b => if Even b.val then (r : ℝ) - j' else (j' : ℝ)) a =
            ((r : ℝ) - j' - rh) * gam l + ((j' : ℝ) - rh) * rho l ∧
          chSol d l ((r : ℝ) - rh) (fun b => if Even b.val then (r : ℝ) - j' else (j' : ℝ)) a ≤
            ((r - j' - j : ℕ) : ℝ) * gam l + ((j + j' : ℕ) : ℝ) / ((l : ℝ) - 1)) ∧
      ∀ a : ZMod d,
        chSol d l ((r : ℝ) - rh) (fun _ => (r : ℝ) - j') a = ((j' : ℝ) - rh) / ((l : ℝ) - 1) ∧
          ((j' : ℝ) - rh) / ((l : ℝ) - 1) ≤ ((j + j' : ℕ) : ℝ) / ((l : ℝ) - 1)
def NewtonWindow : Prop :=
  ∀ (R : Type) [CommRing R] (I : AddSubgroup R) (D : ℕ) (a : ℕ → R) (y0 : ℕ),
    (∀ t ≤ D, (∑ s ∈ Finset.range (D + 1), a s * ((Nat.choose (y0 + t) s : ℕ) : R)) ∈ I) →
      ∀ y : ℕ, (∑ s ∈ Finset.range (D + 1), a s * ((Nat.choose y s : ℕ) : R)) ∈ I
def capNat (n0 y : ℕ) : ℕ := ∏ a ∈ Finset.range n0, (y + a).factorial / a.factorial
def CapVal : Prop :=
  ∀ l : ℕ, l.Prime → ∀ n0 n y : ℕ, n0 ≤ n →
    (padicValNat l (capNat n0 y) : ℝ) ≤ (n0 : ℝ) * y / ((l : ℝ) - 1) + n * (Real.logb l n + 1)
def uFac (l x : ℕ) : ℚ := (-1) ^ x * ((l * x).factorial : ℚ) / ((l : ℚ) ^ x * (x.factorial : ℚ))
def FactSplit : Prop :=
  ∀ l : ℕ, 2 ≤ l → ∀ i x : ℕ,
    (((l ^ i * x).factorial : ℕ) : ℚ) =
      (-1) ^ ((∑ s ∈ Finset.range i, l ^ s) * x) * (l : ℚ) ^ ((∑ s ∈ Finset.range i, l ^ s) * x) *
        (x.factorial : ℚ) * ∏ s ∈ Finset.range i, uFac l (l ^ s * x)
def WeightIdentities : Prop :=
  ∀ l : ℕ, 2 ≤ l → ∀ i : ℕ, 1 ≤ i →
    (-(1 + ((l : ℝ) ^ i - l) * rho l) + (l : ℝ) ^ i * (rho l + ((l : ℝ) ^ i)⁻¹ / 2) +
        (rho l + 1 / 2) = 1 / ((l : ℝ) - 1)) ∧
      (∀ B : ℝ, ((l : ℝ) ^ i * B) * (rho l + ((l : ℝ) ^ i)⁻¹ / 2) + B * (rho l + 1 / 2) =
        B * ((1 + ((l : ℝ) ^ i - l) * rho l) + 1 / ((l : ℝ) - 1))) ∧
      (((l : ℝ) ^ i - 1) / ((l : ℝ) - 1) - (1 + ((l : ℝ) ^ i - l) * rho l) + 1 / ((l : ℝ) - 1) =
        ((l : ℝ) ^ i + 1) * gam l - 1) ∧
      0 ≤ ((l : ℝ) ^ i + 1) * gam l - 1
def ContentShift : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d → ∀ (th : ℝ) (D' E : ZMod d → ℝ),
    0 ≤ th → 0 ≤ D' → 0 ≤ E → (∀ a, E a ≤ 2 * th * D' a) →
      Fnum l d D' ≤ Fnum l d (D' + E) + 6 * th * (∑ a : ZMod d, D' a) / l
def LevelTail : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → ∀ (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ), IsFlow l d D x →
    ∀ i0 : ℕ,
      (∑ a : ZMod d, ∑ i ∈ (oddLevels d).filter (fun i => i0 ≤ i), x a i) ≤
        (∑ a : ZMod d, D a) / (l : ℝ) ^ i0
end Formalism.IncomingBounds


