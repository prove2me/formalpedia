-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LeafCoeffVal
-- name    : Formalism_PeriodIntegrals_LeafCoeffVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:34.410279+00:00
-- url     : https://prove2.me/theorems/172d6b14-6204-408b-8dc2-4f1609d576eb
-- title:
--   Leaf Coeff Val
-- statement:
--   Definitions and structural lemmas for Leaf Coeff Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LeafCoeffVal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
open Finset
def posSub {n' : ℕ} (s : Fin n') (d : ℕ) : Fin n' :=
  ⟨(s.val + n' * d - d) % n', Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt)⟩
def posAdd {n' : ℕ} (s : Fin n') (e : ℕ) : Fin n' :=
  ⟨(s.val + e) % n', Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt)⟩
def IsLeaf (p : ℕ) {K : Type} [Field K] {h : ℕ} (t : Fin h → PowerSeries K) : Prop :=
  (∀ i, PowerSeries.constantCoeff (t i) = 0) ∧
  ∀ (i : Fin h) (n : ℕ), ∑ k ∈ range (n + 1), PowerSeries.coeff n ((t (posSub i k)) ^ (p ^ (2 * k))) / (p : K) ^ k =
    if i.val = 0 ∧ n = 1 then 1 else 0
def ze3 (p : ℕ) {K : Type} [Field K] {h : ℕ} (t : Fin h → PowerSeries K) (i1 : Fin h) : PowerSeries K :=
  PowerSeries.mk fun n =>
    ∑ k ∈ range (n + 1), PowerSeries.coeff n ((t (posSub i1 k)) ^ (p ^ (2 * k + 1))) / (p : K) ^ (k + 1)
def LeafCoeffVal : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (i0 : Fin 1) (t : Fin 1 → PowerSeries ℚ), IsLeaf p t → ∀ e : ℕ,
    padicValRat p (PowerSeries.coeff (p ^ 3 * p ^ e) ((-ze3 p t (posAdd i0 1)) ^ (p ^ e)) / ((p ^ e).factorial : ℚ)) =
      -(((p : ℤ) + 1) * (p : ℤ) ^ e + padicValNat p (p ^ e).factorial)
end PI
end


