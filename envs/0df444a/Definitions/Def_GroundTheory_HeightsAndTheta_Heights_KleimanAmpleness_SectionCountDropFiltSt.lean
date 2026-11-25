-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltSt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:12:25.963781+00:00
-- url     : https://prove2.me/theorems/8203bc28-25f2-453a-8393-50392d8ea29b
-- title:
--   Section Count Drop Filt St
-- statement:
--   Definitions and structural lemmas for Section Count Drop Filt St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SectionCountDropFiltSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open Filter
noncomputable section
universe u w
open Classical in

def SectionCount.Drop.Filt.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) → 1 ≤ b →
    ∃ β ∈ (twistSys k x (b : ℤ)).secs,
      (∃ I, β ∉ ((twistSys k x (b : ℤ)).twist (idealSys x (primeOf (S := k) x))).sub I) ∧
      ∃ (m : ℕ) (pp : Fin m → Ideal (Poly k N)) (e : Fin m → ℕ) (c : Fin m → ℤ),
        (∀ j, IsSubvar x (pp j) (e j) ∧ e j ≤ d ∧
          primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β ≤ pp j) ∧
        (∀ qq : Ideal (Poly k N),
          ((Finset.univ.filter fun j => e j = d ∧ pp j = qq).card : ℤ) =
            if h : qq ∈ (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β).minimalPrimes ∧
                IsSubvar x qq d then
              haveI : qq.IsPrime := h.1.1.1
              ((cutMult (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β) qq).toNat : ℤ)
            else 0) ∧
        ∀ n i : ℕ,
          (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℤ) -
              (Module.finrank k (twistMul Nb.toSubSystem n (-(((i + 1 : ℕ) : ℤ) * b))).secs : ℤ) ≤
            ∑ j, (Module.finrank k (SubSystem.quotH
              ((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x (c j)))
              (((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x (c j))).twist
                (idealSys x (pp j))) 0) : ℤ)
end
end GroundTheory.Heights₂.Heights.Kleiman


