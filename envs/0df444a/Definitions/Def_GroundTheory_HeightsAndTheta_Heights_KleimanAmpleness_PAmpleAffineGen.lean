-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:00:34.564799+00:00
-- url     : https://prove2.me/theorems/e72923a7-b227-4441-a677-a11a3854773b
-- title:
--   PAmple Affine Gen
-- statement:
--   Definitions and structural lemmas for PAmple Affine Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_pow_768a0aeb472a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_pow_mem_pow_9418c8e10619

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
open MvPolynomial
noncomputable section
universe u w
namespace AmpleAffineGen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
def unionChart (I J : Chart x) : Chart x :=
  ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩
def chartRatio (I J : Chart x) : Ω := xProd J ^ I.1.card / xProd I ^ J.1.card
def monoProd (T : Finset (Fin (N + 1))) : Poly S N := ∏ i ∈ T, X i
def ampleSubalg (H : SubSystem S x Ω) (m : ℕ) (h : Ω) (I : Chart x)
    (hh : h ∈ (H.pow m).sub I) : Subalgebra S Ω where
  carrier := ampleChart H m h I
  mul_mem' := by
    rintro a b ⟨n, hn⟩ ⟨n', hn'⟩
    refine ⟨n + n', ?_⟩
    have e : a * b * h ^ (n + n') = a * h ^ n * (b * h ^ n') := by ring
    rw [e, Nat.mul_add]
    exact AmpleTwistLocal.mul_mem_pow H I hn _ hn'
  add_mem' := by
    rintro a b ⟨n, hn⟩ ⟨n', hn'⟩
    refine ⟨n + n', ?_⟩
    have e : (a + b) * h ^ (n + n') = a * h ^ n * h ^ n' + b * h ^ n' * h ^ n := by ring
    rw [e, Nat.mul_add]
    refine add_mem (AmpleTwistLocal.mul_mem_pow H I hn _ (AmpleTwistLocal.pow_mem_pow H I hh n')) ?_
    rw [Nat.add_comm (m * n)]
    exact AmpleTwistLocal.mul_mem_pow H I hn' _ (AmpleTwistLocal.pow_mem_pow H I hh n)
  algebraMap_mem' s := ⟨0, by
    rw [pow_zero, mul_one, Nat.mul_zero]
    change _ ∈ twistMod S x 0 I
    have := Submodule.smul_mem (twistMod S x 0 I) (algebraMap S (chartRing S x I) s)
      (one_mem_twistMod_zero I)
    rwa [chartRing_smul_def, mul_one] at this⟩
def secChart (Q H : SubSystem S x Ω) (m b : ℕ) (h : Ω) (I : Chart x) : Set Ω :=
  {z | ∃ k : ℕ, z * h ^ k ∈ (Q.twist (H.pow (b + m * k))).sub I}
end AmpleAffineGen
end
end GroundTheory.Heights₂.Heights.Kleiman


