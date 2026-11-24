-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusOnRingA
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusOnRingA
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:42:46.629849+00:00
-- url     : https://prove2.me/theorems/b4d248bd-4f16-409c-b81b-7da1afba8cf2
-- title:
--   Frobenius On Ring A
-- statement:
--   Definitions and structural lemmas for Frobenius On Ring A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusOnRingA.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
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
namespace Formalism.L2.Th1.D
variable (l : ℕ) [Fact l.Prime]
def muSub : Submonoid ℂ_[l] where
  carrier := muPrime l
  one_mem' := ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.mp h), by simp⟩
  mul_mem' := by
    rintro a b ⟨n, hn, hln, ha⟩ ⟨m, hm, hlm, hb⟩
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases (Fact.out : l.Prime).dvd_mul.mp h with h | h
      exacts [hln h, hlm h]
    · rw [mul_pow, pow_mul, ha, one_pow, mul_comm n m, pow_mul, hb, one_pow, one_mul]
def evK (k : ℕ) : MonoidAlgebra ℤ (muSub l) →ₐ[ℤ] ℂ_[l] :=
  MonoidAlgebra.lift ℤ ℂ_[l] (muSub l) ((muSub l).subtype.comp (powMonoidHom k))
lemma evK_of (k : ℕ) (g : muSub l) :
    evK l k (MonoidAlgebra.of ℤ (muSub l) g) = (g : ℂ_[l]) ^ k := by
  simp [evK]
lemma evK_mem (k : ℕ) (r : MonoidAlgebra ℤ (muSub l)) : evK l k r ∈ ringA l := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    rw [evK_of]
    exact Subring.pow_mem _ (Subring.subset_closure g.2) k
  | add x y hx hy =>
    rw [map_add]
    exact Subring.add_mem _ hx hy
  | smul a x hx =>
    rw [zsmul_eq_mul, map_mul, map_intCast]
    exact Subring.mul_mem _ (intCast_mem _ a) hx
def evA (k : ℕ) : MonoidAlgebra ℤ (muSub l) →+* ringA l :=
  (evK l k).toRingHom.codRestrict (ringA l) (evK_mem l k)
end Formalism.L2.Th1.D


