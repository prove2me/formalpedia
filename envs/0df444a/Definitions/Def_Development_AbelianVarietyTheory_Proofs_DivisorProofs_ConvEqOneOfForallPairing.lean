-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:05.856466+00:00
-- url     : https://prove2.me/theorems/dd585929-ff7d-437c-8e94-99148bcb123d
-- title:
--   Conv Eq One Of Forall Pairing
-- statement:
--   Definitions and structural lemmas for Conv Eq One Of Forall Pairing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Theorems.Thm_GlobalTheory_PDivGroup_TateOver_conv_succ_pow
import Theorems.Thm_GlobalTheory_PDiv_pow_digit_natCast
import Theorems.Thm_ReciprocityTheory_PGsh_IsPtDer_map_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
namespace GlobalTheory
namespace TateFree
section Points
variable (O C A : Type) [CommRing O] [Field C] [Algebra O C] [IsIntegrallyClosedIn O C]
  [CommRing A]
variable [IsAlgClosed C] [CharZero C] [HopfAlgebra O A] [Module.Finite O A]
end Points
section Padic
variable {p : ℕ} [Fact p.Prime] {M N : Type} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup N]
  [Module ℤ_[p] N]
end Padic
end TateFree
namespace PDivGroup
open PDiv TateFree
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
section General
variable {B : Type} [CommRing B] [Algebra O B]
theorem ptsMap_res_injective (n : ℕ) : Function.Injective (pointsMap B (G.res n)) := fun x y h =>
  ofConv_injective <| AlgHom.ext fun a => by
    obtain ⟨b, rfl⟩ := G.res_surjective n a
    exact DFunLike.congr_fun (congrArg ofConv h) b
variable [Fact p.Prime] {G}
theorem TateOver.p_smul_conv (x : G.TateOver B) (n : ℕ) :
    ((p : ℤ_[p]) • x).conv n = x.conv n ^ p :=
  pow_digit_natCast (G.pts_pow_self n _) p
theorem TateOver.eq_zero_of_p_smul (t : G.TateOver B) (h : (p : ℤ_[p]) • t = 0) : t = 0 :=
  TateOver.ext_conv fun n => G.ptsMap_res_injective n <| by
    rw [← t.conv_succ_pow, ← TateOver.p_smul_conv, h, TateOver.zero_conv, TateOver.zero_conv,
      map_one]
instance TateOver.isTorsionFree : IsTorsionFree ℤ_[p] (G.TateOver B) := by
  refine .of_smul_eq_zero fun a t h => ?_
  by_cases ha : a = 0
  · exact .inl ha
  refine .inr ?_
  have key : ∀ (k : ℕ) (t : G.TateOver B), (p : ℤ_[p]) ^ k • t = 0 → t = 0 := fun k => by
    induction k with
    | zero => intro t h; rwa [pow_zero, one_smul] at h
    | succ k ih =>
      intro t h
      exact t.eq_zero_of_p_smul (ih _ (by rwa [pow_succ, mul_smul] at h))
  rw [PadicInt.unitCoeff_spec ha, mul_smul] at h
  exact key _ t ((Units.isUnit _).smul_eq_zero.1 h)
variable (G) in

def tateLevel (n : ℕ) : G.Tate →+ Additive (WithConv (G.A n →ₐ[O] O)) where
  toFun t := Additive.ofMul (t.conv n)
  map_zero' := rfl
  map_add' _ _ := rfl
end General
section Closed
variable (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C]
  [CharZero C]
include C
variable [Fact p.Prime]
end Closed
end PDivGroup
end GlobalTheory


