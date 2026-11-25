-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PSmall
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_PSmall
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:21.899975+00:00
-- url     : https://prove2.me/theorems/88f8f0c7-dbc5-4a5d-b457-75b231b371fa
-- title:
--   PSmall
-- statement:
--   Definitions and structural lemmas for PSmall, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean

import Definitions.Def_Formalism_SizeWindowBrackets_SSmall
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_unitOfCoprime_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.LFunctionChainParameters.LSmall
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section Conj
open Matrix Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
section
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}
end
end Conj
section Host
open Formalism.LFunctionChainParameters.LHost
open Formalism.FrobeniusOrbits (HostHyp HGrp hcl)
lemma hOf_of_coprime {e m : ℕ} (h : m.Coprime (2 ^ (e + 2))) :
    hOf e m = Additive.ofMul (hcl e (ZMod.unitOfCoprime m h)) := dif_pos h
section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]
end
section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]
end
lemma odd_iff_cop (e m : ℕ) : Odd m ↔ m.Coprime (2 ^ (e + 2)) := by
  rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_two_right]
lemma hOf_one (e : ℕ) : hOf e 1 = 0 := by
  rw [hOf_of_coprime (Nat.coprime_one_left _), unitOfCoprime_one]
  rfl
lemma hOf_mul (e : ℕ) {a b : ℕ} (ha : Odd a) (hb : Odd b) : hOf e (a * b) = hOf e a + hOf e b := by
  have ca := (odd_iff_cop e a).1 ha
  have cb := (odd_iff_cop e b).1 hb
  rw [hOf_of_coprime ca, hOf_of_coprime cb, hOf_of_coprime (Nat.Coprime.mul_left ca cb)]
  have : ZMod.unitOfCoprime (a * b) (Nat.Coprime.mul_left ca cb) = ZMod.unitOfCoprime a ca * ZMod.unitOfCoprime b cb := by
    ext; simp
  rw [this]
  rfl
lemma omV_one (e : ℕ) (ψ : AddChar (E0 × HA e) ℂ) : omV e ψ 1 = 1 := by
  unfold omV
  split_ifs with h1 h2
  · rfl
  · rw [hOf_one]; exact AddChar.map_zero_eq_one ψ
  · exact absurd odd_one h2
lemma omV_mul (e : ℕ) (ψ : AddChar (E0 × HA e) ℂ) (a b : ℕ) : omV e ψ (a * b) = omV e ψ a * omV e ψ b := by
  unfold omV
  by_cases h1 : ∀ t : HA e, ψ ((0, 0), t) = 1
  · simp only [if_pos h1, mul_one]
  simp only [if_neg h1]
  by_cases ha : Odd a
  · by_cases hb : Odd b
    · rw [if_pos ha, if_pos hb, if_pos (ha.mul hb), hOf_mul e ha hb, ← AddChar.map_add_eq_mul]
      simp
    · rw [if_neg hb, if_neg (fun h => hb (Nat.odd_mul.1 h).2), mul_zero]
  · rw [if_neg ha, if_neg (fun h => ha (Nat.odd_mul.1 h).1), zero_mul]
lemma laV_one (s : ℂ) (l : ℕ) : laV s l 1 = 1 := by
  unfold laV
  split_ifs
  · rfl
  · simp
lemma laV_mul (s : ℂ) (l a b : ℕ) : laV s l (a * b) = laV s l a * laV s l b := by
  unfold laV
  split_ifs
  · simp
  · rw [Nat.cast_mul, jacobiSym.mul_left]; push_cast; rfl
def prodHom (e q d : ℕ) (ψ : AddChar (E0 × HA e) ℂ) : ℕ →* ℂ where
  toFun m := omV e ψ m * laV (ψ sg) q m * laV (ψ sgc0) d m
  map_one' := by rw [omV_one, laV_one, laV_one]; norm_num
  map_mul' a b := by rw [omV_mul, laV_mul, laV_mul]; ring
section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]
end
end Host
end Formalism.LFunctionChainParameters.LSmall


