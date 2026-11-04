-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
-- name    : Submission_ThreeSum_TernaryExtensionEncoding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:20.005472+00:00
-- url     : https://prove2.me/theorems/29b9c725-e8bf-4e26-8a99-ced844fe63fa
-- title:
--   Ternary Extension Encoding
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionEncoding.lean

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Nat.Digits.Lemmas
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial
set_option maxHeartbeats 3000000
variable (p : ℕ) [Fact p.Prime]
variable {p}
def coefficients {f : (ZMod p)[X]} (hf : f.Monic) :
    AdjoinRoot f ≃ₗ[ZMod p] (Fin f.natDegree → ZMod p) :=
  (AdjoinRoot.powerBasisAux' hf).equivFun
def constantCoefficient {f : (ZMod p)[X]} (hf : f.Monic) (hd : 0<f.natDegree) :
    AdjoinRoot f →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj (⟨0,hd⟩ : Fin f.natDegree)).comp (coefficients hf).toLinearMap
theorem extension_card {f : (ZMod p)[X]} (hf : f.Monic) :
    Nat.card (AdjoinRoot f)=p^f.natDegree := by
  rw [Nat.card_congr (coefficients hf).toEquiv]
  simp [Nat.card_fun,Nat.card_zmod]
def encode {f : (ZMod p)[X]} (hf : f.Monic) (x : AdjoinRoot f) : ℕ :=
  Nat.ofDigits p (List.ofFn fun i => ((coefficients hf) x i).val)
theorem encode_lt {f : (ZMod p)[X]} (hf : f.Monic) (x : AdjoinRoot f) :
    encode hf x<p^f.natDegree := by
  have hp : 1<p := (Fact.out : p.Prime).one_lt
  have h := Nat.ofDigits_lt_base_pow_length hp
    (l := List.ofFn fun i => ((coefficients hf) x i).val) (by
      intro n hn
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
      exact ZMod.val_lt _)
  simpa [encode] using h
theorem encode_injective {f : (ZMod p)[X]} (hf : f.Monic) :
    Function.Injective (encode hf) := by
  intro x y hxy
  have hlist : (List.ofFn fun i => ((coefficients hf) x i).val)=
      (List.ofFn fun i => ((coefficients hf) y i).val) := by
    apply Nat.ofDigits_inj_of_len_eq (Fact.out : p.Prime).one_lt (by simp)
    · intro n hn
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
      exact ZMod.val_lt _
    · intro n hn
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
      exact ZMod.val_lt _
    · exact hxy
  apply (coefficients hf).injective
  funext i
  apply ZMod.val_injective
  have he := congrArg (fun l : List ℕ => l[i.val]?) hlist
  simpa using he
def encodedEquiv {f : (ZMod p)[X]} (hf : f.Monic) :
    AdjoinRoot f ≃ Fin (p^f.natDegree) := by
  letI : Fintype (AdjoinRoot f) := Fintype.ofEquiv
    (Fin f.natDegree → ZMod p) (coefficients hf).toEquiv.symm
  exact Equiv.ofBijective (fun x => ⟨encode hf x,encode_lt hf x⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y h => encode_injective hf (congrArg Fin.val h),by
        simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using extension_card hf⟩)
end ThreeSum.TernaryExtensionEncoding


