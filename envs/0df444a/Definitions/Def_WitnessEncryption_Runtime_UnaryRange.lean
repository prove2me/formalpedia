-- Prove2me | Definitions.Def_WitnessEncryption_Runtime_UnaryRange
-- name    : WitnessEncryption_Runtime_UnaryRange
-- status  : Definition
-- author  : @vigyan
-- created : 2026-11-16T10:54:18.58451+00:00
-- url     : https://prove2.me/theorems/c8ec4849-c872-48a6-ac66-3ba3dfd9eb34
-- title:
--   Certified enumeration of unary natural ranges
-- statement:
--   For a natural number $k$ in the unary data encoding, this module gives a concrete realizer of the list $[0,1,\ldots,k-1]$, with the empty list when $k=0$. The input encoding has volume $2k+1$, and the enumerated list has exact volume
--
--   $$\operatorname{vol}([0,1,\ldots,k-1])=k^2+k+1.$$
--
--   The realizer has a polynomial resource certificate: there are fixed constants $C,d\in\mathbb N$ such that its charged running time on input $k$ is at most $C(2k+3)^d$. This bound is measured in the unary input volume. The module also supplies the certified unary successor, an encoding-preserving conversion from $k$ to a list of $k$ units, and the prepared-fold certificate used to construct the range program. This range interface is used by the feature-enumeration programs in the witness-encryption rank reduction.
-- source:
--   Runtime formalization supporting Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, Section 6.5 and Theorem 6.1; supplied paper https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf . Exact selected original declarations from WitnessEncryption/Runtime/NatPrimitives.lean, Prime/UnaryPower.lean, PreparedFold.lean and Features/Metadata.lean; original declaration bodies unchanged; export SHA256 1833605fbb0a58fc0c0ab4ab6eb00d6b982b32db94990ed340440edf9821a3a3.

import Definitions.Def_WitnessEncryption_Runtime_Core

set_option autoImplicit false

section
-- Source: WitnessEncryption.Runtime.NatPrimitives

namespace WitnessEncryption.Runtime.NatPrimitives
open OAI.ThreeMachine.StackCompiler

/-- Unary-small Nat successor; this is polynomial in Coding volume, not bit length. -/
theorem succ_certified : Certified Realizer.succ := by
  refine ⟨1, ?_, ?_⟩
  · apply Poly.of_le (g := fun n : ℕ => 200*(volume n+2))
    · intro n
      exact (Realizer.time_succ_le n).trans (by rw [volume_nat]; omega)
    · simpa only [pow_one] using Poly.powerBase (volume : ℕ → ℕ) 200 1
  · apply Poly.of_le (g := fun n : ℕ => volume n+2) _ (Poly.base volume)
    intro n
    change volume (n+1) ≤ volume n+2
    simp only [volume_nat]
    omega











end WitnessEncryption.Runtime.NatPrimitives


end

section
-- Source: WitnessEncryption.Runtime.Prime.UnaryPower

namespace WitnessEncryption.Runtime.Prime
open OAI.ThreeMachine.StackCompiler
namespace UnaryPowerProof

















/-- Unary Nat and an equal-length list of units have exactly the same encoding. -/
theorem enc_units (k : ℕ) : enc (List.replicate k ()) = enc k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,enc_cons,enc_unit,enc_succ,ih]

def unitsR : Realizer (fun k : ℕ => List.replicate k ()) :=
  Realizer.reinterpret _ enc_units

theorem unitsR_certified : Certified unitsR := Certified.reinterpret _ _





end UnaryPowerProof











end WitnessEncryption.Runtime.Prime

end

section
-- Source: WitnessEncryption.Runtime.PreparedFold

namespace WitnessEncryption.Runtime.FeatureCost
open OAI.ThreeMachine.StackCompiler

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [Coding α] [Coding β] [Coding γ]

/-- Certify the actual preparation followed by a fold. Prefix bounds are required
for every input of the whole program, from its literal prepared state. -/
theorem prepared_fold {prepare : α → List β × γ} (P : Realizer prepare) (hP : Certified P)
    {step : β × γ → γ} (R : Realizer step) (hR : Certified R)
    (hV : ∃ C k : ℕ, ∀ (x : α) (j : ℕ), j ≤ (prepare x).1.length →
      volume (((prepare x).1.take j).foldl (fun s a => step (a,s)) (prepare x).2) ≤
        C*(volume x+2)^k) : Certified (P.comp R.fold) := by
  rcases hP with ⟨e,hpt,hpv⟩
  rcases hR with ⟨d,⟨D,hD⟩,_⟩
  rcases hV with ⟨C,k,hC⟩
  let size : α → ℕ := volume
  let V : α → ℕ := fun x => C*(size x+2)^k
  let T : α → ℕ := fun x => D*(volume (prepare x)+V x+3)^d
  have hx : Poly size (fun x => volume (prepare x).1) e :=
    Poly.of_le (fun x => by rw [volume_prod]; omega) hpv
  have hl : Poly size (fun x => (prepare x).1.length) e :=
    Poly.of_le (fun x => length_le_volume (prepare x).1) hx
  have hv : Poly size V k := Poly.powerBase size C k
  have hsum : Poly size (fun x => volume (prepare x)+V x+3) (max e k) := by
    simpa only [Nat.max_zero] using (hpv.add hv).add
      (OAI.ThreeMachine.StackCompiler.Poly.const size 3)
  have ht : Poly size T ((max e k)*d) := by
    simpa only [Nat.zero_add] using
      (OAI.ThreeMachine.StackCompiler.Poly.const size D).mul (hsum.pow d)
  have hbound := (OAI.ThreeMachine.StackCompiler.Poly.const size 50).mul
    ((hl.add (OAI.ThreeMachine.StackCompiler.Poly.const size 1)).mul
      (((ht.add hx).add hv).add (OAI.ThreeMachine.StackCompiler.Poly.const size 1)))
  have hfoldtime := Poly.of_le
    (g := fun x => 50*((prepare x).1.length+1)*(T x+volume (prepare x).1+V x+1))
    (fun x => time_fold_prefix_bound R (prepare x).1 (prepare x).2 (T x) (V x)
      (fun j hj => hC x j hj) (by
        intro a ha s hs
        have hmem := volume_mem_le ha
        have hxs : volume (prepare x).1 ≤ volume (prepare x) := by rw [volume_prod]; omega
        exact (hD (a,s)).trans (Nat.mul_le_mul_left D
          (Nat.pow_le_pow_left (by rw [volume_pair]; omega) d))))
    (by simpa only [Nat.mul_assoc] using hbound)
  have hover : Poly size (fun x => 10*(volume (prepare x)+1)) e := by
    simpa only [Nat.max_zero,Nat.zero_add] using
      (OAI.ThreeMachine.StackCompiler.Poly.const size 10).mul
        (hpv.add (OAI.ThreeMachine.StackCompiler.Poly.const size 1))
  have htime := Poly.of_le (fun x => le_of_eq (Realizer.time_comp P R.fold x))
    (by simpa only [Nat.mul_assoc] using (hpt.add hfoldtime).add hover)
  have hout : Poly size (fun x =>
      volume ((prepare x).1.foldl (fun s a => step (a,s)) (prepare x).2)) k :=
    Poly.of_le (fun x => by
      simpa only [List.take_length,V,size] using
        hC x (prepare x).1.length (Nat.le_refl _)) hv
  exact ⟨_,htime.lift (Nat.le_max_left _ _),hout.lift (Nat.le_max_right _ _)⟩

end WitnessEncryption.Runtime.FeatureCost

end

section
-- Source: WitnessEncryption.Runtime.Features.Metadata

namespace WitnessEncryption.Runtime.FeatureMetadata
open OAI.ThreeMachine.StackCompiler
open WitnessEncryption.Runtime.ListPrimitives

















universe u
variable {δ : Type u} [Coding δ]













universe v
variable {η : Type v} [Coding η]



















abbrev RangeState := ℕ × List ℕ

def rangeStep (x : Unit × RangeState) : RangeState := (x.2.1+1,x.2.1::x.2.2)

def rangeStepR : Realizer rangeStep := Realizer.snd.comp Realizer.rangeStep

theorem rangeStep_certified : Certified rangeStepR :=
  Certified.snd.comp ((Certified.fst.comp NatPrimitives.succ_certified).pair cons_certified)

theorem range_fold_iterate (us : List Unit) (s : RangeState) :
    us.foldl (fun s u => rangeStep (u,s)) s=
      (fun s : RangeState => (s.1+1,s.1::s.2))^[us.length] s := by
  induction us generalizing s with
  | nil => rfl
  | cons u us ih => rw [List.foldl_cons,ih,List.length_cons,Function.iterate_succ_apply]; rfl

theorem range_fold_zero (us : List Unit) :
    us.foldl (fun s u => rangeStep (u,s)) (0,[])=
      (us.length,(List.range us.length).reverse) := by
  rw [range_fold_iterate]
  exact Realizer.rangeStep_iterate us.length

theorem volume_range (n : ℕ) : volume (List.range n)=n*n+n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hv := volume_append (List.range n) [n]
    rw [List.range_succ]
    simp only [volume_cons,volume_nil,volume_nat] at hv
    nlinarith

def rangePrepareR : Realizer (fun n : ℕ => (List.replicate n (),(0,([] : List ℕ)))) :=
  Prime.UnaryPowerProof.unitsR.pair (Realizer.constant (0,([] : List ℕ)))

theorem rangePrepare_certified : Certified rangePrepareR :=
  Prime.UnaryPowerProof.unitsR_certified.pair (Certified.constant (0,([] : List ℕ)))

theorem rangePrepared_certified : Certified (rangePrepareR.comp rangeStepR.fold) := by
  apply FeatureCost.prepared_fold rangePrepareR rangePrepare_certified rangeStepR rangeStep_certified
  refine ⟨10,2,?_⟩
  intro n j hj
  simp only [List.length_replicate] at hj
  have ht := range_fold_zero ((List.replicate n ()).take j)
  have hl : ((List.replicate n ()).take j).length=j := by
    rw [List.length_take,List.length_replicate,Nat.min_eq_left hj]
  rw [hl] at ht
  change volume (((List.replicate n ()).take j).foldl (fun s u => rangeStep (u,s)) (0,[])) ≤ _
  rw [ht]
  simp only [volume_prod,volume_nat,volume_reverse,volume_range,pow_two]
  have hp := Nat.mul_le_mul hj hj
  nlinarith

def rangeR : Realizer List.range :=
  ((rangePrepareR.comp rangeStepR.fold).comp (Realizer.snd.comp reverseR)).congr (fun n => by
    have h := congrArg (fun s : RangeState => s.2.reverse) (range_fold_zero (List.replicate n ()))
    simpa only [Function.comp_apply,id_eq,List.length_replicate,List.reverse_reverse] using h)

theorem range_certified : Certified rangeR :=
  (rangePrepared_certified.comp (Certified.snd.comp reverse_certified)).congr (fun n => by
    have h := congrArg (fun s : RangeState => s.2.reverse) (range_fold_zero (List.replicate n ()))
    simpa only [Function.comp_apply,id_eq,List.length_replicate,List.reverse_reverse] using h)

end WitnessEncryption.Runtime.FeatureMetadata

end


