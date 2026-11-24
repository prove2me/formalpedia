-- Prove2me | Definitions.Def_CSL_Shared_Programs_ScanProgramLift
-- name    : CSL_Shared_Programs_ScanProgramLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:37:10.362355+00:00
-- url     : https://prove2.me/theorems/a7ea9ba2-9fe8-439a-852b-bcd1a01926d9
-- title:
--   Coded sorting library: Shared / Programs / ScanProgramLift
-- statement:
--   Module `CodedSorting.Shared.Programs.ScanProgramLift` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Finite programs composed only of actual online disk-to-disk stream passes
--   and aligned-block reflection passes. Each step records its actual execution
--   and canonical output file, so consecutive steps share the same disk contents
--   without an uncharged repacking operation.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.ScanProgramLift

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Memory_DiskStreamPass
import Definitions.Def_CSL_Interchange_Framework_Fields_FieldReflection

section ScanProgram
/-! Finite programs composed only of actual online disk-to-disk stream passes
and aligned-block reflection passes. Each step records its actual execution
and canonical output file, so consecutive steps share the same disk contents
without an uncharged repacking operation. -/

namespace CSL.ScanProgram

open BucketReader TagErasure BlockReflection

variable {V : ℕ} {Value : Type*}

inductive Pass (V : ℕ) where
  | streams (K : ℕ) (e : Equiv.Perm (Fin V)) (key : Fin V → Fin K)
      (increasing : ∀ x y, x < y → key x = key y → e x < e y)
  | reverse (T L : ℕ) (positive : 0 < L) (volume : T * L = V)

def reversePerm (T L : ℕ) (hV : T * L = V) : Equiv.Perm (Fin V) :=
  (finCongr hV).symm.trans ((segmentReverseEquiv T L).trans (finCongr hV))

theorem reversePerm_involutive (T L : ℕ) (hV : T * L = V) :
    Function.Involutive (reversePerm T L hV) := by
  intro x
  simp only [reversePerm,Equiv.trans_apply,Equiv.symm_apply_apply]
  rw [segmentReverse_involutive T L,Equiv.apply_symm_apply]

theorem reversePerm_symm (T L : ℕ) (hV : T * L = V) :
    (reversePerm T L hV).symm = reversePerm T L hV := by
  apply Equiv.ext
  intro x
  apply (reversePerm T L hV).injective
  rw [Equiv.apply_symm_apply,reversePerm_involutive]

def Pass.permutation : Pass V → Equiv.Perm (Fin V)
  | .streams _ e _ _ => e
  | .reverse T L _ hV => reversePerm T L hV

def Pass.constant : Pass V → ℕ
  | .streams K _ _ _ => 2*K+6
  | .reverse _ _ _ _ => 5

def Pass.buffers : Pass V → ℕ
  | .streams K _ _ _ => K+2
  | .reverse _ _ _ _ => 5

def moved (p : Pass V) (F : Fin V → Value) : Fin V → Value :=
  fun y => F (p.permutation.symm y)

/-- The stream branch consumes and emits canonical disk blocks via actual
Reader/Writer transitions. Reflection accepts arbitrary external contents
outside the valid input and arbitrary initial target contents. -/
def StepEvidence [Inhabited Value] (p : Pass V) (F : Fin V → Value)
    (B : ℕ) (hB : 0 < B) (cost : ℕ) : Prop :=
  match p with
  | .streams _ e key _ => ∃ result,
      DiskStreamPass.run e key B (BucketMachine.pack B hB (inputValues F)) = some result ∧
      result.output.finish = BucketMachine.pack B hB (outputValues e F) ∧
      cost = result.transfers ∧ result.output.Valid B ∧
      (∀ k, (result.readers k).Valid B)
  | .reverse T L hL hV =>
      ∀ (source target : Disk Value), (∀ y : Fin V, source y.val = F y) →
      let result := run source B L hB ((V+B-1)/B) ⟨target,[]⟩
      cost = result.trace.length ∧ ∀ y : Fin V,
        result.disk y.val = moved (.reverse T L hL hV) F y

theorem ceil_le_floor_add_one (V B : ℕ) (hB : 0 < B) :
    (V+B-1)/B ≤ V/B+1 := by
  calc
    (V+B-1)/B ≤ (V+B)/B := Nat.div_le_div_right (by omega)
    _ = V/B+1 := Nat.add_div_right V hB

/-- A concrete execution witness exists for each constructor; no scan-cost
assumption is supplied by a caller. -/
theorem pass_correct [Inhabited Value] (p : Pass V) (F : Fin V → Value)
    (B : ℕ) (hB : 0 < B) :
    ∃ cost, StepEvidence p F B hB cost ∧ cost ≤ p.constant * (V/B+1) := by
  cases p with
  | streams K e key hi =>
    obtain ⟨result,hr,ho,hc,hw,hreaders⟩ :=
      DiskStreamPass.run_packed_canonical e key hi F B hB
    refine ⟨result.transfers,⟨result,hr,ho,rfl,hw,hreaders⟩,?_⟩
    try dsimp only [Pass.constant]
    have hm := Nat.mul_le_mul_right (V/B) (show 4 ≤ 2*K+6 by omega)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  | reverse T L hL hV =>
    refine ⟨5*((V+B-1)/B),?_,Nat.mul_le_mul_left 5 (ceil_le_floor_add_one V B hB)⟩
    intro source target hagree
    obtain ⟨hr,hc⟩ := full_reversal source target B T L hB hL
    rw [hV] at hc
    refine ⟨hc.symm,?_⟩
    intro y
    have hy := hr ((finCongr hV).symm y)
    simp only [hV] at hy
    change (run source B L hB ((V+B-1)/B) ⟨target,[]⟩).disk y.val =
      F ((reversePerm T L hV).symm y)
    rw [reversePerm_symm]
    have hv : (reversePerm T L hV y).val =
        (segmentReverseEquiv T L ((finCongr hV).symm y)).val := rfl
    rw [←hv] at hy
    exact hy.trans (hagree (reversePerm T L hV y))

def eval : List (Pass V) → (Fin V → Value) → (Fin V → Value)
  | [],F => F
  | p::ps,F => eval ps (moved p F)

def totalConstant (ps : List (Pass V)) : ℕ := (ps.map Pass.constant).sum

/-- The next primitive consumes exactly the external array produced by its
predecessor. Costs refer to the real primitive loops above. -/
inductive Execution [Inhabited Value] (B : ℕ) (hB : 0 < B) :
    List (Pass V) → (Fin V → Value) → ℕ → Prop where
  | nil (F) : Execution B hB [] F 0
  | cons (p) (ps) (F) (c d)
      (head : StepEvidence p F B hB c)
      (tail : Execution B hB ps (moved p F) d) : Execution B hB (p::ps) F (c+d)

theorem program_correct [Inhabited Value] (ps : List (Pass V))
    (F : Fin V → Value) (B : ℕ) (hB : 0 < B) :
    ∃ cost, Execution B hB ps F cost ∧ cost ≤ totalConstant ps * (V/B+1) := by
  induction ps generalizing F with
  | nil => exact ⟨0,Execution.nil F,by simp [totalConstant]⟩
  | cons p ps ih =>
    obtain ⟨c,hc,hcb⟩ := pass_correct p F B hB
    obtain ⟨d,hd,hdb⟩ := ih (moved p F)
    refine ⟨c+d,Execution.cons p ps F c d hc hd,?_⟩
    simp only [totalConstant,List.map_cons,List.sum_cons,add_mul]
    exact Nat.add_le_add hcb hdb

def destination : List (Pass V) → Equiv.Perm (Fin V)
  | [] => Equiv.refl _
  | p::ps => p.permutation.trans (destination ps)

theorem eval_eq_pullback (ps : List (Pass V)) (F : Fin V → Value) (y : Fin V) :
    eval ps F y = F ((destination ps).symm y) := by
  induction ps generalizing F with
  | nil => rfl
  | cons p ps ih => exact ih (moved p F)

/-- The buffer count includes the input/output blocks in a stream pass. -/
theorem Pass.buffers_le_constant (p : Pass V) : p.buffers ≤ p.constant := by
  cases p <;> simp only [Pass.buffers,Pass.constant] <;> omega

/-- Sequential passes reuse RAM, so even the sum of fixed primitive constants
is a valid uniform upper bound on the peak number of block buffers. -/
theorem member_buffers_le_total (ps : List (Pass V)) (p : Pass V) (hp : p ∈ ps) :
    p.buffers ≤ totalConstant ps := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [List.mem_cons] at hp
    simp only [totalConstant,List.map_cons,List.sum_cons]
    rcases hp with he | ht
    · subst p
      exact (Pass.buffers_le_constant q).trans (Nat.le_add_right _ _)
    · exact (ih ht).trans (Nat.le_add_left _ _)

end CSL.ScanProgram
end ScanProgram

section ScanProgramLift
/-! Lift an implemented middle-field permutation to all prefixes and suffixes.
Streams are shared globally; a reflected middle subfield uses two physical
segment reflections. No loop restarts at prefix boundaries. -/

namespace CSL.ScanProgramLift

open ScanProgram TriangularStreams FieldReflection

variable {V P S : ℕ}

def fieldReflections (P Q S : ℕ) (hQ : 0 < Q) (hS : 0 < S)
    (hV : P*(Q*S)=V) : List (Pass V) :=
  [.reverse P (Q*S) (Nat.mul_pos hQ hS) hV,
   .reverse (P*Q) S hS ((Nat.mul_assoc _ _ _).trans hV)]

theorem fieldReflections_destination (P Q S : ℕ) (hQ : 0 < Q) (hS : 0 < S)
    (hV : P*(Q*S)=V) (z : Fin (P*(Q*S))) :
    destination (fieldReflections P Q S hQ hS hV) (finCongr hV z) =
      finCongr hV (globalFieldEquiv (S := S) (fun (_ : Fin P) => Fin.revPerm) z) := by
  change reversePerm (P*Q) S _ (reversePerm P (Q*S) hV (finCongr hV z)) = _
  have hfirst : reversePerm P (Q*S) hV (finCongr hV z) =
      finCongr hV (BlockReflection.segmentReverseEquiv _ _ z) := by simp [reversePerm]
  rw [hfirst]
  have hsecond (w : Fin (P*(Q*S))) :
      reversePerm (P*Q) S ((Nat.mul_assoc _ _ _).trans hV) (finCongr hV w) =
      finCongr hV (suffixReverse w) := rfl
  rw [hsecond]
  exact congrArg (fun e : Equiv.Perm (Fin (P*(Q*S))) => finCongr hV (e z)) two_reversals

theorem liftedVolume (T L : ℕ) (hV : T*L=V) :
    (P*T)*(L*S)=P*(V*S) := by rw [←hV]; ring

/-- Reassociation preserves the numeric address exactly. -/
theorem flatten_four (T L : ℕ) (hV : T*L=V)
    (p : Fin P) (t : Fin T) (l : Fin L) (s : Fin S) :
    finCongr (liftedVolume (P := P) (S := S) T L hV)
      (tripleEncode (finProdFinEquiv (p,t),l,s)) =
    tripleEncode (p,finCongr hV (finProdFinEquiv (t,l)),s) := by
  apply Fin.ext
  change s.val+S*l.val+(L*S)*(t.val+T*p.val) =
    s.val+S*(l.val+L*t.val)+(V*S)*p.val
  rw [←hV]
  ring

noncomputable def liftPass (P S : ℕ) (hS : 0 < S) : Pass V → List (Pass (P*(V*S)))
  | .streams K e key hi =>
      [.streams K (globalFieldEquiv (fun (_ : Fin P) => e))
        (globalKey (fun (_ : Fin P) => key))
        (global_increasing_streams _ _ (fun _ => hi))]
  | .reverse T L hL hV =>
      fieldReflections (P*T) L S hL hS (liftedVolume T L hV)

theorem liftPass_destination (P S : ℕ) (hS : 0 < S) (p : Pass V) :
    destination (liftPass P S hS p) =
      globalFieldEquiv (fun (_ : Fin P) => p.permutation) := by
  cases p with
  | streams K e key hi => rfl
  | reverse T L hL hV =>
    apply Equiv.ext
    intro y
    obtain ⟨⟨p,v,s⟩,rfl⟩ := tripleEncode.surjective y
    obtain ⟨v,rfl⟩ := (finCongr hV).surjective v
    obtain ⟨⟨t,l⟩,rfl⟩ := finProdFinEquiv.surjective v
    change destination (fieldReflections (P*T) L S hL hS (liftedVolume T L hV)) _ = _
    rw [globalFieldEquiv_encoded]
    rw [←flatten_four T L hV p t l s,fieldReflections_destination,
      globalFieldEquiv_encoded,Fin.revPerm_apply]
    try dsimp only [Prod.fst,Prod.snd]
    rw [flatten_four T L hV]
    change tripleEncode (p,finCongr hV (finProdFinEquiv (t,l.rev)),s) =
      tripleEncode (p,reversePerm T L hV (finCongr hV (finProdFinEquiv (t,l))),s)
    simp [reversePerm,BlockReflection.segmentReverse_pair]

noncomputable def liftProgram (P S : ℕ) (hS : 0 < S) (ps : List (Pass V)) :
    List (Pass (P*(V*S))) := ps.flatMap (liftPass P S hS)

theorem destination_append {W : ℕ} (xs ys : List (Pass W)) :
    destination (xs++ys) = (destination xs).trans (destination ys) := by
  induction xs with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append,destination,ih]; rfl

theorem global_comp (e f : Equiv.Perm (Fin V)) :
    (globalFieldEquiv (S := S) (fun (_ : Fin P) => e)).trans
      (globalFieldEquiv (fun (_ : Fin P) => f)) =
      globalFieldEquiv (fun (_ : Fin P) => e.trans f) := by
  apply Equiv.ext
  intro y
  obtain ⟨⟨p,v,s⟩,rfl⟩ := tripleEncode.surjective y
  simp only [Equiv.trans_apply,globalFieldEquiv_encoded]

theorem liftProgram_destination (P S : ℕ) (hS : 0 < S) (ps : List (Pass V)) :
    destination (liftProgram P S hS ps) =
      globalFieldEquiv (fun (_ : Fin P) => destination ps) := by
  induction ps with
  | nil =>
    apply Equiv.ext
    intro y
    obtain ⟨⟨p,v,s⟩,rfl⟩ := tripleEncode.surjective y
    simp [liftProgram,destination,globalFieldEquiv_encoded]
  | cons p ps ih =>
    change destination (liftPass P S hS p ++ liftProgram P S hS ps) = _
    rw [destination_append,liftPass_destination,ih,global_comp]
    rfl

theorem liftPass_constant (P S : ℕ) (hS : 0 < S) (p : Pass V) :
    totalConstant (liftPass P S hS p) ≤ 2*p.constant := by
  cases p with
  | streams K e key hi => simp [liftPass,totalConstant,Pass.constant]
  | reverse T L hL hV => simp [liftPass,fieldReflections,totalConstant,Pass.constant]

theorem liftProgram_constant (P S : ℕ) (hS : 0 < S) (ps : List (Pass V)) :
    totalConstant (liftProgram P S hS ps) ≤ 2*totalConstant ps := by
  induction ps with
  | nil => simp [liftProgram,totalConstant]
  | cons p ps ih =>
    change totalConstant (liftPass P S hS p ++ liftProgram P S hS ps) ≤ _
    simp only [totalConstant,List.map_append,List.sum_append] at *
    have hp := liftPass_constant P S hS p
    simp only [totalConstant] at hp
    simp only [List.map_cons,List.sum_cons,Nat.mul_add]
    exact Nat.add_le_add hp ih

end CSL.ScanProgramLift
end ScanProgramLift


