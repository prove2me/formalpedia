-- Prove2me | Definitions.Def_CSL_Shared_Memory_BlockDigitMove
-- name    : CSL_Shared_Memory_BlockDigitMove
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:55:40.692235+00:00
-- url     : https://prove2.me/theorems/eedd08a7-73a3-4280-ac6e-f0ede7fce803
-- title:
--   Coded sorting library: Shared / Memory / BlockDigitMove
-- statement:
--   Module `CodedSorting.Shared.Memory.BlockDigitMove` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Moving a consecutive high field by actual single-digit scans.
--   The recursion extracts the next highest digit, then recurses inside the
--   now fixed prefix. Only q streams are used, regardless of field width.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Memory.BlockDigitMove

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Programs_DigitMove
import Definitions.Def_CSL_Shared_Programs_ScanProgramLift
import Definitions.Def_CSL_Interchange_Framework_Recursion_ArbitrarySchedule

/-! Moving a consecutive high field by actual single-digit scans.
The recursion extracts the next highest digit, then recurses inside the
now fixed prefix. Only q streams are used, regardless of field width. -/

namespace CSL.BlockDigitMove
open DigitMove ScanProgram TriangularStreams

/-- Equal cardinalities identify the same physical positions; this is not
a permutation of payloads. -/
def castPass {V W : ℕ} (h : V=W) : Pass V → Pass W := by
  subst W
  exact id

def castProgram {V W : ℕ} (h : V=W) (ps : List (Pass V)) : List (Pass W) :=
  ps.map (castPass h)

theorem castProgram_length {V W : ℕ} (h : V=W) (ps : List (Pass V)) :
    (castProgram h ps).length=ps.length := by simp [castProgram]

theorem castProgram_constant {V W : ℕ} (h : V=W) (ps : List (Pass V)) :
    totalConstant (castProgram h ps)=totalConstant ps := by subst W; simp [castProgram,castPass]

theorem castProgram_destination {V W : ℕ} (h : V=W) (ps : List (Pass V))
    (x : Fin V) : destination (castProgram h ps) (finCongr h x) =
      finCongr h (destination ps x) := by subst W; simp [castProgram,castPass]

def digitPass (Outer P q S : ℕ) : Pass (Outer*(P*(q*S))) :=
  .streams q (insidePrefix Outer P q S) (insideKey Outer P q S)
    (insidePrefix_increasing Outer P q S)

/-- One pass per digit. Already extracted high digits join the fixed prefix. -/
def program (Outer P q S : ℕ) : (ρ : ℕ) → List (Pass (Outer*(P*(q^ρ*S))))
  | 0 => []
  | ρ+1 =>
      castPass (by rw [pow_succ]; ring)
        (digitPass Outer P q (q^ρ*S)) ::
      castProgram (by ring) (program (Outer*q) P q S ρ)

theorem program_length (Outer P q S ρ : ℕ) :
    (program Outer P q S ρ).length=ρ := by
  induction ρ generalizing Outer with
  | zero => rfl
  | succ ρ ih => simp [program,castProgram_length,ih]

theorem program_constant (Outer P q S ρ : ℕ) :
    totalConstant (program Outer P q S ρ)=ρ*(2*q+6) := by
  induction ρ generalizing Outer with
  | zero => simp [program,totalConstant]
  | succ ρ ih =>
    have hcast {V W : ℕ} (h : V=W) (p : Pass V) :
        (castPass h p).constant=p.constant := by subst W; rfl
    simp only [program,totalConstant,List.map_cons,List.sum_cons,hcast]
    change (2*q+6)+totalConstant (castProgram _ (program (Outer*q) P q S ρ)) = _
    rw [castProgram_constant,ih]
    ring

/-- Physical row-major encoding, with four consecutive fields. -/
def encode (Outer P H S : ℕ) (o : Fin Outer) (p : Fin P) (h : Fin H) (s : Fin S) :
    Fin (Outer*(P*(H*S))) := finProdFinEquiv (o,tripleEncode (p,h,s))

theorem encode_val (Outer P H S : ℕ) (o : Fin Outer) (p : Fin P) (h : Fin H) (s : Fin S) :
    (encode Outer P H S o p h s).val = o.val*(P*(H*S))+p.val*(H*S)+h.val*S+s.val := by
  simp [encode,tripleEncode,finProdFinEquiv,add_assoc] <;> ring

theorem digit_encoded (Outer P q S : ℕ) (o : Fin Outer) (p : Fin P) (h : Fin q) (s : Fin S) :
    (insidePrefix Outer P q S (encode Outer P q S o p h s)).val =
      o.val*(P*(q*S))+h.val*(P*S)+p.val*S+s.val := by
  rw [encode,insidePrefix_encoded,toFront_encoded]
  simp [tripleEncode,finProdFinEquiv,add_assoc] <;> ring


theorem castPass_permutation {V W : ℕ} (h : V=W) (p : Pass V) (x : Fin V) :
    (castPass h p).permutation (finCongr h x)=finCongr h (p.permutation x) := by
  subst W
  rfl

/-- The digit scans move precisely the complete high field, in its original
order, while preserving all other fields. -/
theorem program_encoded (Outer P q S ρ : ℕ) (o : Fin Outer) (p : Fin P)
    (h : Fin (q^ρ)) (s : Fin S) :
    (destination (program Outer P q S ρ) (encode Outer P (q^ρ) S o p h s)).val =
      o.val*((q^ρ)*(P*S))+h.val*(P*S)+p.val*S+s.val := by
  induction ρ generalizing Outer with
  | zero =>
    have hz : h.val=0 := by
      have hh : h.val<1 := by simpa using h.isLt
      omega
    change (encode Outer P (q^0) S o p h s).val = _
    rw [encode_val, hz]
    simp
  | succ ρ ih =>
    let hp : q*q^ρ=q^(ρ+1) := by simp [pow_succ']
    obtain ⟨h,rfl⟩ := (finCongr hp).surjective h
    obtain ⟨⟨a,b⟩,rfl⟩ := (finProdFinEquiv : Fin q × Fin (q^ρ) ≃ Fin (q*q^ρ)).surjective h
    let firstSize : Outer*(P*(q*(q^ρ*S)))=Outer*(P*(q^(ρ+1)*S)) := by rw [pow_succ']; ring
    let restSize : (Outer*q)*(P*(q^ρ*S))=Outer*(P*(q^(ρ+1)*S)) := by rw [pow_succ']; ring
    let x := encode Outer P q (q^ρ*S) o p a (finProdFinEquiv (b,s))
    let y := encode (Outer*q) P (q^ρ) S (finProdFinEquiv (o,a)) p b s
    have hx : encode Outer P (q^(ρ+1)) S o p (finCongr hp (finProdFinEquiv (a,b))) s =
        finCongr firstSize x := by
      apply Fin.ext
      simp [x,encode,tripleEncode,finProdFinEquiv,finCongr,pow_succ'] <;> ring
    have hy : (castPass firstSize (digitPass Outer P q (q^ρ*S))).permutation
        (finCongr firstSize x)=finCongr restSize y := by
      rw [castPass_permutation]
      apply Fin.ext
      change (insidePrefix Outer P q (q^ρ*S) x).val=y.val
      rw [show x=encode Outer P q (q^ρ*S) o p a (finProdFinEquiv (b,s)) from rfl,
        digit_encoded]
      simp [y,encode,tripleEncode,finProdFinEquiv] <;> ring
    change (destination (castPass firstSize (digitPass Outer P q (q^ρ*S)) ::
      castProgram restSize (program (Outer*q) P q S ρ)) _).val = _
    rw [destination,Equiv.trans_apply,hx,hy,castProgram_destination]
    change (destination (program (Outer*q) P q S ρ) y).val = _
    rw [ih (Outer*q) (finProdFinEquiv (o,a)) b]
    simp [finCongr,finProdFinEquiv,pow_succ'] <;> ring



theorem program_destination (Outer P q S ρ : ℕ) :
    destination (program Outer P q S ρ)=insidePrefix Outer P (q^ρ) S := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨o,x⟩,rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨p,h,s⟩,rfl⟩ := tripleEncode.surjective x
  apply Fin.ext
  change (destination (program Outer P q S ρ) (encode Outer P (q^ρ) S o p h s)).val =
    (insidePrefix Outer P (q^ρ) S (encode Outer P (q^ρ) S o p h s)).val
  rw [program_encoded,digit_encoded]
  ring

/-- The actual online file interpreter, with no uncharged intermediate
packing between the rho consecutive scans. -/
theorem program_execution {Value : Type*} [Inhabited Value]
    (Outer P q S ρ B : ℕ) (hB : 0 < B)
    (F : Fin (Outer*(P*(q^ρ*S))) → Value) :
    ∃ cost, Execution B hB (program Outer P q S ρ) F cost ∧
      eval (program Outer P q S ρ) F =
        (fun y => F ((insidePrefix Outer P (q^ρ) S).symm y)) ∧
      cost≤ρ*(2*q+6)*((Outer*(P*(q^ρ*S)))/B+1) := by
  obtain ⟨cost,he,hc⟩ := program_correct (program Outer P q S ρ) F B hB
  refine ⟨cost,he,?_,?_⟩
  · funext y
    rw [eval_eq_pullback,program_destination]
  · simpa only [program_constant] using hc

/-- Inverse passes retain the same q-bucket count. -/
def invertPass {V : ℕ} : Pass V → Pass V
  | .streams K e key hi => .streams K e.symm (fun y => key (e.symm y))
      (AffineStreams.inverse_increasing_streams e key hi)
  | .reverse T L hL hV => .reverse T L hL hV

def inverseProgram {V : ℕ} (ps : List (Pass V)) : List (Pass V) :=
  ps.reverse.map invertPass

theorem invertPass_permutation {V : ℕ} (p : Pass V) :
    (invertPass p).permutation=p.permutation.symm := by
  cases p with
  | streams K e key hi => rfl
  | reverse T L hL hV => exact (reversePerm_symm T L hV).symm

theorem destination_append {V : ℕ} (ps qs : List (Pass V)) :
    destination (ps++qs)=(destination ps).trans (destination qs) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append,destination,ih]; rfl

theorem inverseProgram_destination {V : ℕ} (ps : List (Pass V)) :
    destination (inverseProgram ps)=(destination ps).symm := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [inverseProgram,List.reverse_cons,List.map_append,List.map_cons,List.map_nil]
    rw [destination_append]
    change (destination (inverseProgram ps)).trans ((invertPass p).permutation.trans (Equiv.refl _)) = _
    rw [ih,invertPass_permutation]
    rfl

theorem inverseProgram_constant {V : ℕ} (ps : List (Pass V)) :
    totalConstant (inverseProgram ps)=totalConstant ps := by
  have hi (p : Pass V) : (invertPass p).constant=p.constant := by cases p <;> rfl
  simp [inverseProgram,totalConstant,List.map_map,Function.comp_def,hi,List.map_reverse]



theorem castPass_buffers {V W : ℕ} (h : V=W) (p : Pass V) :
    (castPass h p).buffers=p.buffers := by subst W; rfl

theorem castProgram_buffers {V W K : ℕ} (h : V=W) (ps : List (Pass V))
    (hb : ∀ p∈ps,p.buffers=K) : ∀ p∈castProgram h ps,p.buffers=K := by
  intro p hp
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
  rw [castPass_buffers]
  exact hb a ha

/-- The buffers are reused after each pass: the peak bound is q+2 blocks,
independent of the number rho of extracted digits. -/
theorem program_buffers (Outer P q S ρ : ℕ) :
    ∀ p∈program Outer P q S ρ,p.buffers=q+2 := by
  induction ρ generalizing Outer with
  | zero => intro p hp; exact absurd hp List.not_mem_nil
  | succ ρ ih =>
    intro p hp
    simp only [program,List.mem_cons] at hp
    rcases hp with rfl | hp
    · rw [castPass_buffers]
      rfl
    · exact castProgram_buffers _ _ (ih (Outer*q)) p hp

theorem inverseProgram_buffers {V K : ℕ} (ps : List (Pass V))
    (hb : ∀ p∈ps,p.buffers=K) : ∀ p∈inverseProgram ps,p.buffers=K := by
  intro p hp
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
  have ha' : a∈ps := List.mem_reverse.mp ha
  have hi : (invertPass a).buffers=a.buffers := by cases a <;> rfl
  rw [hi]
  exact hb a ha'


end CSL.BlockDigitMove


