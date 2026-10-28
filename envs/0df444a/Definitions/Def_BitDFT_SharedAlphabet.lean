-- Prove2me | Definitions.Def_BitDFT_SharedAlphabet
-- name    : BitDFT_SharedAlphabet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T22:11:29.948186+00:00
-- url     : https://prove2.me/theorems/3193a66d-8cd1-4934-a8ed-144577ecf0bc
-- title:
--   A shared finite alphabet for two component machines
-- statement:
--   Given two finite multitape machines, form a finite product alphabet that carries one symbol from each machine at every tape cell. The two component alphabets embed injectively while preserving their blank, marker, binary symbols, and separator. This supplies a common tape alphabet for composing the arbitrary Fourier child machine with the supplied integer multiplier.
-- source:
--   Finite product alphabet and explicit embeddings, locally checked against the multitape model. It is an adapter definition for composing machine components; runtime preservation is supplied separately by the existing alphabet-embedding theorem.

import Definitions.Def_BitDFT_AlphabetEmbedding

noncomputable section
namespace BitDFT.SharedAlphabet
open IntMul

/-- A finite alphabet holder; its transition only enters halt without moving. -/
abbrev carrier (A M : MultitapeTM) : MultitapeTM where
  Sym := A.Sym × M.Sym
  blank := (A.blank,M.blank)
  startSym := (A.startSym,M.startSym)
  zero := (A.zero,M.zero)
  one := (A.one,M.one)
  sep := (A.sep,M.sep)
  syms_distinct := by
    have h := A.syms_distinct
    simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,not_or] at h ⊢
    simp only [Prod.mk.injEq]
    aesop
  K := Bool
  qStart := false
  qHalt := true
  start_ne_halt := by decide
  k := 2
  two_le_k := by decide
  δ := fun _ a => (true,fun i => (a i,.stay))
  start_preserved := by intro q a i hi; exact ⟨hi,by change Move.stay ≠ Move.left; decide⟩
  start_only_at_start := by intro q a i hi; exact hi
  halt_fixed := by intro a; rfl
  input_readonly := by intro q a; rfl

def mate (A M : MultitapeTM) (a : A.Sym) : M.Sym := by
  classical
  exact if a = A.blank then M.blank else if a = A.startSym then M.startSym else
    if a = A.zero then M.zero else if a = A.one then M.one else if a = A.sep then M.sep else M.blank

def left (A M : MultitapeTM) : AlphabetEmbedding.Map A (carrier A M) where
  encode := { toFun := fun a => (a,mate A M a), inj' := by intro a b h; exact congrArg Prod.fst h }
  blank := by
    classical
    simp [mate]
  marker := by
    classical
    have h := A.syms_distinct
    simp [List.nodup_cons,List.mem_cons,not_or] at h
    rcases h with ⟨⟨h01,h02,h03,h04⟩,⟨h12,h13,h14⟩,⟨h23,h24⟩,h34⟩
    simp [mate,Ne.symm h01,Ne.symm h02,Ne.symm h03,Ne.symm h04,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h23,Ne.symm h24,Ne.symm h34]
  zero := by
    classical
    have h := A.syms_distinct
    simp [List.nodup_cons,List.mem_cons,not_or] at h
    rcases h with ⟨⟨h01,h02,h03,h04⟩,⟨h12,h13,h14⟩,⟨h23,h24⟩,h34⟩
    simp [mate,Ne.symm h01,Ne.symm h02,Ne.symm h03,Ne.symm h04,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h23,Ne.symm h24,Ne.symm h34]
  one := by
    classical
    have h := A.syms_distinct
    simp [List.nodup_cons,List.mem_cons,not_or] at h
    rcases h with ⟨⟨h01,h02,h03,h04⟩,⟨h12,h13,h14⟩,⟨h23,h24⟩,h34⟩
    simp [mate,Ne.symm h01,Ne.symm h02,Ne.symm h03,Ne.symm h04,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h23,Ne.symm h24,Ne.symm h34]
  sep := by
    classical
    have h := A.syms_distinct
    simp [List.nodup_cons,List.mem_cons,not_or] at h
    rcases h with ⟨⟨h01,h02,h03,h04⟩,⟨h12,h13,h14⟩,⟨h23,h24⟩,h34⟩
    simp [mate,Ne.symm h01,Ne.symm h02,Ne.symm h03,Ne.symm h04,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h23,Ne.symm h24,Ne.symm h34]

def right (A M : MultitapeTM) : AlphabetEmbedding.Map M (carrier A M) where
  encode := { toFun := fun m => (mate M A m,m), inj' := by intro a b h; exact congrArg Prod.snd h }
  blank := by
    classical
    simp [mate]
  marker := by
    classical
    have h := M.syms_distinct
    simp [List.nodup_cons,List.mem_cons,not_or] at h
    rcases h with ⟨⟨h01,h02,h03,h04⟩,⟨h12,h13,h14⟩,⟨h23,h24⟩,h34⟩
    simp [mate,Ne.symm h01,Ne.symm h02,Ne.symm h03,Ne.symm h04,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h23,Ne.symm h24,Ne.symm h34]
  zero := by
    classical
    have h := M.syms_distinct
    simp [List.nodup_cons,List.mem_cons,not_or] at h
    rcases h with ⟨⟨h01,h02,h03,h04⟩,⟨h12,h13,h14⟩,⟨h23,h24⟩,h34⟩
    simp [mate,Ne.symm h01,Ne.symm h02,Ne.symm h03,Ne.symm h04,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h23,Ne.symm h24,Ne.symm h34]
  one := by
    classical
    have h := M.syms_distinct
    simp [List.nodup_cons,List.mem_cons,not_or] at h
    rcases h with ⟨⟨h01,h02,h03,h04⟩,⟨h12,h13,h14⟩,⟨h23,h24⟩,h34⟩
    simp [mate,Ne.symm h01,Ne.symm h02,Ne.symm h03,Ne.symm h04,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h23,Ne.symm h24,Ne.symm h34]
  sep := by
    classical
    have h := M.syms_distinct
    simp [List.nodup_cons,List.mem_cons,not_or] at h
    rcases h with ⟨⟨h01,h02,h03,h04⟩,⟨h12,h13,h14⟩,⟨h23,h24⟩,h34⟩
    simp [mate,Ne.symm h01,Ne.symm h02,Ne.symm h03,Ne.symm h04,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h23,Ne.symm h24,Ne.symm h34]

end BitDFT.SharedAlphabet


