-- Prove2me | Definitions.Def_SubspaceEvasion312_GMC_updates
-- name    : SubspaceEvasion312_GMC_updates
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-22T23:18:12.256447+00:00
-- url     : https://prove2.me/theorems/d2869118-20c3-4890-96f3-7afd28959390
-- title:
--   Preservation of relocated-call simulation
-- statement:
--   These preservation lemmas show that the caller/callee simulation relation is unchanged by control transfers and is updated compatibly when a callee natural or field register is written. Together with the four-instruction translation blocks, they allow an induction over the callee's instructions without exposing the detailed machine-state bookkeeping at each later stage.
-- source:
--   Supporting formal infrastructure for the uniform generator-matrix implementation of explicit codes in STOC 2027 submission #312, Theorem 17, printed p.10 (PDF p.11).

import Definitions.Def_SubspaceEvasion312_GMC_reloc

namespace SubspaceEvasion312.Explicit.Dev.GMC
open SubspaceEvasion312.Explicit
variable {F : Type} [Field F]

lemma rn_same {natBase fieldBase fo no B base : ℕ} {z z' w₀ w w' : MachineState F}
    (hR : RnB natBase fieldBase fo no B base z w₀ w)
    (hzn : z'.natReg = z.natReg) (hzf : z'.fieldReg = z.fieldReg)
    (hzo : z'.out = z.out) (hzno : z'.natOut = z.natOut)
    (hn : w'.natReg = w.natReg) (hf : w'.fieldReg = w.fieldReg)
    (ho : w'.out = w.out) (hno : w'.natOut = w.natOut)
    (hpc : w'.pc = base + 4*z'.pc) : RnB natBase fieldBase fo no B base z' w₀ w' := by
  refine ⟨hpc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hn, hzn]; exact hR.subN j
  · intro a ha; rw [hn, hzno]; exact hR.mainN a ha
  · intro j; rw [hf, hzf]; exact hR.subF j
  · intro a ha; rw [hf, hzo]; exact hR.mainF a ha
  · rw [hn]; exact hR.bnd
  · rw [ho, hR.out]
  · rw [hno, hR.nout]

lemma rn_natw {natBase fieldBase fo no B base d v : ℕ} {z z' w₀ w w' : MachineState F}
    (hR : RnB natBase fieldBase fo no B base z w₀ w) (hv : v ≤ B)
    (hzn : z'.natReg = Function.update z.natReg d v) (hzf : z'.fieldReg = z.fieldReg)
    (hzo : z'.out = z.out) (hzno : z'.natOut = z.natOut)
    (hn : w'.natReg = Function.update w.natReg (N natBase d) v) (hf : w'.fieldReg = w.fieldReg)
    (ho : w'.out = w.out) (hno : w'.natOut = w.natOut)
    (hpc : w'.pc = base + 4*z'.pc) : RnB natBase fieldBase fo no B base z' w₀ w' := by
  refine ⟨hpc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hn, hzn]
    by_cases hd : j = d
    · subst hd; simp
    · rw [Function.update_of_ne hd, Function.update_of_ne (fun h => hd (by unfold N at h; omega))]
      exact hR.subN j
  · intro a ha
    rw [hn, Function.update_of_ne (by unfold N; omega), hzno, hR.mainN a ha]
  · intro j; rw [hf, hzf]; exact hR.subF j
  · intro a ha; rw [hf, hzo]; exact hR.mainF a ha
  · rw [hn]; exact bnd_upd hR.bnd hv
  · rw [ho, hR.out]
  · rw [hno, hR.nout]

lemma rn_fldw {natBase fieldBase fo no B base d : ℕ} {v : F} {z z' w₀ w w' : MachineState F}
    (hR : RnB natBase fieldBase fo no B base z w₀ w)
    (hzn : z'.natReg = z.natReg) (hzf : z'.fieldReg = Function.update z.fieldReg d v)
    (hzo : z'.out = z.out) (hzno : z'.natOut = z.natOut)
    (hn : w'.natReg = w.natReg) (hf : w'.fieldReg = Function.update w.fieldReg (A fieldBase d) v)
    (ho : w'.out = w.out) (hno : w'.natOut = w.natOut)
    (hpc : w'.pc = base + 4*z'.pc) : RnB natBase fieldBase fo no B base z' w₀ w' := by
  refine ⟨hpc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hn, hzn]; exact hR.subN j
  · intro a ha; rw [hn, hzno]; exact hR.mainN a ha
  · intro j; rw [hf, hzf]
    by_cases hd : j = d
    · subst hd; simp
    · rw [Function.update_of_ne hd, Function.update_of_ne (fun h => hd (by unfold A at h; omega))]
      exact hR.subF j
  · intro a ha; rw [hf, Function.update_of_ne (by unfold A; omega), hzo, hR.mainF a ha]
  · rw [hn]; exact hR.bnd
  · rw [ho, hR.out]
  · rw [hno, hR.nout]

end SubspaceEvasion312.Explicit.Dev.GMC


