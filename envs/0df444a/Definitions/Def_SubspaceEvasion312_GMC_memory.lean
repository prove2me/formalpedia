-- Prove2me | Definitions.Def_SubspaceEvasion312_GMC_memory
-- name    : SubspaceEvasion312_GMC_memory
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T00:24:39.34391+00:00
-- url     : https://prove2.me/theorems/328721d7-4350-4285-a41a-a40072334310
-- title:
--   Memory, temporary and output updates for relocated calls
-- statement:
--   These lemmas extend the relocation simulation to temporary address arithmetic, indirect stores, and output copies. They preserve caller data outside the designated output registers while updating the caller-side value associated with a singleton field or natural output.
-- source:
--   Supporting operational infrastructure for STOC 2027 submission #312, Theorem 17's explicit linear code programs, printed p.10 (PDF p.11).

import Definitions.Def_SubspaceEvasion312_GMC_updates

namespace SubspaceEvasion312.Explicit.Dev.GMC
open SubspaceEvasion312.Explicit
variable {F : Type} [Field F]

lemma rn_tmp {natBase fieldBase fo no B base v : ℕ} {z z' w₀ w w' : MachineState F}
    (hR : RnB natBase fieldBase fo no B base z w₀ w) (hv : v ≤ B)
    (hz : z' = z) (hn : w'.natReg = Function.update w.natReg natBase v)
    (hf : w'.fieldReg = w.fieldReg) (ho : w'.out = w.out) (hno : w'.natOut = w.natOut)
    (hpc : w'.pc = base + 4*z'.pc) : RnB natBase fieldBase fo no B base z' w₀ w' := by
  subst z'
  refine ⟨hpc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hn, Function.update_of_ne (by unfold N; omega)]; exact hR.subN j
  · intro a ha; rw [hn, Function.update_of_ne (by omega)]; exact hR.mainN a ha
  · intro j; rw [hf]; exact hR.subF j
  · intro a ha; rw [hf]; exact hR.mainF a ha
  · rw [hn]; exact bnd_upd hR.bnd hv
  · rw [ho, hR.out]
  · rw [hno, hR.nout]

lemma rn_memw {natBase fieldBase fo no B base d s : ℕ} {z z' w₀ w w' : MachineState F}
    (hR : RnB natBase fieldBase fo no B base z w₀ w)
    (hzn : z'.natReg = z.natReg)
    (hzf : z'.fieldReg = Function.update z.fieldReg (z.natReg d) (z.fieldReg s))
    (hzo : z'.out = z.out) (hzno : z'.natOut = z.natOut)
    (hn : w'.natReg = w.natReg)
    (hf : w'.fieldReg = Function.update w.fieldReg (fieldBase + z.natReg d) (w.fieldReg (A fieldBase s)))
    (ho : w'.out = w.out) (hno : w'.natOut = w.natOut)
    (hpc : w'.pc = base + 4*z'.pc) : RnB natBase fieldBase fo no B base z' w₀ w' := by
  refine ⟨hpc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hn, hzn]; exact hR.subN j
  · intro a ha; rw [hn, hzno]; exact hR.mainN a ha
  · intro j; rw [hf, hzf, hR.subF]
    by_cases hj : j = z.natReg d
    · subst hj; simp only [Function.update_self, A]
    · rw [Function.update_of_ne hj, Function.update_of_ne (by unfold A; omega)]
      exact hR.subF j
  · intro a ha; rw [hf, Function.update_of_ne (by omega), hzo, hR.mainF a ha]
  · rw [hn]; exact hR.bnd
  · rw [ho, hR.out]
  · rw [hno, hR.nout]

lemma rn_outF {natBase fieldBase fo no B base d : ℕ} {v : F} {z z' w₀ w w' : MachineState F}
    (hR : RnB natBase fieldBase fo no B base z w₀ w) (hfo : fo < fieldBase)
    (hzn : z'.natReg = z.natReg) (hzf : z'.fieldReg = z.fieldReg)
    (hzo : z'.out = [v]) (hzno : z'.natOut = z.natOut)
    (hn : w'.natReg = w.natReg) (hf : w'.fieldReg = Function.update w.fieldReg fo v)
    (ho : w'.out = w.out) (hno : w'.natOut = w.natOut)
    (hpc : w'.pc = base + 4*z'.pc) : RnB natBase fieldBase fo no B base z' w₀ w' := by
  refine ⟨hpc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hn, hzn]; exact hR.subN j
  · intro a ha; rw [hn, hzno]; exact hR.mainN a ha
  · intro j; rw [hf, Function.update_of_ne (by unfold A; omega), hzf]; exact hR.subF j
  · intro a ha; rw [hf]
    by_cases hafo : a = fo
    · subst hafo; simp [hzo]
    · rw [Function.update_of_ne hafo, hR.mainF a ha, if_neg hafo]
      simp [hafo]
  · rw [hn]; exact hR.bnd
  · rw [ho, hR.out]
  · rw [hno, hR.nout]

lemma rn_outN {natBase fieldBase fo no B base d : ℕ} {v : ℕ} {z z' w₀ w w' : MachineState F}
    (hR : RnB natBase fieldBase fo no B base z w₀ w) (hnoB : no < natBase) (hv : v ≤ B)
    (hzn : z'.natReg = z.natReg) (hzf : z'.fieldReg = z.fieldReg)
    (hzo : z'.out = z.out) (hzno : z'.natOut = [v])
    (hn : w'.natReg = Function.update w.natReg no v) (hf : w'.fieldReg = w.fieldReg)
    (ho : w'.out = w.out) (hno : w'.natOut = w.natOut)
    (hpc : w'.pc = base + 4*z'.pc) : RnB natBase fieldBase fo no B base z' w₀ w' := by
  refine ⟨hpc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hn, Function.update_of_ne (by unfold N; omega), hzn]; exact hR.subN j
  · intro a ha; rw [hn]
    by_cases hano : a = no
    · subst hano; simp [hzno]
    · rw [Function.update_of_ne hano, hR.mainN a ha, if_neg hano]
      simp [hano]
  · intro j; rw [hf, hzf]; exact hR.subF j
  · intro a ha; rw [hf, hzo]; exact hR.mainF a ha
  · rw [hn]; exact bnd_upd hR.bnd hv
  · rw [ho, hR.out]
  · rw [hno, hR.nout]

end SubspaceEvasion312.Explicit.Dev.GMC


