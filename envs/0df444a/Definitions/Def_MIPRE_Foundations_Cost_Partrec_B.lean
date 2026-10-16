-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
-- name    : MIPRE_Foundations_Cost_Partrec_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:24:43.163199+00:00
-- url     : https://prove2.me/theorems/463e3ba5-74ec-47e6-8fa2-41f3b160d557
-- title:
--   Ambient evaluation is partial recursive: the step lemmas and the encoded-output bridge (partrec addendum)
-- statement:
--   This bundle adds thirteen theorems, and no new definitions, to the already published bundle `MIPRE_Foundations_Cost_Partrec`, the bridge from the ambient cost model to Mathlib's computability. The evaluation machine on data has a step function `stepData`, a finality test `IsFinalD`, a result extraction `resultD` and an initial configuration `initData`; `evalStep d` returns `Sum.inl (resultD d)` on a final configuration and `Sum.inr (stepData d)` otherwise, and `evalData p x` is the `PFun.fix` of `evalStep` from `initData p x`. The added lemmas, by group: the encoders of the two kinds of control (`evD`, `retD`) and the tag reader $d \mapsto \mathrm{unaryToNat}\,(\mathrm{left}\,d)$ are `Primrec`; the two halves of the step (`stepEv` on evaluate controls, `stepRet` on return controls) and `stepData` itself are `Primrec`; `IsFinalD` is a `PrimrecPred`, `resultD` is `Primrec`, `initData` is `Primrec₂`; `evalStep` is `Computable` and `evalData` is `Partrec₂`. Finally, for a polynomial-time function $F$ of the model between `SizedEncoding` types and every input $a$,
--
--   $$\mathrm{evalData}\,(\mathrm{encode}\,F.\mathrm{code})\,(\mathrm{encode}\,a) \;=\; \mathrm{Part.some}\,(\mathrm{encode}\,(F\,a)),$$
--
--   and, for a `Primcodable` type $\gamma$ and a map $h : \gamma \to \alpha$ whose encoded values $c \mapsto \mathrm{encode}\,(h\,c)$ are `Computable`, the encoded outputs $c \mapsto \mathrm{encode}\,(F\,(h\,c))$ are `Computable`. This last form needs no `Primcodable` instance on the output type, which is what lets a `PolyTimeFun _ Prog` such as the sampler program of a gap compression reach a computability proof.
--
--   **Formalization Note** The declarations are `primrec_evD`, `primrec_retD`, `primrec_tag`, `primrec_stepEv` (stated on triples `Data × Data × Data`), `primrec_stepRet`, `primrec_stepData`, `primrec_isFinalD`, `primrec_resultD`, `primrec_initData`, `computable_evalStep`, `partrec_evalData`, `evalData_encode` and `PolyTimeFun.computable_encode_comp`. The bridge is stated as `Computable fun c => (encode (F (h c)) : Data)` from `hh : Computable fun c => (encode (h c) : Data)`; `F.code` is the program of the polynomial-time function and `encode` the `SizedEncoding` into `Data`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Partrec.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Partrec.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Partrec does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Theorems.Thm_MIPRE_Cost_Machine_mem_evalData_iff

/-!
# Ambient evaluation is partial recursive

The step of the evaluation machine on data is primitive recursive (`primrec_stepData`),
so evaluation — its `PFun.fix` from the initial configuration — is partial recursive
(`partrec_evalData`), and agrees with `Eval` (`mem_evalData_iff`). Consequently a
polynomial-time function of the ambient model is Mathlib-computable, as soon as its input
is produced by a computable encoding (`PolyTimeFun.computable_comp`). This is the bridge
from the ambient model to Mathlib's computability used by the halting-problem form of the
compression lemma; the other bridge (from `Nat.Partrec.Code` into the model) is
`Cost/FromPartrec.lean`.
-/

namespace MIPRE.Cost

namespace Machine

open Primrec

/-! ## The step is primitive recursive -/

theorem primrec_evD : Primrec evD := Data.primrec_cons.comp (const Data.nil) Primrec.id

theorem primrec_retD : Primrec retD := Data.primrec_cons.comp (const (Data.cons .nil .nil)) Primrec.id

/-- `p ↦ unaryToNat p.left`, the tag of an encoded program or frame. -/
theorem primrec_tag : Primrec fun d : Data => Data.unaryToNat d.left :=
  Data.primrec_unaryToNat.comp Data.primrec_left

theorem primrec_stepEv : Primrec fun q : Data × Data × Data => stepEv q.1 q.2.1 q.2.2 := by
  have hp : Primrec fun q : Data × Data × Data => q.1 := fst
  have henv : Primrec fun q : Data × Data × Data => q.2.1 := fst.comp snd
  have hk : Primrec fun q : Data × Data × Data => q.2.2 := snd.comp snd
  have htag : Primrec fun q : Data × Data × Data => Data.unaryToNat q.1.left := primrec_tag.comp hp
  have hbody : Primrec fun q : Data × Data × Data => q.1.right := Data.primrec_right.comp hp
  have hget0 : Primrec fun q : Data × Data × Data =>
      Data.getList q.2.1 (Data.unaryToNat q.1.right) :=
    Data.primrec_getList.comp henv (Data.primrec_unaryToNat.comp hbody)
  have hgetE : Primrec fun q : Data × Data × Data =>
      Data.getList q.2.1 (Data.unaryToNat q.1.right.left) :=
    Data.primrec_getList.comp henv (Data.primrec_unaryToNat.comp (Data.primrec_left.comp hbody))
  have heq : ∀ n : ℕ, PrimrecPred fun q : Data × Data × Data => Data.unaryToNat q.1.left = n :=
    fun n => PrimrecRel.comp Primrec.eq htag (const n)
  refine Primrec.ite (heq 0) ?_ (Primrec.ite (heq 1) ?_ (Primrec.ite (heq 2) ?_
    (Primrec.ite (heq 3) ?_ (Primrec.ite (heq 4) ?_ (Primrec.ite (heq 5) ?_ ?_)))))
  · exact Data.primrec_cons.comp (primrec_retD.comp hget0) (Data.primrec_cons.comp henv hk)
  · exact Data.primrec_cons.comp (primrec_retD.comp (const Data.nil)) (Data.primrec_cons.comp henv hk)
  · exact Data.primrec_cons.comp (primrec_evD.comp (Data.primrec_left.comp hbody))
      (Data.primrec_cons.comp henv (Data.primrec_cons.comp
        (Data.primrec_cons.comp (const (Data.ofNat 0))
          (Data.primrec_cons.comp (Data.primrec_right.comp hbody) henv)) hk))
  · refine Primrec.ite (PrimrecRel.comp Primrec.eq hgetE (const Data.nil)) ?_ ?_
    · exact Data.primrec_cons.comp
        (primrec_evD.comp (Data.primrec_left.comp (Data.primrec_right.comp hbody)))
        (Data.primrec_cons.comp henv hk)
    · exact Data.primrec_cons.comp
        (primrec_evD.comp (Data.primrec_right.comp (Data.primrec_right.comp hbody)))
        (Data.primrec_cons.comp (Data.primrec_cons.comp (Data.primrec_left.comp hgetE)
          (Data.primrec_cons.comp (Data.primrec_right.comp hgetE) henv)) hk)
  · exact Data.primrec_cons.comp (primrec_evD.comp (Data.primrec_left.comp hbody))
      (Data.primrec_cons.comp henv (Data.primrec_cons.comp
        (Data.primrec_cons.comp (const (Data.ofNat 2))
          (Data.primrec_cons.comp (Data.primrec_right.comp hbody) henv)) hk))
  · exact Data.primrec_cons.comp (primrec_evD.comp hbody)
      (Data.primrec_cons.comp henv (Data.primrec_cons.comp
        (Data.primrec_cons.comp (const (Data.ofNat 3)) (Data.primrec_cons.comp hbody henv)) hk))
  · exact Data.primrec_cons.comp (primrec_retD.comp hbody) (Data.primrec_cons.comp henv hk)

theorem primrec_stepRet : Primrec fun q : Data × Data × Data => stepRet q.1 q.2.1 q.2.2 := by
  have hv : Primrec fun q : Data × Data × Data => q.1 := fst
  have henv : Primrec fun q : Data × Data × Data => q.2.1 := fst.comp snd
  have hk : Primrec fun q : Data × Data × Data => q.2.2 := snd.comp snd
  have hfr : Primrec fun q : Data × Data × Data => q.2.2.left := Data.primrec_left.comp hk
  have hk' : Primrec fun q : Data × Data × Data => q.2.2.right := Data.primrec_right.comp hk
  have hftag : Primrec fun q : Data × Data × Data => Data.unaryToNat q.2.2.left.left :=
    primrec_tag.comp hfr
  have hfb : Primrec fun q : Data × Data × Data => q.2.2.left.right := Data.primrec_right.comp hfr
  have hfb1 : Primrec fun q : Data × Data × Data => q.2.2.left.right.left :=
    Data.primrec_left.comp hfb
  have hfb2 : Primrec fun q : Data × Data × Data => q.2.2.left.right.right :=
    Data.primrec_right.comp hfb
  have hfb22 : Primrec fun q : Data × Data × Data => q.2.2.left.right.right.right :=
    Data.primrec_right.comp hfb2
  have heq : ∀ n : ℕ, PrimrecPred fun q : Data × Data × Data =>
      Data.unaryToNat q.2.2.left.left = n :=
    fun n => PrimrecRel.comp Primrec.eq hftag (const n)
  refine Primrec.ite (PrimrecRel.comp Primrec.eq hk (const Data.nil)) ?_
    (Primrec.ite (heq 0) ?_ (Primrec.ite (heq 1) ?_ (Primrec.ite (heq 2) ?_
      (Primrec.ite (PrimrecRel.comp Primrec.eq hv (const Data.nil)) ?_
        (Primrec.ite (PrimrecRel.comp Primrec.eq (Data.primrec_left.comp hv) (const Data.nil)) ?_
          ?_)))))
  · exact Data.primrec_cons.comp (primrec_retD.comp hv) (Data.primrec_cons.comp henv hk)
  · exact Data.primrec_cons.comp (primrec_evD.comp hfb1)
      (Data.primrec_cons.comp hfb2 (Data.primrec_cons.comp
        (Data.primrec_cons.comp (const (Data.ofNat 1)) hv) hk'))
  · exact Data.primrec_cons.comp (primrec_retD.comp (Data.primrec_cons.comp hfb hv))
      (Data.primrec_cons.comp henv hk')
  · exact Data.primrec_cons.comp (primrec_evD.comp hfb1)
      (Data.primrec_cons.comp (Data.primrec_cons.comp hv hfb2) hk')
  · exact Data.primrec_cons.comp (primrec_retD.comp (const Data.nil)) (Data.primrec_cons.comp hfb2 hk')
  · exact Data.primrec_cons.comp (primrec_retD.comp (Data.primrec_right.comp hv))
      (Data.primrec_cons.comp hfb2 hk')
  · exact Data.primrec_cons.comp (primrec_evD.comp hfb1)
      (Data.primrec_cons.comp (Data.primrec_cons.comp (Data.primrec_right.comp hv) hfb22)
        (Data.primrec_cons.comp (Data.primrec_cons.comp (const (Data.ofNat 3))
          (Data.primrec_cons.comp hfb1
            (Data.primrec_cons.comp (Data.primrec_right.comp hv) hfb22))) hk'))

theorem primrec_stepData : Primrec stepData := by
  have hq : Primrec fun d : Data => (d.left.right, d.right.left, d.right.right) :=
    Primrec.pair (Data.primrec_right.comp Data.primrec_left)
      (Primrec.pair (Data.primrec_left.comp Data.primrec_right)
        (Data.primrec_right.comp Data.primrec_right))
  exact Primrec.ite
    (PrimrecRel.comp Primrec.eq (Data.primrec_left.comp Data.primrec_left) (const Data.nil))
    (primrec_stepEv.comp hq) (primrec_stepRet.comp hq)

theorem primrec_isFinalD : PrimrecPred IsFinalD := by
  have h1 : PrimrecPred fun d : Data => d.left.left ≠ .nil :=
    (PrimrecRel.comp Primrec.eq (Data.primrec_left.comp Data.primrec_left) (const Data.nil)).not
  have h2 : PrimrecPred fun d : Data => d.right.right = .nil :=
    PrimrecRel.comp Primrec.eq (Data.primrec_right.comp Data.primrec_right) (const Data.nil)
  exact h1.and h2

theorem primrec_resultD : Primrec resultD := Data.primrec_right.comp Data.primrec_left

theorem primrec_initData : Primrec₂ initData :=
  Data.primrec_cons.comp (primrec_evD.comp fst)
    (Data.primrec_cons.comp (Data.primrec_cons.comp snd (const Data.nil)) (const Data.nil))

/-! ## Evaluation as a fixed point -/

theorem computable_evalStep : Computable evalStep :=
  (Primrec.ite primrec_isFinalD (Primrec.sumInl.comp primrec_resultD)
    (Primrec.sumInr.comp primrec_stepData)).to_comp

theorem partrec_evalData : Partrec₂ evalData :=
  (Partrec.fix computable_evalStep).comp
    (primrec_initData.to_comp.comp Computable.fst Computable.snd)

end Machine

/-! ## Polynomial-time functions are computable -/

theorem evalData_encode {α β : Type*} [SizedEncoding α] [SizedEncoding β] (F : PolyTimeFun α β)
    (a : α) : Machine.evalData (encode F.code) (encode a) = Part.some (encode (F a)) := by
  refine Part.eq_some_iff.2 ?_
  rw [show (encode F.code : Data) = F.code.toData from rfl, Machine.mem_evalData_iff]
  obtain ⟨t, -, h⟩ := F.computes a
  exact ⟨t, h⟩

/-- **The `Data`-level form**: a polynomial-time function of the ambient model, precomposed
with a computable encoding of its input, has a computable *encoded* output. No `Primcodable`
on the output type is needed, which matters — `Prog` deliberately has none (see the module
docstring of `Cost/Codable.lean`), so this is the only way a `PolyTimeFun _ Prog` such as
`GapCompression.samplerProg` can reach a computability proof at all. -/
theorem PolyTimeFun.computable_encode_comp {α β γ : Type*} [SizedEncoding α] [SizedEncoding β]
    [Primcodable γ] (F : PolyTimeFun α β) (h : γ → α)
    (hh : Computable fun c => (encode (h c) : Data)) :
    Computable fun c => (encode (F (h c)) : Data) :=
  Partrec.of_eq_tot (Machine.partrec_evalData.comp (Computable.const (encode F.code)) hh)
    fun c => by rw [evalData_encode]; exact Part.mem_some _

end MIPRE.Cost


