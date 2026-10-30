-- Prove2me | Definitions.Def_OAIQ081S192
-- name    : OAIQ081S192
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:51:21.188751+00:00
-- url     : https://prove2.me/theorems/956bc0fb-8f1f-42ef-9ae0-8ec0f41e3495
-- title:
--   Definitions bundle OAIQ081S192 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 3 definitions and 5 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.preparationConstant`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.preparationDegree`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.preparationResources`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_HighQuerySetup`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySetup.lean), [`SubexponentialSAT_SqrtLogSpace_NativeQueryArithmetic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeQueryArithmetic.lean), [`SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeQueryPreparation.lean).
--
--   **Imports.** It imports the bundles `OAIQ081S189` and `OAIQ081S190` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.prepare_seed`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S189
import Definitions.Def_OAIQ081S190

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual query arithmetic with fixed ordinary polynomial time and space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query CostAssembly.Polynomial

/-- Exact degree bytes follow from the actual searched producer and survive
the interpolation and denominator stages. This is the source proof from
LeafProgramQueryDegree.arithmetic_degree without its unrelated query constructor. -/
theorem arithmetic_degree (base out : Data) (n : ℕ)
    (he : Eval arithmeticCommand n base out)
    (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (LeafRingSetupProgram.registers 8 (by decide)) LeafRingSetupProgram.parameters
      (projectState LeafRingSetupProgram.wideRegisters LeafRingSetupProgram.wideStacks base) = Bank.state r w)
    (S : ℕ) (hinit : ∀ i, (base.stacks i).length ≤ S)
    (hv : ∀ i, (Circuit.result Serialization.code m).val i ≤ S)
    (hw : ∀ i, (Circuit.result Serialization.code m).len i ≤ S)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (hexp : (Circuit.result Serialization.code m).val 44 = 3 ^ (m.val 34) - 2)
    (h728 : base.stacks 728 = []) : out.stacks 204 = List.replicate (m.val 34) true := by
  obtain ⟨nr, hnr, e, M, cache, u, b, hr, hp, hlow, h713, h714, h715, h716,
    h717, hprivate, hhigh, hcollector, hregs, hlowBlank, hdegree⟩ :=
    LeafProgram.Query.Ring.command_eval_degree base m w r hs ha S S S hinit hv hw ht hd hexp
  have hf728 : b.stacks 728 = base.stacks 728 :=
    hhigh _ (by decide) (by decide) (by decide)
  have hbwidth : ∀ i, (b.stacks i).length ≤ S + LeafProgram.Query.Ring.budget m S S S + 1 := by
    intro i
    have hi := LeafRingSetupProgram.Interpolation.eval_width hr hinit i
    omega
  obtain ⟨nd, hnd, last, he', hout, hinv, hdregs⟩ :=
    LayoutDenominatorProgramQuery.produced_command_eval b m ht hd M cache u e hp hlow
      (fun i hi hj => hprivate i hi (by omega)) (hf728.trans h728) _ hbwidth
  have heq := SubexpPrimeProgram.eval_result_unique he (hr.seq he') 0 0
  rw [heq, hout, Function.update_of_ne (by decide : (204 : Fin 768) ≠ 728)]
  exact hdegree

/-- One pair of polynomial coefficients is fixed before the physical input
and numeric model. The returned ring, cache and denominator proofs are all
produced by this same concrete arithmetic execution. -/
theorem arithmetic_resources : ∃ C d : ℕ,
    ∀ (base : Data) (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs),
      Circuit.Shape m w →
      projectState (LeafRingSetupProgram.registers 8 (by decide)) LeafRingSetupProgram.parameters
        (projectState LeafRingSetupProgram.wideRegisters LeafRingSetupProgram.wideStacks base) =
          Bank.state r w →
      ∀ S : ℕ, (∀ i, (base.stacks i).length ≤ S) →
        (∀ i, (Circuit.result Serialization.code m).val i ≤ S) →
        (∀ i, (Circuit.result Serialization.code m).len i ≤ S) →
        (∀ i, m.val i ≤ S) → (∀ i, m.len i ≤ S) →
        ∀ (ht : 0 < m.val 33) (hd : 0 < m.val 34),
          (Circuit.result Serialization.code m).val 44 = 3 ^ (m.val 34) - 2 →
          3 ^ (m.val 34) ≤ 16 * (m.val 21 + 1) ^ 2 → base.stacks 728 = [] →
          ∃ steps, ∃ (e : LeafRingSetupProgram.Data)
            (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
            (cache : RingProgram.ScalarCache 3 (m.val 33))
            (half : RingProgram.ScalarCode 3 (m.val 33)) (out : Data),
            steps ≤ C * (S + 1) ^ d ∧ Eval arithmeticCommand steps base out ∧
            ArithmeticOutput base out m hd M cache half e ∧
            out.stacks 204 = List.replicate (m.val 34) true ∧
            (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
              (LayoutDenominatorProgramQuery.value (m.val 33) (IrreducibleSearch.data hd)
                M cache half (base.stacks 740).length) *
              (2 : (IrreducibleSearch.data hd).O (m.val 33)) ^ ((base.stacks 740).length - 1) = 1 ∧
            (∀ i, (out.stacks i).length ≤ S + C * (S + 1) ^ d) ∧
            Trace (compiled arithmeticCommand 700 728) (steps + 1)
              (base.withPC (some (compiled arithmeticCommand 700 728).entry)) (out.withPC none) ∧
            ∀ k c, k ≤ steps + 1 → Trace (compiled arithmeticCommand 700 728) k
              (base.withPC (some (compiled arithmeticCommand 700 728).entry)) c →
              ∀ i, (c.stacks i).length ≤ S + C * (S + 1) ^ d + 1 := by
  obtain ⟨C, d, hpoly⟩ := LeafProgram.Query.Width.arithmetic_budget_polynomial
  refine ⟨C, d, ?_⟩
  intro base m w r hs ha S hinit hv hw hmv hml ht hd hexp hfield h728
  obtain ⟨steps, hsteps, e, M, cache, half, out, he, ho, hinv⟩ :=
    arithmetic_eval base m w r hs ha S S S hinit hv hw ht hd hexp h728
  change Eval arithmeticCommand steps base out at he
  have htbound := hsteps.trans (hpoly m S S S (base.stacks 740).length S
    le_rfl le_rfl le_rfl (hinit 740) hml hmv hfield)
  have hdegree := arithmetic_degree base out steps he m w r hs ha S hinit hv hw ht hd hexp h728
  have hhalt : Trace (compiled arithmeticCommand 700 728) (steps + 1)
      (base.withPC (some (compiled arithmeticCommand 700 728).entry)) (out.withPC none) :=
    halt_trace_of_eval he 700 728
  refine ⟨steps, e, M, cache, half, out, htbound, he, ho, hdegree, hinv, ?_,
    hhalt, ?_⟩
  · intro i
    have hg : (out.stacks i).length ≤ (base.stacks i).length + steps := by
      simpa [selectedStackBits] using
        trace_selectedStackBits (compiled arithmeticCommand 700 728) {i} (compiled_trace he 700 728)
    have hi := hinit i
    omega
  · intro k c hk hc i
    have hg : (c.stacks i).length ≤ (base.stacks i).length + k := by
      simpa [selectedStackBits] using trace_selectedStackBits _ {i} hc
    have hi := hinit i
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query packing and arithmetic preparation. Numeric and physical
input caps are kept separate from the subsequent exponential node traversal.
Every arithmetic object is returned by its actual native producer. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query CostAssembly.Polynomial

/-- Complete preparation from the physical post-frontend sources. All
numeric premises are compact parameter caps; every requested algorithmic
stage is executed here and no evaluator service is supplied. -/
theorem command_resources : ∃ C d : ℕ,
    ∀ (base : Data) (p : PackingCallerProgram.Problem) (m : Circuit.Model)
      (w : Bank.Words) (r : Bank.Regs),
      PackingCallerProgram.Sources base p → PackingCallerProgram.Empty base →
      Circuit.Shape m w → projectState Exports.bankRegs Exports.bank base = Bank.state r w →
      ∀ S : ℕ, (∀ i, (base.stacks i).length ≤ S) →
        p.n ≤ S → p.factors ≤ S → p.incidences ≤ S → p.r ≤ S → p.Q ≤ S → p.s ≤ S →
        p.r ^ (2 * p.Q) ≤ S →
        (∀ i, (Circuit.result Serialization.code m).val i ≤ S) →
        (∀ i, (Circuit.result Serialization.code m).len i ≤ S) →
        (∀ i, m.val i ≤ S) → (∀ i, m.len i ≤ S) →
        ∀ (ht : 0 < m.val 33) (hd : 0 < m.val 34),
          (Circuit.result Serialization.code m).val 44 = 3 ^ (m.val 34) - 2 →
          3 ^ (m.val 34) ≤ 16 * (m.val 21 + 1) ^ 2 → base.stacks 728 = [] →
          ∃ first : MulticolorTypes.Word p.r p.Q,
            ∃ rest : List (MulticolorTypes.Word p.r p.Q), ∃ packed : Data, ∃ np na,
            ∃ (e : LeafRingSetupProgram.Data)
              (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
              (cache : RingProgram.ScalarCache 3 (m.val 33))
              (half : RingProgram.ScalarCode 3 (m.val 33)) (out : Data),
              (first :: rest).map Subexp.ReadPlan.encodeWord =
                Subexp.AssignmentAlphabetSemantics.wordBytes p.r p.Q ∧
              (first :: rest).Nodup ∧ (∀ z, z ∈ first :: rest) ∧
              Eval PackingCallerProgram.command np base packed ∧
              packed.stacks = (PackingCallerProgram.result base p first rest).stacks ∧
              Eval arithmeticCommand na packed out ∧
              ArithmeticOutput packed out m hd M cache half e ∧
              out.stacks 204 = List.replicate (m.val 34) true ∧
              (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
                (LayoutDenominatorProgramQuery.value (m.val 33) (IrreducibleSearch.data hd)
                  M cache half (packed.stacks 740).length) *
                (2 : (IrreducibleSearch.data hd).O (m.val 33)) ^ ((packed.stacks 740).length - 1) = 1 ∧
              Eval command (np + na) base out ∧ np + na ≤ C * (S + 1) ^ d ∧
              (∀ i, (out.stacks i).length ≤ C * (S + 1) ^ d) ∧
              Trace (compiled command 700 728) (np + na + 1)
                (base.withPC (some (compiled command 700 728).entry)) (out.withPC none) ∧
              ∀ k c, k ≤ np + na + 1 → Trace (compiled command 700 728) k
                (base.withPC (some (compiled command 700 728).entry)) c →
                ∀ i, (c.stacks i).length ≤ C * (S + 1) ^ d := by
  obtain ⟨Cp, dp, hdp, hpackpoly⟩ := PackingCallerProgram.budget_polynomial
  obtain ⟨Ca, da, harith⟩ := arithmetic_resources
  obtain ⟨C, d, hpoly⟩ := setupEnvelope_polynomial Cp dp Ca da
  refine ⟨C, d, ?_⟩
  intro base p m w r hsources hempty hshape hbank S hinit hn hf hD hr hQ heps htypes
    hv hw hmv hml ht hd hexp hfield h728
  obtain ⟨first, rest, hrows, hnodup, hall⟩ := Subexp.AssignmentAlphabetSemantics.wordBytes_order p.hr p.Q
  obtain ⟨np, packed, hnp, hep, hbytes, hregs⟩ :=
    PackingCallerProgram.command_eval base p hsources hempty first rest hrows hnodup hall
  have hG := packing_size_le base p S hsources hinit hn hf hD hr hQ heps htypes
  obtain ⟨hbudget, hpacked⟩ := hpackpoly base p first rest hsources hempty hrows
  let P := Cp * (790 * (S + 1)) ^ dp
  let A := S + P
  have hP : PackingCallerProgram.budget base p first rest ≤ P :=
    hbudget.trans (Nat.mul_le_mul_left Cp (Nat.pow_le_pow_left hG dp))
  have hPwords : ∀ i, (packed.stacks i).length ≤ P := by
    intro i
    rw [hbytes]
    exact (hpacked i).trans (Nat.mul_le_mul_left Cp (Nat.pow_le_pow_left hG dp))
  have hSA : S ≤ A := by dsimp [A]; omega
  have hPA : P ≤ A := by dsimp [A]; omega
  have hpackedFrame (i : Fin 768) (hb : i.val < 417 ∨ 481 ≤ i.val)
      (hl : i.val < 128 ∨ 142 ≤ i.val) (hh : i.val < 730 ∨ 744 ≤ i.val) :
      packed.stacks i = base.stacks i := by
    rw [hbytes]
    exact PackingCallerProgram.result_frame base p first rest i hb hl hh
  have hpackedBank := ring_bank_of_frame base packed w r hbank
    (fun i hi hj => hpackedFrame i (Or.inl hj) (Or.inr (by omega)) (Or.inl (by omega)))
  have hpacked728 : packed.stacks 728 = [] :=
    (hpackedFrame 728 (by decide) (by decide) (by decide)).trans h728
  obtain ⟨na, e, M, cache, half, out, hna, hea, hout, hdegree, hinverse, hfinal, _, _⟩ :=
    harith packed m w (packed.regs ∘ Exports.bankRegs) hshape hpackedBank A
      (fun i => (hPwords i).trans hPA)
      (fun i => (hv i).trans hSA) (fun i => (hw i).trans hSA)
      (fun i => (hmv i).trans hSA) (fun i => (hml i).trans hSA)
      ht hd hexp hfield hpacked728
  have heval : Eval command (np + na) base out := hep.seq hea
  have htotal : S + (np + na) + 1 ≤ setupEnvelope Cp dp Ca da S := by
    change S + (np + na) + 1 ≤ S + P + Ca * (A + 1) ^ da + 1
    omega
  have hcap := htotal.trans (hpoly S)
  refine ⟨first, rest, packed, np, na, e, M, cache, half, out, hrows, hnodup, hall,
    hep, hbytes, hea, hout, hdegree, hinverse, heval, by omega, ?_,
    compiled_halt_trace heval 700 728, ?_⟩
  · intro i
    have hi := hfinal i
    have hfull := hpoly S
    change A + Ca * (A + 1) ^ da + 1 ≤ C * (S + 1) ^ d at hfull
    omega
  · intro k c hk hc i
    have hg : (c.stacks i).length ≤ (base.stacks i).length + k := by
      simpa [selectedStackBits] using trace_selectedStackBits _ {i} hc
    have hi := hinit i
    omega

/-- Retiming a concrete semantic execution uses a bounded visible shadow.
The resulting run is the same fixed command on the original physical input;
its time excludes arbitrary carried words and its prefixes include them. -/
theorem command_source_resources : ∃ C d : ℕ,
    ∀ (base out : Data) (oldSteps : ℕ), Eval command oldSteps base out →
    ∀ (p : PackingCallerProgram.Problem) (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs),
      PackingCallerProgram.Sources base p → PackingCallerProgram.Empty base →
      Circuit.Shape m w → projectState Exports.bankRegs Exports.bank base = Bank.state r w →
      ∀ S B : ℕ,
        (∀ i, ¬ LeafProgram.OuterCarried.hidden i → (base.stacks i).length ≤ S) →
        (∀ i, LeafProgram.OuterCarried.hidden i → (base.stacks i).length ≤ B) →
        p.n ≤ S → p.factors ≤ S → p.incidences ≤ S → p.r ≤ S → p.Q ≤ S → p.s ≤ S →
        p.r ^ (2 * p.Q) ≤ S →
        (∀ i, (Circuit.result Serialization.code m).val i ≤ S) →
        (∀ i, (Circuit.result Serialization.code m).len i ≤ S) →
        (∀ i, m.val i ≤ S) → (∀ i, m.len i ≤ S) →
        ∀ (_ht : 0 < m.val 33) (_hd : 0 < m.val 34),
          (Circuit.result Serialization.code m).val 44 = 3 ^ (m.val 34) - 2 →
          3 ^ (m.val 34) ≤ 16 * (m.val 21 + 1) ^ 2 → base.stacks 728 = [] →
          oldSteps ≤ C * (S + 1) ^ d ∧
            Trace (compiled command 700 728) (oldSteps + 1)
              (base.withPC (some (compiled command 700 728).entry)) (out.withPC none) ∧
            ∀ k c, k ≤ oldSteps + 1 → Trace (compiled command 700 728) k
              (base.withPC (some (compiled command 700 728).entry)) c →
              ∀ i, (c.stacks i).length ≤ max (C * (S + 1) ^ d) B := by
  obtain ⟨C,d,hresources⟩ := command_resources
  refine ⟨C,d,?_⟩
  intro base out oldSteps hsem p m w r hs he hshape hbank S B hvisible hhidden
    hn hf hD hr hQ heps htypes hv hw hmv hml ht hd hexp hfield h728
  have hshadow : ∀ i, ((shadow base).stacks i).length ≤ S :=
    CommandStackTransport.shadow_stack_bound LeafProgram.OuterCarried.hidden base S hvisible
  obtain ⟨first,rest,packed,np,na,e,M,cache,half,shadowOut,_,_,_,_,_,_,_,_,_,
      hrun,htime,_,_,hprefix⟩ :=
    hresources (shadow base) p m w r (shadow_sources base p hs) (shadow_empty base he)
      hshape ((shadow_bank base).trans hbank) S hshadow hn hf hD hr hQ heps htypes
      hv hw hmv hml ht hd hexp hfield ((shadow_visible base 728 (by decide)).trans h728)
  have hactual := CommandStackTransport.eval_shadow LeafProgram.OuterCarried.hidden command_avoids hrun
  have hsteps : oldSteps = np + na := StreamResources.eval_steps_eq 700 728 hsem hactual
  refine ⟨by simpa only [hsteps] using htime, compiled_halt_trace hsem 700 728, ?_⟩
  rw [hsteps]
  exact CommandStackTransport.eval_shadow_prefix_bound LeafProgram.OuterCarried.hidden command_avoids
    700 728 hrun (fun k c hk hc i _ => hprefix k c hk hc i) hhidden


/-- Fully instantiated preparation after the actual guarded frontend. The
semantic producer run is constructed here; the same run has a source-only
time bound and a maximum-prefix bound retaining arbitrary carried words. -/
theorem front_resources : ∃ C d : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
      (base front : Data) (l : Fin 8 → ℕ) (bw : Bank.Words) (S B : ℕ),
      FrontState q k base front l bw →
      (∀ i, ¬ LeafProgram.OuterCarried.hidden i → (front.stacks i).length ≤ S) →
      (∀ i, LeafProgram.OuterCarried.hidden i → (front.stacks i).length ≤ B) →
      (∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) l)).val i ≤ S) →
      (∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) l)).len i ≤ S) →
      front.stacks 728 = [] →
      Nonempty (FrontRun q k hg front l S B (C * (S + 1) ^ d)) := by
  obtain ⟨Cs,ds,hsemantic⟩ := command_resources
  obtain ⟨C,d,htimed⟩ := command_source_resources
  refine ⟨C,d,?_⟩
  intro q k hg base front l bw S B hfront hvisible hhidden hv hl h728
  obtain ⟨hs,he,hshape,hbank,hn,hf,hD,hr,hQ,heps,htypes,hmv,hml,ht,hd,hexp,hfield⟩ :=
    front_numeric_inputs q k hg base front l bw hfront S hv hl
  have hSA : S ≤ S+B := Nat.le_add_right _ _
  have hall : ∀ i, (front.stacks i).length ≤ S+B := by
    intro i
    by_cases hi : LeafProgram.OuterCarried.hidden i
    · exact (hhidden i hi).trans (Nat.le_add_left _ _)
    · exact (hvisible i hi).trans hSA
  obtain ⟨first,rest,packed,np,na,e,M,cache,half,out,hrows,hnodup,hcomplete,
      hpack,hbytes,harith,houtput,hdegree,hinverse,hrun,_,_,_,_⟩ :=
    hsemantic front (packingProblem q k hg) (Execute.guardedModel (q.input k) l)
      bw (front.regs ∘ Exports.bankRegs) hs he hshape hbank (S+B) hall
      (hn.trans hSA) (hf.trans hSA) (hD.trans hSA) (hr.trans hSA) (hQ.trans hSA)
      (heps.trans hSA) (htypes.trans hSA) (fun i => (hv i).trans hSA)
      (fun i => (hl i).trans hSA) (fun i => (hmv i).trans hSA)
      (fun i => (hml i).trans hSA) ht hd hexp hfield h728
  obtain ⟨htime,htrace,hprefix⟩ := htimed front out (np+na) hrun
    (packingProblem q k hg) (Execute.guardedModel (q.input k) l)
    bw (front.regs ∘ Exports.bankRegs) hs he hshape hbank S B hvisible hhidden
    hn hf hD hr hQ heps htypes hv hl hmv hml ht hd hexp hfield h728
  let packingData : FrontPackingData q k hg := {
    first := first
    rest := rest
    packed := packed
    packingSteps := np }
  let arithmeticData : FrontArithmeticData q k l := (na, e, M, cache, half, out)
  let data : FrontData q k hg l := (packingData, arithmeticData)
  let execution : FrontExecution q k hg front l data := {
    rows := hrows
    nodup := hnodup
    complete := hcomplete
    packing := hpack
    packed_words := hbytes
    arithmetic := harith
    arithmetic_output := houtput
    degree := hdegree
    inverse := hinverse
    command := hrun }
  have houtputSpace : ∀ i, (out.stacks i).length ≤ max (C * (S + 1) ^ d) B :=
    fun i => hprefix (np + na + 1) (out.withPC none) le_rfl htrace i
  let bounds : FrontBounds front S B (C * (S + 1) ^ d) data := {
    time := htime
    output_space := houtputSpace
    trace := htrace
    prefix_space := hprefix }
  exact ⟨⟨data, execution, bounds⟩⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQuerySetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete preparation and fresh high-counter initialization for the fixed
marked and accepted queries. The witness below is produced by the actual
programs; no implementation or evaluator is supplied as a hypothesis. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound
open HighMarkedFrontend

noncomputable def preparationConstant : ℕ :=
  Classical.choose NativeQueryPreparation.front_resources

noncomputable def preparationDegree : ℕ :=
  Classical.choose (Classical.choose_spec NativeQueryPreparation.front_resources)

abbrev preparationResources :=
  Classical.choose_spec (Classical.choose_spec NativeQueryPreparation.front_resources)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end


