-- Prove2me | Definitions.Def_PricingWithTips3DM_a8f5b6ef34401b5c44b30a21
-- name    : PricingWithTips3DM_a8f5b6ef34401b5c44b30a21
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:18:03.515074+00:00
-- url     : https://prove2.me/theorems/9ecdb41d-9359-427b-8030-8e6818299900
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionInputCompiler
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_bedc98df39f74f59e866c0e6
import Definitions.Def_PricingWithTips3DM_3d06fdaba09255b5d609af60
import Definitions.Def_PricingWithTips3DM_a79ce5303af3440f3d4b538f
import Definitions.Def_PricingWithTips3DM_df80aaf2b7d1945f94047704
import Definitions.Def_PricingWithTips3DM_56d251adbc3208bd35124d6d
import Definitions.Def_PricingWithTips3DM_0d878c712ea6e5d2ff7ff4fc
import Definitions.Def_PricingWithTips3DM_f34f433683fba432c5a857ff
import Definitions.Def_PricingWithTips3DM_9dc18a35c2492954536db4de
import Definitions.Def_PricingWithTips3DM_a68af1eb054191c79090656a
import Definitions.Def_PricingWithTips3DM_f627e6e08a4b59ba4a2206e2
import Definitions.Def_PricingWithTips3DM_ac13eecbb48e82abd310aed6
import Definitions.Def_PricingWithTips3DM_8afb3d01056601e0a512522a
import Definitions.Def_PricingWithTips3DM_4cd655ad6f5d3d5353ce8e98
import Definitions.Def_PricingWithTips3DM_1c67dd2c7aa5fb07b4a07325
import Definitions.Def_PricingWithTips3DM_a39abcc00b238b2d99ed7809
import Definitions.Def_PricingWithTips3DM_242f8497e98ec1ade577bf97
import Definitions.Def_PricingWithTips3DM_36570cf17835ff3cd7b5773d
import Definitions.Def_PricingWithTips3DM_80093cef933cf2579e62a92d
import Definitions.Def_PricingWithTips3DM_6c65e964c341e01e5d179d87
import Definitions.Def_PricingWithTips3DM_5a2dd8815216c377c022b769
import Definitions.Def_PricingWithTips3DM_efd72c44ac034595ed784104
import Definitions.Def_PricingWithTips3DM_eaae5484694ceacc9e409ff2
import Definitions.Def_PricingWithTips3DM_70df6a0e9df126ca570cf4a7
import Definitions.Def_PricingWithTips3DM_e21fd01d42817c93da25cf29
import Definitions.Def_PricingWithTips3DM_ad2f6a0f56affeb774827237
import Definitions.Def_PricingWithTips3DM_0bb960a327ec3d6b434d8235
import Definitions.Def_PricingWithTips3DM_db3082542c22a405e990621a
import Definitions.Def_PricingWithTips3DM_c9fc920e12cb3e507dd93b3d
import Definitions.Def_PricingWithTips3DM_68256059a3447c2893af340b
import Definitions.Def_PricingWithTips3DM_68c5fb77697279bbfde458e3
import Definitions.Def_PricingWithTips3DM_6c6d3d95ade0edcb4d22e302
import Definitions.Def_PricingWithTips3DM_9a3f6d04d98bfcc3d719183a
import Definitions.Def_PricingWithTips3DM_6872f3b1675deeb7dc77bbb8
import Definitions.Def_PricingWithTips3DM_d2fa27f500bf7b4f265ee08e
import Definitions.Def_PricingWithTips3DM_5f13282bdcbed83283f67f78
import Definitions.Def_PricingWithTips3DM_87b54f5fbcefb1855733306a
import Definitions.Def_PricingWithTips3DM_f81e0827028909cc514a0a80
import Definitions.Def_PricingWithTips3DM_0494881124b985a9615d29a0
import Definitions.Def_PricingWithTips3DM_a94d89ea25eb0a43c9e9c84a
import Definitions.Def_PricingWithTips3DM_fe7acafb16602f26daa60f56
import Definitions.Def_PricingWithTips3DM_8f5a0e5f7c4d0ac6c65b2125
import Definitions.Def_PricingWithTips3DM_0a2139be1262bce20289f938
import Definitions.Def_PricingWithTips3DM_8f9707790d2fe4661e77ce3f
import Definitions.Def_PricingWithTips3DM_9a9f8fb577d39c8a680f1347
import Definitions.Def_PricingWithTips3DM_505ffbbfb0335e9bd0e7f9f7
import Definitions.Def_PricingWithTips3DM_77b120564d1e166b09d2c3fb
import Definitions.Def_PricingWithTips3DM_aee87cb5b1ae90b59d1556c3
import Definitions.Def_PricingWithTips3DM_99e979353117a4f12232fdd9
import Definitions.Def_PricingWithTips3DM_8c56e542ed74eee3e3ee4089
import Definitions.Def_PricingWithTips3DM_c67ece6c69d5b0ef567eae8d
import Definitions.Def_PricingWithTips3DM_4bc768e3be9f86ad3801aa72
import Definitions.Def_PricingWithTips3DM_4093ca502fd72b056a9cc59c
import Definitions.Def_PricingWithTips3DM_af4f7f7eb260f6bfe78aaf7b
import Definitions.Def_PricingWithTips3DM_20b8755a66e9405218e1fb7f
import Definitions.Def_PricingWithTips3DM_965b45da5c516cd6bc7eb8b7
import Definitions.Def_PricingWithTips3DM_2b2043d97c6219d5e9e3ac58
import Definitions.Def_PricingWithTips3DM_ca80a4821d90bc35010bdc9e
import Definitions.Def_PricingWithTips3DM_4a293d66f128f2e85ba2cdfc
import Definitions.Def_PricingWithTips3DM_d2a9f6f08cc2cdf915c27a51
import Definitions.Def_PricingWithTips3DM_cf6cb4efc6cc53d645a5e539
import Definitions.Def_PricingWithTips3DM_45546bf402a6e35f72655d8e
import Definitions.Def_PricingWithTips3DM_66c095df44f03ac8a1bcce5e
import Definitions.Def_PricingWithTips3DM_75d94427a4778dc6ded2093a
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Canonical complete transition-family input

This file fixes the exact byte target of the remaining transition source
compiler.  The raw-input row seeds, their complete arithmetic expansion, the
runtime family controller input, and the semantic transition gate stream are
connected by literal equalities rather than extensional substitutes.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open StateTransition
open PolyBuilder

/-- Expand a row-major seed family to the complete runtime scripts consumed by
the transition-family controller.  The following public row starts exactly one
configuration width after the current row. -/
def transitionSeedFamilyScripts (tm : _root_.Turing.FinTM2)
    (seeds : List TransitionRowSeed) : List AffineTransitionScript :=
  seeds.map fun seed =>
    transitionScriptFromSeed tm seed
      (seed.rowBase + cfgBitCount tm seed.height)

/-- Exact controller alphabet encoding of a complete seed family. -/
def transitionSeedFamilyInput (tm : _root_.Turing.FinTM2)
    (seeds : List TransitionRowSeed) : List AffineStmtScriptSym :=
  encodeAffineTransitionFamily (transitionSeedFamilyScripts tm seeds)

/-- Pure-unary form of the same family input, before embedding it into the
statement-controller alphabet.  All phase tags of the continuous statement
controller are themselves encoded by fixed unary prefixes. -/
def transitionSeedFamilyUnaryInput (tm : _root_.Turing.FinTM2)
    (seeds : List TransitionRowSeed) : List UnaryFrameSym :=
  encodeAffineTransitionFamilyUnary (transitionSeedFamilyScripts tm seeds)

/-- Pure-unary payload of one row seed, including the local controller's
trailing terminator but excluding the outer family's leading marker. -/
def transitionSeedLocalUnaryInput (tm : _root_.Turing.FinTM2)
    (seed : TransitionRowSeed) : List UnaryFrameSym :=
  encodeAffineTransitionLocalUnary
    (transitionScriptFromSeed tm seed
      (seed.rowBase + cfgBitCount tm seed.height))

/-- The complete unary target is a literal row-major packet stream.  This is
the interface used by the forthcoming fixed seed-family expander. -/
theorem transitionSeedFamilyUnaryInput_eq_flatMap
    (tm : _root_.Turing.FinTM2) (seeds : List TransitionRowSeed) :
    transitionSeedFamilyUnaryInput tm seeds =
      seeds.flatMap fun seed =>
        .frameEnd :: transitionSeedLocalUnaryInput tm seed := by
  unfold transitionSeedFamilyUnaryInput transitionSeedFamilyScripts
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineTransitionFamilyUnary,
        transitionSeedLocalUnaryInput, ih]

/-- The controller-alphabet target is only the fixed `.data` symbol map over
the pure-unary seed expansion. -/
theorem transitionSeedFamilyInput_eq_map_data
    (tm : _root_.Turing.FinTM2) (seeds : List TransitionRowSeed) :
    transitionSeedFamilyInput tm seeds =
      (transitionSeedFamilyUnaryInput tm seeds).map .data := by
  rfl

/-- Complete transition scripts derived from the verifier's concrete
raw-input seed family. -/
def verifierTransitionFamilyScripts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineTransitionScript :=
  transitionSeedFamilyScripts W.machine.tm
    (verifierTransitionRowSeeds W input)

/-- Unique byte-level target for the remaining raw-input transition source
compiler. -/
def verifierTransitionFamilyInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineStmtScriptSym :=
  transitionSeedFamilyInput W.machine.tm
    (verifierTransitionRowSeeds W input)

/-- Raw-verifier specialization of the pure-unary source target. -/
def verifierTransitionFamilyUnaryInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  transitionSeedFamilyUnaryInput W.machine.tm
    (verifierTransitionRowSeeds W input)

/-- The exact controller input is the verified fixed symbol map of the unary
source target. -/
theorem verifierTransitionFamilyInputTarget_eq_map_data
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionFamilyInputTarget W input =
      (verifierTransitionFamilyUnaryInputTarget W input).map .data := by
  rfl

/-- Raw-input unary target in explicit row-packet order. -/
theorem verifierTransitionFamilyUnaryInputTarget_eq_flatMap
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionFamilyUnaryInputTarget W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        .frameEnd :: transitionSeedLocalUnaryInput W.machine.tm seed := by
  exact transitionSeedFamilyUnaryInput_eq_flatMap W.machine.tm
    (verifierTransitionRowSeeds W input)

/-! ## Concrete marked seed source -/

/-- Ordinary value-level triples underlying a transition seed family. -/
def transitionRowSeedTriples (seeds : List TransitionRowSeed) :
    List (Nat × Nat × Nat) :=
  seeds.map fun seed => (seed.height, seed.start, seed.rowBase)

/-- The raw seed source is exactly the ordinary flat triple encoding expected
by the reusable row marker. -/
theorem verifierTransitionRowSeedFrames_eq_triples
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionRowSeedFrames W input =
      encodeUnaryTripleRows
        (transitionRowSeedTriples (verifierTransitionRowSeeds W input)) := by
  rw [verifierTransitionRowSeedFrames_eq_seeds]
  simp [encodeUnaryTripleRows, transitionRowSeedTriples,
    List.flatMap_map]

/-- Row-delimited transition seeds produced from the raw verifier word.  The
marker follows each complete three-field seed and is consumed by the local-row
source controller, so it cannot be confused with field separators. -/
def verifierTransitionRowMarkedSeedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  markUnaryTripleRows (verifierTransitionRowSeedFrames W input)

/-- Exact semantic packet order of the marked raw-input seed source. -/
theorem verifierTransitionRowMarkedSeedFrames_eq_seeds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionRowMarkedSeedFrames W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame [seed.height, seed.start, seed.rowBase] ++
          [.frameEnd] := by
  unfold verifierTransitionRowMarkedSeedFrames
  rw [verifierTransitionRowSeedFrames_eq_triples,
    markUnaryTripleRows_encode]
  simp [encodeUnaryTripleMarkedRows, transitionRowSeedTriples,
    List.flatMap_map]

/-- A concrete fixed polynomial-time TM2 generates the row-delimited seed
packets directly from the raw verifier word. -/
noncomputable def
    verifierTransitionRowMarkedSeedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionRowMarkedSeedFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionRowSeedFrames_computableInPolyTime W)
      markUnaryTripleRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => markUnaryTripleRows
      (verifierTransitionRowSeedFrames W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Expanding the polynomial-time row seeds recovers the canonical semantic
transition-family script, field for field. -/
theorem verifierTransitionFamilyScripts_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionFamilyScripts W input =
      compileTransitionFamilyScriptsAt W.machine.tm
        ((verifierHeight W).eval input.length)
        ((verifierHorizon W).eval input.length) := by
  exact verifierTransitionRowSeeds_expand_eq_scripts W input

/-- Consequently the source target is literally the runtime encoding expected
by the already verified transition-family controller. -/
theorem verifierTransitionFamilyInputTarget_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionFamilyInputTarget W input =
      encodeAffineTransitionFamily
        (compileTransitionFamilyScriptsAt W.machine.tm
          ((verifierHeight W).eval input.length)
          ((verifierHorizon W).eval input.length)) := by
  change encodeAffineTransitionFamily
      (verifierTransitionFamilyScripts W input) = _
  rw [verifierTransitionFamilyScripts_eq_canonical]

/-- Interpreting the seed-expanded family yields exactly the frozen semantic
transition suffix of the verifier circuit. -/
theorem verifierTransitionFamilyGateStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    affineTransitionFamilyGateStream
        (verifierTransitionFamilyScripts W input) =
      verifierTransitionGateStream W input := by
  rw [verifierTransitionFamilyScripts_eq_canonical]
  simpa [verifierTransitionGateStream,
    verifierTransitionGateStreamByLength] using
    compileTransitionFamilyScriptsAt_gateStream_eq W.machine.tm
      ((verifierHeight W).eval input.length)
      ((verifierHorizon W).eval input.length)

/-- The fixed transition-family controller runs directly on the exact
seed-derived byte target and halts with the semantic transition suffix. -/
def verifierTransitionFamily_run
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionFamilyRevProgram)
      (affineTransitionFamilyLoopCfg
        (verifierTransitionFamilyInputTarget W input) output)
      (some (haltCfg affineTransitionFamilyRevProgram
        ((verifierTransitionGateStream W input).reverse ++ output)))
      (affineTransitionFamilyTotalSteps
        (verifierTransitionFamilyScripts W input)) := by
  have hrun := affineTransitionFamily_run
    (verifierTransitionFamilyScripts W input) output
  rw [verifierTransitionFamilyGateStream_eq W input] at hrun
  simpa [verifierTransitionFamilyInputTarget,
    transitionSeedFamilyInput,
    verifierTransitionFamilyScripts] using hrun

/-- The verified fixed symbol map lifts any concrete unary source compiler to
the exact controller-alphabet input target. -/
noncomputable def
    verifierTransitionFamilyInputTarget_computableInPolyTime_of_unaryCompiler
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (compiler : _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionFamilyUnaryInputTarget W)) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionFamilyInputTarget W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch compiler
      (listMap_computableInPolyTime AffineStmtScriptSym.data)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input =>
      (verifierTransitionFamilyUnaryInputTarget W input).map
        AffineStmtScriptSym.data)
  simpa only [Function.comp_def] using Classical.choice composed

/-- Once a concrete source TM2 emits the exact target fixed above, generic
machine composition produces the verifier transition gate stream.  The
premise is deliberately byte-level, so the remaining source proof cannot hide
an oracle-valued script behind an encoding equivalence. -/
noncomputable def
    verifierTransitionGateStream_computableInPolyTime_of_inputCompiler
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (compiler : _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionFamilyInputTarget W)) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionGateStream W) := by
  let typedCompiler : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineTransitionFamily (verifierTransitionFamilyScripts W) :=
    { tm := compiler.tm
      inputAlphabet := compiler.inputAlphabet
      outputAlphabet := compiler.outputAlphabet
      time := compiler.time
      outputsFun := fun input => by
        simpa only [id_eq, verifierTransitionFamilyInputTarget,
          transitionSeedFamilyInput, verifierTransitionFamilyScripts]
          using compiler.outputsFun input }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedCompiler affineTransitionFamilyGateStream_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionFamilyGateStream_eq W input] using run }

end CLRS.Chapter34.Turing.CookLevin


