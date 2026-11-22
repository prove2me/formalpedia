-- Prove2me | Definitions.Def_InfoLossLAR_ReversibleStringInjection
-- name    : InfoLossLAR_ReversibleStringInjection
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T06:00:45.990566+00:00
-- url     : https://prove2.me/theorems/cd279a38-e7d6-44a5-af21-83e36f51aaa2
-- title:
--   Register layout for an injective classical string program
-- statement:
--   The circuit uses registers for the original string, its padded image, and workspaces for a forward program and a proposed inverse. The forward oracle writes the output into a fresh register. Exchanging the roles of the two data registers in the inverse oracle provides a circuit for restoring the original register to zero. The layout also specifies the canonical computational basis states at the input and output.
-- source:
--   Register layout used by the reversible machine stage of https://prove2.me/theorems/d106aba4-0ad7-4239-9c6b-4a9dc8c9ebc4

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_01
import Definitions.Def_InfoLossLAR_RegevSearch_PhysicalFourierReadout
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_ShorAlgorithms_QFT_Circuit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordLayout

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open TM2Boolean TM2Boolean.PolyProgramCircuit CodeGenerator

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PolynomialBudget

variable {f : Str → Str} (P : PolyProgram id id f) (p : Polynomial ℕ)

def width (n : ℕ) : ℕ := n+((compiled P n).ops.length+1)

end InfoLossLAR.WorstCase.NativeWordLayout

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordCoherent

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open scoped BigOperators

/-- Append arbitrary data/reference wires; original instruction addresses
remain fixed and every CNOT control/target remains distinct. -/
def extendInstr (k : ℕ) {W : ℕ} : Instr W → Instr (W+k)
  | .h i => .h (i.castAdd k)
  | .s i => .s (i.castAdd k)
  | .t i => .t (i.castAdd k)
  | .x i => .x (i.castAdd k)
  | .cnot i j h => .cnot (i.castAdd k) (j.castAdd k) (by intro he;exact h (Fin.castAdd_inj.mp he))

def extendCircuit (k : ℕ) {W : ℕ} (gates : Layered W) : Layered (W+k) :=
  gates.map (List.map (extendInstr k))

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentClassicalOracle

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute NativeWordCoherent NativeWordLayout

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

open scoped BigOperators

variable {f : Str → Str} (P : PolyProgram id id f)

def controls (n : ℕ) (i : Fin (capacity P n)) : Fin (width P n) := outputWire P n i (some true)

def base (n : ℕ) : Layered (width P n) := PolyProgramCircuit.circuit P n

def fullCircuit (n : ℕ) : Layered (width P n+capacity P n) :=
  extendCircuit (capacity P n) (base P n)++CoherentXorCopy.circuit (controls P n)++
    extendCircuit (capacity P n) (inverseCircuit (base P n))

end InfoLossLAR.WorstCase.CoherentClassicalOracle

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentClassicalOracle

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute NativeWordCoherent NativeWordLayout

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

variable {f : Str → Str} (P : PolyProgram id id f)

def paddedOutput (word : Str) : Str :=
  List.ofFn (fun i : Fin (capacity P word.length) => wordExtension (f word) i.val)

end InfoLossLAR.WorstCase.CoherentClassicalOracle

end

end

section

namespace InfoLossLAR.WorstCase.CoherentInjection

open QAlgorithms.Complexity FiniteGateTransport

/-- Physical order: padded original input, forward output, forward machine
workspace, inverse machine workspace. Both machine workspaces are retained. -/
def width (x y a b : ℕ) := x+y+a+b

def forwardWires (n x y a b : ℕ) (hn : n ≤ x) : Fin (n+a+y) ↪ Fin (width x y a b) where
  toFun i :=
    if h : i.val<n then ⟨i.val,by unfold width;omega⟩
    else if h' : i.val<n+a then ⟨x+y+(i.val-n),by unfold width;omega⟩
    else ⟨x+(i.val-(n+a)),by unfold width;omega⟩
  inj' := by
    intro i j he
    have hv := congrArg Fin.val he
    simp only at hv
    split_ifs at hv <;> simp_all only <;> apply Fin.ext <;> omega

def backwardWires (x y a b : ℕ) : Fin (y+b+x) ↪ Fin (width x y a b) where
  toFun i :=
    if h : i.val<y then ⟨x+i.val,by unfold width;omega⟩
    else if h' : i.val<y+b then ⟨x+y+a+(i.val-y),by unfold width;omega⟩
    else ⟨i.val-(y+b),by unfold width;omega⟩
  inj' := by
    intro i j he
    have hv := congrArg Fin.val he
    simp only at hv
    split_ifs at hv <;> simp_all only <;> apply Fin.ext <;> omega

def dataBits {x y a b : ℕ} (old : Bits x) (fresh : Bits y) : Bits (width x y a b) :=
  fun i => if hx : i.val<x then old ⟨i.val,hx⟩
    else if hy : i.val<x+y then fresh ⟨i.val-x,by omega⟩ else false

end InfoLossLAR.WorstCase.CoherentInjection

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentInjection

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

open scoped BigOperators

variable {f g : Str → Str} (P : PolyProgram id id f) (Q : PolyProgram id id g)

abbrev outputSize (n : ℕ) := capacity P n

abbrev originalSize (n : ℕ) := capacity Q (outputSize P n)

abbrev forwardWork (n : ℕ) := (compiled P n).ops.length+1

abbrev backwardWork (n : ℕ) := (compiled Q (outputSize P n)).ops.length+1

abbrev totalWidth (n : ℕ) := width (originalSize P Q n) (outputSize P n) (forwardWork P n) (backwardWork P Q n)

def firstWires (n : ℕ) : Fin (NativeWordLayout.width P n+capacity P n) ↪ Fin (totalWidth P Q n) :=
  forwardWires n (originalSize P Q n) (outputSize P n) (forwardWork P n) (backwardWork P Q n)
    (by simp only [originalSize,outputSize,capacity]; omega)

def secondWires (n : ℕ) : Fin (NativeWordLayout.width Q (outputSize P n)+capacity Q (outputSize P n)) ↪ Fin (totalWidth P Q n) :=
  backwardWires (originalSize P Q n) (outputSize P n) (forwardWork P n) (backwardWork P Q n)

def firstCircuit (n : ℕ) : Layered (totalWidth P Q n) :=
  relocateCircuit (firstWires P Q n) (CoherentClassicalOracle.fullCircuit P n)

def secondCircuit (n : ℕ) : Layered (totalWidth P Q n) :=
  relocateCircuit (secondWires P Q n) (CoherentClassicalOracle.fullCircuit Q (outputSize P n))

def circuit (n : ℕ) : Layered (totalWidth P Q n) := firstCircuit P Q n++secondCircuit P Q n

end InfoLossLAR.WorstCase.CoherentInjection

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentInjection

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

open scoped BigOperators

variable {f g : Str → Str} (P : PolyProgram id id f) (Q : PolyProgram id id g)

def inputBitsAt (n : ℕ) (word : Str) : Bits (totalWidth P Q n) :=
  dataBits (fun i => wordExtension word i.val) (fun _ => false)

def finalBitsAt (n : ℕ) (word : Str) : Bits (totalWidth P Q n) :=
  dataBits (fun _ => false) (fun i => wordExtension (f word) i.val)

variable {I : Type*} [Fintype I]

end InfoLossLAR.WorstCase.CoherentInjection

end

end


