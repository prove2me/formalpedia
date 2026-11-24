-- Prove2me | Definitions.Def_CSL_Circuit_Framework_CodedSimulation
-- name    : CSL_Circuit_Framework_CodedSimulation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:34:13.186552+00:00
-- url     : https://prove2.me/theorems/b9d61fa7-0715-4f61-a557-f0798e9f4454
-- title:
--   Coded sorting library: Circuit / Framework / CodedSimulation
-- statement:
--   Module `CodedSorting.Circuit.Framework.CodedSimulation` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Executing finite XOR programs in changing address layouts
--
--   This file gives an actual gate-by-gate functional execution.  Before a gate,
--   only its listed ports are converted from their current locations to the
--   gate's common location.  The finite XOR gate is then evaluated pointwise,
--   and its ports acquire the new location.  Other registers retain both their
--   contents and their locations.  Thus location consistency is propagated by
--   the program; it is not an axiom about a completed computation.
--
--   These are exact array semantics.  Physical disk costs, rank decompositions,
--   and the concrete matrix assignment are additional interfaces.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Framework.CodedSimulation

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Memory_Address
import Definitions.Def_CSL_Circuit_Framework_CircuitProgram
import Definitions.Def_CSL_Shared_Memory_Streams

/-!
# Executing finite XOR programs in changing address layouts

This file gives an actual gate-by-gate functional execution.  Before a gate,
only its listed ports are converted from their current locations to the
gate's common location.  The finite XOR gate is then evaluated pointwise,
and its ports acquire the new location.  Other registers retain both their
contents and their locations.  Thus location consistency is propagated by
the program; it is not an axiom about a completed computation.

These are exact array semantics.  Physical disk costs, rank decompositions,
and the concrete matrix assignment are additional interfaces.
-/

set_option autoImplicit false

namespace CSL.CodedSimulation

open CSL.Circuit
open CSL.CircuitProgram
open CSL.Address

variable {Reg Addr : Type*} [DecidableEq Reg]

abbrev Locations (Reg Addr : Type*) := Reg → Equiv.Perm Addr
abbrev StreamState (Reg Addr : Type*) := Reg → Addr → Bit

/-- The listed finite gate and the address layout common to all its ports. -/
structure Stage (Reg Addr : Type*) [DecidableEq Reg] where
  gate : XorGate Reg
  location : Equiv.Perm Addr

def encode (locations : Locations Reg Addr) (F : StreamState Reg Addr) :
    StreamState Reg Addr := fun r => transport (locations r) (F r)

def decode (locations : Locations Reg Addr) (F : StreamState Reg Addr) :
    StreamState Reg Addr := fun r => transport (locations r).symm (F r)

omit [DecidableEq Reg] in
theorem encode_decode (locations : Locations Reg Addr) (F : StreamState Reg Addr) :
    encode locations (decode locations F) = F := by
  funext r a
  simp [encode, decode, transport]

omit [DecidableEq Reg] in
theorem decode_encode (locations : Locations Reg Addr) (F : StreamState Reg Addr) :
    decode locations (encode locations F) = F := by
  funext r a
  simp [encode, decode, transport]

def afterLocations (locations : Locations Reg Addr) (stage : Stage Reg Addr) :
    Locations Reg Addr := fun r =>
  if r ∈ stage.gate.ports then stage.location else locations r

/-- Actual address changes on exactly the incoming register wires. -/
def alignedInput (locations : Locations Reg Addr) (stage : Stage Reg Addr)
    (F : StreamState Reg Addr) : StreamState Reg Addr := fun r =>
  if r ∈ stage.gate.ports then
    transport ((locations r).symm.trans stage.location) (F r)
  else F r

def pointwiseGate (gate : XorGate Reg) (F : StreamState Reg Addr) :
    StreamState Reg Addr := fun r a => gate.eval (fun j => F j a) r

def physicalGate (locations : Locations Reg Addr) (stage : Stage Reg Addr)
    (F : StreamState Reg Addr) : StreamState Reg Addr :=
  pointwiseGate stage.gate (alignedInput locations stage F)

theorem aligned_encoded_port (locations : Locations Reg Addr)
    (stage : Stage Reg Addr) (F : StreamState Reg Addr) (r : Reg)
    (hr : r ∈ stage.gate.ports) :
    alignedInput locations stage (encode locations F) r =
      transport stage.location (F r) := by
  funext a
  simp [alignedInput, hr, encode, transport]

/-- Exact one-gate simulation, including untouched registers. -/
theorem physicalGate_correct (locations : Locations Reg Addr)
    (stage : Stage Reg Addr) (F : StreamState Reg Addr) :
    physicalGate locations stage (encode locations F) =
      encode (afterLocations locations stage) (pointwiseGate stage.gate F) := by
  funext r a
  by_cases hr : r ∈ stage.gate.ports
  · have hinputs : ∀ j ∈ stage.gate.ports,
        alignedInput locations stage (encode locations F) j a =
          F j (stage.location.symm a) := by
      intro j hj
      rw [aligned_encoded_port locations stage F j hj]
      rfl
    have heval := stage.gate.eval_congr_on_ports
      (fun j => alignedInput locations stage (encode locations F) j a)
      (fun j => F j (stage.location.symm a)) hinputs r hr
    simpa only [physicalGate, pointwiseGate, encode, afterLocations,
      if_pos hr, transport] using heval
  · change stage.gate.eval
        (fun j => alignedInput locations stage (encode locations F) j a) r = _
    rw [stage.gate.eval_outside_ports _ r hr]
    simp only [alignedInput, if_neg hr, encode, afterLocations, transport,
      pointwiseGate]
    exact (stage.gate.eval_outside_ports
      (fun j => F j ((locations r).symm a)) r hr).symm

def finalLocations : List (Stage Reg Addr) → Locations Reg Addr → Locations Reg Addr
  | [], locations => locations
  | stage :: rest, locations => finalLocations rest (afterLocations locations stage)

def runCoded : List (Stage Reg Addr) → Locations Reg Addr →
    StreamState Reg Addr → StreamState Reg Addr
  | [], _, F => F
  | stage :: rest, locations, F =>
    runCoded rest (afterLocations locations stage) (physicalGate locations stage F)

def liftProgram (program : List (XorGate Reg)) (F : StreamState Reg Addr) :
    StreamState Reg Addr := fun r a => runProgram program (fun j => F j a) r

theorem liftProgram_cons (gate : XorGate Reg) (program : List (XorGate Reg))
    (F : StreamState Reg Addr) :
    liftProgram (gate :: program) F = liftProgram program (pointwiseGate gate F) := rfl

/-- Whole finite execution follows by induction over the literal gate list. -/
theorem runCoded_conjugacy (trace : List (Stage Reg Addr))
    (locations : Locations Reg Addr) (F : StreamState Reg Addr) :
    runCoded trace locations (encode locations F) =
      encode (finalLocations trace locations)
        (liftProgram (trace.map Stage.gate) F) := by
  induction trace generalizing locations F with
  | nil => rfl
  | cons stage rest ih =>
    simp only [runCoded, finalLocations, List.map_cons, liftProgram_cons]
    rw [physicalGate_correct, ih]

/-- The initial inverse layout is a mathematical description of the existing
input.  `runCoded` itself does not perform an extra initial decode. -/
theorem runCoded_arbitrary_input (trace : List (Stage Reg Addr))
    (locations : Locations Reg Addr) (F : StreamState Reg Addr) :
    runCoded trace locations F =
      encode (finalLocations trace locations)
        (liftProgram (trace.map Stage.gate) (decode locations F)) := by
  have h := runCoded_conjugacy trace locations (decode locations F)
  rw [encode_decode] at h
  exact h

/-- The logical circuit's proved permutation produces an exact physical
endpoint address transform for every independent register stream. -/
theorem output_of_permutation (trace : List (Stage Reg Addr))
    (locations : Locations Reg Addr) (σ : Equiv.Perm Reg)
    (hprogram : ∀ s : Reg → Bit,
      runProgram (trace.map Stage.gate) s = fun r => s (σ.symm r))
    (F : StreamState Reg Addr) (i : Reg) :
    runCoded trace locations F (σ i) =
      transport ((locations i).symm.trans (finalLocations trace locations (σ i)))
        (F i) := by
  rw [runCoded_arbitrary_input]
  have hlogical : liftProgram (trace.map Stage.gate) (decode locations F) (σ i) =
      decode locations F i := by
    funext a
    simp only [liftProgram, hprogram, Equiv.symm_apply_apply]
  change transport (finalLocations trace locations (σ i))
    (liftProgram (trace.map Stage.gate) (decode locations F) (σ i)) = _
  rw [hlogical]
  exact transport_comp (locations i).symm
    (finalLocations trace locations (σ i)) (F i)

theorem all_streams_same_update (trace : List (Stage Reg Addr))
    (locations : Locations Reg Addr) (σ : Equiv.Perm Reg)
    (hprogram : ∀ s : Reg → Bit,
      runProgram (trace.map Stage.gate) s = fun r => s (σ.symm r))
    (update : Equiv.Perm Addr)
    (hendpoints : ∀ i, (locations i).symm.trans
      (finalLocations trace locations (σ i)) = update)
    (F : StreamState Reg Addr) (i : Reg) :
    runCoded trace locations F (σ i) = transport update (F i) := by
  rw [output_of_permutation trace locations σ hprogram F i, hendpoints]

/-- Explicit final wire conversions from the last visited gate to the
declared sink labels.  These edges must also be included in cost accounting. -/
def terminalConvert (current sinks : Locations Reg Addr)
    (F : StreamState Reg Addr) : StreamState Reg Addr := fun r =>
  transport ((current r).symm.trans (sinks r)) (F r)

omit [DecidableEq Reg] in
theorem terminalConvert_encoded (current sinks : Locations Reg Addr)
    (F : StreamState Reg Addr) :
    terminalConvert current sinks (encode current F) = encode sinks F := by
  funext r a
  simp [terminalConvert, encode, transport]

def runCodedTo (trace : List (Stage Reg Addr))
    (sources sinks : Locations Reg Addr) (F : StreamState Reg Addr) :
    StreamState Reg Addr :=
  terminalConvert (finalLocations trace sources) sinks (runCoded trace sources F)

/-- Includes both initial source-to-first-gate and last-gate-to-sink edges. -/
theorem runCodedTo_conjugacy (trace : List (Stage Reg Addr))
    (sources sinks : Locations Reg Addr) (F : StreamState Reg Addr) :
    runCodedTo trace sources sinks F =
      encode sinks (liftProgram (trace.map Stage.gate) (decode sources F)) := by
  unfold runCodedTo
  rw [runCoded_arbitrary_input, terminalConvert_encoded]

theorem output_at_sink (trace : List (Stage Reg Addr))
    (sources sinks : Locations Reg Addr) (σ : Equiv.Perm Reg)
    (hprogram : ∀ s : Reg → Bit,
      runProgram (trace.map Stage.gate) s = fun r => s (σ.symm r))
    (F : StreamState Reg Addr) (i : Reg) :
    runCodedTo trace sources sinks F (σ i) =
      transport ((sources i).symm.trans (sinks (σ i))) (F i) := by
  rw [runCodedTo_conjugacy]
  have hlogical : liftProgram (trace.map Stage.gate) (decode sources F) (σ i) =
      decode sources F i := by
    funext a
    simp only [liftProgram, hprogram, Equiv.symm_apply_apply]
  change transport (sinks (σ i))
    (liftProgram (trace.map Stage.gate) (decode sources F) (σ i)) = _
  rw [hlogical]
  exact transport_comp (sources i).symm (sinks (σ i)) (F i)

theorem all_sink_streams_update (trace : List (Stage Reg Addr))
    (sources sinks : Locations Reg Addr) (σ : Equiv.Perm Reg)
    (hprogram : ∀ s : Reg → Bit,
      runProgram (trace.map Stage.gate) s = fun r => s (σ.symm r))
    (update : Equiv.Perm Addr)
    (hendpoints : ∀ i, (sources i).symm.trans (sinks (σ i)) = update)
    (F : StreamState Reg Addr) (i : Reg) :
    runCodedTo trace sources sinks F (σ i) = transport update (F i) := by
  rw [output_at_sink trace sources sinks σ hprogram F i, hendpoints]

/-- The whole-array middle update: split full rows, execute the literal
finite coded program, restore output-port order, and gather full rows. -/
theorem split_execute_gather {Rows Roles : ℕ} {Inner : Type*}
    (trace : List (Stage (Fin Roles) (Fin Rows × Inner)))
    (locations : Locations (Fin Roles) (Fin Rows × Inner))
    (σ : Equiv.Perm (Fin Roles))
    (hprogram : ∀ s : Fin Roles → Bit,
      runProgram (trace.map Stage.gate) s = fun r => s (σ.symm r))
    (update : Equiv.Perm Inner)
    (hendpoints : ∀ i, (locations i).symm.trans
      (finalLocations trace locations (σ i)) =
        Equiv.prodCongr (Equiv.refl (Fin Rows)) update)
    (F : Fin (Rows * Roles) → Inner → Bit) :
    Streams.gatherRows (fun i j a =>
      runCoded trace locations
        (fun r b => Streams.splitRows F r b.1 b.2) (σ i) (j, a)) =
      Streams.insideRows update F := by
  calc
    _ = Streams.gatherRows (fun i j a => Streams.splitRows F i j (update.symm a)) := by
      apply congrArg Streams.gatherRows
      funext i j a
      rw [all_streams_same_update trace locations σ hprogram
        (Equiv.prodCongr (Equiv.refl (Fin Rows)) update) hendpoints]
      rfl
    _ = _ := Streams.gather_processed_rows update F

section CompleteExchange

variable {H Prefix Gap Suffix : Type*} [AddCommGroup H]

def lowerSubtractEquiv : Equiv.Perm (H × H) where
  toFun := lowerSubtract
  invFun := lowerAdd
  left_inv x := by
    apply Prod.ext <;> simp [lowerSubtract, lowerAdd]
  right_inv x := by
    apply Prod.ext <;> simp [lowerSubtract, lowerAdd]

def lowerReflectEquiv : Equiv.Perm (H × H) where
  toFun := lowerReflect
  invFun := lowerReflect
  left_inv x := by
    apply Prod.ext <;> simp [lowerReflect]
  right_inv x := by
    apply Prod.ext <;> simp [lowerReflect]

theorem full_three_step_exchange :
    (mapPairEquiv (lowerSubtractEquiv (H := H))).trans
      ((mapPairEquiv (shear (id : H → H))).trans
        (mapPairEquiv (lowerReflectEquiv (H := H)))) =
      (exchangeEquiv : Equiv.Perm (FullAddress Prefix H Gap Suffix)) := by
  apply Equiv.ext
  intro a
  cases a with
  | mk p h g d z =>
    change FullAddress.mk p
      (lowerReflect (upperAdd (lowerSubtract (h, d)))).1 g
      (lowerReflect (upperAdd (lowerSubtract (h, d)))).2 z = _
    rw [three_updates_exchange]
    rfl

theorem insideRows_comp {Rows Roles : ℕ} {Inner : Type*}
    (e₁ e₂ : Equiv.Perm Inner) (F : Fin (Rows * Roles) → Inner → Bit) :
    Streams.insideRows e₂ (Streams.insideRows e₁ F) =
      Streams.insideRows (e₁.trans e₂) F := rfl

/-- The literal split / coded gates / output-port restoration / gather pipeline. -/
def executeRows {Rows Roles : ℕ} {Inner : Type*}
    (trace : List (Stage (Fin Roles) (Fin Rows × Inner)))
    (locations : Locations (Fin Roles) (Fin Rows × Inner))
    (σ : Equiv.Perm (Fin Roles))
    (F : Fin (Rows * Roles) → Inner → Bit) : Fin (Rows * Roles) → Inner → Bit :=
  Streams.gatherRows (fun i j a =>
    runCoded trace locations
      (fun r b => Streams.splitRows F r b.1 b.2) (σ i) (j, a))

theorem executeRows_correct {Rows Roles : ℕ} {Inner : Type*}
    (trace : List (Stage (Fin Roles) (Fin Rows × Inner)))
    (locations : Locations (Fin Roles) (Fin Rows × Inner))
    (σ : Equiv.Perm (Fin Roles))
    (hprogram : ∀ s : Fin Roles → Bit,
      runProgram (trace.map Stage.gate) s = fun r => s (σ.symm r))
    (update : Equiv.Perm Inner)
    (hendpoints : ∀ i, (locations i).symm.trans
      (finalLocations trace locations (σ i)) =
        Equiv.prodCongr (Equiv.refl (Fin Rows)) update)
    (F : Fin (Rows * Roles) → Inner → Bit) :
    executeRows trace locations σ F = Streams.insideRows update F :=
  split_execute_gather trace locations σ hprogram update hendpoints F

/-- The same concrete pipeline with explicit terminal sink conversions. -/
def executeRowsTo {Rows Roles : ℕ} {Inner : Type*}
    (trace : List (Stage (Fin Roles) (Fin Rows × Inner)))
    (sources sinks : Locations (Fin Roles) (Fin Rows × Inner))
    (σ : Equiv.Perm (Fin Roles))
    (F : Fin (Rows * Roles) → Inner → Bit) : Fin (Rows * Roles) → Inner → Bit :=
  Streams.gatherRows (fun i j a =>
    runCodedTo trace sources sinks
      (fun r b => Streams.splitRows F r b.1 b.2) (σ i) (j, a))

theorem executeRowsTo_correct {Rows Roles : ℕ} {Inner : Type*}
    (trace : List (Stage (Fin Roles) (Fin Rows × Inner)))
    (sources sinks : Locations (Fin Roles) (Fin Rows × Inner))
    (σ : Equiv.Perm (Fin Roles))
    (hprogram : ∀ s : Fin Roles → Bit,
      runProgram (trace.map Stage.gate) s = fun r => s (σ.symm r))
    (update : Equiv.Perm Inner)
    (hendpoints : ∀ i, (sources i).symm.trans (sinks (σ i)) =
      Equiv.prodCongr (Equiv.refl (Fin Rows)) update)
    (F : Fin (Rows * Roles) → Inner → Bit) :
    executeRowsTo trace sources sinks σ F = Streams.insideRows update F := by
  unfold executeRowsTo
  calc
    _ = Streams.gatherRows (fun i j a => Streams.splitRows F i j (update.symm a)) := by
      apply congrArg Streams.gatherRows
      funext i j a
      rw [all_sink_streams_update trace sources sinks σ hprogram
        (Equiv.prodCongr (Equiv.refl (Fin Rows)) update) hendpoints]
      rfl
    _ = _ := Streams.gather_processed_rows update F

/-- Three-step full exchange, with the middle step executed by the finite
coded gate sequence, not replaced by an assumed address permutation. -/
def exchangeViaProgram {Rows Roles : ℕ}
    (trace : List (Stage (Fin Roles)
      (Fin Rows × FullAddress Prefix H Gap Suffix)))
    (locations : Locations (Fin Roles) (Fin Rows × FullAddress Prefix H Gap Suffix))
    (σ : Equiv.Perm (Fin Roles))
    (F : Fin (Rows * Roles) → FullAddress Prefix H Gap Suffix → Bit) :
    Fin (Rows * Roles) → FullAddress Prefix H Gap Suffix → Bit :=
  Streams.insideRows (mapPairEquiv lowerReflectEquiv)
    (executeRows trace locations σ
      (Streams.insideRows (mapPairEquiv lowerSubtractEquiv) F))

/-- All spectators, every payload bit, and the original complete-row order
are accounted for.  The two explicit hypotheses are logical correctness
of the supplied finite XOR program and its endpoint address labels. -/
theorem exchangeViaProgram_correct {Rows Roles : ℕ}
    (trace : List (Stage (Fin Roles)
      (Fin Rows × FullAddress Prefix H Gap Suffix)))
    (locations : Locations (Fin Roles) (Fin Rows × FullAddress Prefix H Gap Suffix))
    (σ : Equiv.Perm (Fin Roles))
    (hprogram : ∀ s : Fin Roles → Bit,
      runProgram (trace.map Stage.gate) s = fun r => s (σ.symm r))
    (hendpoints : ∀ i, (locations i).symm.trans
      (finalLocations trace locations (σ i)) =
        Equiv.prodCongr (Equiv.refl (Fin Rows))
          (mapPairEquiv (shear (id : H → H))))
    (F : Fin (Rows * Roles) → FullAddress Prefix H Gap Suffix → Bit) :
    exchangeViaProgram trace locations σ F = Streams.insideRows exchangeEquiv F := by
  unfold exchangeViaProgram
  rw [executeRows_correct trace locations σ hprogram _ hendpoints]
  rw [insideRows_comp, insideRows_comp, full_three_step_exchange]

def exchangeViaProgramTo {Rows Roles : ℕ}
    (trace : List (Stage (Fin Roles)
      (Fin Rows × FullAddress Prefix H Gap Suffix)))
    (sources sinks : Locations (Fin Roles) (Fin Rows × FullAddress Prefix H Gap Suffix))
    (σ : Equiv.Perm (Fin Roles))
    (F : Fin (Rows * Roles) → FullAddress Prefix H Gap Suffix → Bit) :
    Fin (Rows * Roles) → FullAddress Prefix H Gap Suffix → Bit :=
  Streams.insideRows (mapPairEquiv lowerReflectEquiv)
    (executeRowsTo trace sources sinks σ
      (Streams.insideRows (mapPairEquiv lowerSubtractEquiv) F))

/-- Complete functional exchange with source and sink edges included. -/
theorem exchangeViaProgramTo_correct {Rows Roles : ℕ}
    (trace : List (Stage (Fin Roles)
      (Fin Rows × FullAddress Prefix H Gap Suffix)))
    (sources sinks : Locations (Fin Roles) (Fin Rows × FullAddress Prefix H Gap Suffix))
    (σ : Equiv.Perm (Fin Roles))
    (hprogram : ∀ s : Fin Roles → Bit,
      runProgram (trace.map Stage.gate) s = fun r => s (σ.symm r))
    (hendpoints : ∀ i, (sources i).symm.trans (sinks (σ i)) =
      Equiv.prodCongr (Equiv.refl (Fin Rows))
        (mapPairEquiv (shear (id : H → H))))
    (F : Fin (Rows * Roles) → FullAddress Prefix H Gap Suffix → Bit) :
    exchangeViaProgramTo trace sources sinks σ F =
      Streams.insideRows exchangeEquiv F := by
  unfold exchangeViaProgramTo
  rw [executeRowsTo_correct trace sources sinks σ hprogram _ hendpoints]
  rw [insideRows_comp, insideRows_comp, full_three_step_exchange]

end CompleteExchange

section EnumeratedRoles

/-- The literal circuit may use structured register names rather than
`Fin Roles`. Enumeration is used only for splitting/gathering disk rows;
the actual XOR gate program retains its original register names. -/
def executeFiniteRowsTo {Rows Roles : ℕ} {Inner : Type*}
    (enumeration : Reg ≃ Fin Roles)
    (trace : List (Stage Reg (Fin Rows × Inner)))
    (sources sinks : Locations Reg (Fin Rows × Inner)) (σ : Equiv.Perm Reg)
    (F : Fin (Rows * Roles) → Inner → Bit) : Fin (Rows * Roles) → Inner → Bit :=
  Streams.gatherRows (fun i j a =>
    runCodedTo trace sources sinks
      (fun r b => Streams.splitRows F (enumeration r) b.1 b.2)
      (σ (enumeration.symm i)) (j, a))

theorem executeFiniteRowsTo_correct {Rows Roles : ℕ} {Inner : Type*}
    (enumeration : Reg ≃ Fin Roles)
    (trace : List (Stage Reg (Fin Rows × Inner)))
    (sources sinks : Locations Reg (Fin Rows × Inner)) (σ : Equiv.Perm Reg)
    (hprogram : ∀ s : Reg → Bit,
      runProgram (trace.map Stage.gate) s = fun r => s (σ.symm r))
    (update : Equiv.Perm Inner)
    (hendpoints : ∀ i, (sources i).symm.trans (sinks (σ i)) =
      Equiv.prodCongr (Equiv.refl (Fin Rows)) update)
    (F : Fin (Rows * Roles) → Inner → Bit) :
    executeFiniteRowsTo enumeration trace sources sinks σ F =
      Streams.insideRows update F := by
  unfold executeFiniteRowsTo
  calc
    _ = Streams.gatherRows (fun i j a => Streams.splitRows F i j (update.symm a)) := by
      apply congrArg Streams.gatherRows
      funext i j a
      rw [all_sink_streams_update trace sources sinks σ hprogram
        (Equiv.prodCongr (Equiv.refl (Fin Rows)) update) hendpoints]
      simp only [transport, Equiv.prodCongr_symm, Equiv.refl_symm,
        Equiv.prodCongr_apply, Equiv.refl_apply, Equiv.apply_symm_apply]
      rfl
    _ = _ := Streams.gather_processed_rows update F

variable {H Prefix Gap Suffix : Type*} [AddCommGroup H]

def exchangeViaFiniteProgramTo {Rows Roles : ℕ}
    (enumeration : Reg ≃ Fin Roles)
    (trace : List (Stage Reg (Fin Rows × FullAddress Prefix H Gap Suffix)))
    (sources sinks : Locations Reg (Fin Rows × FullAddress Prefix H Gap Suffix))
    (σ : Equiv.Perm Reg)
    (F : Fin (Rows * Roles) → FullAddress Prefix H Gap Suffix → Bit) :
    Fin (Rows * Roles) → FullAddress Prefix H Gap Suffix → Bit :=
  Streams.insideRows (mapPairEquiv lowerReflectEquiv)
    (executeFiniteRowsTo enumeration trace sources sinks σ
      (Streams.insideRows (mapPairEquiv lowerSubtractEquiv) F))

theorem exchangeViaFiniteProgramTo_correct {Rows Roles : ℕ}
    (enumeration : Reg ≃ Fin Roles)
    (trace : List (Stage Reg (Fin Rows × FullAddress Prefix H Gap Suffix)))
    (sources sinks : Locations Reg (Fin Rows × FullAddress Prefix H Gap Suffix))
    (σ : Equiv.Perm Reg)
    (hprogram : ∀ s : Reg → Bit,
      runProgram (trace.map Stage.gate) s = fun r => s (σ.symm r))
    (hendpoints : ∀ i, (sources i).symm.trans (sinks (σ i)) =
      Equiv.prodCongr (Equiv.refl (Fin Rows))
        (mapPairEquiv (shear (id : H → H))))
    (F : Fin (Rows * Roles) → FullAddress Prefix H Gap Suffix → Bit) :
    exchangeViaFiniteProgramTo enumeration trace sources sinks σ F =
      Streams.insideRows exchangeEquiv F := by
  unfold exchangeViaFiniteProgramTo
  rw [executeFiniteRowsTo_correct enumeration trace sources sinks σ hprogram _ hendpoints]
  rw [insideRows_comp, insideRows_comp, full_three_step_exchange]

end EnumeratedRoles

section MatrixLocations

variable {R I Prefix Gap Suffix : Type*} [Ring R] [Fintype I] [DecidableEq I]

def matrixLocation (M : Matrix I I R) :
    Equiv.Perm (FullAddress Prefix (I → R) Gap Suffix) :=
  mapPairEquiv (shear M.mulVec)

/-- The address conversion used by the interpreter is exactly the shear
of the edge's target-minus-source matrix difference. -/
theorem matrixLocation_transition (Ms Mt : Matrix I I R) :
    (matrixLocation (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) Ms).symm.trans
      (matrixLocation Mt) = matrixLocation (Mt - Ms) := by
  apply Equiv.ext
  intro a
  cases a with
  | mk p h g d z =>
    change FullAddress.mk p (h - Ms.mulVec d + Mt.mulVec d) g d z =
      FullAddress.mk p (h + (Mt - Ms).mulVec d) g d z
    rw [Matrix.sub_mulVec]
    apply congrArg (fun x => FullAddress.mk p x g d z)
    abel

theorem matrixLocation_one :
    (matrixLocation (1 : Matrix I I R) :
      Equiv.Perm (FullAddress Prefix (I → R) Gap Suffix)) =
      mapPairEquiv (shear (id : (I → R) → (I → R))) := by
  have h : (1 : Matrix I I R).mulVec = (id : (I → R) → (I → R)) := by
    funext x
    exact Matrix.one_mulVec x
  unfold matrixLocation
  rw [h]

def rowMatrixLocation {Rows : ℕ} (M : Matrix I I R) :
    Equiv.Perm (Fin Rows × FullAddress Prefix (I → R) Gap Suffix) :=
  Equiv.prodCongr (Equiv.refl (Fin Rows)) (matrixLocation M)

theorem rowMatrixLocation_transition {Rows : ℕ} (Ms Mt : Matrix I I R) :
    (rowMatrixLocation (Rows := Rows) (Prefix := Prefix) (Gap := Gap)
      (Suffix := Suffix) Ms).symm.trans (rowMatrixLocation Mt) =
      rowMatrixLocation (Mt - Ms) := by
  apply Equiv.ext
  intro a
  apply Prod.ext
  · rfl
  · exact congrArg (fun e => e a.2) (matrixLocation_transition Ms Mt)

/-- Every gate gets its specified matrix label. The gate list itself is
unchanged, as proved below; no correct-circuit oracle replaces its execution. -/
def matrixStages {Rows : ℕ} (program : List (XorGate Reg))
    (frames : ℕ → Matrix I I R) :
    List (Stage Reg (Fin Rows × FullAddress Prefix (I → R) Gap Suffix)) :=
  program.zipIdx.map (fun pair => ⟨pair.1, rowMatrixLocation (frames pair.2)⟩)

theorem matrixStages_gates {Rows : ℕ} (program : List (XorGate Reg))
    (frames : ℕ → Matrix I I R) :
    (matrixStages (Rows := Rows) (Prefix := Prefix) (Gap := Gap)
      (Suffix := Suffix) program frames).map Stage.gate = program := by
  simp only [matrixStages, List.map_map]
  change program.zipIdx.map Prod.fst = program
  exact List.zipIdx_map_fst 0 program

/-- Finite-role version of the complete exchange, with the abstract endpoint
layout condition discharged by the concrete matrix equation `Mt-Ms=I`. -/
theorem matrixProgram_exchange_correct {Rows Roles : ℕ}
    (program : List (XorGate (Fin Roles))) (frames : ℕ → Matrix I I R)
    (Ms Mt : Fin Roles → Matrix I I R) (σ : Equiv.Perm (Fin Roles))
    (hprogram : ∀ s : Fin Roles → Bit, runProgram program s = fun r => s (σ.symm r))
    (hendpoints : ∀ i, Mt (σ i) - Ms i = 1)
    (F : Fin (Rows * Roles) → FullAddress Prefix (I → R) Gap Suffix → Bit) :
    exchangeViaProgramTo (matrixStages program frames)
      (fun i => rowMatrixLocation (Ms i)) (fun i => rowMatrixLocation (Mt i)) σ F =
      Streams.insideRows exchangeEquiv F := by
  apply exchangeViaProgramTo_correct
  · intro s
    simpa only [matrixStages_gates] using hprogram s
  · intro i
    rw [rowMatrixLocation_transition, hendpoints]
    unfold rowMatrixLocation
    rw [matrixLocation_one]

theorem matrixFiniteProgram_exchange_correct {Rows Roles : ℕ}
    (enumeration : Reg ≃ Fin Roles)
    (program : List (XorGate Reg)) (frames : ℕ → Matrix I I R)
    (Ms Mt : Reg → Matrix I I R) (σ : Equiv.Perm Reg)
    (hprogram : ∀ s : Reg → Bit, runProgram program s = fun r => s (σ.symm r))
    (hendpoints : ∀ i, Mt (σ i) - Ms i = 1)
    (F : Fin (Rows * Roles) → FullAddress Prefix (I → R) Gap Suffix → Bit) :
    exchangeViaFiniteProgramTo enumeration (matrixStages program frames)
      (fun i => rowMatrixLocation (Ms i)) (fun i => rowMatrixLocation (Mt i)) σ F =
      Streams.insideRows exchangeEquiv F := by
  apply exchangeViaFiniteProgramTo_correct
  · intro s
    simpa only [matrixStages_gates] using hprogram s
  · intro i
    rw [rowMatrixLocation_transition, hendpoints]
    unfold rowMatrixLocation
    rw [matrixLocation_one]

variable {d : ℕ}

/-- Source matrices from the manuscript, for every data and auxiliary stream. -/
def paperSourceMatrix (P : DataIndex d → Matrix I I R) : GlobalReg d → Matrix I I R
  | .inl (.inl a) => -P a
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- Sink matrices; crossed X/Y demand pairs are represented by globalSwap. -/
def paperSinkMatrix (P : DataIndex d → Matrix I I R) : GlobalReg d → Matrix I I R
  | .inl (.inl _) => 1
  | .inl (.inr a) => 1 - P a
  | .inr _ => 1

theorem paper_endpoint_difference (P : DataIndex d → Matrix I I R)
    (r : GlobalReg d) :
    paperSinkMatrix P (globalSwap r) - paperSourceMatrix P r = 1 := by
  rcases r with (a | a) | aux
  · change (1 - P a) - (-P a) = 1
    abel
  · change (1 : Matrix I I R) - 0 = 1
    simp
  · change (1 : Matrix I I R) - 0 = 1
    simp

/-- The manuscript's actual three-round register program, with all its
gates, independently initialized auxiliary registers and real port sets. -/
noncomputable def actualThreeRoundExchange {Rows Roles : ℕ}
    (enumeration : GlobalReg d ≃ Fin Roles)
    (P : DataIndex d → Matrix I I R) (frames : ℕ → Matrix I I R)
    (F : Fin (Rows * Roles) → FullAddress Prefix (I → R) Gap Suffix → Bit) :
    Fin (Rows * Roles) → FullAddress Prefix (I → R) Gap Suffix → Bit :=
  exchangeViaFiniteProgramTo enumeration (matrixStages (globalProgram d) frames)
    (fun r => rowMatrixLocation (paperSourceMatrix P r))
    (fun r => rowMatrixLocation (paperSinkMatrix P r)) globalSwap F

/-- End-to-end functional correctness of the actual three-round coded
exchange. No hypothetical program correctness or endpoint condition remains.
The projection matrices and gate frames may be arbitrary here: their special
choice is required for the I/O/rank bound, not for this correctness identity. -/
theorem actualThreeRoundExchange_correct {Rows Roles : ℕ}
    (enumeration : GlobalReg d ≃ Fin Roles)
    (P : DataIndex d → Matrix I I R) (frames : ℕ → Matrix I I R)
    (F : Fin (Rows * Roles) → FullAddress Prefix (I → R) Gap Suffix → Bit) :
    actualThreeRoundExchange enumeration P frames F =
      Streams.insideRows exchangeEquiv F := by
  unfold actualThreeRoundExchange
  apply matrixFiniteProgram_exchange_correct
  · intro s
    change runProgram (globalProgram d) s = fun r => s (globalSwap r)
    exact globalProgram_correct s
  · exact paper_endpoint_difference P

end MatrixLocations

end CSL.CodedSimulation


