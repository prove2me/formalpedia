-- Prove2me | Definitions.Def_CSL_NetworkCoding_FiniteCodes_BinaryLinearPipeline
-- name    : CSL_NetworkCoding_FiniteCodes_BinaryLinearPipeline
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:11:42.724206+00:00
-- url     : https://prove2.me/theorems/441c17ae-0c69-4112-be25-e8004d90f5e1
-- title:
--   Coded sorting library: NetworkCoding / FiniteCodes / BinaryLinearPipeline
-- statement:
--   Module `CodedSorting.NetworkCoding.FiniteCodes.BinaryLinearPipeline` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Checkable binary linearity of the actual finite stateful pipeline
--
--   `BinaryLinearBlock` is a property of the operational `BlockCode` itself.
--   After identifying booleans with GF(2), every local initial-state map, emitted
--   bit, state update and decoded vector is represented by a linear map. The
--   protocol's transmission direction depends only on the public clock and edge.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.NetworkCoding.FiniteCodes.BinaryLinearPipeline

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_NetworkCoding_Model_PipelineBlockCode

/-!
# Checkable binary linearity of the actual finite stateful pipeline

`BinaryLinearBlock` is a property of the operational `BlockCode` itself.
After identifying booleans with GF(2), every local initial-state map, emitted
bit, state update and decoded vector is represented by a linear map. The
protocol's transmission direction depends only on the public clock and edge.
-/

set_option autoImplicit false

namespace CSL.Construction.BinaryLinearPipeline

open CSL.Circuit CSL.NetworkProtocol

def bitOfBool : Bool → Bit | false => 0 | true => 1
def boolOfBit (x : Bit) : Bool := decide (x ≠ 0)

@[simp] theorem bitOfBool_boolOfBit : ∀ x : Bit, bitOfBool (boolOfBit x) = x := by decide
@[simp] theorem boolOfBit_bitOfBool : ∀ b : Bool, boolOfBit (bitOfBool b) = b := by decide

variable {Node Edge Session : Type}
variable (net : RankedNetwork Node Edge) (source sink : Session → Node)

/-- A linearity certificate for this specific operational block-code object. -/
structure BinaryLinearBlock {k T : ℕ} (block : NetworkRates.BlockCode net source sink k T)
    [AddCommMonoid block.State] [Module Bit block.State] : Prop where
  emission : ∀ t v e, ∃ f : block.State →ₗ[Bit] Bit,
    ∀ s, bitOfBool (block.protocol.emit t v s e) = f s
  transition : ∀ t v, ∃ f : (block.State × (Edge → Bit)) →ₗ[Bit] block.State,
    ∀ s received, block.protocol.update t v s (fun e => boolOfBit (received e)) = f (s, received)
  initialization : ∀ v, ∃ f : ({i : Session // source i = v} → Fin k → Bit) →ₗ[Bit] block.State,
    ∀ input, block.initial v (fun i b => boolOfBit (input i b)) = f input
  decoding : ∀ i, ∃ f : block.State →ₗ[Bit] (Fin k → Bit),
    ∀ s b, bitOfBool (block.decode i s b) = f s b

variable (code : LinearCode net Session) (k : ℕ)

abbrev State := PipelineBlockCode.LocalState (Edge := Edge) (Session := Session) k

abbrev Input (v : Node) :=
  {i : Session // code.source i = v} ⊕ {e : Edge // net.head e = v}

noncomputable section

def inputMap (v : Node) (b : Fin k) : State (Edge := Edge) (Session := Session) k →ₗ[Bit]
    (Input net code v → Bit) where
  toFun state port := match port with
    | .inl i => state.1 i.val b
    | .inr e => state.2 e.val b
  map_add' x y := by funext p; cases p <;> rfl
  map_smul' a x := by funext p; cases p <;> rfl

def emissionMap (t : ℕ) (v : Node) (e : Edge) :
    State (Edge := Edge) (Session := Session) k →ₗ[Bit] Bit := by
  classical
  exact if he : net.tail e = v then
    if hb : net.rank v ≤ t ∧ t - net.rank v < k then
      (LinearMap.proj ⟨e, he⟩).comp ((code.localMap v).comp
        (inputMap net code k v ⟨t - net.rank v, hb.2⟩))
    else 0
  else 0

theorem emissionMap_correct (t : ℕ) (v : Node) (e : Edge)
    (state : State (Edge := Edge) (Session := Session) k) :
    bitOfBool ((PipelineBlockCode.protocol net code k).emit t v state e) =
      emissionMap net code k t v e state := by
  classical
  simp only [PipelineBlockCode.protocol]
  unfold emissionMap
  split_ifs
  · change bitOfBool (boolOfBit _) = _
    rw [bitOfBool_boolOfBit]
    rfl
  all_goals rfl

def transitionMap (t : ℕ) (v : Node) :
    (State (Edge := Edge) (Session := Session) k × (Edge → Bit)) →ₗ[Bit]
      State (Edge := Edge) (Session := Session) k := by
  classical
  exact {
    toFun p := (p.1.1, fun e b =>
      if net.head e = v ∧ t = sendTime net b e then p.2 e else p.1.2 e b)
    map_add' x y := by
      apply Prod.ext
      · rfl
      · funext e b
        by_cases h : net.head e = v ∧ t = sendTime net b e <;> simp [h]
    map_smul' a x := by
      apply Prod.ext
      · rfl
      · funext e b
        by_cases h : net.head e = v ∧ t = sendTime net b e <;> simp [h]
  }

theorem transitionMap_correct (t : ℕ) (v : Node)
    (state : State (Edge := Edge) (Session := Session) k) (received : Edge → Bit) :
    (PipelineBlockCode.protocol net code k).update t v state
      (fun e => boolOfBit (received e)) = transitionMap net k t v (state, received) := by
  classical
  apply Prod.ext
  · rfl
  · funext e b
    by_cases h : net.head e = v ∧ t = sendTime net b e
    · change (if net.head e = v ∧ t = sendTime net b e then
        bitOfBool (boolOfBit (received e)) else state.2 e b) = _
      simp [transitionMap, h]
    · change (if net.head e = v ∧ t = sendTime net b e then
        bitOfBool (boolOfBit (received e)) else state.2 e b) = _
      simp [transitionMap, h]

def initializationMap (v : Node) :
    ({i : Session // code.source i = v} → Fin k → Bit) →ₗ[Bit]
      State (Edge := Edge) (Session := Session) k := by
  classical
  exact {
    toFun input := (fun i b => if h : code.source i = v then input ⟨i,h⟩ b else 0,
      fun _ _ => 0)
    map_add' x y := by
      apply Prod.ext
      · funext i b
        by_cases h : code.source i = v <;> simp [h]
      · rfl
    map_smul' a x := by
      apply Prod.ext
      · funext i b
        by_cases h : code.source i = v <;> simp [h]
      · funext e b; simp
  }

theorem initializationMap_correct (v : Node)
    (input : {i : Session // code.source i = v} → Fin k → Bit) :
    PipelineBlockCode.localInitial net code k v (fun i b => boolOfBit (input i b)) =
      initializationMap net code k v input := by
  classical
  apply Prod.ext
  · funext i b
    by_cases h : code.source i = v
    · change (if h : code.source i = v then bitOfBool (boolOfBit (input ⟨i,h⟩ b)) else 0) = _
      simp [initializationMap, h]
    · change (if h : code.source i = v then bitOfBool (boolOfBit (input ⟨i,h⟩ b)) else 0) = _
      simp [initializationMap, h]
  · rfl

def mailboxMap (i : Session) (b : Fin k) :
    State (Edge := Edge) (Session := Session) k →ₗ[Bit]
      ({e : Edge // net.head e = code.sink i} → Bit) where
  toFun state e := state.2 e.val b
  map_add' x y := rfl
  map_smul' a x := rfl

def decodingMap (i : Session) : State (Edge := Edge) (Session := Session) k →ₗ[Bit]
    (Fin k → Bit) :=
  LinearMap.pi (fun b => (code.decoder i).comp (mailboxMap net code k i b))

theorem decodingMap_correct (i : Session)
    (state : State (Edge := Edge) (Session := Session) k) (b : Fin k) :
    bitOfBool (PipelineBlockCode.localDecode net code k i state b) =
      decodingMap net code k i state b := by
  change bitOfBool (boolOfBit _) = _
  rw [bitOfBool_boolOfBit]
  rfl

/-- The protocol's actual state, not a replacement state, has its natural
pointwise GF(2)-module structure. -/
instance blockStateAddCommMonoid {D : ℕ} (hcorrect : Correct net code)
    (hdepth : ∀ e, net.rank (net.tail e) ≤ D) :
    AddCommMonoid (PipelineBlockCode.blockCode net code k hcorrect hdepth).State :=
  inferInstanceAs (AddCommMonoid (State (Edge := Edge) (Session := Session) k))

instance blockStateModule {D : ℕ} (hcorrect : Correct net code)
    (hdepth : ∀ e, net.rank (net.tail e) ≤ D) :
    Module Bit (PipelineBlockCode.blockCode net code k hcorrect hdepth).State :=
  inferInstanceAs (Module Bit (State (Edge := Edge) (Session := Session) k))

/-- The actual schedule always uses the fixed forward orientation, independently
of all source messages and stored states. -/
theorem pipeline_direction (t : ℕ) (e : Edge) :
    (PipelineBlockCode.protocol net code k).forward t e = true := rfl

/-- Every operational function of the actual finite pipeline is GF(2)-linear. -/
theorem binaryLinear_blockCode {D : ℕ} (hcorrect : Correct net code)
    (hdepth : ∀ e, net.rank (net.tail e) ≤ D) :
    BinaryLinearBlock net code.source code.sink
      (PipelineBlockCode.blockCode net code k hcorrect hdepth) := by
  constructor
  · intro t v e
    exact ⟨emissionMap net code k t v e, emissionMap_correct net code k t v e⟩
  · intro t v
    exact ⟨transitionMap net k t v, transitionMap_correct net code k t v⟩
  · intro v
    exact ⟨initializationMap net code k v, initializationMap_correct net code k v⟩
  · intro i
    exact ⟨decodingMap net code k i, decodingMap_correct net code k i⟩

end

#print axioms binaryLinear_blockCode
#print axioms pipeline_direction

end CSL.Construction.BinaryLinearPipeline


