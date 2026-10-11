-- Prove2me | Definitions.Def_Algo2Lean
-- name    : Algo2Lean
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:38:56.408974+00:00
-- url     : https://prove2.me/theorems/1af2fec6-c4db-4522-a2d9-327ad2c971ef
-- title:
--   Algo2Lean execution, mutable heap and transcript definitions
-- statement:
--   The common runtime semantics includes mathematical integer-indexed sequences, mutable objects and typed collections, allocation counters, and named natural-number clocks. A configuration carries a current frame, suspended caller frames, heap and return state. `Reaches` describes finite sequences of small steps; transcript validity checks the corresponding finite observations.
--
--   Generated source functions expose `Call`, `Run`, `Returns` and cost views over this shared semantics. A reusable call preserves its arbitrary suspended caller context while permitting the heap effects specified by its contract. Named ticks are explicit source events; generated transitions do not automatically count as runtime ticks.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2Lean.lean

import Std

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

-- Copyright 2026 Lunjia Hu and contributors.
-- SPDX-License-Identifier: Apache-2.0

/-

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/

namespace Algo2LeanCore

universe u v w

/-- A suspended caller remembers its local frame and where to put the result. -/
abbrev Stack (Frame : Type v) (Result : Type w) := List (Result → Frame)

/-- Heap snapshots preserve object identities and historical contents. -/
inductive Config (Heap : Type u) (Frame : Type v) (Result : Type w) where
  | active (heap : Heap) (frame : Frame) (stack : Stack Frame Result)
  | done (heap : Heap) (result : Result)

variable {Heap : Type u} {Frame : Type v} {Result : Type w}

def Config.heap : Config Heap Frame Result → Heap
  | .active heap _ _ => heap
  | .done heap _ => heap

/-- The suspended callers; completed top-level executions have no callers. -/
def Config.stack : Config Heap Frame Result → Stack Frame Result
  | .active _ _ stack => stack
  | .done _ _ => []

def start (heap : Heap) (frame : Frame) : Config Heap Frame Result :=
  .active heap frame []

def resumeConfig (heap : Heap) (result : Result) (stack : Stack Frame Result) :
    Config Heap Frame Result :=
  match stack with
  | [] => .done heap result
  | resume :: rest => .active heap (resume result) rest

/-- Every state has at most one successor under the supplied transition relation. -/
def Deterministic {State : Type u} (step : State → State → Prop) : Prop :=
  ∀ {a b c}, step a b → step a c → b = c

/-- A terminal configuration has no next transition. -/
def Terminal {State : Type u} (step : State → State → Prop) (state : State) : Prop :=
  ∀ next, ¬ step state next

/-- A finite transcript includes its initial and final states, and may stop at
    any state. In particular, validity does not require a completed call. -/
inductive Valid {State : Type u} (step : State → State → Prop) :
    State → List State → State → Prop where
  | single (state) : Valid step state [state] state
  | cons : step before after → Valid step after rest final →
      Valid step before (before :: rest) final

namespace Valid

variable {State : Type u} {step nextProperty : State → State → Prop}

theorem nonempty (h : Valid step initial states final) : states ≠ [] := by
  cases h <;> simp

/-- Endpoint properties can be read from any theorem about transcript members. -/
theorem final_mem (valid : Valid step initial states final) : final ∈ states := by
  induction valid with
  | single => simp
  | cons _ _ ih => exact List.mem_cons_of_mem _ ih

/-- Every local transition property lifts to an arbitrary valid transcript. -/
theorem lift (h : Valid step initial states final)
    (localProperty : ∀ a b, step a b → nextProperty a b) :
    Valid nextProperty initial states final := by
  induction h with
  | single => exact .single _
  | cons transition _ ih => exact .cons (localProperty _ _ transition) ih

/-- Reuse a local preservation theorem without constructing a transcript. -/
theorem invariant (h : Valid step initial states final) (property : State → Prop)
    (atStart : property initial)
    (preserve : ∀ a b, step a b → property a → property b) : property final := by
  induction h with
  | single => exact atStart
  | cons transition _ ih => exact ih (preserve _ _ transition atStart)

theorem all_states (h : Valid step initial states final) (property : State → Prop)
    (atStart : property initial)
    (preserve : ∀ a b, step a b → property a → property b) :
    ∀ state ∈ states, property state := by
  induction h with
  | single => simpa using atStart
  | cons transition _ ih =>
    intro state member
    rcases List.mem_cons.mp member with same | later
    · simpa [same] using atStart
    · exact ih (preserve _ _ transition atStart) state later

/-- Concatenation keeps the shared endpoint once. -/
theorem append (first : Valid step a xs b) (second : Valid step b ys c) :
    Valid step a (xs.dropLast ++ ys) c := by
  induction first with
  | single => simpa using second
  | @cons before after rest final transition tail ih =>
    have split : (before :: rest).dropLast = before :: rest.dropLast := by
      cases rest with
      | nil => exact (tail.nonempty rfl).elim
      | cons head rest => simp
    simpa [split] using Valid.cons transition (ih second)

/-- Deterministic completed runs agree, regardless of their transcript witnesses. -/
theorem eq_of_terminal (deterministic : Deterministic step)
    (first : Valid step a xs b) (second : Valid step a ys c)
    (atFirst : Terminal step b) (atSecond : Terminal step c) : b = c := by
  induction first generalizing ys c with
  | single =>
    cases second with
    | single => rfl
    | cons transition => exact False.elim (atFirst _ transition)
  | cons transition _ inductionHypothesis =>
    cases second with
    | single => exact False.elim (atSecond _ transition)
    | cons other tail =>
      cases deterministic transition other
      exact inductionHypothesis tail atFirst atSecond

end Valid

/-- Reachability is a view of explicit transcript validity, not another
    execution relation. The existential witness need not be computed in proofs. -/
def Reaches {State : Type u} (step : State → State → Prop) (a b : State) : Prop :=
  ∃ transcript, Valid step a transcript b

namespace Reaches

variable {State : Type u} {step : State → State → Prop}

theorem refl (state : State) : Reaches step state state := ⟨[state], .single _⟩

theorem single (transition : step a b) : Reaches step a b :=
  ⟨[a, b], .cons transition (.single _)⟩

theorem trans (first : Reaches step a b) (second : Reaches step b c) : Reaches step a c := by
  obtain ⟨xs, first⟩ := first
  obtain ⟨ys, second⟩ := second
  exact ⟨xs.dropLast ++ ys, first.append second⟩

/-- Extend an execution segment by one local transition at its beginning. -/
theorem prepend (transition : step a b) (rest : Reaches step b c) : Reaches step a c :=
  (single transition).trans rest

/-- Turn a constructed result into a theorem about every completed execution. -/
theorem eq_of_terminal (deterministic : Deterministic step)
    (first : Reaches step a b) (second : Reaches step a c)
    (atFirst : Terminal step b) (atSecond : Terminal step c) : b = c := by
  obtain ⟨_, first⟩ := first
  obtain ⟨_, second⟩ := second
  exact Valid.eq_of_terminal (step := step) deterministic first second atFirst atSecond

theorem invariant (run : Reaches step a b) (property : State → Prop)
    (atStart : property a)
    (preserve : ∀ before after, step before after → property before → property after) : property b := by
  obtain ⟨_, transcript⟩ := run
  exact transcript.invariant property atStart preserve

end Reaches

/-- A function summary can be reused under any suspended caller stack. -/
def Summary (step : Config Heap Frame Result → Config Heap Frame Result → Prop)
    (heap : Heap) (frame : Frame) (heap' : Heap) (result : Result) : Prop :=
  ∀ stack, Reaches step (.active heap frame stack) (resumeConfig heap' result stack)

theorem Summary.root (summary : Summary step heap frame heap' result) :
    Reaches step (start heap frame) (.done heap' result) := by
  simpa [start, resumeConfig] using summary []

end Algo2LeanCore

/- Integer sequences are mathematical objects, addressed by stable identities. -/
namespace Algo2LeanGenerated

abbrev Seq := Int → Int
abbrev SeqRef := Nat
abbrev ObjectRef := Nat
/-- One identity space for typed collections; additional collection kinds can share it. -/
abbrev CollectionRef := Nat
/-- Independent named counters for user-selected algorithmic operations. -/
abbrev Clocks := String → Nat

/-- A cost specification that charges just one named counter. -/
def Clocks.single (name : String) (amount : Nat) : Clocks :=
  fun clock => if clock = name then amount else 0

/-- Combine cost specifications pointwise, including overlapping counters. -/
def Clocks.add (first second : Clocks) : Clocks :=
  fun clock => first clock + second clock

/-- Stored field values. A missing field is distinct from an initialized `None`. -/
inductive ObjectValue where
  | intValue (value : Int)
  | boolValue (value : Bool)
  | seqValue (value : SeqRef)
  | collectionValue (value : CollectionRef)
  | objectValue (value : ObjectRef)
  | noneValue
  deriving DecidableEq

def ObjectValue.asInt : ObjectValue → Option Int
  | .intValue value => some value
  | _ => none

def ObjectValue.asBool : ObjectValue → Option Bool
  | .boolValue value => some value
  | _ => none

def ObjectValue.asSeq : ObjectValue → Option SeqRef
  | .seqValue value => some value
  | _ => none

def ObjectValue.asCollection : ObjectValue → Option CollectionRef
  | .collectionValue value => some value
  | _ => none

def ObjectValue.asObject : ObjectValue → Option ObjectRef
  | .objectValue value => some value
  | _ => none

def ObjectValue.asNone : ObjectValue → Option Unit
  | .noneValue => some ()
  | _ => none

def ObjectValue.asNullableObject : ObjectValue → Option (Option ObjectRef)
  | .objectValue value => some (some value)
  | .noneValue => some none
  | _ => none

structure Object where
  className : String
  fields : String → Option ObjectValue := fun _ => none

/-- Collection payloads keep identities separate from their contents. The element
    type is a source type tag, checked before reading a typed sequence. -/
inductive Collection where
  | sequence (elementType : String) (values : Int → ObjectValue)

structure Heap where
  nextRef : Nat := 0
  store : SeqRef → Seq := fun _ _ => 0
  nextObject : Nat := 0
  objects : ObjectRef → Option Object := fun _ => none
  clocks : Clocks := fun _ => 0
  nextCollection : Nat := 0
  collections : CollectionRef → Option Collection := fun _ => none

/-- Observe a counter locally, without assuming reachability or a transcript. -/
def clock {Frame Result : Type} (state : Algo2LeanCore.Config Heap Frame Result)
    (name : String) : Nat := state.heap.clocks name

/-- One source `tick` increases exactly one shared counter by a natural amount. -/
def Heap.tick (h : Heap) (name : String) (amount : Nat := 1) : Heap :=
  { h with clocks := fun clock => if clock = name then h.clocks clock + amount else h.clocks clock }

/-- Counts accrued between two heap snapshots, including nested calls. -/
def Heap.cost (initial final : Heap) : Clocks :=
  fun clock => final.clocks clock - initial.clocks clock

/-- Describe a segment's aggregate clock effect without changing program data.
    This proof helper does not add a source operation or a transition rule. -/
def Heap.charge (h : Heap) (costs : Clocks) : Heap :=
  { h with clocks := Clocks.add h.clocks costs }

@[simp] theorem Heap.charge_zero (h : Heap) :
    h.charge (fun _ => 0) = h := by
  have unchanged : Clocks.add h.clocks (fun _ => 0) = h.clocks := by
    funext clock
    simp [Clocks.add]
  simp [charge, unchanged]

@[simp] theorem Heap.clocks_charge (h : Heap) (costs : Clocks) (name : String) :
    (h.charge costs).clocks name = h.clocks name + costs name := rfl

/-- Aggregated segment costs compose by pointwise addition. -/
theorem Heap.charge_add (h : Heap) (first second : Clocks) :
    (h.charge first).charge second = h.charge (Clocks.add first second) := by
  simp only [charge]
  congr 1
  funext clock
  simp [Clocks.add, Nat.add_assoc]

theorem Heap.charge_single (h : Heap) (name : String) (amount : Nat) :
    h.charge (Clocks.single name amount) = h.tick name amount := by
  simp only [charge, tick]
  congr 1
  funext clock
  by_cases same : clock = name <;> simp [Clocks.add, Clocks.single, same]

/-- Prepend one concrete tick to an abstract segment cost. -/
theorem Heap.tick_charge (h : Heap) (name : String) (amount : Nat) (costs : Clocks) :
    (h.tick name amount).charge costs =
      h.charge (Clocks.add (Clocks.single name amount) costs) := by
  rw [← charge_single, charge_add]

@[simp] theorem Heap.cost_charge (h : Heap) (costs : Clocks) :
    cost h (h.charge costs) = costs := by
  funext clock
  simp [cost]

@[simp] theorem Heap.clocks_tick_same (h : Heap) (name : String) (amount : Nat := 1) :
    (h.tick name amount).clocks name = h.clocks name + amount := by simp [tick]

@[simp] theorem Heap.clocks_tick_other (h : Heap) (name clock : String)
    (different : clock ≠ name) (amount : Nat := 1) :
    (h.tick name amount).clocks clock = h.clocks clock := by simp [tick, different]

theorem Heap.clocks_le_tick (h : Heap) (name clock : String) (amount : Nat := 1) :
    h.clocks clock ≤ (h.tick name amount).clocks clock := by
  by_cases same : clock = name <;> simp [tick, same]

@[simp] theorem Heap.tick_zero (h : Heap) (name : String) :
    h.tick name 0 = h := by simp [tick]

/-- Combine adjacent increments of one counter. -/
theorem Heap.tick_add (h : Heap) (name : String) (a b : Nat) :
    (h.tick name a).tick name b = h.tick name (a + b) := by
  simp only [tick]
  congr 1
  funext clock
  by_cases same : clock = name <;> simp [same, Nat.add_assoc]

/-- Counter updates commute, so independent call costs can be regrouped. -/
theorem Heap.tick_comm (h : Heap) (first second : String) (a b : Nat) :
    (h.tick first a).tick second b = (h.tick second b).tick first a := by
  simp only [tick]
  congr 1
  funext clock
  by_cases one : clock = first <;> by_cases two : clock = second <;>
    simp_all [Nat.add_right_comm]

@[simp] theorem Heap.tick_store (h : Heap) (name : String) (amount : Nat := 1) :
    (h.tick name amount).store = h.store := rfl

@[simp] theorem Heap.tick_nextRef (h : Heap) (name : String) (amount : Nat := 1) :
    (h.tick name amount).nextRef = h.nextRef := rfl

@[simp] theorem Heap.tick_objects (h : Heap) (name : String) (amount : Nat := 1) :
    (h.tick name amount).objects = h.objects := rfl

@[simp] theorem Heap.tick_nextObject (h : Heap) (name : String) (amount : Nat := 1) :
    (h.tick name amount).nextObject = h.nextObject := rfl

@[simp] theorem Heap.cost_self (h : Heap) (clock : String) :
    cost h h clock = 0 := by simp [cost]

@[simp] theorem Heap.cost_tick_same (h : Heap) (name : String) (amount : Nat := 1) :
    cost h (h.tick name amount) name = amount := by simp [cost]

@[simp] theorem Heap.cost_tick_other (h : Heap) (name clock : String)
    (different : clock ≠ name) (amount : Nat := 1) :
    cost h (h.tick name amount) clock = 0 := by simp [cost, different]

/-- Consecutive execution segments add their costs. The premises rule out
    truncated subtraction between arbitrary, unrelated heap snapshots. -/
theorem Heap.cost_add (initial middle final : Heap) (clock : String)
    (first : initial.clocks clock ≤ middle.clocks clock)
    (second : middle.clocks clock ≤ final.clocks clock) :
    cost initial final clock = cost initial middle clock + cost middle final clock := by
  simp only [cost]
  omega

def Heap.read (h : Heap) (ref : SeqRef) (index : Int) : Int := h.store ref index

@[simp] theorem Heap.read_tick (h : Heap) (name : String) (amount : Nat)
    (ref : SeqRef) (index : Int) :
    (h.tick name amount).read ref index = h.read ref index := rfl

@[simp] theorem Heap.read_charge (h : Heap) (costs : Clocks)
    (ref : SeqRef) (index : Int) :
    (h.charge costs).read ref index = h.read ref index := rfl

@[simp] theorem Heap.charge_nextRef (h : Heap) (costs : Clocks) :
    (h.charge costs).nextRef = h.nextRef := rfl

def Heap.write (h : Heap) (ref : SeqRef) (index value : Int) : Heap :=
  { h with store := fun r i => if r = ref ∧ i = index then value else h.store r i }

def Heap.allocate (h : Heap) (contents : Seq) : Heap :=
  { h with nextRef := h.nextRef + 1, store := fun r => if r = h.nextRef then contents else h.store r }

def Heap.objectClass (h : Heap) (ref : ObjectRef) : Option String :=
  (h.objects ref).map Object.className

def Heap.readField (h : Heap) (ref : ObjectRef) (field : String) : Option ObjectValue :=
  (h.objects ref).bind (fun object => object.fields field)

def Heap.writeField (h : Heap) (ref : ObjectRef) (field : String) (value : ObjectValue) : Heap :=
  { h with objects := fun r => if r = ref then
      (h.objects r).map (fun object =>
        { object with fields := fun name => if name = field then some value else object.fields name })
    else h.objects r }

/-- Allocate an object before its initializer runs. Fields start uninitialized. -/
def Heap.allocateObject (h : Heap) (className : String) : Heap :=
  { h with
    nextObject := h.nextObject + 1
    objects := fun r => if r = h.nextObject then some { className := className } else h.objects r }

@[simp] theorem Heap.objectClass_allocate (h : Heap) (values : Seq) (ref : ObjectRef) :
    (h.allocate values).objectClass ref = h.objectClass ref := rfl

@[simp] theorem Heap.readField_allocate (h : Heap) (values : Seq) (ref : ObjectRef) (field : String) :
    (h.allocate values).readField ref field = h.readField ref field := rfl

def Heap.sequenceType (h : Heap) (ref : CollectionRef) : Option String :=
  (h.collections ref).map fun | .sequence elementType _ => elementType

def Heap.readElement (h : Heap) (ref : CollectionRef) (index : Int) : Option ObjectValue :=
  (h.collections ref).map fun | .sequence _ values => values index

/-- A write preserves the collection's type and every other index. -/
def Heap.writeElement (h : Heap) (ref : CollectionRef) (index : Int)
    (value : ObjectValue) : Heap :=
  { h with collections := fun r => if r = ref then
      (h.collections r).map (fun
        | .sequence elementType values =>
          .sequence elementType (fun i => if i = index then value else values i))
    else h.collections r }

def Heap.allocateSequence (h : Heap) (elementType : String)
    (values : Int → ObjectValue) : Heap :=
  { h with
    nextCollection := h.nextCollection + 1
    collections := fun r => if r = h.nextCollection then
      some (.sequence elementType values) else h.collections r }

/-- Shallow validity permits shared references and cycles. Decoding and using an
    element checks that element, without traversing the whole collection. -/
def Heap.validSequence (h : Heap) (ref : CollectionRef) (elementType : String) : Prop :=
  ref < h.nextCollection ∧ h.sequenceType ref = some elementType

instance (h : Heap) (ref : CollectionRef) (elementType : String) :
    Decidable (h.validSequence ref elementType) :=
  inferInstanceAs (Decidable (ref < h.nextCollection ∧ h.sequenceType ref = some elementType))

/-- Build a typed sequence in a mathematical input heap, returning its identity. -/
def Heap.createSequence (h : Heap) (elementType : String)
    (values : Int → ObjectValue) : Heap × CollectionRef :=
  (h.allocateSequence elementType values, h.nextCollection)

@[simp] theorem Heap.write_clocks (h : Heap) (ref : SeqRef) (index value : Int) :
    (h.write ref index value).clocks = h.clocks := rfl

@[simp] theorem Heap.allocate_clocks (h : Heap) (contents : Seq) :
    (h.allocate contents).clocks = h.clocks := rfl

@[simp] theorem Heap.writeField_clocks (h : Heap) (ref : ObjectRef)
    (field : String) (value : ObjectValue) :
    (h.writeField ref field value).clocks = h.clocks := rfl

@[simp] theorem Heap.allocateObject_clocks (h : Heap) (className : String) :
    (h.allocateObject className).clocks = h.clocks := rfl

@[simp] theorem Heap.write_objects (h : Heap) (ref : SeqRef) (index value : Int) :
    (h.write ref index value).objects = h.objects := rfl

@[simp] theorem Heap.allocate_objects (h : Heap) (contents : Seq) :
    (h.allocate contents).objects = h.objects := rfl

@[simp] theorem Heap.write_nextObject (h : Heap) (ref : SeqRef) (index value : Int) :
    (h.write ref index value).nextObject = h.nextObject := rfl

@[simp] theorem Heap.allocate_nextObject (h : Heap) (contents : Seq) :
    (h.allocate contents).nextObject = h.nextObject := rfl

@[simp] theorem Heap.writeField_store (h : Heap) (ref : ObjectRef)
    (field : String) (value : ObjectValue) :
    (h.writeField ref field value).store = h.store := rfl

@[simp] theorem Heap.writeField_nextRef (h : Heap) (ref : ObjectRef)
    (field : String) (value : ObjectValue) :
    (h.writeField ref field value).nextRef = h.nextRef := rfl

@[simp] theorem Heap.allocateObject_store (h : Heap) (className : String) :
    (h.allocateObject className).store = h.store := rfl

@[simp] theorem Heap.allocateObject_nextRef (h : Heap) (className : String) :
    (h.allocateObject className).nextRef = h.nextRef := rfl

@[simp] theorem Heap.writeField_nextObject (h : Heap) (ref : ObjectRef)
    (field : String) (value : ObjectValue) :
    (h.writeField ref field value).nextObject = h.nextObject := rfl

@[simp] theorem Heap.objectClass_writeField (h : Heap) (ref target : ObjectRef)
    (field : String) (value : ObjectValue) :
    (h.writeField target field value).objectClass ref = h.objectClass ref := by
  by_cases equal : ref = target
  · subst ref
    cases found : h.objects target <;> simp [objectClass, writeField, found]
  · simp [objectClass, writeField, equal]

@[simp] theorem Heap.readField_writeField_same (h : Heap) (ref : ObjectRef)
    (field : String) (value : ObjectValue) (className : String)
    (present : h.objectClass ref = some className) :
    (h.writeField ref field value).readField ref field = some value := by
  cases found : h.objects ref <;> simp_all [objectClass, readField, writeField]

@[simp] theorem Heap.readField_writeField_other_ref (h : Heap) (ref target : ObjectRef)
    (field name : String) (value : ObjectValue) (different : ref ≠ target) :
    (h.writeField target field value).readField ref name = h.readField ref name := by
  simp [readField, writeField, different]

@[simp] theorem Heap.readField_writeField_other_field (h : Heap) (ref : ObjectRef)
    (field name : String) (value : ObjectValue) (different : name ≠ field) :
    (h.writeField ref field value).readField ref name = h.readField ref name := by
  cases found : h.objects ref <;> simp [readField, writeField, found, different]

@[simp] theorem Heap.allocateObject_nextObject (h : Heap) (className : String) :
    (h.allocateObject className).nextObject = h.nextObject + 1 := rfl

@[simp] theorem Heap.objectClass_allocateObject_new (h : Heap) (className : String) :
    (h.allocateObject className).objectClass h.nextObject = some className := by
  simp [objectClass, allocateObject]

@[simp] theorem Heap.readField_allocateObject_new (h : Heap) (className field : String) :
    (h.allocateObject className).readField h.nextObject field = none := by
  simp [readField, allocateObject]

@[simp] theorem Heap.objects_allocateObject_old (h : Heap) (className : String)
    (ref : ObjectRef) (allocated : ref < h.nextObject) :
    (h.allocateObject className).objects ref = h.objects ref := by
  simp [allocateObject, Nat.ne_of_lt allocated]

@[simp] theorem Heap.write_nextRef (h : Heap) (ref : SeqRef) (index value : Int) :
    (h.write ref index value).nextRef = h.nextRef := rfl

@[simp] theorem Heap.allocate_nextRef (h : Heap) (contents : Seq) :
    (h.allocate contents).nextRef = h.nextRef + 1 := rfl

@[simp] theorem Heap.read_write_same (h : Heap) (ref : SeqRef) (index value : Int) :
    (h.write ref index value).read ref index = value := by simp [read, write]

@[simp] theorem Heap.read_write_other_ref (h : Heap) (ref target : SeqRef)
    (index position value : Int) (different : ref ≠ target) :
    (h.write target position value).read ref index = h.read ref index := by
  simp [read, write, different]

@[simp] theorem Heap.read_write_other_index (h : Heap) (ref : SeqRef)
    (index position value : Int) (different : index ≠ position) :
    (h.write ref position value).read ref index = h.read ref index := by
  simp [read, write, different]

@[simp] theorem Heap.read_allocate_new (h : Heap) (contents : Seq) (index : Int) :
    (h.allocate contents).read h.nextRef index = contents index := by simp [read, allocate]

@[simp] theorem Heap.read_allocate_old (h : Heap) (contents : Seq) (ref : SeqRef)
    (index : Int) (allocated : ref < h.nextRef) :
    (h.allocate contents).read ref index = h.read ref index := by
  simp [read, allocate, Nat.ne_of_lt allocated]

@[simp] theorem Heap.sequenceType_writeElement (h : Heap) (ref target : CollectionRef)
    (index : Int) (value : ObjectValue) :
    (h.writeElement target index value).sequenceType ref = h.sequenceType ref := by
  by_cases equal : ref = target
  · subst ref
    cases found : h.collections target with
    | none => simp [sequenceType, writeElement, found]
    | some collection => cases collection <;> simp [sequenceType, writeElement, found]
  · simp [sequenceType, writeElement, equal]

@[simp] theorem Heap.readElement_writeElement_same (h : Heap) (ref : CollectionRef)
    (index : Int) (value : ObjectValue) (elementType : String)
    (present : h.sequenceType ref = some elementType) :
    (h.writeElement ref index value).readElement ref index = some value := by
  cases found : h.collections ref with
  | none => simp [sequenceType, found] at present
  | some collection => cases collection <;> simp [readElement, writeElement, found]

@[simp] theorem Heap.readElement_writeElement_other_ref (h : Heap) (ref target : CollectionRef)
    (index position : Int) (value : ObjectValue) (different : ref ≠ target) :
    (h.writeElement target position value).readElement ref index = h.readElement ref index := by
  simp [readElement, writeElement, different]

@[simp] theorem Heap.readElement_writeElement_other_index (h : Heap) (ref : CollectionRef)
    (index position : Int) (value : ObjectValue) (different : index ≠ position) :
    (h.writeElement ref position value).readElement ref index = h.readElement ref index := by
  cases found : h.collections ref with
  | none => simp [readElement, writeElement, found]
  | some collection => cases collection <;> simp [readElement, writeElement, found, different]

@[simp] theorem Heap.writeElement_nextCollection (h : Heap) (ref : CollectionRef)
    (index : Int) (value : ObjectValue) :
    (h.writeElement ref index value).nextCollection = h.nextCollection := rfl

@[simp] theorem Heap.validSequence_writeElement (h : Heap) (ref target : CollectionRef)
    (index : Int) (value : ObjectValue) (elementType : String) :
    (h.writeElement target index value).validSequence ref elementType ↔
      h.validSequence ref elementType := by simp [validSequence]

@[simp] theorem Heap.allocateSequence_nextCollection (h : Heap) (elementType : String)
    (values : Int → ObjectValue) :
    (h.allocateSequence elementType values).nextCollection = h.nextCollection + 1 := rfl

@[simp] theorem Heap.sequenceType_allocateSequence_new (h : Heap) (elementType : String)
    (values : Int → ObjectValue) :
    (h.allocateSequence elementType values).sequenceType h.nextCollection = some elementType := by
  simp [sequenceType, allocateSequence]

@[simp] theorem Heap.readElement_allocateSequence_new (h : Heap) (elementType : String)
    (values : Int → ObjectValue) (index : Int) :
    (h.allocateSequence elementType values).readElement h.nextCollection index = some (values index) := by
  simp [readElement, allocateSequence]

@[simp] theorem Heap.collections_allocateSequence_old (h : Heap) (elementType : String)
    (values : Int → ObjectValue) (ref : CollectionRef) (allocated : ref < h.nextCollection) :
    (h.allocateSequence elementType values).collections ref = h.collections ref := by
  simp [allocateSequence, Nat.ne_of_lt allocated]

@[simp] theorem Heap.validSequence_allocateSequence_new (h : Heap) (elementType : String)
    (values : Int → ObjectValue) :
    (h.allocateSequence elementType values).validSequence h.nextCollection elementType := by
  simp [validSequence]

theorem Heap.validSequence_allocateSequence_old (h : Heap) (elementType oldType : String)
    (values : Int → ObjectValue) (ref : CollectionRef) (valid : h.validSequence ref oldType) :
    (h.allocateSequence elementType values).validSequence ref oldType := by
  exact ⟨Nat.lt_trans valid.1 (Nat.lt_succ_self _), by
    simpa [sequenceType, collections_allocateSequence_old h elementType values ref valid.1]
      using valid.2⟩

@[simp] theorem Heap.writeElement_store (h : Heap) (ref : CollectionRef)
    (index : Int) (value : ObjectValue) :
    (h.writeElement ref index value).store = h.store := rfl

@[simp] theorem Heap.writeElement_nextRef (h : Heap) (ref : CollectionRef)
    (index : Int) (value : ObjectValue) :
    (h.writeElement ref index value).nextRef = h.nextRef := rfl

@[simp] theorem Heap.writeElement_objects (h : Heap) (ref : CollectionRef)
    (index : Int) (value : ObjectValue) :
    (h.writeElement ref index value).objects = h.objects := rfl

@[simp] theorem Heap.writeElement_nextObject (h : Heap) (ref : CollectionRef)
    (index : Int) (value : ObjectValue) :
    (h.writeElement ref index value).nextObject = h.nextObject := rfl

@[simp] theorem Heap.writeElement_clocks (h : Heap) (ref : CollectionRef)
    (index : Int) (value : ObjectValue) :
    (h.writeElement ref index value).clocks = h.clocks := rfl

@[simp] theorem Heap.allocateSequence_store (h : Heap) (elementType : String)
    (values : Int → ObjectValue) :
    (h.allocateSequence elementType values).store = h.store := rfl

@[simp] theorem Heap.allocateSequence_nextRef (h : Heap) (elementType : String)
    (values : Int → ObjectValue) :
    (h.allocateSequence elementType values).nextRef = h.nextRef := rfl

@[simp] theorem Heap.allocateSequence_objects (h : Heap) (elementType : String)
    (values : Int → ObjectValue) :
    (h.allocateSequence elementType values).objects = h.objects := rfl

@[simp] theorem Heap.allocateSequence_nextObject (h : Heap) (elementType : String)
    (values : Int → ObjectValue) :
    (h.allocateSequence elementType values).nextObject = h.nextObject := rfl

@[simp] theorem Heap.allocateSequence_clocks (h : Heap) (elementType : String)
    (values : Int → ObjectValue) :
    (h.allocateSequence elementType values).clocks = h.clocks := rfl

@[simp] theorem Heap.write_collections (h : Heap) (ref : SeqRef) (index value : Int) :
    (h.write ref index value).collections = h.collections := rfl

@[simp] theorem Heap.write_nextCollection (h : Heap) (ref : SeqRef) (index value : Int) :
    (h.write ref index value).nextCollection = h.nextCollection := rfl

@[simp] theorem Heap.allocate_collections (h : Heap) (contents : Seq) :
    (h.allocate contents).collections = h.collections := rfl

@[simp] theorem Heap.allocate_nextCollection (h : Heap) (contents : Seq) :
    (h.allocate contents).nextCollection = h.nextCollection := rfl

@[simp] theorem Heap.writeField_collections (h : Heap) (ref : ObjectRef)
    (field : String) (value : ObjectValue) :
    (h.writeField ref field value).collections = h.collections := rfl

@[simp] theorem Heap.writeField_nextCollection (h : Heap) (ref : ObjectRef)
    (field : String) (value : ObjectValue) :
    (h.writeField ref field value).nextCollection = h.nextCollection := rfl

@[simp] theorem Heap.allocateObject_collections (h : Heap) (className : String) :
    (h.allocateObject className).collections = h.collections := rfl

@[simp] theorem Heap.allocateObject_nextCollection (h : Heap) (className : String) :
    (h.allocateObject className).nextCollection = h.nextCollection := rfl

@[simp] theorem Heap.tick_collections (h : Heap) (name : String) (amount : Nat := 1) :
    (h.tick name amount).collections = h.collections := rfl

@[simp] theorem Heap.tick_nextCollection (h : Heap) (name : String) (amount : Nat := 1) :
    (h.tick name amount).nextCollection = h.nextCollection := rfl

/-- Typed value encoding for collection elements. References encode object
    identities, without copying the contents of the referenced objects. -/
structure ValueCodec (α : Type) where
  encode : α → ObjectValue
  decode : ObjectValue → Option α
  decode_encode : ∀ value, decode (encode value) = some value

/-- A typed sequence descriptor with an element tag, encoder, and partial decoder. -/
structure SequenceType (α : Type) extends ValueCodec α where
  name : String

namespace SequenceType

variable {α : Type} (type : SequenceType α)

def valid (h : Heap) (ref : CollectionRef) : Prop := h.validSequence ref type.name

instance (h : Heap) (ref : CollectionRef) : Decidable (type.valid h ref) :=
  inferInstanceAs (Decidable (h.validSequence ref type.name))

/-- Read one element without traversing the sequence or any referenced objects. -/
def get (h : Heap) (ref : CollectionRef) (index : Int) : Option α :=
  if type.valid h ref then (h.readElement ref index).bind type.decode else none

def set (h : Heap) (ref : CollectionRef) (index : Int) (value : α) : Heap :=
  h.writeElement ref index (type.encode value)

def create (h : Heap) (values : Int → α) : Heap × CollectionRef :=
  h.createSequence type.name (fun i => type.encode (values i))

/-- Every index initially contains the same value, including the same identity
    when that value is an object or collection reference. -/
def const (h : Heap) (value : α) : Heap × CollectionRef :=
  type.create h (fun _ => value)

/-- A fresh outer collection with the same stored elements. Referenced objects
    and nested collections remain shared; this does not recursively copy them. -/
def copy (h : Heap) (ref : CollectionRef) : Heap × CollectionRef :=
  h.createSequence type.name (fun index => (h.readElement ref index).getD .noneValue)

@[simp] theorem valid_set (h : Heap) (ref target : CollectionRef) (index : Int) (value : α) :
    type.valid (type.set h target index value) ref ↔ type.valid h ref := by
  simp [valid, set]

@[simp] theorem get_set_same (h : Heap) (ref : CollectionRef) (index : Int)
    (value : α) (present : type.valid h ref) :
    type.get (type.set h ref index value) ref index = some value := by
  have stored := present.2
  simp [get, set, valid, Heap.validSequence, present.1, stored, type.decode_encode]

@[simp] theorem get_set_other_ref (h : Heap) (ref target : CollectionRef)
    (index position : Int) (value : α) (different : ref ≠ target) :
    type.get (type.set h target position value) ref index = type.get h ref index := by
  simp [get, set, valid, different] <;> rfl

@[simp] theorem get_set_other_index (h : Heap) (ref : CollectionRef)
    (index position : Int) (value : α) (different : index ≠ position) :
    type.get (type.set h ref position value) ref index = type.get h ref index := by
  simp [get, set, valid, different] <;> rfl

@[simp] theorem valid_create (h : Heap) (values : Int → α) :
    type.valid (type.create h values).1 (type.create h values).2 := by
  simp [valid, create, Heap.createSequence]

@[simp] theorem get_create (h : Heap) (values : Int → α) (index : Int) :
    type.get (type.create h values).1 (type.create h values).2 index = some (values index) := by
  simp [get, create, Heap.createSequence, valid, type.decode_encode]

@[simp] theorem valid_const (h : Heap) (value : α) :
    type.valid (type.const h value).1 (type.const h value).2 := by simp [const]

@[simp] theorem get_const (h : Heap) (value : α) (index : Int) :
    type.get (type.const h value).1 (type.const h value).2 index = some value := by simp [const]

@[simp] theorem valid_copy (h : Heap) (ref : CollectionRef) :
    type.valid (type.copy h ref).1 (type.copy h ref).2 := by
  simp [valid, copy, Heap.createSequence]

@[simp] theorem get_copy (h : Heap) (ref : CollectionRef) (index : Int)
    (present : type.valid h ref) :
    type.get (type.copy h ref).1 (type.copy h ref).2 index = type.get h ref index := by
  have stored := present.2
  cases found : h.collections ref with
  | none => simp [Heap.sequenceType, found] at stored
  | some collection =>
    cases collection
    simp only [get, valid_copy, present, if_true]
    simp [copy, Heap.createSequence, Heap.readElement, Heap.allocateSequence, found]

end SequenceType

end Algo2LeanGenerated


