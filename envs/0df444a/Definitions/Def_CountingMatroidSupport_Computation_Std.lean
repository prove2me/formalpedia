-- Prove2me | Definitions.Def_CountingMatroidSupport_Computation_Std
-- name    : CountingMatroidSupport_Computation_Std
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:39:01.712198+00:00
-- url     : https://prove2.me/theorems/9204a1fa-6f41-45ea-961a-5b27691a0c87
-- title:
--   A standard operation vocabulary and size-dependent charge specifications
-- statement:
--   The standard operation type is the disjoint union of the roster, dictionary, heap, queue, randomness, categorical-draw, slot, and numeric operation alphabets: $$\mathcal S=\mathcal R_{\mathrm{roster}}\sqcup\mathcal R_{\mathrm{dict}}\sqcup\mathcal R_{\mathrm{heap}}\sqcup\mathcal R_{\mathrm{queue}}\sqcup\mathcal R_{\mathrm{rand}}\sqcup\mathcal R_{\mathrm{draw}}\sqcup\mathcal R_{\mathrm{slot}}\sqcup\mathcal R_{\mathrm{num}}.$$ Constructor maps supply injective naming interfaces for all eight alphabets, and an explicit list enumerates every standard operation. The abstract cell-category type has four labels: roster, dictionary, heap, and queue; default cell interfaces assign the corresponding label to each container family. A separate growth-label type has the three constructors flat, logarithmic, and linear.
--
--   A standard implementation specification consists of a charge vector $r(o,s):\mathcal O\to\mathbb N$ and an upper bound $B(o,s)\in\mathbb N$, where $o\in\mathcal S$, $s\in\mathbb N$ is a container-size parameter, and $\mathcal O$ is the primitive-operation alphabet. It requires $$\sum_{a\in\mathcal O}r(o,s)(a)\le B(o,s),\qquad B(o,s)\ge1,$$ and $B(o,s)\le B(o,t)$ whenever $s\le t$.
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/Computation/Std.lean#L95-L314

/-
Required support modules adapted from meelgroup/arlib, commit 6262f60ad7556be62e94e87f6b5811cf299e7d94. Copyright and authorship notices are preserved in each file. Module import paths use CountingMatroidSupport; original declaration namespaces are retained for proof compatibility. Arlib is not a Lake package dependency.

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
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

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
import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

section
/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/


/-!
# The standard currency, and what it costs on the machine

A tally is `CostVec κ = κ → ℕ`, one function over one type, while an algorithm
touches several sealed carriers, each with its own operation type.  Somebody has
to supply the type that covers all of them, and until now that was the
development: it declared an inductive, wrote a `RosterOps`/`RandOps`/`SlotOps`
instance mapping arlib's operations onto its own names, and discharged
`charge_injective` by `decide`.

That table is a translation a reader has to check, and it buys nothing when every
operation a development performs is already one of arlib's.  `StdOp` is the
coproduct of **all eight** sealed carriers' currencies — `Roster`, `Dict`, `Heap`,
`Queue`, `Coins`/`Sampler`, `Draws`, `Slot` and `Num` — supplied here, with the
eight instances as injections, so there is nothing to choose and nothing to
check.

**A development declares an operation only when arlib has no analogue for it**,
and then declares that operation and its cost, and nothing else.

## Where cost becomes machine operations

`StdImpl` is the join to `Arlib.Computation.Machine`: `rate o s` says what one
standard operation costs in word operations **when the carrier it touches holds
`s` elements**, and `Charged.exchange` carries a bound in `StdOp` across to a
bound in `Op`.

The size parameter is the whole of the interface's content, and it is what an
earlier `bound : ℕ` could not express.  `Roster.filterErase` performs `2 * |d|`
dictionary operations, honestly counted; but on a list-backed carrier each erase
is itself `Θ(|d|)` word operations and on a search tree `Θ(log |d|)`, so a
thinning pass is `Θ(|d|²)` or `Θ(|d| log |d|)` word operations and no uniform
per-operation ceiling can say so.  With `rate` and `bound` taking the carrier's
size, `StdImpl.listBacked` and `StdImpl.balanced` are inhabitants that state
exactly those two costs, and `listBacked_thin_wordSteps_le` derives the quadratic.

`StdImpl` remains a **hypothesis** — a description of an implementation, not an
implementation.  What has changed is that it is now a hypothesis realistic
structures satisfy: `StdImpl.constantTime` is the `O(1)` assumption the old
`StdImpl.trivial` silently made, and it is no longer the only inhabitant.

Two limits are worth stating rather than discovering.

**The ceiling is worst-case.**  A hash table meets `constantTime` in expectation
only, and an expectation is not an inhabitant of this interface.  That is
deliberate: a worst-case exchange rate is what `CostVec.steps_exchange_le`
multiplies through, and an expected-time structure needs a different theorem, not
a laxer field.

**No inhabitant is compiled.**  Discharging that is the open work: write a
`Roster` as a `RAM` program over `HoldsList`, prove its five operations meet
`StdImpl.balanced`, and every bound stated against `StdOp` becomes a bound in
word operations with a program behind it.  The interface no longer blocks it.

## Main definitions

* `StdOp` — every operation arlib's sealed carriers perform.
* `Cell` — one storage kind per carrier, for a development that does not declare
  its own.
* `Growth` — how one operation's cost grows with the size of its carrier.
* `StdImpl` — what one standard operation costs in word operations, at a size.
* `StdImpl.listBacked`, `StdImpl.balanced`, `StdImpl.constantTime` — three
  implementations, described by their cost.

## Main results

* `StdImpl.wordSteps_le` — a bound in standard operations becomes a bound in word
  operations, at a size ceiling.
* `size_le_of_peak_le` — the tool that discharges the size ceiling from a space
  bound, so the ceiling is a proved side condition rather than an assumption.
* `listBacked_thin_wordSteps_le`, `balanced_thin_wordSteps_le` — what a thinning
  pass costs on each of the two realistic carriers.
-/

namespace Arlib.Computation

universe u

/-! ## The work currency -/

/-- Every operation arlib's sealed carriers perform: the set operations of
`Roster`, the map operations of `Dict`, the priority-queue operations of `Heap`,
the FIFO operations of `Queue`, the randomness operations of `Block`/`Coins`/
`Sampler`, the categorical draw of `Draws`, the answer-register operations of
`Slot`, and the arithmetic and loop entry of `Num`. -/
inductive StdOp
  | roster : RosterOp → StdOp
  | dict : DictOp → StdOp
  | heap : HeapOp → StdOp
  | queue : QueueOp → StdOp
  | rand : RandOp → StdOp
  | draw : DrawOp → StdOp
  | slot : SlotOp → StdOp
  | num : NumOp → StdOp
  deriving DecidableEq

namespace StdOp

/-- Every standard operation, as a list. -/
def all : List StdOp :=
  [.roster .erase, .roster .insert, .roster .size, .roster .cardEq, .roster .mem,
   .dict .find, .dict .insert, .dict .erase, .dict .size, .dict .cardEq,
   .heap .push, .heap .pop, .heap .peek, .heap .size, .heap .isEmpty, .heap .cmp,
   .queue .enqueue, .queue .dequeue, .queue .isEmpty,
   .rand .flip, .rand .accept, .rand .halve, .rand .inflate,
   .draw .pick,
   .slot .test, .slot .fill,
   .num .lit, .num .add, .num .sub, .num .mul, .num .div, .num .max, .num .min,
   .num .cmp, .num .ceil, .num .loop]

/-- INTERNAL: `all` is exhaustive, which is what makes `Fintype` legal. -/
theorem mem_all (o : StdOp) : o ∈ all := by
  cases o <;> rename_i x <;> cases x <;> decide

/-- The currency is finite, so `CostVec.steps` can sum over it. -/
instance : Fintype StdOp := Fintype.ofList all mem_all

end StdOp

/-- The set operations, under their own names.  An injection, so
`charge_injective` is a `cases` rather than a table to read. -/
instance stdRosterOps : RosterOps StdOp where
  charge := StdOp.roster
  charge_injective := by intro a b h; simpa using h

/-- The map operations, under their own names. -/
instance stdDictOps : DictOps StdOp where
  charge := StdOp.dict
  charge_injective := by intro a b h; simpa using h

/-- The priority-queue operations, under their own names. -/
instance stdHeapOps : HeapOps StdOp where
  charge := StdOp.heap
  charge_injective := by intro a b h; simpa using h

/-- The FIFO operations, under their own names. -/
instance stdQueueOps : QueueOps StdOp where
  charge := StdOp.queue
  charge_injective := by intro a b h; simpa using h

/-- The randomness operations, under their own names. -/
instance stdRandOps : RandOps StdOp where
  charge := StdOp.rand
  charge_injective := by intro a b h; simpa using h

/-- The categorical draw, under its own name. -/
instance stdDrawOps : DrawOps StdOp where
  charge := StdOp.draw
  charge_injective := by rintro ⟨⟩ ⟨⟩ _; rfl

/-- The answer-register operations, under their own names. -/
instance stdSlotOps : SlotOps StdOp where
  charge := StdOp.slot
  charge_injective := by intro a b h; simpa using h

/-- The arithmetic and the loop entry, under their own names. -/
instance stdNumOps : NumOps StdOp where
  charge := StdOp.num
  charge_injective := by intro a b h; simpa using h

/-! ## The storage currency -/

/-- One kind of storage cell per carrier, for a development that does not care to
distinguish two rosters from each other.

There is one constructor per carrier rather than one in total, because a bound on
"the cells a run holds" that cannot say whether they are the estimator's samples
or its key table is not a bound anybody can read.  A development that holds two
*rosters* whose cells should be bounded separately still declares its own kind
type: that is a genuine choice about what is being counted, unlike the naming of
an operation, which is not. -/
inductive Cell
  /-- A cell holding one element of a `Roster`. -/
  | roster
  /-- A cell holding one entry of a `Dict`. -/
  | dict
  /-- A cell holding one element of a `Heap`. -/
  | heap
  /-- A cell holding one element of a `Queue`. -/
  | queue
  deriving DecidableEq

namespace Cell

/-- Every storage kind, as a list. -/
def all : List Cell := [.roster, .dict, .heap, .queue]

/-- INTERNAL: the currency is finite. -/
instance : Fintype Cell := Fintype.ofList all (fun k => by cases k <;> decide)

end Cell

/-- One element of any roster occupies one `Cell.roster`.  Low priority, so a
development that declares its own kinds wins. -/
instance (priority := low) stdRosterCells (ι : Type u) : RosterCells ι Cell :=
  ⟨Cell.roster⟩

/-- One entry of any map occupies one `Cell.dict`. -/
instance (priority := low) stdDictCells (ι α : Type u) : DictCells ι α Cell :=
  ⟨Cell.dict⟩

/-- One element of any heap occupies one `Cell.heap`. -/
instance (priority := low) stdHeapCells (α : Type u) : HeapCells α Cell :=
  ⟨Cell.heap⟩

/-- One element of any queue occupies one `Cell.queue`. -/
instance (priority := low) stdQueueCells (ι : Type u) : QueueCells ι Cell :=
  ⟨Cell.queue⟩

/-! ## How a cost grows with what is held -/

/-- **How the work one operation does grows with the size of the carrier it
touches.**

Three shapes, because three are what the realistic representations of a finite
set give: a scan of an unordered list, a descent of a balanced tree, and a read
of a field that does not depend on the contents at all.

`work` is the number of *elements the operation touches*, not a cost:
`StdImpl.ofGrowth` turns it into a tally of word operations by charging a load, a
pointer advance and a comparison for each. -/
inductive Growth
  /-- The work does not grow with the carrier: a cached length, a register, a
  word of arithmetic. -/
  | flat
  /-- The work is the depth of a balanced tree over the carrier. -/
  | log
  /-- The work is a pass over the carrier. -/
  | linear
  deriving DecidableEq, Repr

namespace Growth













end Growth

/-! ## What a standard operation costs on the machine -/

/-- An implementation of the sealed carriers, described only by what its
operations cost in word operations **as a function of how much the carrier
holds**.

`rate o s` is the tally of machine operations one `o` performs against a carrier
of `s` elements, and `bound o s` is a ceiling on it.  `s` is the size of the
carrier the operation touches: the number of elements a `Roster`, `Dict`, `Heap`
or `Queue` holds, the number of outcomes a `Draws` ranges over, and the level of
a `Sampler`'s rate.  For `Slot` and `Num` — a register and a word — the parameter
is ignored, and a `flat` shape says so.

Nothing here says the implementation exists or is correct; it says what it would
cost, which is all `Charged.exchange` needs.

`one_le_bound` is the field that keeps `⟨fun _ _ => 0, fun _ _ => 0, _, _⟩` out.
It is `Rate.one_le`'s counterpart one level up: without it there is a legal
`StdImpl` under which every carrier is free, and the area would ship a generator
of the zero-cost non-algorithm it exists to exclude. -/
structure StdImpl where
  /-- What one standard operation costs, in word operations, against a carrier of
  `s` elements. -/
  rate : StdOp → ℕ → CostVec Op
  /-- A ceiling on the cost of a single operation, at each size. -/
  bound : StdOp → ℕ → ℕ
  /-- Every standard operation is within its ceiling. -/
  bound_ok : ∀ o s, CostVec.steps CostModel.unitCost (rate o s) ≤ bound o s
  /-- A bigger carrier is not cheaper.  This is what lets a ceiling taken at the
  largest size a run reaches stand for every size it reaches. -/
  bound_mono : ∀ o, Monotone (bound o)
  /-- Every operation costs something. -/
  one_le_bound : ∀ o s, 1 ≤ bound o s

namespace StdImpl

variable (I : StdImpl)















/-! ### Carrying a bound across to the machine -/







end StdImpl

/-! ### Discharging the size ceiling

`StdImpl.atSize n` prices a run as though no carrier ever exceeded `n` elements.
That is a claim about the run, and this is what proves it: a `Profile`'s `peak`
is the largest excursion above the level it started from, and
`Profile.net_le_peak_mul` says every *prefix*'s net is below the *whole*'s peak.
So a carrier that started with `s₀` elements, in a run whose profile peaks no
more than `n - s₀` above that, never held more than `n` at any point — not merely
at the end. -/



namespace StdImpl

/-! ## Three implementations, described by their cost

Each is a table of `Growth`s and a setup constant, and each is a *description* —
no program is exhibited.  What they establish is that the interface can state the
cost of a real representation, which a uniform `bound : ℕ` could not. -/









/-! ### The three tables -/

















/-! ### What a thinning pass really costs

`Roster.cost_filterErase` says a pass over a roster of `d` elements charges one
test per element and one `RosterOp.erase` per rejection: at most `2 * d` standard
operations, and that count is honest.  These two theorems are what it becomes on
the machine, and they are the claim the interface could not previously make. -/







end StdImpl

end Arlib.Computation

end


