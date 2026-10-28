-- Prove2me | Definitions.Def_CountingMatroidSupport_Computation_Heap
-- name    : CountingMatroidSupport_Computation_Heap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:33:17.289597+00:00
-- url     : https://prove2.me/theorems/5d5e792e-4d06-41a8-b2d7-7fb231f810fc
-- title:
--   Heap operation vocabulary and tree representation
-- statement:
--   The finite heap-operation vocabulary is $$\mathrm{HeapOp}=\{\mathrm{push},\mathrm{pop},\mathrm{peek},\mathrm{size},\mathrm{isEmpty},\mathrm{cmp}\}.$$ These names respectively denote insertion, removal of a minimum, inspection of a minimum, size inspection, emptiness inspection, and key comparison. The bundle supplies enumeration, decidable equality, representation, and a default element. For any operation-label type $\kappa$, a heap-operation interface specifies an injective map $$\operatorname{charge}:\mathrm{HeapOp}\hookrightarrow\kappa.$$ For an element type $\alpha$ and a storage-label type $\kappa_s$, a heap-cell interface selects one label in $\kappa_s$ for elements of $\alpha$.
--
--   The underlying tree representation has an empty constructor and a node constructor with a natural rank annotation, an element of $\alpha$, and two child trees: $$T_\alpha=\mathrm{nil}\ \mid\ \mathrm{node}(r,x,l,u),\qquad r\in\mathbb N,\ x\in\alpha,\ l,u\in T_\alpha.$$ The Heap wrapper stores one such tree.
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/Computation/Heap.lean#L57-L385

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
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
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
# A sealed priority queue, whose comparisons are charged

A `Heap α` is a leftist heap over a linear order that a program can touch only
through a charged operation.  It holds a private tree; its contents, its
cardinality and its root are `noncomputable`, so the smallest element is behind
`peek` and `pop` rather than available for free.

`push`, `pop`, `peek`, `size` and `isEmpty` each charge one operation, under the
opcode the development's `HeapOps` instance names.  `push` and `pop` are each one
merge, and the merge charges one `HeapOp.cmp` per key comparison it performs.
The number of comparisons is therefore the length of the two right spines the
merge walked, and `rank_le_log`, `cost_push_le`, `steps_push_le` and their `pop`
counterparts bound it by `log₂ (n + 1)`.

The heap is leftist because a leftist merge's every step is a key comparison, so
its cost is a single number, bounded by the rank invariant the merges maintain.

`Heap.Valid` — the leftist and heap-order invariants — is a predicate rather than
a field of `Heap`, since `push` builds its result from the tree a charged merge
produced.  `valid_empty`, `valid_push` and `valid_pop` are its closure; the
theorems that need heap order or the rank bound take it as a hypothesis.

An element occupies one cell of the kind `HeapCells` names.  A comparison holds
nothing, so a whole merge has profile `1`.

## Main definitions

* `Heap α` — a sealed leftist heap.
* `Heap.toMultiset`, `Heap.card`, `Heap.root` — the specification view;
  noncomputable.
* `HeapOp`, `HeapOps` — the standard operations, and what a development's
  currency calls each of them.
* `HeapCells` — the kind of cell one element occupies.
* `Heap.empty`, `Heap.push`, `Heap.pop`, `Heap.peek`, `Heap.size`,
  `Heap.isEmpty` — the operations.
* `Heap.Valid` — the leftist and heap-order invariants.
* `Heap.root_le` — the root is the smallest element.
* `Heap.rank_le_log`, `Heap.steps_push_le`, `Heap.steps_pop_le` — the
  logarithmic bounds.
-/

namespace Arlib.Computation

universe u

/-- The standard priority-queue operations.  All but `cmp` are charged once per
call; `cmp` is charged once per key comparison the merge performs. -/
inductive HeapOp
  /-- Add an element. -/
  | push
  /-- Take the smallest element, destructively. -/
  | pop
  /-- Look at the smallest element without taking it. -/
  | peek
  /-- Ask how many elements are held. -/
  | size
  /-- Ask whether the heap is empty. -/
  | isEmpty
  /-- Compare two keys.  Charged once per comparison the merge performs. -/
  | cmp
  deriving DecidableEq, Repr, Inhabited

instance : Fintype HeapOp where
  elems := {.push, .pop, .peek, .size, .isEmpty, .cmp}
  complete := fun x => by cases x <;> decide

/-- Which opcode of a development's currency `κ` names each standard heap
operation.  A name, not an amount.  `charge_injective` keeps distinct operations
under distinct names, and is discharged by `decide`. -/
class HeapOps (κ : Type) where
  /-- The development's opcode for a standard heap operation. -/
  charge : HeapOp → κ
  /-- Distinct operations keep distinct names. -/
  charge_injective : Function.Injective charge



/-- The kind of storage cell one element of a heap over `α` occupies.

One instance per element type per development.  The kind comes from the data
rather than from a parameter at each operation. -/
class HeapCells (α : Type u) (κₛ : outParam Type) where
  /-- The kind of cell one element of a heap over `α` occupies. -/
  cell : κₛ

/-- INTERNAL: the leftist tree underneath a `Heap`.  Private, as is every
function on it: these are the representation. -/
 inductive HTree (α : Type u) where
  | Arlib.Computation.HTree.nil
  | Arlib.Computation.HTree.node (rk : ℕ) (x : α) (l r : HTree α)

namespace HTree

variable {α : Type}


































































end HTree

/-- A leftist heap over `α` that a program can touch only through a charged
operation.

The tree is `private` and every view of it is `noncomputable`, so outside this
module the only way to obtain a heap is `empty` together with the operations
below. -/
structure Heap (α : Type u) where
  private mk ::
  private tree : Arlib.Computation.HTree α

namespace Heap

variable {κ κₛ : Type} {α : Type} [DecidableEq κ] [DecidableEq κₛ] [LinearOrder α]



/-! ## The specification view -/











variable [HeapOps κ]

/-! ## The merge, and its comparisons

`push` and `pop` are each one merge.  `mergeC` charges one `HeapOp.cmp` per key
comparison, and the three theorems after it give its value, its profile and its
cost. -/















/-! ## What a heap occupies -/







/-! ## The operations -/















































/-! ## Looking, counting, and asking whether there is anything left -/

























/-! ## The logarithmic bounds

A leftist tree's right spine is at most `log₂ (n + 1)` long, the merge charges one
comparison per level of the two spines it walks, and `push` and `pop` are each one
merge. -/









end Heap

end Arlib.Computation

end


