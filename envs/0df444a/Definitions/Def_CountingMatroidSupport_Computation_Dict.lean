-- Prove2me | Definitions.Def_CountingMatroidSupport_Computation_Dict
-- name    : CountingMatroidSupport_Computation_Dict
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:32:17.177163+00:00
-- url     : https://prove2.me/theorems/f292ba0d-bb5d-41ce-b223-4428cd39b550
-- title:
--   Dictionary operation names and abstract entry categories
-- statement:
--   The dictionary-operation alphabet is $$\mathcal D=\{\mathrm{find},\mathrm{insert},\mathrm{erase},\mathrm{size},\mathrm{cardEq}\}.$$ The labels denote key lookup, insertion, deletion, reading the number of entries, and comparison of that number with a specified number. For an ambient operation type $\kappa$, a dictionary naming interface supplies an injective map $c:\mathcal D\hookrightarrow\kappa$. For a key type $\iota$, a value type $\alpha$, and an abstract cell-category type $\kappa_s$, an entry interface chooses $$\operatorname{cell}_{\iota,\alpha}\in\kappa_s.$$ The finite operation alphabet has decidable equality and an explicit enumeration.
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/Computation/Dict.lean#L62-L97

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
import Mathlib.Data.List.Nodup
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
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
# A sealed finite map, whose operations charge

A `Dict ι α` is a finite map from `ι` to `α` that a program can touch only
through a charged operation.  It holds a private list of entries with
duplicate-free keys; the lookup function, the key set and the cardinality are
`noncomputable`, so `d.lookup k` is specification vocabulary and `Dict.find k d`
is the program.

`find`, `insert`, `erase`, `size` and `cardEq` each charge one operation, under
the opcode the development's `DictOps` instance names.  A caller computes the
value it inserts and pays for that computation in the monad on the way; `insert`
charges for the store.

There is no `modify`: a program that changes the value at a key does `find` then
`insert`, and pays for both.  There is no membership test either — `find` returns
the value, and testing an `Option` costs nothing once the lookup is paid for.

An entry occupies one cell of the kind `DictCells` names, whatever the value is.
A development whose values are themselves large names a kind whose cell means
"one entry of this table" and prices it in its space model.

Keys without values belong in `Arlib.Computation.Roster ι`.

## Main definitions

* `Dict ι α` — a sealed finite map.
* `Dict.lookup`, `Dict.keys`, `Dict.card` — the specification view; noncomputable.
* `Dict.ofFinset` — the map with a given domain; noncomputable.
* `DictOp`, `DictOps` — the standard operations, and what a development's
  currency calls each of them.
* `DictCells` — the kind of cell one entry occupies.
* `Dict.empty`, `Dict.find`, `Dict.insert`, `Dict.erase`, `Dict.size`,
  `Dict.cardEq` — the operations, one charge each.
* `Dict.occupancy` — the measure an `ExactNet` obligation is stated against.
-/

namespace Arlib.Computation

universe u



/-- The standard dictionary operations.  Each of the operations below charges
exactly one of these, and takes no opcode parameter. -/
inductive DictOp
  /-- Retrieve the value stored at a key, if any. -/
  | find
  /-- Store a value at a key, replacing whatever was there. -/
  | insert
  /-- Remove a key and its value. -/
  | erase
  /-- Ask how many entries are held. -/
  | size
  /-- Compare the number of entries held against a number. -/
  | cardEq
  deriving DecidableEq, Repr, Inhabited

instance : Fintype DictOp where
  elems := {.find, .insert, .erase, .size, .cardEq}
  complete := fun x => by cases x <;> decide

/-- Which opcode of a development's currency `κ` names each standard dictionary
operation.  A name, not an amount: the amount is one charge per call, fixed by
the operations below.  `charge_injective` keeps distinct operations under
distinct names, and is discharged by `decide`. -/
class DictOps (κ : Type) where
  /-- The development's opcode for a standard dictionary operation. -/
  charge : DictOp → κ
  /-- Distinct operations keep distinct names. -/
  charge_injective : Function.Injective charge

/-- The kind of storage cell one entry of a `Dict ι α` occupies.

One instance per key/value pair of types per development.  The kind comes from
the data rather than from a parameter at each operation. -/
class DictCells (ι : Type u) (α : Type u) (κₛ : outParam Type) where
  /-- The kind of cell one entry of a `Dict ι α` occupies. -/
  cell : κₛ

namespace Dict

variable {κ κₛ ι α : Type} [DecidableEq κ] [DecidableEq κₛ] [DecidableEq ι]





/-! ## The list underneath

The two functions the operations are built from, and their laws.  Both are
`private`: they are the representation. -/













/-! ## The specification view

Every declaration in this section is `noncomputable`, and so cannot appear in a
program. -/



















/-! ## What a dictionary occupies

**A dictionary occupies one cell of the storage kind it is given, per entry, and
nothing of any other kind.**  The `space_*` theorems below follow from this and
from what each operation does to the entry list. -/



















/-! ## The operations -/









variable [DictOps κ]

















































end Dict

end Arlib.Computation

end


