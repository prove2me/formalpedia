-- Prove2me | Definitions.Def_CountingMatroidSupport_Computation_Machine
-- name    : CountingMatroidSupport_Computation_Machine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:38:18.777868+00:00
-- url     : https://prove2.me/theorems/b38b1709-67d1-4b6d-9d44-52b2fdfe5627
-- title:
--   Word representations and stateful computations with accumulated charges
-- statement:
--   For a word width $w\in\mathbb N$, a word is a wrapper around a $w$-bit vector. A RAM state $\sigma$ consists of a finite memory array and a finite output array of $w$-bit vectors; the output array defaults to empty. For a result type $\alpha$, a computation is represented by a function $$\operatorname{run}:\operatorname{State}_w\longrightarrow\alpha\times\operatorname{State}_w\times\mathbb N^{\mathcal O},$$ where $\mathcal O$ is the primitive-operation alphabet and the final component records its charge vector.
--
--   Returning a value $a\in\alpha$ preserves the state and has zero charge: $$\operatorname{pure}(a)(\sigma)=(a,\sigma,0).$$ Sequential composition first runs $p$ and then runs $f(a)$ on its resulting state. If $p(\sigma)=(a,\sigma',c)$ and $f(a)(\sigma')=(b,\sigma'',d)$, then $$\operatorname{bind}(p,f)(\sigma)=(b,\sigma'',c+d).$$ These operations give the provided monadic interface. The bundle also contains an internal vector representation consisting of a list of width-$w$ words and a separate width-$w$ word storing a length field.
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/Computation/Machine.lean#L68-L656

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
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
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
# The machine, and the language written against it

A word RAM, and the monad in which algorithms over it are written.  This is one
module rather than several because the seal that makes the cost honest is Lean's
`private`, which is file-scoped: `Word` and the primitives that produce and
consume it must live together.

## The seal

An algorithm here is an ordinary Lean function.  The objection to that is that a
Lean function computes anything for free, so `pure (median l)` would be a
zero-cost program.  Three things answer it, and the third is checked by the
compiler rather than by review.

1. `Word` has a **private constructor and a private field**, and carries no
   `Add`, `LT` or `DecidableEq` instance.  So `x + y` and `if x < y then _` do
   not elaborate: arithmetic and comparison go through the charged primitives
   below, and `Bool`-branching afterwards is free precisely because the
   comparison paid for it.
2. `RAM` has a **private constructor**.  Its `run` field is public — observing a
   program is harmless — but no client can build a `RAM` except from the
   primitives and the monad operations, so no client can write a program that
   moves the state without charging for it.
3. `Word.toNat`, the view a *specification* needs, is **`noncomputable`**.  A
   program that inspects a word without a primitive therefore fails to compile:
   Lean reports `failed to compile definition, consider marking it as
   'noncomputable'`.  The only way past it is to write `noncomputable def`
   explicitly, which `scripts/ComputationAudit.lean` rejects.

A fourth thing closes the route the first three leave open.  A structure with
private *fields* still has a public `casesOn`, and `Word.casesOn x (fun v => v)`
projected the field out.  `Word` is therefore a public alias for a `private`
structure, `WordRep`: the elaborator generates the eliminators under a name that
`private` mangles with this module, so no client can write one.
`ArlibTest/Computation.lean` §3 checks all four rejections.

The cost is that `Word` is a `def` rather than a `structure`, so its own module
names the representation through the file-scoped `Word.val` and `Word.mk` below,
and `Word.ext` proves what a structure would have given for free.  `Word` is
deliberately not an `abbrev`: an `abbrev` is reducible, dot notation would see
through it to the private field, and the seal would be a formality.

## Main definitions

* `Word w` — a `w`-bit machine word, sealed.
* `RamState w` — memory, and an output log for testing.
* `RAM w α` — the monad: a state transformer that also accumulates a `Cost`.
* `lit`, `add`, …, `load`, `store`, `alloc`, `emit` — the primitives.
* `RAM.cost`, `RAM.steps` — the time operator.
-/

namespace Arlib.Computation

universe u

/-! ## Words -/

/-- INTERNAL: the representation of a machine word.

`private` at the *structure* level rather than at the field level, which is what
closes the `casesOn` route.  A structure with private fields still has a public
`casesOn`, and `Word.casesOn x (fun v => v)` projects the field back out; a
private structure has no name a client can write.  `Word` below is a public alias
for it, so the type is usable everywhere and its representation is reachable only
from this file. -/
 structure WordRep (w : ℕ) where
  mk :: val : BitVec w

/-- A `w`-bit machine word.

A public alias for a `private` representation, and deliberately carrying no
arithmetic, order or decidability instances: outside this module a `Word` can be
produced and consumed only by a charged primitive.

`Word` is a `def` and not an `abbrev`.  An `abbrev` is reducible, so dot notation
would see through it to the private field, and the seal would be a formality. -/
def Word (w : ℕ) := WordRep w

namespace Word















end Word

/-! ## The machine state -/

/-- The machine's state: a flat memory of words, and an output log.

Memory is an `Array` indexed by `ℕ`, so the address space is **decoupled from
the word width**.  A memory of `2 ^ w` cells at `w = ⌈log₂ n⌉` would be `Θ(n)`
cells, too few to hold the working space of a polynomial-time computation; the
`Array` avoids building that restriction into the model.  Cells outside the
array read as zero.

`out` exists so that a test can observe a program's answer without a projection
out of `Word`, which would breach the seal.  `emit` is the only writer, and it
charges. -/
structure RamState (w : ℕ) where
  /-- The allocated memory. -/
  mem : Array (BitVec w)
  /-- What the program has emitted, oldest first. -/
  out : Array (BitVec w) := #[]

namespace RamState







end RamState

/-! ## The monad -/

/-- A program: a state transformer that also accumulates the operations it
performed.

The constructor is `private`, so a client can obtain a `RAM` only from the
primitives below and the monad operations.  The `run` field is public: observing
a program cannot make one cheaper. -/
structure RAM (w : ℕ) (α : Type u) where
  private mk ::
  /-- Run the program: its result, the state it leaves, and what it did. -/
  run : RamState w → α × RamState w × Cost

namespace RAM

variable {w : ℕ} {α β : Type u}









 def pure' (a : α) : RAM w α := ⟨fun σ => (a, σ, 0)⟩

 def bind' (p : RAM w α) (f : α → RAM w β) : RAM w β :=
  ⟨fun σ =>
    let r := p.run σ
    let s := (f r.1).run r.2.1
    (s.1, s.2.1, r.2.2 + s.2.2)⟩

instance : Monad (RAM w) where
  pure := pure'
  bind := bind'




















end RAM

/-! ## Cost is monotone along a program

The deterministic analogue of `Arlib.Approximation.IsFPRAS.Charges`, which is
the predicate that excludes the zero-cost non-algorithm.  There it has to be
assumed; here a program that performs any primitive at all has positive cost,
and these two lemmas are how that is discharged for a composite program. -/

namespace RAM

variable {w : ℕ} {α β : Type u}





end RAM

/-! ## The primitives

Each performs exactly one operation of the corresponding `Op`, except `alloc`,
which performs one per cell.  These are the only inhabitants of `RAM` a client
can obtain, so they are the only source of cost in the library. -/

section Primitives

variable {w : ℕ}









































end Primitives

/-! ## Specification lemmas

For each primitive: what it returns, what it leaves the state, and what it cost.
The value lemmas are stated through `Word.toNat`, because that is the only view
of a word a client outside this module has.

These are the whole public API of the machine.  Everything in
`Arlib.Computation.Lib` is proved from them and from `RAM.cost_bind`. -/

section Spec

variable {w : ℕ} (σ : RamState w) (x y : Word w)






















































































































end Spec

/-! ## Charged authoring primitives over the same sealed words
These trusted primitives live with the word seal. Their exact correspondence
lemmas allow clients to author with Charged while executing RAM counterparts.
-/



namespace ChargedWord
variable {w : Nat} {κₛ : Type}
























































end ChargedWord

 structure ChargedVectorRep (w : Nat) where
  cells : List (Word w)
  length : Word w

namespace ChargedVector
variable {w : Nat} {κₛ : Type}


















end ChargedVector

end Arlib.Computation

end


