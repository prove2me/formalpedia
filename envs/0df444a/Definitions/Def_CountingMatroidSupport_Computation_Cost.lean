-- Prove2me | Definitions.Def_CountingMatroidSupport_Computation_Cost
-- name    : CountingMatroidSupport_Computation_Cost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:19:44.290096+00:00
-- url     : https://prove2.me/theorems/306ec2cb-3fe1-489e-a164-50b6fc594e6f
-- title:
--   Primitive-operation tallies and positive pricing
-- statement:
--   The primitive-operation alphabet $\mathcal O$ has twenty labels: literal, addition, subtraction, low and high multiplication, unsigned quotient and remainder, bitwise and/or/xor, left and right shifts, count-leading-zeros, less-than/less-or-equal/equality comparisons, load, store, allocation, and random-bit read. It has an explicit finite enumeration and decidable equality.
--
--   For any operation type $\kappa$, a cost vector is a function $c:\kappa\to\mathbb N$. When equality on $\kappa$ is decidable, the one-operation and repeated-operation vectors are $$e_o(a)=\begin{cases}1,&a=o,\\0,&a\ne o,\end{cases}\qquad e_{o,m}(a)=\begin{cases}m,&a=o,\\0,&a\ne o,\end{cases}$$ for $o,a\in\kappa$ and $m\in\mathbb N$. A rate assigns a positive integer $r(a)\ge1$ to every operation; the unit rate assigns one to all operations. When $\kappa$ is finite, the scalar charge of a tally is $$\operatorname{steps}_r(c)=\sum_{a\in\kappa}r(a)c(a).$$ The aliases Cost and CostModel specialize vectors and rates to $\mathcal O$.
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/Computation/Cost.lean#L43-L198

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
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
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
# The cost of a primitive operation

This module is the single place in the library where "an addition costs one" is
written down.  Everything in `Arlib.Computation` reduces to it.

The design has two halves, and keeping them apart is what makes an algorithm
readable.

* A **`Cost`** is a vector of operation counts — `Op → ℕ` — not a number.  A
  program's cost is therefore recorded in units of *what it did*, with no cost
  model in sight, which is why `Arlib.Computation.Machine`'s primitives take no
  cost-model argument and an algorithm mentions none.
* A **`CostModel`** turns that vector into a number, once, at the end, by
  `Cost.steps`.  This is the "resource currency" arrangement of [HL21]: the
  program accumulates abstract currencies and the exchange rate is applied last.

Every entry of a `CostModel` is at least one (`CostModel.one_le`).  Without that
field `fun _ => 0` would be a legal cost model under which every program is free,
and the area would ship a generator of the zero-cost non-algorithm it exists to
exclude.

## Main definitions

* `Op` — the primitive operations of the machine.
* `Cost` — a vector of operation counts.
* `CostModel` — a charge for each operation, everywhere at least one.
* `CostModel.unitCost` — the unit-cost RAM; every operation costs one.
* `Cost.steps` — the scalar cost of a `Cost` under a model.
-/

namespace Arlib.Computation

/-- The primitive operations of the machine.  This enumeration is the interface
of `Arlib.Computation.Machine`: a program is a composition of these and nothing
else, so a cost claim about a program is a claim about how many of each it
performs.

`mulHi` (the high half of a `w`-by-`w`-bit product) and `udiv` are present
because a polynomial hash needs `(a * x + b) % p` with `a, x < p ≤ 2 ^ w`, whose
product does not fit in a word.  `mul`, `mulHi`, `udiv`, the variable shifts and
`clz` are all outside `AC⁰`, so including them strengthens the model relative to
the instruction set usually assumed in the word-RAM literature; this is recorded
in the area root. -/
inductive Op
  | lit | add | sub | mul | mulHi | udiv | umod
  | band | bor | bxor | shl | shr | clz
  | lt | le | eq
  | load | store | alloc | randBit
  deriving DecidableEq, Repr, Inhabited

namespace Op

/-- Every operation, as a list.  `Fintype` is built from this rather than
derived, because the `deriving Fintype` handler does not elaborate against the
`Finset` API of this Mathlib revision. -/
def all : List Op :=
  [.lit, .add, .sub, .mul, .mulHi, .udiv, .umod,
   .band, .bor, .bxor, .shl, .shr, .clz,
   .lt, .le, .eq,
   .load, .store, .alloc, .randBit]

theorem mem_all (o : Op) : o ∈ all := by cases o <;> simp [all]

instance : Fintype Op := Fintype.ofList all mem_all



end Op

/-- A tally of work done, in a currency `κ`: how many times each operation of
`κ` was performed.

A *vector* rather than a number, so that a program accumulates what it did and
the price is applied afterwards (`CostVec.steps`).  Costs add, which is the whole
compositionality story: `RAM.cost_bind` is a consequence of the monad laws
rather than a rule anyone has to trust.

The currency is a parameter because the machine's word operations are not the
only unit anyone wants to count.  An algorithm stated over an abstract
dictionary is naturally charged in dictionary operations, and a *rate* between
currencies (`Rate.exchange`) is what converts one analysis into the other; this
is the arrangement of [HL21].  `Cost` below is the machine's instance. -/
abbrev CostVec (κ : Type) := κ → ℕ

/-- The machine's own currency: a tally of primitive word operations. -/
abbrev Cost := CostVec Op

namespace CostVec

variable {κ : Type} [DecidableEq κ]

/-- The cost of performing `o` once. -/
def one (o : κ) : CostVec κ := fun o' => if o' = o then 1 else 0

/-- The cost of performing `o` exactly `n` times. -/
def many (o : κ) (n : ℕ) : CostVec κ := fun o' => if o' = o then n else 0























end CostVec

/-- What each primitive operation costs.

Indexed by the operation only, never by its operands.  An operand-dependent
charge — so that a logarithmic-cost measure would be expressible — makes every
loop bound in the library underivable, because a loop's total is then a sum over
intermediate values that the bound does not know; collapsing it needs an upper
bound this structure would not carry.  A different cost measure is a different
type, not a different field shape.

`one_le` is not defensive.  Without it `⟨fun _ => 0, _⟩` is a legal model under
which every program is free. -/
structure Rate (κ : Type) where
  /-- The charge for one instance of `o`. -/
  cost : κ → ℕ
  /-- Every operation charges.  This is what makes `RAM.steps_pos` — and hence
  `Arlib.Approximation.IsFPRAS.Charges` for a program — a theorem. -/
  one_le : ∀ o, 1 ≤ cost o

/-- What each primitive *word* operation costs. -/
abbrev CostModel := Rate Op

namespace Rate

variable {κ : Type}

/-- Every operation costs one.  For the machine's currency this is the unit-cost
RAM, and `CostVec.steps_unit_le` shows it is the cheapest rate, so a caller may
supply their own table but not make a program look faster. -/
def unit (κ : Type) : Rate κ where
  cost := fun _ => 1
  one_le := fun _ => le_refl 1





end Rate

namespace CostModel

/-- The unit-cost RAM: every primitive word operation costs one step. -/
abbrev unitCost : CostModel := Rate.unit Op



end CostModel

namespace CostVec

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The scalar cost of `c` under the rate `R`: the number of steps. -/
def steps (C : Rate κ) (c : CostVec κ) : ℕ := ∑ o, C.cost o * c o






















end CostVec

end Arlib.Computation

end


