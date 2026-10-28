-- Prove2me | Definitions.Def_CountingMatroidSupport_Computation_Charged
-- name    : CountingMatroidSupport_Computation_Charged
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:31:22.87325+00:00
-- url     : https://prove2.me/theorems/233c9540-bfd5-41d5-9865-be5448ded790
-- title:
--   Computations carrying values, operation tallies, and space profiles
-- statement:
--   For an operation-label type $\kappa$, a storage-label type $\kappa_s$, and a value type $\alpha$, a charged computation stores a value in $\alpha$, an operation tally in the imported type $\mathrm{CostVec}(\kappa)$, and a space profile in the imported type $\mathrm{Profile}(\kappa_s)$. The projections expose these three components for specifications and analysis. Pure return has zero tally and the identity profile. Sequencing is defined by $$\operatorname{val}(p\mathbin{\gg=}f)=\operatorname{val}(f(\operatorname{val}(p))),$$ $$\operatorname{cost}(p\mathbin{\gg=}f)=\operatorname{cost}(p)+\operatorname{cost}(f(\operatorname{val}(p))),\qquad \operatorname{space}(p\mathbin{\gg=}f)=\operatorname{space}(p)\operatorname{space}(f(\operatorname{val}(p))).$$ Thus work tallies add and profiles compose in their imported monoid.
--
--   The bundle supplies the monad and its laws, extensional equality from equality of the three components, and the facts that pure mapping of a result leaves its tally and profile unchanged. For $o\in\kappa$, a primitive can return a supplied value with one charge at $o$, or with $m\in\mathbb N$ charges there; both have identity profile.
--
--   A list fold sequences charged steps and accumulates their tallies and profiles. Its early-stop variant executes a step returning an optional accumulator: a missing result stops the fold, retains the previous accumulator, and still includes the charge and profile of that final attempted step. The fixed-count and early-stop repetition operators are these folds over the indices $0,\ldots,m-1$.
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/Computation/Charged.lean#L91-L381

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
# Charged computation: the cost comes from the program

`Arlib.Computation.Machine` seals a word RAM, which is the right model when an
algorithm is written against words and memory.  Many algorithms are not: the
CVM distinct-elements estimator is written against a *set*, and the natural unit
of its running time is the container operation, not the machine word.

The temptation, when there is no machine, is to write the cost down beside the
program:

```
def stepCost (s : State) : CostVec Op := one .delete + one .insert   -- a claim
def step (s : State) : State := …                                    -- a program
```

Nothing relates the two.  `stepCost := 0` typechecks, every theorem downstream
still holds, and the running-time result is vacuous.  This is exactly the defect
`Arlib.Computation` exists to remove, and it is the one the Lean standard
algorithms library's `TimeM` records in its own docstring: its annotations are
trusted, not verified.

This module removes it without a machine.  `Charged κ κₛ α` is a value paired
with a tally, with a **private constructor**: the only ways to build one are
`pure` (free), `bind` (costs add), and `Charged.op` (one operation, one charge).
So a program's tally is not a claim its author writes; it is a function of the
program's text, computed by the elaborator.  Writing the wrong cost is not a
thing one can do — there is no place to write it.

## Two resources, one program

A computation carries a third field: a `Profile κₛ` recording what it does to
*what is held*, in the storage currency `κₛ`.  It is not a second object to be
related to the first — the accuracy theorem, the time theorem and the space
theorem are three operators applied to one `Charged` value.

The two resources compose differently and that is the content, not an accident.
Time is a commutative monoid under `+`; space is a `(net, peak)` pair whose
composition takes a `max`, is not commutative, and is the subject of
`Arlib.Computation.Space`.  `Charged.op` is space-neutral — a comparison is work
but not storage — and `Charged.opUpdate` is the one operation that changes what
is held.

## The hole this does not close

`pure` has the identity profile whatever its argument is, so `pure (x, x)` is
free and holds twice.  Space credits are *linear* where time credits are affine
([MP22], [MPV25]), and Lean is not a linear language; `Charged.val`'s
noncomputability blocks the only laundering syntax for time, and there is no
analogous block for holding a bound variable twice.  `ExactNet` below is the
obligation that fails on it, at proof time rather than silently.

## What this does and does not seal

`Charged` alone stops a program from *understating* a step it takes.  It does not
by itself stop `pure (expensiveThing x)`, because Lean will happily compute
`expensiveThing` for free.  That gap is closed the way `Machine.lean` closes it:
by sealing the *data*.  `Arlib.Computation.Roster` is the instance of that for
finite sets — its contents are private and its `Finset` view is
`noncomputable`, so outside its own module the only thing one can do with a
roster is call a charged operation on it.  The two modules together are what
make "the cost is computed from the process" true rather than aspirational.

## Main definitions

* `Charged κ κₛ α` — a value, the tally of work that produced it, and what it
  did to what is held.
* `Charged.op` — one operation of the currency, with its result.  Space-neutral.
* `Charged.opUpdate` — the one operation that changes what is held.
* `Charged.foldl` — bounded iteration, with the cost of the whole fold.
* `Charged.steps` — the time operator.
* `Charged.space` — the space operator.  `noncomputable`, unlike `cost`.
* `Charged.ExactNet` — the linearity obligation, and the hypothesis of every
  space bound.
* `Charged.residency_le_peak_of_prefix` — what is held at any point of a program
  is below its peak.
-/

namespace Arlib.Computation

universe u v

/-- A value, together with the tally of work that produced it.

The constructor is `private`, so outside this module a `Charged` value can only
be built by `pure`, `bind` and `Charged.op`.  That is the whole point: the cost
of a program is then determined by which operations it performs, and there is no
syntax for asserting a cost independently of the program that incurs it. -/
structure Charged (κ κₛ : Type) (α : Type u) where
  private mk ::
  private value : α
  private tally : CostVec κ
  private prof : Profile κₛ

namespace Charged

variable {κ κₛ : Type} {α β γ : Type u}

/-- The value a computation produced.  **Specification-only.**

Noncomputable for the same reason as `Word.toNat`, and it is the same hole it
closes: `val` were it computable would make `pure p.val` a copy of `p` that costs
nothing, so any program could erase its own charges.  A program gets at a result
by *binding*, which pays. -/
noncomputable def val (p : Charged κ κₛ α) : α := p.value

/-- What a computation cost, as a tally of operations.

Computable, unlike `val`, because execution tests read a tally — but **an
algorithm may not read it**.  `Roster.cost_filterErase` equates a thinning pass's
tally to `d.card`, so `(filterErase …).cost coin` is a free cardinality and
`pure (decide (… = thr))` a zero-cost `cardEq`.  What closes that is the seal:
`Charged.cost` is on `forbiddenInProgram`, and the scan is transitive, so
`Charged.steps` and anything built on it is caught without being named.  See
`docs/dev/Space-Modelling-Design.md` §0.2–§0.3. -/
def cost (p : Charged κ κₛ α) : CostVec κ := p.tally

/-- **What a computation does to what is held**: the net change in residency, and
the largest excursion above the level it started from.

`noncomputable`, and unlike `cost` this one the compiler enforces.  A profile is
a function of how much data is held, which is exactly what the data seal exists
to hide: given a computable projection, `decide (p.space.net k = 1)` after an
insertion is a free membership test, and every container in a development
becomes transparent. -/
noncomputable def space (p : Charged κ κₛ α) : Profile κₛ := p.prof









@[ext] theorem ext {p q : Charged κ κₛ α} (hv : p.val = q.val) (hc : p.cost = q.cost)
    (hs : p.space = q.space) : p = q := by
  cases p; cases q; simp_all [val, cost, space]

/-- Producing a value that was already to hand costs nothing. -/
protected def pure (a : α) : Charged κ κₛ α := ⟨a, 0, 1⟩

/-- Running `p` and then `f` on its result.  **Costs add** — and this is a
definition, not an axiom, which is what makes the cost of a composite program a
consequence of the costs of its parts. -/
protected def bind (p : Charged κ κₛ α) (f : α → Charged κ κₛ β) : Charged κ κₛ β :=
  ⟨(f p.value).value, p.tally + (f p.value).tally, p.prof * (f p.value).prof⟩

instance : Monad (Charged κ κₛ) where
  pure := Charged.pure
  bind := Charged.bind

@[simp] theorem val_pure (a : α) : (pure a : Charged κ κₛ α).val = a := rfl

@[simp] theorem cost_pure (a : α) : (pure a : Charged κ κₛ α).cost = 0 := rfl

/-- **Producing a value already to hand holds nothing new.**  Note what this does
*not* say: `pure a` has the identity profile whatever `a` is, so `pure (x, x)` is
free.  That is the one hole a shallow embedding over persistent data cannot
close, and `ExactNet` below is what fails on it. -/
@[simp] theorem space_pure (a : α) : (pure a : Charged κ κₛ α).space = 1 := rfl

@[simp] theorem val_bind (p : Charged κ κₛ α) (f : α → Charged κ κₛ β) :
    (p >>= f).val = (f p.val).val := rfl

/-- **The cost of a sequence is the sum of the costs.**  A consequence of the
monad's definition, so no author has to be trusted about it. -/
@[simp] theorem cost_bind (p : Charged κ κₛ α) (f : α → Charged κ κₛ β) :
    (p >>= f).cost = p.cost + (f p.val).cost := rfl

/-- **What a sequence holds is what its parts hold, composed.**

Not a sum.  `Profile`'s multiplication takes the first peak, or the second peak
displaced by what the first left behind — whichever is higher — which is why
the space of a composite program is a consequence of the space of its parts
without being their total.  Like `cost_bind`, a consequence of the monad's
definition rather than a rule anyone has to trust. -/
@[simp] theorem space_bind (p : Charged κ κₛ α) (f : α → Charged κ κₛ β) :
    (p >>= f).space = p.space * (f p.val).space := rfl

@[simp] theorem val_map (f : α → β) (p : Charged κ κₛ α) : (f <$> p).val = f p.val := rfl

/-- Post-processing a result is free.  It performs no operation, so there is
nothing for it to charge. -/
@[simp] theorem cost_map (f : α → β) (p : Charged κ κₛ α) : (f <$> p).cost = p.cost := by
  show p.cost + (0 : CostVec κ) = p.cost
  simp

/-- **Post-processing holds nothing new** — and this is a hazard, not a comfort.

For time it is the whole story: `f` cannot manufacture work.  For space it can
manufacture *data*: `(fun n => (n, n)) <$> p` has `p`'s profile and holds twice
as much.  The lemma is true and it is the reason `ExactNet.map` below carries a
hypothesis instead of being a corollary. -/
@[simp] theorem space_map (f : α → β) (p : Charged κ κₛ α) : (f <$> p).space = p.space := by
  show p.prof * (1 : Profile κₛ) = p.prof
  simp

/-- The monad laws still hold, and the third field is why `mul_one`, `one_mul`
and `mul_assoc` for `Profile` are needed: with two fields `id_map` was `rfl`, and
with three it is not, because `p.prof * 1` is not definitionally `p.prof`. -/
instance : LawfulMonad (Charged κ κₛ) := LawfulMonad.mk'
  (id_map := by
    intro α x
    exact ext rfl (by simp) (by simp)
  )
  (pure_bind := by
    intro α β x f
    exact ext rfl (by simp) (by simp)
  )
  (bind_assoc := by
    intro α β γ x f g
    exact ext rfl (by simp [add_assoc]) (by simp [mul_assoc])
  )

/-- **One operation of the currency, and what it returns.**

This is the only way to spend.  A charged interface — a roster, a sampler, a
priority queue — is built by giving each of its operations as `op o result`, and
the cost of any program written against that interface is then whatever sequence
of operations it performs. -/
def op [DecidableEq κ] (o : κ) (a : α) : Charged κ κₛ α := ⟨a, CostVec.one o, 1⟩







/-- `n` instances of the operation `o` at once.  For an operation whose price is
genuinely proportional to a length that the program already knows. -/
def opMany [DecidableEq κ] (o : κ) (n : ℕ) (a : α) : Charged κ κₛ α := ⟨a, CostVec.many o n, 1⟩







/-! ## The operation that changes what is held -/









/-! ## Iteration -/

/-- Fold a charged step over a list, accumulating both the value and the cost.

Iteration is a combinator rather than general recursion for the same reason as
`Arlib.Computation.iterate`: the cost of a loop is then something one lemma
delivers, rather than something each caller re-derives. -/
def foldl {α : Type v} {β : Type u} (f : β → α → Charged κ κₛ β) :
    List α → β → Charged κ κₛ β
  | [], b => ⟨b, 0, 1⟩
  | a :: l, b =>
      let p := f b a
      let q := foldl f l p.value
      ⟨q.value, p.tally + q.tally, p.prof * q.prof⟩

variable {ι : Type v}













/-! ### Iteration with a `Break`

A bounded loop that can stop early — the `Break` of a Karp–Luby estimator when a
sample list runs out, and every "stop as soon as" line of a paper's pseudocode.

Writing it as a `foldl` with a flag in the accumulator would keep running the
body and pay for it; writing it outside the fold makes the realised round count
a second definition alongside the program, which is the defect this area exists
to remove.  Here the round count *is* the fold: the loop stops when the body
declines to continue, and its tally stops with it. -/

/-- Fold a charged step over a list, **stopping as soon as a step returns
`none`**.  Both the value and the cost stop with it. -/
def foldlWhile {α : Type v} {β : Type u} (f : β → α → Charged κ κₛ (Option β)) :
    List α → β → Charged κ κₛ β
  | [], b => ⟨b, 0, 1⟩
  | a :: l, b =>
      let p := f b a
      match p.value with
      | none => ⟨b, p.tally, p.prof⟩
      | some b' =>
          let q := foldlWhile f l b'
          ⟨q.value, p.tally + q.tally, p.prof * q.prof⟩







/-- **Run `f` a fixed number of times, stopping early if it declines.**

The list `foldlWhile` folds over is the loop's own round index, generated here
rather than read off anything: `Arlib.Computation.Num.iterateWhile` is what
supplies `n` from a number the algorithm computed, and this is the piece that
does not need to see it. -/
def repeatWhile {β : Type u} (f : ℕ → β → Charged κ κₛ (Option β)) (n : ℕ) (b : β) :
    Charged κ κₛ β :=
  foldlWhile (fun b r => f r b) (List.range n) b

/-- **Run `f` a fixed number of times.** -/
def repeatFor {β : Type u} (f : ℕ → β → Charged κ κₛ β) (n : ℕ) (b : β) :
    Charged κ κₛ β :=
  foldl (fun b r => f r b) (List.range n) b









/-! ## The time operator -/

variable [Fintype κ]

/-! ## Changing currency -/



































/-! ## What is held, and the obligation that makes the peak mean something

A `Profile` composes correctly whatever a program does.  That its `net` is
*really* the change in what the program holds is a separate fact, and it is not
automatic: `pure (x, x)` has net zero and holds twice.

`ExactNet` is that fact, stated as a proposition.  It is the linearity discipline
that AARA and the space-credit separation logics get from linear types, which
Lean does not have — so here it is discharged per development rather than
provided by the framework.  Saying otherwise would claim a guarantee this module
has not got.

It is **heterogeneous** in the value's type, because a real program's step takes
a roster and returns a state record; a version fixing one type cannot be
stated for the program it is meant to be about.

Note what `ExactNet` does *not* audit: both sides are computed from the measures
handed to it, so a measure that reports zero satisfies it. It audits the
*program*, not the measure. What audits a measure is a theorem relating each
operation's profile to a specification view of the data — `Roster.space_insert` and
its siblings. Neither substitutes for the other. -/

section ExactNet

variable {κ κₛ : Type} {R S T : Type u} {ι : Type v}



















end ExactNet

end Charged

end Arlib.Computation

end


