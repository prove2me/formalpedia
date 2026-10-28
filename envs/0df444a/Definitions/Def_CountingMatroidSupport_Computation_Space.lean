-- Prove2me | Definitions.Def_CountingMatroidSupport_Computation_Space
-- name    : CountingMatroidSupport_Computation_Space
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:28:45.481996+00:00
-- url     : https://prove2.me/theorems/63ed384a-5820-46f6-a201-4ff20b2f7db4
-- title:
--   Sequential composition of abstract residency profiles
-- statement:
--   Let $\kappa_s$ be a type of resource-cell categories. A profile $p$ records integer-valued functions $n_p,h_p:\kappa_s\to\mathbb Z$, interpreted as net resource change and peak increase above the starting level. It includes the conditions $$0\le h_p(k),\qquad n_p(k)\le h_p(k)\qquad(k\in\kappa_s).$$ The specification views net and peak expose these two functions, and profiles are equal when both views agree.
--
--   The identity profile has $n_1(k)=h_1(k)=0$. Sequential composition is defined by $$n_{pq}(k)=n_p(k)+n_q(k),\qquad h_{pq}(k)=\max\{h_p(k),\ n_p(k)+h_q(k)\}.$$ The bundle supplies the resulting monoid structure, so composition is associative and the zero profile is a two-sided identity. Negative net changes represent resource release, while each peak remains nonnegative.
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/Computation/Space.lean#L131-L235

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
# Residency: the algebra of a resource that is given back

`Arlib.Computation.Cost` is the algebra of time.  A tally is a vector of counts,
tallies add, and `Charged.cost_bind` is a consequence of the monad's definition.
Everything about a running-time bound in this library is that commutative monoid
plus induction.

**Space is not that monoid, and this module is the one it is.**

A program that allocates a cell and frees it, twice, uses one cell, not two.  The
quantity that composes along `bind` is not the total but the *high-water mark*,
and a high-water mark is not a function of the totals of the parts.  It is,
however, still a monoid — over a pair:

```
(net₁, peak₁) ⋆ (net₂, peak₂) = (net₁ + net₂, max peak₁ (net₁ + peak₂))
```

`net` is the change in what is held and `peak` the largest excursion above the
starting level.  This is the resource-pair composition of the amortised-analysis
literature; see `docs/dev/Space-Modelling-Design.md` §1.1 for the references and
for why it is the right object.

## Why the two side conditions are fields

`Profile` carries `0 ≤ peak` and `net ≤ peak` as *fields*, not as lemmas about
the operation.  They are exactly what the two unit laws need — the first for
`1 * p = p`, the second for `p * 1 = p`, and associativity needs neither — so
bundling them makes the monoid laws hold on the nose and leaves no
well-formedness hypothesis to thread through every downstream lemma.

## Why `net` is an `ℤ`

Because it goes down.  [GCP18] abandoned `ℕ`-valued credits for exactly this
reason: truncated subtraction forces a nontrivial strengthening of every loop
invariant.  `docs/dev/Computation-ROADMAP.md` §13.3 records the lesson, and this
is the first module in the library that has to obey it.

## Why the monoid is not commutative

Because that is the content.  `free ⋆ alloc` peaks at zero and `alloc ⋆ free`
peaks at one.  Time's monoid is commutative, which is why a time analysis never
has to know the order in which a program does things and a space analysis always
does.

## Main definitions

* `Residency κₛ` — how many cells of each kind a value occupies.  **Sealed**: a
  program may build one and may never read one, because reading one is a free
  size query on its own data.
* `Profile κₛ` — the `(net, peak)` pair, with its `Monoid` instance.
* `Profile.between` — the profile of moving from one residency to another.  The
  only way to obtain a non-identity profile, and it takes two *measured*
  residencies rather than a number.

## Main results

* `Profile`'s `Monoid` instance — composition along `bind`.
* `net_le_peak_mul` — **every prefix's net is below the whole's peak.**  The
  lemma every residency argument goes through.
* `peak_foldProfiles_le` — **a loop that keeps itself below a ceiling stays below
  it, however long it runs.**  This is the lemma a real algorithm needs, and the
  one with no counterpart on the time side: residency is a property of the state,
  so an invariant can cap it, while time is cumulative and no invariant can.  A
  bound independent of the iteration count is what a streaming algorithm's space
  claim says, and a `+`-based analysis cannot state it.
* `peak_compose_le_of_net_nonpos`, `peak_compose_le` — the same for a loop
  described by its steps alone.  Weaker than they look: a body that only ever
  erases-then-reinserts still nets `+1` on a fresh item, so the first does not
  apply to CVM and the second gives `Θ(m)`.  They are general facts about lists
  of profiles, not the shape an algorithm's bound comes in.
* `le_peak_compose` — the lower bound, so a bound proved above is not a bound on
  a loop that does nothing.  For space this matters more than for time: the
  failure mode a space bound must exclude is exactly "the program stores
  nothing", which an upper bound alone permits.
-/

namespace Arlib.Computation

universe u

variable {κₛ : Type}

/-! ## Residency -/



namespace Residency









end Residency

/-! ## The profile -/

/-- **What a computation does to what is held**: the net change, and the largest
excursion above the level it started from.

The two side conditions are fields because the monoid laws need them: `0 ≤ peak`
is what `one_mul` needs and `net ≤ peak` is what `mul_one` needs.  Carrying them
here rather than as hypotheses is what keeps every downstream statement free of
well-formedness clutter.

Both views are `noncomputable`, so a program cannot read its own profile.  That
is not belt-and-braces: a profile is a function of how much data is held, which
is exactly what the data seal exists to hide, and `decide (p.net k = 1)` would be
a free membership test. -/
structure Profile (κₛ : Type) where
  private mk ::
  private netCells : κₛ → ℤ
  private peakCells : κₛ → ℤ
  private peak_nonneg' : ∀ k, 0 ≤ peakCells k
  private net_le_peak' : ∀ k, netCells k ≤ peakCells k

namespace Profile

/-- The net change in what is held.  **Specification-only.** -/
noncomputable def net (p : Profile κₛ) : κₛ → ℤ := p.netCells

/-- The largest excursion above the starting level.  **Specification-only.** -/
noncomputable def peak (p : Profile κₛ) : κₛ → ℤ := p.peakCells









/-- **A peak is never negative.**  One of the two facts the monoid needs. -/
theorem zero_le_peak (p : Profile κₛ) (k : κₛ) : 0 ≤ p.peak k := p.peak_nonneg' k

/-- **What is held at the end is no more than the peak.**  The other. -/
theorem net_le_peak (p : Profile κₛ) (k : κₛ) : p.net k ≤ p.peak k := p.net_le_peak' k

@[ext] theorem ext {p q : Profile κₛ} (hn : p.net = q.net) (hp : p.peak = q.peak) :
    p = q := by
  cases p; cases q; simp_all [net, peak]

/-- Holding still. -/
instance : One (Profile κₛ) :=
  ⟨⟨fun _ => 0, fun _ => 0, fun _ => le_refl 0, fun _ => le_refl 0⟩⟩

/-- **Composition along `bind`.**  The nets add; the peak is the first peak, or
the second peak displaced by what the first left behind — whichever is higher.

This is a definition, not an axiom, which is what makes the space of a composite
program a consequence of the space of its parts in the same way `cost_bind`
does for time. -/
instance : Mul (Profile κₛ) :=
  ⟨fun p q =>
    ⟨fun k => p.netCells k + q.netCells k,
     fun k => max (p.peakCells k) (p.netCells k + q.peakCells k),
     fun k => le_trans (p.peak_nonneg' k) (le_max_left _ _),
     fun k => le_trans (by have := q.net_le_peak' k; omega)
       (le_max_right (p.peakCells k) (p.netCells k + q.peakCells k))⟩⟩

@[simp] theorem net_mul (p q : Profile κₛ) (k : κₛ) :
    (p * q).net k = p.net k + q.net k := rfl

@[simp] theorem peak_mul (p q : Profile κₛ) (k : κₛ) :
    (p * q).peak k = max (p.peak k) (p.net k + q.peak k) := rfl

@[simp] theorem net_one (k : κₛ) : (1 : Profile κₛ).net k = 0 := rfl

@[simp] theorem peak_one (k : κₛ) : (1 : Profile κₛ).peak k = 0 := rfl

instance : Monoid (Profile κₛ) where
  mul_assoc p q r := by
    refine ext ?_ ?_
    · funext k; simp; omega
    · funext k; simp; omega
  one_mul p := by
    refine ext ?_ ?_
    · funext k; simp
    · funext k
      simp only [peak_mul, net_one, peak_one, zero_add]
      exact max_eq_right (p.zero_le_peak k)
  mul_one p := by
    refine ext ?_ ?_
    · funext k; simp
    · funext k
      simp only [peak_mul, peak_one, add_zero]
      exact max_eq_left (p.net_le_peak k)













end Profile

/-! ## Loops

`Cost-Modelling-Protocol.md` Phase 4 requires that a loop's cost come from a
combinator lemma once, rather than from each caller.  For time that lemma is
`Charged.steps_foldl_le`.  It does **not** transpose: `cost_foldl_eq`'s
hypothesis is that the price may depend on the element but not on how much the
accumulator has grown, and for space that is exactly false — the peak of a fold
is `maxᵢ (net_{<i} + peakᵢ)` by construction.

So space needs its own, and there are three. -/



namespace Profile











/-! ### The lemma a real algorithm needs

The three lemmas above are facts about lists of profiles, and for a real
algorithm they are the wrong shape.  CVM is the example: its arrival erases the
incoming item and conditionally reinserts it, so on a *fresh* accepted item the
erase is a no-op and the net is `+1`.  No hypothesis about a single step bounds
the run, and `peak_compose_le` gives `Θ(m)` — which is tight for that shape, so
strengthening its hypotheses does not help.

The reason CVM's space is bounded is not a property of its steps.  It is an
*invariant*: the body compares the sample against the threshold and thins when it
reaches it, so the residency after every step is at most `B`.  That is a
state-dependent fact, and this is the lemma that turns it into a bound.

`hstep` is the honest hypothesis — **from any state below the ceiling, the body's
excursion is at most the headroom** — and `hnet` is the exactness condition of
`docs/dev/Space-Modelling-Design.md`, which says the state's size really does
move by the profile's net. -/



variable {σ : Type u}









end Profile

end Arlib.Computation

end


