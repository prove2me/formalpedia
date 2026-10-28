-- Prove2me | Definitions.Def_CountingMatroidSupport_MarkovChains_Chains_Metropolis
-- name    : CountingMatroidSupport_MarkovChains_Chains_Metropolis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:05:44.370452+00:00
-- url     : https://prove2.me/theorems/ceeedcbf-69d4-4f7a-bf33-2650703498b9
-- title:
--   Metropolis rates and stochastic completion
-- statement:
--   In the project's local Markov-chain support library, let $\Omega$ be finite, let $\mu$ be a probability distribution, and let $Q$ be any proposal Markov chain. Define the rate, holding probability, and completed chain by
--   $$
--   a(x,y)=Q(x,y)\min\{1,\mu(y)/\mu(x)\},\qquad
--   h(x)=1-\sum_{y\ne x}a(x,y),\qquad
--   P(x,y)=
--   \begin{cases}h(x),&x=y,\\a(x,y),&x\ne y.\end{cases}
--   $$
--   Real division is totalized, so these definitions include states of zero $\mu$-mass. The supplied lemmas establish $0\le a(x,y)\le Q(x,y)$, $\sum_{y\ne x}a(x,y)\le1$, and $h(x)\ge0$. Hence $P$ is a stochastic chain without symmetry or strict-positivity assumptions. For each $x$ satisfying $\mu(x)>0$, the included rate identity is
--   $$
--   \mu(x)a(x,y)=Q(x,y)\min\{\mu(x),\mu(y)\}.
--   $$
--   This identity alone does not assert reversibility for an arbitrary nonsymmetric proposal. The declarations are local support code under the Arlib namespace.
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/MarkovChains/Chains/Metropolis.lean#L51-L54

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
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
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

namespace Arlib
end Arlib
section
/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Metropolis–Hastings chain

The general theory in `Arlib.MarkovChains.Techniques` is stated for a chain `P`
together with a distribution `μ` reversible for it.  This module supplies such
pairs.  Given an arbitrary *symmetric* proposal chain `Q` and an arbitrary
target `μ` of full support, the Metropolis construction manufactures a chain
that is reversible with respect to `μ`: propose a move `x → y` according to
`Q`, and accept it with probability `min 1 (μ y / μ x)`.  The acceptance ratio
is exactly what is needed to turn the symmetry of `Q` into detailed balance for
`μ`, because `μ x * min 1 (μ y / μ x) = min (μ x) (μ y)` is already symmetric
in `x` and `y`.  That one line is the whole idea; everything else is
bookkeeping to check that the resulting matrix is stochastic.

This is why the construction belongs in the `Chains/` half of the library: it
is the standard way to *produce* a reversible chain with a prescribed
stationary distribution, and hence the source of the objects the spectral
theory in `Techniques/` talks about.

* `mhRate` — the off-diagonal transition rate `Q x y * min 1 (μ y / μ x)`.
* `mhRate_nonneg`, `mhRate_le_proposal` — the two elementary bounds.
* `mhRate_detailed_balance` — `μ x * mhRate μ Q x y = Q x y * min (μ x) (μ y)`,
  the identity that does all the work.
* `mhStay` — the holding probability `1 - ∑ z ≠ x, mhRate μ Q x z`, together
  with `sum_erase_mhRate_le_one` and `mhStay_nonneg`.
* `metropolis` — the Metropolis chain itself, as a `FinChain Ω`.
* `metropolis_reversible` — **the main theorem**: for `μ` of full support and
  `Q` symmetric, `μ` satisfies detailed balance for `metropolis μ Q`.
* `metropolis_stationary` — the resulting stationarity statement.
* `uniformProposal` and `metropolis_uniform_reversible` — a concrete
  instantiation with the uniform proposal, to exhibit the interface in use.

Everything here is proved from first principles with no `sorry`.
-/


namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The acceptance rate -/

/-- The off-diagonal transition rate of the Metropolis chain: propose `y` with
probability `Q x y` and accept with probability `min 1 (μ y / μ x)`. -/
noncomputable def mhRate (μ : FinDist Ω) (Q : FinChain Ω) (x y : Ω) : ℝ :=
  Q x y * min 1 (μ y / μ x)

theorem mhRate_apply (μ : FinDist Ω) (Q : FinChain Ω) (x y : Ω) :
    mhRate μ Q x y = Q x y * min 1 (μ y / μ x) := rfl

/-- The Metropolis rate is a nonnegative number. -/
theorem mhRate_nonneg (μ : FinDist Ω) (Q : FinChain Ω) (x y : Ω) :
    0 ≤ mhRate μ Q x y :=
  mul_nonneg (Q.coe_nonneg x y)
    (le_min zero_le_one (div_nonneg (μ.coe_nonneg y) (μ.coe_nonneg x)))

/-- Rejection only removes mass: the Metropolis rate never exceeds the proposal
rate. -/
theorem mhRate_le_proposal (μ : FinDist Ω) (Q : FinChain Ω) (x y : Ω) :
    mhRate μ Q x y ≤ Q x y :=
  mul_le_of_le_one_right (Q.coe_nonneg x y) (min_le_left _ _)

/-- **Detailed balance.**  Multiplying the Metropolis rate by the target mass
at the source produces the symmetric expression `Q x y * min (μ x) (μ y)`.
This is the entire content of the construction. -/
theorem mhRate_detailed_balance {μ : FinDist Ω} (Q : FinChain Ω) {x : Ω} (y : Ω)
    (hx : 0 < μ x) : μ x * mhRate μ Q x y = Q x y * min (μ x) (μ y) := by
  have hdiv : μ x * (μ y / μ x) = μ y := by
    field_simp
  have hmin : μ x * min 1 (μ y / μ x) = min (μ x) (μ y) := by
    rw [mul_min_of_nonneg _ _ hx.le, mul_one, hdiv]
  calc μ x * mhRate μ Q x y = Q x y * (μ x * min 1 (μ y / μ x)) := by
        rw [mhRate_apply]; ring
    _ = Q x y * min (μ x) (μ y) := by rw [hmin]



/-! ## The holding probability -/

section Stay

variable [DecidableEq Ω]

/-- The holding probability of the Metropolis chain at `x`: whatever mass is
left over after all the off-diagonal moves. -/
noncomputable def mhStay (μ : FinDist Ω) (Q : FinChain Ω) (x : Ω) : ℝ :=
  1 - ∑ z ∈ univ.erase x, mhRate μ Q x z

/-- The total off-diagonal mass leaving `x` is at most `1`: each Metropolis
rate is dominated by the corresponding proposal rate, and the proposal rates
already sum to `1` over all of `univ`. -/
theorem sum_erase_mhRate_le_one (μ : FinDist Ω) (Q : FinChain Ω) (x : Ω) :
    ∑ z ∈ univ.erase x, mhRate μ Q x z ≤ 1 := by
  calc ∑ z ∈ univ.erase x, mhRate μ Q x z ≤ ∑ z ∈ univ.erase x, Q x z :=
        Finset.sum_le_sum fun z _ => mhRate_le_proposal μ Q x z
    _ ≤ ∑ z, Q x z :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun z _ _ => Q.coe_nonneg x z)
    _ = 1 := Q.sum_coe x

/-- The holding probability is nonnegative. -/
theorem mhStay_nonneg (μ : FinDist Ω) (Q : FinChain Ω) (x : Ω) :
    0 ≤ mhStay μ Q x :=
  sub_nonneg.mpr (sum_erase_mhRate_le_one μ Q x)

end Stay

/-! ## The Metropolis chain -/

section Chain

variable [DecidableEq Ω]

/-- The **Metropolis chain** built from a target `μ` and a proposal `Q`: move
off the diagonal at rate `mhRate μ Q x y`, and stay put with the remaining
probability `mhStay μ Q x`.

No hypotheses on `μ` or `Q` are needed for this to be a bona fide Markov
chain; positivity of `μ` and symmetry of `Q` enter only in
`metropolis_reversible`. -/
noncomputable def metropolis (μ : FinDist Ω) (Q : FinChain Ω) : FinChain Ω where
  P x y := if x = y then mhStay μ Q x else mhRate μ Q x y
  P_nonneg x y := by
    split
    · exact mhStay_nonneg μ Q x
    · exact mhRate_nonneg μ Q x y
  P_sum x := by
    have hoff : ∀ z ∈ univ.erase x,
        (if x = z then mhStay μ Q x else mhRate μ Q x z) = mhRate μ Q x z := by
      intro z hz
      exact if_neg (Ne.symm (Finset.ne_of_mem_erase hz))
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), Finset.sum_congr rfl hoff]
    rw [if_pos rfl, mhStay]
    ring

/-- Off the diagonal the Metropolis chain moves at the Metropolis rate. -/
theorem metropolis_apply_of_ne (μ : FinDist Ω) (Q : FinChain Ω) {x y : Ω}
    (h : x ≠ y) : metropolis μ Q x y = mhRate μ Q x y := if_neg h







end Chain

/-! ## A concrete instance: the uniform proposal -/

section Uniform

variable (Ω)
variable [Nonempty Ω]







variable {Ω}





end Uniform

end Arlib.MarkovChains

end


