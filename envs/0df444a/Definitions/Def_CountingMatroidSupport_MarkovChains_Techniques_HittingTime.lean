-- Prove2me | Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
-- name    : CountingMatroidSupport_MarkovChains_Techniques_HittingTime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:07:02.049238+00:00
-- url     : https://prove2.me/theorems/a252c1e0-70b5-49ce-8034-4dcf4c86d01c
-- title:
--   Killed Markov operators and finite-horizon survival
-- statement:
--   This Arlib support bundle considers a Markov kernel $K$ on a finite state space $\Omega$ and a target set $T\subseteq\Omega$. Define the off-target indicator and killed operator by
--   $$u_0(x)=\mathbf1_{\{x\notin T\}},\qquad
--   (K_Tf)(x)=
--   \begin{cases}0&x\in T,\\ \sum_yK(x,y)f(y)&x\notin T.\end{cases}$$
--   The survival functions satisfy
--   $$u_{m+1}=K_Tu_m.$$
--   Thus $u_m(x)$ is the probability of avoiding $T$ at every time $0,\ldots,m$ when starting at $x$; a starting point already in $T$ has survival zero.
--
--   The bundle includes the defining equations, the bounds $0\leq u_0\leq1$, and proofs that the killed operator preserves nonnegativity and pointwise inequalities. It proves nonnegativity of every survival function, vanishing on $T$, and monotonicity in the horizon:
--   $$0\leq u_{m+1}(x)\leq u_m(x),\qquad
--   m\leq n\Longrightarrow u_n(x)\leq u_m(x).$$
--   The comparison follows by the order-preserving killed recursion and the row sums of the Markov kernel. No reversibility, stationarity, or tail-decay rate is assumed or asserted.
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/MarkovChains/Techniques/HittingTime.lean#L58-L60

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
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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

namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib
end Arlib
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
section
/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Hitting times of a finite Markov chain, without measure theory

The whole of this module is an elementary, purely algebraic account of the
question *"how long does a finite chain take to hit a set `T`?"*.  No trajectory
space, no σ-algebra and no measure is ever constructed: every statement is about
finite sums and one real series.

The single definition everything rests on is the **killed operator**

  `killed K T f x = 0` if `x ∈ T`, and `∑ y, K x y * f y` otherwise,

i.e. the one-step operator of `PotentialDecay` with the target set turned into a
graveyard.  Iterating it on the indicator of `Tᶜ` gives the **survival
probabilities**

  `survive K T n x = Pr_x[H_T > n]`,

which are the only probabilistic objects in the file.  They satisfy the
recursion that *defines* them, so no theorem is needed to connect them to a
trajectory measure — they are taken as the definition of the hitting-time law,
and every downstream statement is phrased in terms of them.

* `offTarget`, `killed`, `survive` — the three definitions.
* `survive_nonneg`, `survive_le_one`, `survive_eq_zero_of_mem`,
  `survive_antitone` — the basic shape of `n ↦ Pr_x[H_T > n]`.
* `killed_iterate_offTarget` / `survive_add` — `survive` *is* an iterate, which
  is what makes the next lemma available.
* `survive_add_le` — **submultiplicativity**: if `survive K T n ≤ c` off `T`,
  then `survive K T (m + n) ≤ c · survive K T m`.  This is the workhorse: it
  turns "the chain hits `T` with probability `≥ 1 - c` in `n` steps, from
  wherever it is" into geometric decay of the survival probabilities.
* `AlmostSureReach` — the specification: `Pr_x[H_T > n] → 0`.
* `EHT` — the **expected hitting time** `∑' n, Pr_x[H_T > n]`, the tail-sum
  formula taken as the definition, together with `HittingSummable` (the
  hypothesis under which that series means what it says).
* `EHT_recursion` — the one-step recursion `E_x[H_T] = 1 + ∑ y, K x y · E_y[H_T]`
  off the target, which is the form a *certificate* consumes.

Everything is proved from first principles with no `sorry`.
-/


namespace Arlib.MarkovChains

open scoped BigOperators
open Finset FinKernel

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## The killed operator and the survival probabilities -/

/-- The indicator of the complement of the target set: `1` off `T`, `0` on `T`.
This is `Pr_x[H_T > 0]`, the starting point of the survival recursion. -/
def offTarget (T : Finset Ω) : Ω → ℝ := fun x => if x ∈ T then 0 else 1

/-- The one-step operator **killed** on `T`: the chain is stopped (sent to a
graveyard of value `0`) as soon as it enters `T`. -/
def killed (K : FinChain Ω) (T : Finset Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => if x ∈ T then 0 else act K f x

/-- `survive K T n x` is `Pr_x[H_T > n]`, the probability that the chain started
at `x` has *not* visited `T` at any of the times `0, 1, …, n`.

This recursion is the definition, not a theorem: `Pr_x[H_T > 0] = 1` iff `x ∉ T`,
and `Pr_x[H_T > n+1] = ∑ y, K x y · Pr_y[H_T > n]` for `x ∉ T`. -/
def survive (K : FinChain Ω) (T : Finset Ω) : ℕ → Ω → ℝ
  | 0 => offTarget T
  | (n + 1) => killed K T (survive K T n)

omit [Fintype Ω] in
@[simp] theorem offTarget_apply (T : Finset Ω) (x : Ω) :
    offTarget T x = if x ∈ T then 0 else 1 := rfl

@[simp] theorem killed_apply (K : FinChain Ω) (T : Finset Ω) (f : Ω → ℝ) (x : Ω) :
    killed K T f x = if x ∈ T then 0 else act K f x := rfl

@[simp] theorem survive_zero (K : FinChain Ω) (T : Finset Ω) :
    survive K T 0 = offTarget T := rfl

@[simp] theorem survive_succ (K : FinChain Ω) (T : Finset Ω) (n : ℕ) :
    survive K T (n + 1) = killed K T (survive K T n) := rfl

theorem survive_succ_apply (K : FinChain Ω) (T : Finset Ω) (n : ℕ) (x : Ω) :
    survive K T (n + 1) x = if x ∈ T then 0 else ∑ y, K x y * survive K T n y := rfl

/-! ### Basic shape -/

omit [Fintype Ω] in
theorem offTarget_nonneg (T : Finset Ω) (x : Ω) : 0 ≤ offTarget T x := by
  simp only [offTarget]; split <;> norm_num

omit [Fintype Ω] in
theorem offTarget_le_one (T : Finset Ω) (x : Ω) : offTarget T x ≤ 1 := by
  simp only [offTarget]; split <;> norm_num

theorem killed_mono (K : FinChain Ω) (T : Finset Ω) {f g : Ω → ℝ} (h : ∀ y, f y ≤ g y)
    (x : Ω) : killed K T f x ≤ killed K T g x := by
  simp only [killed]; split
  · exact le_refl _
  · exact act_mono K h x

theorem killed_nonneg (K : FinChain Ω) (T : Finset Ω) {f : Ω → ℝ} (hf : ∀ y, 0 ≤ f y)
    (x : Ω) : 0 ≤ killed K T f x := by
  simp only [killed]; split
  · exact le_refl _
  · exact act_nonneg K f hf x



theorem survive_nonneg (K : FinChain Ω) (T : Finset Ω) (n : ℕ) (x : Ω) :
    0 ≤ survive K T n x := by
  induction n generalizing x with
  | zero => exact offTarget_nonneg T x
  | succ n ih => exact killed_nonneg K T (fun y => ih y) x



theorem survive_eq_zero_of_mem (K : FinChain Ω) (T : Finset Ω) (n : ℕ) {x : Ω}
    (hx : x ∈ T) : survive K T n x = 0 := by
  cases n with
  | zero => simp [hx]
  | succ n => simp [hx]



/-- The survival probabilities are nonincreasing in the horizon: `{H_T > n+1}`
is contained in `{H_T > n}`. -/
theorem survive_succ_le (K : FinChain Ω) (T : Finset Ω) (n : ℕ) (x : Ω) :
    survive K T (n + 1) x ≤ survive K T n x := by
  induction n generalizing x with
  | zero =>
      by_cases hx : x ∈ T
      · simp [hx]
      · rw [survive_succ, survive_zero, killed_apply, if_neg hx, offTarget_apply, if_neg hx]
        calc act K (offTarget T) x = ∑ y, K x y * offTarget T y := rfl
          _ ≤ ∑ y, K x y * 1 :=
              Finset.sum_le_sum fun y _ =>
                mul_le_mul_of_nonneg_left (offTarget_le_one T y) (K.coe_nonneg x y)
          _ = 1 := by rw [← Finset.sum_mul, K.sum_coe x, one_mul]
  | succ n ih => exact killed_mono K T (fun y => ih y) x

theorem survive_antitone (K : FinChain Ω) (T : Finset Ω) {m n : ℕ} (h : m ≤ n) (x : Ω) :
    survive K T n x ≤ survive K T m x := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact le_trans (survive_succ_le K T n x) ih

/-! ### `survive` as an iterate, and submultiplicativity -/













/-! ## Almost-sure reachability -/







/-! ## The expected hitting time -/













/-! ### The block decomposition

A uniform "hit within `n` steps with probability at least `1 - c`" bound turns
into a bound on the whole tail series, by grouping the times into blocks of
length `n`.  This is the one place the geometric series appears, and both
consumers — the completeness half of `RankingSupermartingale` and the
`p_min` bound of `ProgressPath` — go through it. -/











end Arlib.MarkovChains

end


