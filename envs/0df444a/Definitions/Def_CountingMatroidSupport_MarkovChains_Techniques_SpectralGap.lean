-- Prove2me | Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
-- name    : CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:04:15.914843+00:00
-- url     : https://prove2.me/theorems/1552da8a-9f05-4ab8-bd81-135f1c5831e9
-- title:
--   Absolute spectral bound on mean-zero functions
-- statement:
--   In the project's local probability-support library, let $\Omega$ be finite, let $\mu$ be a probability distribution, let $P$ be a Markov chain, and let $c\in\mathbb R$. The predicate $\operatorname{AbsSpectralBound}(\mu,P,c)$ means
--   $$
--   \sum_x\mu(x)f(x)=0
--   \quad\Longrightarrow\quad
--   \left|\sum_x\mu(x)f(x)\sum_yP(x,y)f(y)\right|
--   \le c\sum_x\mu(x)f(x)^2
--   $$
--   for every real-valued function $f$ on $\Omega$. Thus it bounds the absolute quadratic form of the transition operator on mean-zero functions in the $\mu$-weighted inner product. The definition itself requires neither stationarity nor reversibility nor nonnegativity of $c$. This declaration is local support code under the Arlib namespace.
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/MarkovChains/Techniques/SpectralGap.lean#L62-L70

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
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.QuadraticDiscriminant
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
# From the spectral gap to decay of variance

The Poincaré inequality of `Arlib.MarkovChains.Techniques.Dirichlet` bounds the
quadratic form `⟪f, P f⟫_μ`.  What the mixing arguments actually need is a bound
on the *norm* `⟪P f, P f⟫_μ`, i.e. on `‖P‖` rather than on the numerical range.
Textbooks pass between the two through the spectral theorem for self-adjoint
operators.  We do not: the passage is an elementary variational argument, and
this module carries it out.

* `AbsSpectralBound μ P c` — `|⟪f, P f⟫_μ| ≤ c ⟪f, f⟫_μ` for every mean-zero
  `f`.  This is the *absolute* spectral gap in variational clothing: `c` plays
  the role of `λ* = max{λ₂, |λ_N|}`.
* `absSpectralBound_of_gap` — a positive semidefinite chain with spectral gap at
  least `γ` satisfies `AbsSpectralBound μ P (1 - γ)`.  PSD-ness is exactly what
  rules out the eigenvalue near `-1`, which is why the monograph notes that for
  the Glauber dynamics the gap and the absolute gap coincide.
* `ip_act_sq_le` — **the operator bound**: `AbsSpectralBound μ P c` upgrades to
  `⟪P f, P f⟫_μ ≤ c² ⟪f, f⟫_μ` on mean-zero `f`.  The proof evaluates the
  hypothesis at the two test functions `f ± t · P f`, subtracts (the `P²` terms
  cancel), and reads off the discriminant of the resulting nonnegative quadratic
  in `t` — the same discriminant trick that gives `psd_cauchy_schwarz`, and
  again no eigenvalue is involved.
* `Var_act_le`, `Var_iter_le` — `Var_μ(P^t f) ≤ c^{2t} Var_μ(f)`.
* `relDensity_push`, `chiSq_push_le`, `chiSq_iter_le` — the same decay
  transported to the χ²-divergence, which is the quantity that converts into a
  mixing-time bound: for a reversible chain the relative density evolves by the
  chain acting on functions, `ν P / μ = P (ν / μ)`, so `χ²` contracts by `c²` a
  step.

Everything here is proved from first principles with no `sorry`.
-/


namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The action of a kernel on an affine combination -/



/-! ## The absolute spectral bound -/

/-- `P` obeys the **absolute spectral bound** `c` with respect to `μ` when
`|⟪f, P f⟫_μ| ≤ c ⟪f, f⟫_μ` for every mean-zero `f`.

Restricting to mean-zero `f` is essential: on constants `P` acts as the identity,
so no bound better than `1` could ever hold on all of `L²(μ)`.  Mean-zero
functions are the invariant complement of the constants (`Ex_act_of_stationary`),
which is what makes the restriction legitimate. -/
def AbsSpectralBound (μ : FinDist Ω) (P : FinChain Ω) (c : ℝ) : Prop :=
  ∀ f : Ω → ℝ, Ex μ f = 0 → |ip μ f (P.act f)| ≤ c * ip μ f f





/-! ## The operator bound

The numerical-range bound `|⟪f, P f⟫| ≤ c ⟪f, f⟫` upgrades to the norm bound
`⟪P f, P f⟫ ≤ c² ⟪f, f⟫`.  Evaluate the hypothesis at `f + t · P f` and at
`f - t · P f` and subtract: the terms involving `P²` cancel, leaving

  `4 t ⟪P f, P f⟫ ≤ 2c ⟪f, f⟫ + 2c t² ⟪P f, P f⟫`  for every real `t`,

a nonnegative quadratic in `t` whose discriminant must be `≤ 0`. -/



/-! ## Decay of variance -/



section Iterate

variable [DecidableEq Ω]





end Iterate

/-! ## Decay of the χ²-divergence

Variance decay becomes a statement about *distributions* through the relative
density.  For a reversible chain the density of the pushed-forward distribution
is the chain acting on the density: `ν P / μ = P (ν / μ)`.  This is detailed
balance read in the other direction, and it is what makes `χ²` — a functional of
distributions — decay at the rate governing `L²(μ)` functions. -/





end Arlib.MarkovChains

end


