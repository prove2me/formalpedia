-- Prove2me | Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
-- name    : CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:03:37.274098+00:00
-- url     : https://prove2.me/theorems/c980a505-47fb-48f6-bcb4-245dfd85c282
-- title:
--   Dirichlet form, variational spectral gap, and nonnegative definiteness
-- statement:
--   This Arlib support bundle defines three analytic notions for a probability distribution $\mu$ on a finite state space $\Omega$ and a Markov kernel $P$. For real functions $f,g:\Omega\to\mathbb R$, write $\langle f,g\rangle_\mu=\sum_x\mu(x)f(x)g(x)$ and $(Pg)(x)=\sum_yP(x,y)g(y)$. The Dirichlet form is
--   $$\mathcal E_{\mu,P}(f,g)=\langle f,g\rangle_\mu-\langle f,Pg\rangle_\mu.$$
--   For a real number $\gamma$, the spectral-gap predicate means
--   $$\forall f,\qquad \gamma\,\operatorname{Var}_\mu(f)\leq\mathcal E_{\mu,P}(f,f).$$
--   The nonnegative-definiteness predicate means $\langle f,Pf\rangle_\mu\geq0$ for every real function $f$. These are variational definitions; stationarity and reversibility are not hypotheses of their definitions.
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/MarkovChains/Techniques/Dirichlet.lean#L51-L56

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
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
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
# The Dirichlet form, the Poincaré inequality, and positive semidefiniteness

Where `Var_μ(f)` measures the *global* variation of `f`, the Dirichlet form
`ℰ_P(f)` measures its *local* variation along the edges of the transition graph
`(Ω, P)`.  The entire mixing-time theory is the comparison of the two: a chain
mixes quickly exactly when local variation controls global variation, which is
the Poincaré inequality `γ · Var_μ(f) ≤ ℰ_P(f)`.

* `dirichlet μ P f g` — the bilinear form `⟪f, (I - P) g⟫_μ`; the Dirichlet form
  proper is the quadratic case `dirichlet μ P f f`.
* `sum_pair_sq` — the workhorse: for a *stationary* `μ` and any `s : ℝ`,
  `∑ x, ∑ y, μ x * P x y * (f x + s * f y) ^ 2 = (1 + s²)⟪f,f⟫ + 2s⟪f, Pf⟫`.
  Specialising to `s = -1` gives the pair form of the Dirichlet form, and to
  `s = 1` the lower bound `-⟪f,f⟫ ≤ ⟪f, Pf⟫`.  Both signs matter: one says the
  chain is a contraction, the other that it cannot overshoot.
* `dirichlet_self_eq_pair` — `ℰ_P(f) = ½ ∑_{x,y} μ(x) P(x,y) (f x - f y)²`, the
  paper's definition, here a theorem.
* `SpectralGapAtLeast μ P γ` — the Poincaré inequality.  Following the source
  monograph we take this *as* the definition of the spectral gap: for reversible
  chains it agrees with `1 - λ₂`, and for non-reversible ones it is the right
  notion anyway (the "Poincaré constant"), so no eigenvalue is ever needed.
* `NonnegDefinite μ P` — `0 ≤ ⟪f, P f⟫_μ` for all `f`, the PSD condition.  This
  is what upgrades the spectral gap to the *absolute* spectral gap, and hence
  what makes the gap control the decay of variance; see
  `Arlib.MarkovChains.Techniques.SpectralGap`.

The pay-off proved here is `ip_act_le_of_gap`: on a mean-zero function a chain
with gap `γ` which is PSD satisfies `|⟪f, P f⟫_μ| ≤ (1 - γ) ⟪f, f⟫_μ`, the
two-sided bound that drives everything downstream.

Everything here is proved from first principles with no `sorry`; in particular
no eigenvalue, and no spectral theorem, appears anywhere.
-/


namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The Dirichlet form -/

/-- The **Dirichlet form** as a bilinear form: `ℰ_P(f, g) = ⟪f, (I - P) g⟫_μ`.

The Dirichlet form of the monograph is the quadratic case `dirichlet μ P f f`,
for which `dirichlet_self_eq_pair` gives the familiar edge-sum expression. -/
def dirichlet (μ : FinDist Ω) (P : FinChain Ω) (f g : Ω → ℝ) : ℝ :=
  ip μ f g - ip μ f (P.act g)



/-! ## The pair expansion

Everything about the Dirichlet form flows from a single computation: expanding
`∑_{x,y} μ(x) P(x,y) (f x + s · f y)²` for a stationary `μ`.  The `f x²` term is
resummed with `∑_y P x y = 1`, the `f y²` term with stationarity, and the cross
term is `⟪f, P f⟫_μ` on the nose. -/







/-! ## Two-sided control of `⟪f, P f⟫_μ`

A stochastic kernel is a contraction on `L²(μ)`: taking `s = -1` above bounds
`⟪f, P f⟫_μ` from above by `⟪f, f⟫_μ`, and taking `s = 1` bounds it from below
by `-⟪f, f⟫_μ`.  These are the elementary substitutes for "all eigenvalues lie
in `[-1, 1]`". -/







/-! ## Symmetry and bilinearity -/











/-! ## The spectral gap -/

/-- **The Poincaré inequality**: the chain `P` has spectral gap at least `γ` with
respect to `μ` when `γ · Var_μ(f) ≤ ℰ_P(f)` for every `f`.

Following the source monograph, this *is* our definition of the spectral gap.
For a reversible chain it coincides with `1 - λ₂`, and for a non-reversible one
it is the Poincaré constant, which is the notion the mixing arguments actually
use.  Defining it variationally keeps the whole development free of eigenvalues. -/
def SpectralGapAtLeast (μ : FinDist Ω) (P : FinChain Ω) (γ : ℝ) : Prop :=
  ∀ f : Ω → ℝ, γ * Var μ f ≤ dirichlet μ P f f







/-! ## Positive semidefinite chains

A chain is *positive semidefinite* when `0 ≤ ⟪f, P f⟫_μ` for every `f` — the
elementary rendering of "all eigenvalues are nonnegative".  Heat-bath block
dynamics (in particular the Glauber dynamics) are PSD, and it is exactly this
that makes the spectral gap equal to the *absolute* spectral gap and hence makes
the gap control the decay of variance. -/

/-- `P` is **positive semidefinite** with respect to `μ`. -/
def NonnegDefinite (μ : FinDist Ω) (P : FinChain Ω) : Prop :=
  ∀ f : Ω → ℝ, 0 ≤ ip μ f (P.act f)



end Arlib.MarkovChains

end


