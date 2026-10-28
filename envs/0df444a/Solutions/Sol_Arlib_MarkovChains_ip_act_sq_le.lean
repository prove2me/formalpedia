-- Prove2me | solution 1 for Arlib.MarkovChains.ip_act_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:04:46.854039+00:00
-- url     : https://prove2.me/submissions/265d6db3-bbdc-43df-9e10-086005173acc

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
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
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
# The `L²(μ)` functional calculus: expectation, inner product, variance

The functional-analytic side of the spectral-independence machinery is carried
out entirely in `L²(μ)` for a distribution `μ` on a finite type.  This module
sets up the three functionals used everywhere downstream and the identities
relating them.

* `Ex μ f` — expectation `∑ x, μ x * f x`.
* `ip μ f g` — inner product `⟪f, g⟫_μ = ∑ x, μ x * f x * g x`.
* `Var μ f` — variance `μ((f - μ(f))²)`.

The key identities, all elementary algebra over a finite sum:

* `Var_eq_ip_sub_sq` — `Var μ f = ⟪f, f⟫_μ - (μ f)²`;
* `Var_eq_pair` — the *pair form* `Var μ f = ½ ∑ x, ∑ y, μ x * μ y * (f x - f y)²`,
  which is what makes variance directly comparable to a Dirichlet form;
* `Var_eq_ip_self_of_mean_zero` — on mean-zero functions variance *is* the
  squared norm, which is why almost every proof below starts by centering `f`.

We also record that `ip μ` is a positive semidefinite symmetric bilinear form
(`isBilin_ip`, `ip_comm`, `ip_self_nonneg`), so that `psd_cauchy_schwarz` from
`Arlib.Probability.Bilinear` applies to it directly, together with the
lambda-form bilinearity lemmas (`ip_add_left`, `ip_smul_right`, …) that the
computations downstream actually rewrite with.

Two families of "support only" lemmas are here because *every* guarded-total
construction in the development produces a junk value off the support of the
averaging distribution: `Ex_congr_ae`, `Var_congr_ae` and `Ex_mono_of_ne_zero`
say that expectations, variances and their monotonicity see only the support.

Finally, `Ex_push_eq` and `ip_push_eq` transport `Ex` and `ip` along a
*rectangular* kernel; they involve no stationarity and are the bookkeeping that
makes the law of total variance (`Arlib.MarkovChains.Techniques.LevelVariance`)
a three-line
computation.

Everything here is proved from first principles with no `sorry`.
-/


namespace Arlib.Probability

open scoped BigOperators
open Finset

namespace FinDist

variable {Ω : Type*} [Fintype Ω]

/-! ## Expectation -/







theorem Ex_add (μ : FinDist Ω) (f g : Ω → ℝ) :
    Ex μ (fun x => f x + g x) = Ex μ f + Ex μ g := by
  simp only [Ex, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring





theorem Ex_smul (μ : FinDist Ω) (c : ℝ) (f : Ω → ℝ) :
    Ex μ (fun x => c * f x) = c * Ex μ f := by
  simp only [Ex, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring















/-- Stationarity says exactly that the chain preserves expectations. -/
theorem Ex_act_of_stationary {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P)
    (f : Ω → ℝ) : Ex μ (P.act f) = Ex μ f := by
  simp only [Ex, FinKernel.act]
  calc ∑ x, μ x * ∑ y, P x y * f y
      = ∑ x, ∑ y, μ x * P x y * f y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ y, ∑ x, μ x * P x y * f y := Finset.sum_comm
    _ = ∑ y, μ y * f y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_mul, h y]

/-! ## Inner product -/







theorem ip_self_nonneg (μ : FinDist Ω) (f : Ω → ℝ) : 0 ≤ ip μ f f :=
  Finset.sum_nonneg fun x _ => by
    have : μ x * f x * f x = μ x * (f x) ^ 2 := by ring
    rw [this]; exact mul_nonneg (μ.coe_nonneg x) (sq_nonneg _)











/-! ### Explicit bilinearity

`isBilin_ip` states bilinearity in terms of `Pi` addition and scalar
multiplication.  Most computations downstream are much smoother with the
arguments written as explicit lambdas, so we record that form too. -/











/-! ## Variance -/



























/-! ## Pushforwards

Two bookkeeping identities for a *rectangular* kernel `K : α → β`, both plain
`Finset.sum_comm`.  They are what makes the law of total variance a three-line
computation. -/

section Push

variable {α β : Type*} [Fintype α] [Fintype β]





end Push

/-! ## χ²-divergence -/













end FinDist

end Arlib.Probability

/-! ## Compatibility: the `Arlib.MarkovChains` spellings

These declarations used to live in `namespace Arlib.MarkovChains` (in
`Arlib/MarkovChains/Techniques/{Chain,Bilinear,Functional,TotalVariation,Coupling}.lean`).
They are not Markov-chain-specific and now live in `Arlib.Probability`.  The
aliases below reproduce the old fully-qualified names exactly, so that every
`Arlib/MarkovChains/**` module keeps resolving them unchanged.  New code should
use the `Arlib.Probability` names directly; this block can be deleted once the
`Arlib.MarkovChains` call sites have been migrated. -/

namespace Arlib.MarkovChains

export Arlib.Probability.FinDist (Ex   Ex_add   Ex_smul 
        Ex_act_of_stationary
  ip   ip_self_nonneg     
       Var  
       
        
      )

end Arlib.MarkovChains

end

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

/-- `⟪f, P g⟫_μ = ∑_x ∑_y μ(x)·P(x,y)·f(x)·g(y)`: the inner product against the
action of a kernel, written so that the detailed-balance cell `μ(x)·P(x,y)`
occurs as a subterm. -/
theorem ip_act_eq_sum_sum (μ : FinDist Ω) (P : FinChain Ω) (f g : Ω → ℝ) :
    ip μ f (P.act g) = ∑ x, ∑ y, μ x * P x y * (f x * g y) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [FinKernel.act, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **Reversibility is exactly self-adjointness**: `⟪f, P g⟫_μ = ⟪g, P f⟫_μ`. -/
theorem ip_act_comm {μ : FinDist Ω} {P : FinChain Ω} (h : Reversible μ P) (f g : Ω → ℝ) :
    ip μ f (P.act g) = ip μ g (P.act f) := by
  rw [ip_act_eq_sum_sum μ P f g, ip_act_eq_sum_sum μ P g f, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [h x y]; ring







/-! ## The spectral gap -/









/-! ## Positive semidefinite chains

A chain is *positive semidefinite* when `0 ≤ ⟪f, P f⟫_μ` for every `f` — the
elementary rendering of "all eigenvalues are nonnegative".  Heat-bath block
dynamics (in particular the Glauber dynamics) are PSD, and it is exactly this
that makes the spectral gap equal to the *absolute* spectral gap and hence makes
the gap control the decay of variance. -/





end Arlib.MarkovChains

end

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

/-- The action of a kernel on an explicit affine combination. -/
theorem FinKernel.act_add_smul (P : FinChain Ω) (f g : Ω → ℝ) (s : ℝ) :
    P.act (fun x => f x + s * g x) = fun x => P.act f x + s * P.act g x := by
  funext x
  show ∑ y, P x y * (f y + s * g y) = _
  have step : ∀ y : Ω, P x y * (f y + s * g y) = P x y * f y + s * (P x y * g y) :=
    fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => step y, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

/-! ## The absolute spectral bound -/







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
end Arlib.MarkovChains
open Arlib Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The action of a kernel on an affine combination -/



/-! ## The absolute spectral bound -/







/-! ## The operator bound

The numerical-range bound `|⟪f, P f⟫| ≤ c ⟪f, f⟫` upgrades to the norm bound
`⟪P f, P f⟫ ≤ c² ⟪f, f⟫`.  Evaluate the hypothesis at `f + t · P f` and at
`f - t · P f` and subtract: the terms involving `P²` cancel, leaving

  `4 t ⟪P f, P f⟫ ≤ 2c ⟪f, f⟫ + 2c t² ⟪P f, P f⟫`  for every real `t`,

a nonnegative quadratic in `t` whose discriminant must be `≤ 0`. -/

/-- **The operator bound.**  If `P` is reversible with respect to `μ` and obeys
the absolute spectral bound `c ≥ 0`, then `⟪P f, P f⟫_μ ≤ c² ⟪f, f⟫_μ` for every
mean-zero `f`. -/
theorem solution {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P) {c : ℝ}
    (hc : AbsSpectralBound μ P c) {f : Ω → ℝ} (hf : Ex μ f = 0) :
    ip μ (P.act f) (P.act f) ≤ c ^ 2 * ip μ f f := by
  have hst : Stationary μ P := hrev.stationary
  have hPf0 : Ex μ (P.act f) = 0 := by rw [Ex_act_of_stationary hst, hf]
  -- The test functions `f + s · P f` are mean-zero for every `s`.
  have hu0 : ∀ s : ℝ, Ex μ (fun x => f x + s * P.act f x) = 0 := by
    intro s
    rw [Ex_add, Ex_smul, hf, hPf0]; ring
  -- Self-adjointness lets `⟪f, P² f⟫` be rewritten as `⟪P f, P f⟫`.
  have hcross : ip μ f (P.act (P.act f)) = ip μ (P.act f) (P.act f) :=
    ip_act_comm hrev f (P.act f)
  have hquad : ∀ s : ℝ,
      ip μ (fun x => f x + s * P.act f x) (fun x => f x + s * P.act f x)
        = ip μ f f + 2 * s * ip μ f (P.act f) + s ^ 2 * ip μ (P.act f) (P.act f) := by
    intro s
    have key : ∀ x : Ω, μ x * (f x + s * P.act f x) * (f x + s * P.act f x)
        = μ x * f x * f x + 2 * s * (μ x * f x * P.act f x)
          + s ^ 2 * (μ x * P.act f x * P.act f x) := fun x => by ring
    simp only [ip]
    rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hbil : ∀ s : ℝ,
      ip μ (fun x => f x + s * P.act f x) (P.act (fun x => f x + s * P.act f x))
        = ip μ f (P.act f) + 2 * s * ip μ (P.act f) (P.act f)
          + s ^ 2 * ip μ (P.act f) (P.act (P.act f)) := by
    intro s
    have expand : ip μ (fun x => f x + s * P.act f x) (P.act (fun x => f x + s * P.act f x))
        = ip μ f (P.act f) + s * ip μ f (P.act (P.act f)) + s * ip μ (P.act f) (P.act f)
          + s ^ 2 * ip μ (P.act f) (P.act (P.act f)) := by
      rw [FinKernel.act_add_smul]
      have key : ∀ x : Ω,
          μ x * (f x + s * P.act f x) * (P.act f x + s * P.act (P.act f) x)
          = μ x * f x * P.act f x + s * (μ x * f x * P.act (P.act f) x)
            + s * (μ x * P.act f x * P.act f x)
            + s ^ 2 * (μ x * P.act f x * P.act (P.act f) x) := fun x => by ring
      simp only [ip]
      rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum]
    rw [expand, hcross]; ring
  -- The key inequality, valid for every real `t`.
  have hkey : ∀ t : ℝ, 4 * t * ip μ (P.act f) (P.act f)
      ≤ 2 * c * ip μ f f + 2 * c * t ^ 2 * ip μ (P.act f) (P.act f) := by
    intro t
    have h1 := hc _ (hu0 t)
    have h2 := hc _ (hu0 (-t))
    rw [hbil t, hquad t] at h1
    rw [hbil (-t), hquad (-t)] at h2
    have a1 := (abs_le.mp h1).2
    have a2 := (abs_le.mp h2).1
    nlinarith [a1, a2]
  have hq : ∀ t : ℝ, 0 ≤ (2 * c * ip μ (P.act f) (P.act f)) * (t * t)
      + (-4 * ip μ (P.act f) (P.act f)) * t + 2 * c * ip μ f f := by
    intro t; nlinarith [hkey t]
  have hdisc := discrim_le_zero hq
  simp only [discrim] at hdisc
  rcases lt_or_eq_of_le (ip_self_nonneg μ (P.act f)) with hN | hN
  · have h2 : ip μ (P.act f) (P.act f) * ip μ (P.act f) (P.act f)
        ≤ (c ^ 2 * ip μ f f) * ip μ (P.act f) (P.act f) := by nlinarith [hdisc]
    exact le_of_mul_le_mul_right h2 hN
  · rw [← hN]
    exact mul_nonneg (sq_nonneg c) (ip_self_nonneg μ f)
