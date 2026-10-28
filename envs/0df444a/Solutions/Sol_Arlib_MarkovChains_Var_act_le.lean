-- Prove2me | solution 1 for Arlib.MarkovChains.Var_act_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:36:16.998414+00:00
-- url     : https://prove2.me/submissions/96677f1b-f8db-4c5c-aae5-744ca088e8ba

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
import Theorems.Thm_Arlib_MarkovChains_ip_act_sq_le

namespace Arlib
end Arlib
section
/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Finite Markov chains: kernels, stationarity, reversibility

The basic objects of the spectral-independence development, in the form used
throughout: everything is finite and everything stays in `ℝ`.

* `FinDist Ω` — a probability distribution on a finite type.
* `FinKernel α β` — a row-stochastic matrix from `α` to `β`.  Deliberately
  *rectangular*: the up/down operators of the local-to-global machinery move
  between different level types, and it is much less painful to have one notion
  covering both them and ordinary chains.
* `FinChain Ω := FinKernel Ω Ω` — a Markov chain.
* `FinKernel.act` — the action `(P f)(x) = ∑ y, P x y * f y` on functions,
  which is the form in which transition matrices are actually used below.
* `FinKernel.push` — the action `(ν P)(y) = ∑ x, ν x * P x y` on distributions.
* `FinKernel.row` — the `x`-th row of a kernel, i.e. the law of one step started
  at `x`, packaged as a `FinDist`.
* `FinDist.dirac` and `FinKernel.push_dirac` — the point mass, and the identity
  `K.push δ_x = K.row x` that reconciles the two ways of saying "started at
  `x`".
* `Stationary`, `Reversible` — the two standing hypotheses of the theory.

`Reversible.stationary` records that detailed balance implies stationarity.

Everything here is proved from first principles with no `sorry`.
-/


namespace Arlib.Probability

open scoped BigOperators
open Finset

/-! ## Distributions on a finite type -/



namespace FinDist

variable {Ω : Type*} [Fintype Ω]







theorem sum_coe (μ : FinDist Ω) : ∑ x, μ x = 1 := μ.p_sum

theorem sum_coe_mul_const (μ : FinDist Ω) (c : ℝ) : ∑ x, μ x * c = c := by
  rw [← Finset.sum_mul, μ.sum_coe, one_mul]









/-! ### The point mass -/

section Dirac

variable [DecidableEq Ω]





end Dirac

end FinDist

/-! ## Stochastic kernels -/





namespace FinKernel

variable {α β γ : Type*} [Fintype β]













@[simp] theorem act_const (K : FinKernel α β) (c : ℝ) :
    K.act (fun _ => c) = fun _ => c := by
  funext x; simp only [act, ← Finset.sum_mul, K.sum_coe x, one_mul]



theorem act_sub (K : FinKernel α β) (f g : β → ℝ) :
    K.act (fun y => f y - g y) = fun x => K.act f x - K.act g x := by
  funext x
  simp only [act, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem act_sub_const (K : FinKernel α β) (f : β → ℝ) (c : ℝ) :
    K.act (fun y => f y - c) = fun x => K.act f x - c := by
  have := K.act_sub f (fun _ => c)
  simpa [K.act_const c] using this



































end FinKernel



/-! ## Stationarity and reversibility -/

variable {Ω : Type*} [Fintype Ω]









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

export Arlib.Probability (FinDist FinKernel FinChain  Stationary Reversible)

end Arlib.MarkovChains

namespace Arlib.MarkovChains.FinDist

export Arlib.Probability.FinDist (p p_nonneg p_sum mk coe_eq coe_nonneg sum_coe
  sum_coe_mul_const      )

end Arlib.MarkovChains.FinDist

namespace Arlib.MarkovChains.FinKernel

export Arlib.Probability.FinKernel (P P_nonneg P_sum mk coe_eq coe_nonneg sum_coe act
   act_const 
  act_sub act_sub_const        comp
    id  iter iter_zero  )

end Arlib.MarkovChains.FinKernel

namespace Arlib.MarkovChains.Reversible

export Arlib.Probability.Reversible (stationary)

end Arlib.MarkovChains.Reversible

namespace Arlib.MarkovChains.Stationary



end Arlib.MarkovChains.Stationary

end

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





@[simp] theorem Ex_const (μ : FinDist Ω) (c : ℝ) : Ex μ (fun _ => c) = c :=
  μ.sum_coe_mul_const c



theorem Ex_sub (μ : FinDist Ω) (f g : Ω → ℝ) :
    Ex μ (fun x => f x - g x) = Ex μ f - Ex μ g := by
  simp only [Ex, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring





theorem Ex_sub_const (μ : FinDist Ω) (f : Ω → ℝ) (c : ℝ) :
    Ex μ (fun x => f x - c) = Ex μ f - c := by
  rw [Ex_sub, Ex_const]













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



















/-! ### Explicit bilinearity

`isBilin_ip` states bilinearity in terms of `Pi` addition and scalar
multiplication.  Most computations downstream are much smoother with the
arguments written as explicit lambdas, so we record that form too. -/











/-! ## Variance -/



theorem Var_apply (μ : FinDist Ω) (f : Ω → ℝ) :
    Var μ f = ∑ x, μ x * (f x - Ex μ f) ^ 2 := rfl



/-- `Var_μ(f) = ⟪f, f⟫_μ - (μ f)²`. -/
theorem Var_eq_ip_sub_sq (μ : FinDist Ω) (f : Ω → ℝ) :
    Var μ f = ip μ f f - (Ex μ f) ^ 2 := by
  have key : ∀ x, μ x * (f x - Ex μ f) ^ 2
      = μ x * f x * f x - 2 * Ex μ f * (μ x * f x) + (Ex μ f) ^ 2 * μ x := by
    intro x; ring
  rw [Var_apply, Finset.sum_congr rfl fun x _ => key x]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [μ.sum_coe]
  simp only [ip, Ex, mul_one]
  ring



/-- Variance is unchanged by subtracting a constant. -/
theorem Var_sub_const (μ : FinDist Ω) (f : Ω → ℝ) (c : ℝ) :
    Var μ (fun x => f x - c) = Var μ f := by
  simp only [Var, Ex_sub_const]
  exact Finset.sum_congr rfl fun x _ => by ring_nf





/-- On a mean-zero function, variance is the squared `L²(μ)` norm. -/
theorem Var_eq_ip_self_of_mean_zero {μ : FinDist Ω} {f : Ω → ℝ} (h : Ex μ f = 0) :
    Var μ f = ip μ f f := by
  rw [Var_eq_ip_sub_sq, h]; ring

/-- The *centering* of `f`: `f - μ(f)`.  Has mean zero and the same variance. -/
theorem Ex_center (μ : FinDist Ω) (f : Ω → ℝ) : Ex μ (fun x => f x - Ex μ f) = 0 := by
  rw [Ex_sub_const]; ring







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

export Arlib.Probability.FinDist (Ex  Ex_const  Ex_sub   Ex_sub_const
        Ex_act_of_stationary
  ip        
       Var Var_apply 
  Var_eq_ip_sub_sq  Var_sub_const   Var_eq_ip_self_of_mean_zero
  Ex_center      
      )

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



/-! ## Decay of variance -/

/-- **One-step variance contraction.**  `Var_μ(P f) ≤ c² Var_μ(f)`.

Note that no mean-zero hypothesis is needed: the chain commutes with centering
(`act_sub_const`), and both variance and the operator bound are insensitive to
adding a constant. -/
theorem solution {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P) {c : ℝ}
    (hc : AbsSpectralBound μ P c) (f : Ω → ℝ) :
    Var μ (P.act f) ≤ c ^ 2 * Var μ f := by
  have hst : Stationary μ P := hrev.stationary
  set g : Ω → ℝ := fun x => f x - Ex μ f with hg
  have hg0 : Ex μ g = 0 := Ex_center μ f
  have hPg : P.act g = fun x => P.act f x - Ex μ f := P.act_sub_const f (Ex μ f)
  have hPg0 : Ex μ (P.act g) = 0 := by rw [Ex_act_of_stationary hst, hg0]
  have h1 : Var μ (P.act f) = ip μ (P.act g) (P.act g) := by
    rw [← Var_eq_ip_self_of_mean_zero hPg0, hPg, Var_sub_const]
  have h2 : Var μ f = ip μ g g := by
    rw [← Var_eq_ip_self_of_mean_zero hg0, hg, Var_sub_const]
  rw [h1, h2]
  exact ip_act_sq_le hrev hc hg0
