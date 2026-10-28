-- Prove2me | Definitions.Def_CountingMatroidSupport_Probability_FinDist
-- name    : CountingMatroidSupport_Probability_FinDist
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:02:32.13846+00:00
-- url     : https://prove2.me/theorems/724dec64-eafd-48f0-a3e1-34a72ae552e4
-- title:
--   Finite probability distributions and stochastic kernels
-- statement:
--   The project's local probability-support library defines a distribution on a finite type $\Omega$ as a real mass function $\mu$ with $\mu(x)\ge0$ and $\sum_x\mu(x)=1$. A kernel from a type $\alpha$ to a finite type $\beta$ is an array $K(x,y)\ge0$ with $\sum_yK(x,y)=1$ for each $x$; a finite Markov chain is the square case. Coercions expose these arrays as functions, with their nonnegativity and row-sum identities.
--
--   Kernel action and composition are
--   $$
--   (Kf)(x)=\sum_{y\in\beta}K(x,y)f(y),\qquad
--   (KL)(x,z)=\sum_{y\in\beta}K(x,y)L(y,z),
--   $$
--   where $f:\beta\to\mathbb R$ and $L$ has a finite target type. The identity kernel is $I(x,y)=\mathbf1_{\{x=y\}}$, and iterates satisfy $P^0=I$ and $P^{t+1}=PP^t$ for natural $t$.
--
--   For a distribution $\mu$ and a chain $P$ on $\Omega$, stationarity and reversibility mean respectively
--   $$
--   \sum_x\mu(x)P(x,y)=\mu(y),\qquad
--   \mu(x)P(x,y)=\mu(y)P(y,x).
--   $$
--   The included lemma proves that reversibility implies stationarity by summing detailed balance and using a row sum of one. These declarations are local support code under the Arlib namespace.
-- source:
--   https://github.com/meelgroup/arlib/blob/6262f60ad7556be62e94e87f6b5811cf299e7d94/Arlib/Probability/FinDist.lean#L41-L47

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

/-- A probability distribution on a finite type: a nonnegative mass function
summing to `1`. -/
structure FinDist (Ω : Type*) [Fintype Ω] where
  /-- The mass function. -/
  p : Ω → ℝ
  p_nonneg : ∀ x, 0 ≤ p x
  p_sum : ∑ x, p x = 1

namespace FinDist

variable {Ω : Type*} [Fintype Ω]

instance : CoeFun (FinDist Ω) (fun _ => Ω → ℝ) := ⟨FinDist.p⟩

@[simp] theorem coe_eq (μ : FinDist Ω) : (μ : Ω → ℝ) = μ.p := rfl

theorem coe_nonneg (μ : FinDist Ω) (x : Ω) : 0 ≤ μ x := μ.p_nonneg x













/-! ### The point mass -/

section Dirac

variable [DecidableEq Ω]





end Dirac

end FinDist

/-! ## Stochastic kernels -/

/-- A row-stochastic kernel from `α` to `β`: each row is a probability
distribution on `β`.  A Markov chain on `Ω` is the square case `FinKernel Ω Ω`
(see `FinChain`), but the rectangular case is genuinely needed for the up and
down operators of the local-to-global machinery. -/
structure FinKernel (α β : Type*) [Fintype β] where
  /-- The transition matrix. -/
  P : α → β → ℝ
  P_nonneg : ∀ x y, 0 ≤ P x y
  P_sum : ∀ x, ∑ y, P x y = 1

/-- A Markov chain on a finite state space. -/
abbrev FinChain (Ω : Type*) [Fintype Ω] := FinKernel Ω Ω

namespace FinKernel

variable {α β γ : Type*} [Fintype β]

instance : CoeFun (FinKernel α β) (fun _ => α → β → ℝ) := ⟨FinKernel.P⟩

@[simp] theorem coe_eq (K : FinKernel α β) : (K : α → β → ℝ) = K.P := rfl

theorem coe_nonneg (K : FinKernel α β) (x : α) (y : β) : 0 ≤ K x y := K.P_nonneg x y

theorem sum_coe (K : FinKernel α β) (x : α) : ∑ y, K x y = 1 := K.P_sum x

/-- The action of a kernel on functions: `(K f)(x) = ∑ y, K x y * f y`.
This is the "matrix times column vector" reading of `K`. -/
def act (K : FinKernel α β) (f : β → ℝ) : α → ℝ := fun x => ∑ y, K x y * f y

























/-- Composition of kernels: `(K ∘ₖ L)(x, z) = ∑ y, K x y * L y z`. -/
def comp [Fintype γ] (K : FinKernel α β) (L : FinKernel β γ) : FinKernel α γ where
  P x z := ∑ y, K x y * L y z
  P_nonneg x z := Finset.sum_nonneg fun y _ => mul_nonneg (K.coe_nonneg x y) (L.coe_nonneg y z)
  P_sum x := by
    rw [Finset.sum_comm]
    calc ∑ y, ∑ z, K x y * L y z = ∑ y, K x y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.mul_sum, L.sum_coe y, mul_one]
      _ = 1 := K.sum_coe x

@[inherit_doc] infixl:75 " ∘ₖ " => FinKernel.comp





/-- The identity kernel. -/
def id (Ω : Type*) [Fintype Ω] [DecidableEq Ω] : FinChain Ω where
  P x y := if x = y then 1 else 0
  P_nonneg x y := by split <;> norm_num
  P_sum x := by simp



/-- `t`-step iterate of a chain. -/
def iter {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (P : FinChain Ω) : ℕ → FinChain Ω
  | 0 => FinKernel.id Ω
  | (t + 1) => P ∘ₖ P.iter t

@[simp] theorem iter_zero {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (P : FinChain Ω) :
    P.iter 0 = FinKernel.id Ω := rfl





end FinKernel



/-! ## Stationarity and reversibility -/

variable {Ω : Type*} [Fintype Ω]

/-- `μ` is stationary for the chain `P`: `μ P = μ`. -/
def Stationary (μ : FinDist Ω) (P : FinChain Ω) : Prop :=
  ∀ y, ∑ x, μ x * P x y = μ y

/-- **Detailed balance.** `P` is reversible with respect to `μ`:
`μ(x) P(x, y) = μ(y) P(y, x)` for all `x, y`. -/
def Reversible (μ : FinDist Ω) (P : FinChain Ω) : Prop :=
  ∀ x y, μ x * P x y = μ y * P y x

/-- Detailed balance implies stationarity. -/
theorem Reversible.stationary {μ : FinDist Ω} {P : FinChain Ω} (h : Reversible μ P) :
    Stationary μ P := by
  intro y
  calc ∑ x, μ x * P x y = ∑ x, μ y * P y x := Finset.sum_congr rfl fun x _ => h x y
    _ = μ y := by rw [← Finset.mul_sum, P.sum_coe y, mul_one]



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

export Arlib.Probability.FinDist (p p_nonneg p_sum mk coe_eq coe_nonneg 
        )

end Arlib.MarkovChains.FinDist

namespace Arlib.MarkovChains.FinKernel

export Arlib.Probability.FinKernel (P P_nonneg P_sum mk coe_eq coe_nonneg sum_coe act
    
           comp
    id  iter iter_zero  )

end Arlib.MarkovChains.FinKernel

namespace Arlib.MarkovChains.Reversible

export Arlib.Probability.Reversible (stationary)

end Arlib.MarkovChains.Reversible

namespace Arlib.MarkovChains.Stationary



end Arlib.MarkovChains.Stationary

end


