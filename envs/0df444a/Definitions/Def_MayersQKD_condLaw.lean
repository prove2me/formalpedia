-- Prove2me | Definitions.Def_MayersQKD_condLaw
-- name    : MayersQKD_condLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:29.201789+00:00
-- url     : https://prove2.me/theorems/2acce1df-1551-4a75-bc16-50c9b83e54fe
-- title:
--   Conditional law on an event and the information $I(X;Y\mid A)$
-- statement:
--   For nonnegative weights on a finite sample space, the weight of an event $A$ is $\sum_{x\in A}\mathrm{wt}(x)$. When the weights are a probability law this is $\Pr(A)$. If $A$ has positive weight, the law of a random variable $g$ conditioned on $A$ is
--
--   $$
--   \Pr(g=a\mid A)=\frac{\Pr(A\wedge g=a)}{\Pr(A)} .
--   $$
--
--   The information $I(X;Y\mid A)$ is the mutual information, in bits, of the pair $(X,Y)$ under the law conditioned on $A$.
--
--   This is the meaning of the quantity $I(B;V\mid Pass=1\wedge C=1)$ of the goal: an information for a conditioned law, not an average over a conditioning variable.
--
--   **Formalization Note** On an event of weight $0$ the information is $0$ by convention; the goal multiplies it by $\Pr(Pass=1)$, and the paper does not define it there.
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §5, p.8

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_mutualInfo

namespace MayersQKD

open WildeQIT

open Classical in
/-- The total weight `∑_{x ∈ A} wt(x)` of an event `A` on a finite sample space. When `wt` is a
probability law this is `Pr(A)`. -/
noncomputable def mass {Ω : Type} [Fintype Ω] (wt : Ω → ℝ) (A : Ω → Prop) : ℝ :=
  ∑ x ∈ Finset.univ.filter A, wt x

theorem mass_nonneg {Ω : Type} [Fintype Ω] {wt : Ω → ℝ} (hw : ∀ x, 0 ≤ wt x) (A : Ω → Prop) :
    0 ≤ mass wt A := by
  classical exact Finset.sum_nonneg fun x _ => hw x

open Classical in
/-- The law of `g` under the weights `wt` conditioned on an event `A` of positive weight:
`Pr(g = a | A) = Pr(A ∧ g = a) / Pr(A)`. -/
noncomputable def condLaw {Ω α : Type} [Fintype Ω] [Fintype α] (wt : Ω → ℝ) (hw : ∀ x, 0 ≤ wt x)
    (A : Ω → Prop) (g : Ω → α) (hA : 0 < mass wt A) : FinDist α where
  prob a := mass wt (fun x => A x ∧ g x = a) / mass wt A
  nonneg a := div_nonneg (mass_nonneg hw _) hA.le
  sum_eq_one := by
    rw [← Finset.sum_div, div_eq_one_iff_eq hA.ne']
    unfold mass
    rw [← Finset.sum_fiberwise (Finset.univ.filter A) g wt]
    exact Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr (by ext x; simp [Finset.mem_filter]) fun _ _ => rfl

open Classical in
/-- Mayers, arXiv:quant-ph/9606003v1, §5, p.8: the mutual information `I(X; Y | A)` in bits, i.e.
the mutual information of the pair `(X, Y)` for the law conditioned on the event `A`.

**Formalization Note.** This is the information for the conditioned law, not an average over the
values of a conditioning variable. On an event of weight `0` the value is `0`; the paper only uses
it multiplied by `Pr(Pass = 1)` (see `MayersQKD.string_qot_security`). -/
noncomputable def condInfo {Ω α β : Type} [Fintype Ω] [Fintype α] [Fintype β] (wt : Ω → ℝ)
    (hw : ∀ x, 0 ≤ wt x) (A : Ω → Prop) (X : Ω → α) (Y : Ω → β) : ℝ :=
  if h : 0 < mass wt A then mutualInfo (condLaw wt hw A (fun x => (X x, Y x)) h) else 0

end MayersQKD


