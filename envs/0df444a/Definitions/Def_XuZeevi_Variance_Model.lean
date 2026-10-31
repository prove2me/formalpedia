-- Prove2me | Definitions.Def_XuZeevi_Variance_Model
-- name    : XuZeevi_Variance_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:07:31.416218+00:00
-- url     : https://prove2.me/theorems/3af3c8dd-a8bb-429e-b5af-4500ac91d611
-- title:
--   Bounded learning problem, excess-loss class and excess risk
-- statement:
--   Let $H$ be the hypothesis class itself, $Z$ an arbitrary measurable observation space, $P$ its probability law, and $\ell:H\times Z\to\mathbb R$ the loss. The bounded learning predicate asserts $B>0$, measurability of each loss, $|\ell(h;z)|\le B$ for every $h,z$, and $P\ell(h^*;z)\le P\ell(h;z)$ for every $h$. Supplying $h^*:H$ already ensures nonemptiness. It imposes no geometric or cardinality condition.
--
--   The excess-loss class is exactly $F=\{z\mapsto\ell(h;z)-\ell(h^*;z):h\in H\}$, and the excess risk is $\mathcal E(h)=P\ell(h;z)-P\ell(h^*;z)$. Population and empirical risks are imported from the published risk definition. The optimal risk $L_0^*$ is $P\ell(h^*;z)$, not the paper's separate effective-loss parameter. The variance used below is that of $\ell(h^*;z)$, not that of its zero excess loss.
-- source:
--   Xu and Zeevi, arXiv:2011.06186v4, §1.1 p. 3, §3.1 pp. 8-9, (3.2) p. 9 (PDF pages equal printed pages)

import Definitions.Def_XuZeevi_Variance_Sampling

open MeasureTheory NatureSLT.Consistency

namespace XuZeevi.Variance

/-- Bounded statistical learning model, §1.1 and §3.1. The carrier H is the class itself. -/
def IsLearningProblem {H Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) (loss : H → Z → ℝ) (hstar : H) (B : ℝ) : Prop :=
  0 < B ∧ (∀ h, Measurable (loss h)) ∧ (∀ h z, |loss h z| ≤ B) ∧
    ∀ h, risk P loss hstar ≤ risk P loss h

/-- The class (3.2), with its actual zero member at hstar. -/
def excessClass {H Z : Type*} (loss : H → Z → ℝ) (hstar : H) : Set (Z → ℝ) :=
  Set.range (fun h z => loss h z - loss hstar z)

/-- Population excess risk from §1.1, not the effective loss L*. -/
noncomputable def excessRisk {H Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) (loss : H → Z → ℝ) (hstar h : H) : ℝ :=
  risk P loss h - risk P loss hstar

end XuZeevi.Variance


