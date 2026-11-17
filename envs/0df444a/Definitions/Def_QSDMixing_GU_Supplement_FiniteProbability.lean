-- Prove2me | Definitions.Def_QSDMixing_GU_Supplement_FiniteProbability
-- name    : QSDMixing_GU_Supplement_FiniteProbability
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:38:43.549615+00:00
-- url     : https://prove2.me/theorems/1b7c8c49-11d1-4b6b-a090-8c99f0c166ea
-- title:
--   Finite probability laws, convolution powers, and mixing times
-- statement:
--   A **finite probability law** on a finite set $\Omega$ is a function $p:\Omega\to\mathbb R_{\ge0}$ with total mass one. For a finite abelian group, the convolution power $p^{*t}$ is the law of a sum of $t$ independent $p$-distributed increments, with $p^{*0}$ the point mass at zero.
--
--   The file defines both the $\ell^1$ distance and total-variation distance, and defines the abelian mixing time as the least integer $t\ge1$ for which $p^{*t}$ is within the requested $\ell^1$ tolerance of the uniform law. Its value is $\infty$ if no time qualifies.
--
--   These definitions provide the classical probability layer used by Theorems 4--6.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), Theorems 4–6, pp.20–25, eqs. (19), (21)–(25)

import Mathlib

set_option autoImplicit false

namespace QSDMixing.GU.Supplement

noncomputable local instance probabilityWalkDecidableEq {α : Type} : DecidableEq α :=
  Classical.decEq α

/-- A probability mass function on a finite type, kept as real-valued data so the paper's
finite sums can be written literally. -/
structure FiniteProbability (α : Type) [Fintype α] where
  toFun : α → ℝ
  nonneg : ∀ x, 0 ≤ toFun x
  sum_one : ∑ x, toFun x = 1

instance {α : Type} [Fintype α] : CoeFun (FiniteProbability α) (fun _ => α → ℝ) :=
  ⟨FiniteProbability.toFun⟩

/-- The uniform mass function on a nonempty finite type. -/
noncomputable def uniformMass (α : Type) [Fintype α] : α → ℝ :=
  fun _ => 1 / (Fintype.card α : ℝ)

/-- The finite-space ℓ¹ distance used in Theorem 5. -/
noncomputable def l1Distance {α : Type} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ x, |p x - q x|

/-- Total variation distance on a finite space. -/
noncomputable def totalVariation {α : Type} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * l1Distance p q

/-- Convolution of two real mass functions on a finite additive group. -/
noncomputable def addConvolution {A : Type} [AddCommGroup A] [Fintype A]
    (p q : A → ℝ) (z : A) : ℝ :=
  ∑ x, p x * q (z - x)

/-- The law of a sum of `t` independent increments with common law `p`; at time zero it is
the point mass at zero. -/
noncomputable def convolutionPower {A : Type} [AddCommGroup A] [Fintype A]
    (p : A → ℝ) : ℕ → A → ℝ
  | 0 => fun z => if z = 0 then 1 else 0
  | t + 1 => addConvolution (convolutionPower p t) p

/-- The classical ℓ¹ mixing time of the abelian walk, with copy counts starting at one and
value `⊤` if no time qualifies. -/
noncomputable def abelianMixingTime {A : Type} [AddCommGroup A] [Fintype A]
    (p : A → ℝ) (ε : ℝ) : ℕ∞ :=
  sInf {T : ℕ∞ | ∃ t : ℕ, 1 ≤ t ∧ T = t ∧
    l1Distance (convolutionPower p t) (uniformMass A) ≤ ε}

end QSDMixing.GU.Supplement


