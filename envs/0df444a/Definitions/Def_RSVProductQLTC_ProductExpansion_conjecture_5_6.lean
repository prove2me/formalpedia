-- Prove2me | Definitions.Def_RSVProductQLTC_ProductExpansion_conjecture_5_6
-- name    : RSVProductQLTC_ProductExpansion_conjecture_5_6
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:35:59.143227+00:00
-- url     : https://prove2.me/theorems/edadd880-58d8-4220-91b2-eb338867eee7
-- title:
--   Conjecture 5.6 — uniform binary-extension product expansion
-- statement:
--   For every integer $r\ge2$, margin $0<\eta<1$, and balance $\beta\ge1$, the predicate asserts the existence of $\rho>0$ uniform over the following data. Let $E=\mathbb F_{2^e}$, take positive integers $m_i$ satisfying $2m_i\mid e$, and put $s_i=2^{m_i}$ and
--   $$S_i=\{x\in E^\times:x^{s_i+1}=1\}.$$
--   Require the $s_i+1$ to be pairwise coprime and $\max_i(s_i+1)\le\beta\min_i(s_i+1)$. For every degree tuple $d_i\ge0$ with $d_i+1\le(1-\eta)(s_i+1)$, the tuple of affine evaluation codes is $\rho$-product-expanding:
--   $$\bigl(\operatorname{RS}_{d_i}(S_i;E)\bigr)_{i=1}^{r}\text{ is }\rho\text{-product-expanding}.$$
--   Here $\operatorname{RS}_{d}$ uses polynomials of degree at most $d$. Product expansion is the finite axis-code decomposition inequality of Definition 5.5. This predicate is a research premise, not a theorem to be proved in this mission and not a premise asserting the existence of quantum codes.
--
--   **Formalization Note** The existential $\rho$ precedes $E,e,m_i,d_i$. All size and degree comparisons are real inequalities. The pairwise inequalities $s_i+1\le\beta(s_j+1)$ express the same maximum/minimum condition for this nonempty finite tuple. The published affine code has the degree-less-than convention, so its argument is $d_i+1$. The set of evaluation points is represented inside $E$, with nonzeroness explicit. Its cardinality $s_i+1$ follows from the field and divisibility data and is not an added hypothesis.
-- source:
--   Mitali Bafna, Anqi Li, Quynh T. Nguyen, STOC 2027 submission #1136 (October 2026), Definition 5.5 and Conjecture 5.6, printed p.20 (PDF p.21); affine RS convention in §5.4, printed p.19 (PDF p.20)

import Mathlib
import Definitions.Def_GoodQLTC_rsCode
import Definitions.Def_GoodQLTC_IsProductExpanding
set_option autoImplicit false
open Classical

namespace RSVProductQLTC.ProductExpansion

/-- The norm-one evaluation group of Conjecture 5.6, as a subset of the coefficient field. -/
def evaluationGroup {E : Type} [Field E] (m : ℕ) : Set E :=
  {x | x ≠ 0 ∧ x ^ (2 ^ m + 1) = 1}

/-- Conjecture 5.6, printed p.20 (PDF p.21).
The constant is uniform over all field, size, and degree data. `d+1` converts maximum
polynomial degree to the published affine RS dimension convention. -/
def conjecture_5_6 : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (η β : ℝ), 0 < η → η < 1 → 1 ≤ β →
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (E : Type) [Field E] [Fintype E] [CharP E 2] (e : ℕ),
        Fintype.card E = 2 ^ e →
        ∀ (m : Fin r → ℕ), (∀ i, 0 < m i ∧ 2 * m i ∣ e) →
          (∀ i j, i ≠ j → Nat.Coprime (2 ^ m i + 1) (2 ^ m j + 1)) →
          (∀ i j, ((2 ^ m i + 1 : ℕ) : ℝ) ≤ β * ((2 ^ m j + 1 : ℕ) : ℝ)) →
          ∀ (d : Fin r → ℕ),
            (∀ i, ((d i + 1 : ℕ) : ℝ) ≤ (1 - η) * ((2 ^ m i + 1 : ℕ) : ℝ)) →
              GoodQLTC.IsProductExpanding ρ
                (fun i => GoodQLTC.rsCode (evaluationGroup (E := E) (m i)) (d i + 1))

end RSVProductQLTC.ProductExpansion


