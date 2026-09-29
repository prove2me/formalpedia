-- Prove2me | Definitions.Def_SunflowerSpread
-- name    : SunflowerSpread
-- status  : Definition
-- author  : @lunjia
-- created : 2026-09-26T15:52:12.62626+00:00
-- url     : https://prove2.me/theorems/ec6a6eb9-40ec-443f-ba8d-7a5e36836d15
-- title:
--   Spread families and links of finite set systems
-- statement:
--   Let $\mathcal F$ be a finite family of finite subsets of a ground type $\alpha$, and let $R$ be real. We record the normalized spread inequality in denominator-free form:
--
--   $$R^{|T|}\,|\{A\in\mathcal F:T\subseteq A\}|\le |\mathcal F|\qquad\text{for every finite }T.$$
--
--   When $R>1$ and $\mathcal F$ is nonempty, this says that a uniform random member contains each prescribed set $T$ with probability at most $R^{-|T|}$. The algebraic predicate also permits the empty family; results about choosing a random member state nonemptiness separately.
--
--   For a core $S$, its link is
--
--   $$\operatorname{link}(\mathcal F,S)=\{A\setminus S:A\in\mathcal F,\ S\subseteq A\}.$$
--
--   These definitions provide the interface for extracting a spread link and reconstructing a sunflower from disjoint members of that link. Families are represented by finsets, so their members are distinct.
-- source:
--   T. Tao, The sunflower lemma via Shannon entropy (2020), Definition 1 and Lemma 2, https://terrytao.wordpress.com/2020/07/20/the-sunflower-lemma-via-shannon-entropy/ ; L. Hu, Entropy Estimation via Two Chains (2021), Definition 1, https://theorydish.blog/2021/05/19/entropy-estimation-via-two-chains-streamlining-the-proof-of-the-sunflower-lemma/ . Denominator-free finite-family interface; nonemptiness stated separately.

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace Erdos20

/-- Denominator-free spread: at most a fraction `R⁻ᵗ` of the members contain
any prescribed `t`-element set. The family itself may be empty; applications
requiring a uniform random member explicitly assume nonemptiness. -/
def IsSpread {α : Type*} [DecidableEq α] (R : ℝ) (F : Finset (Finset α)) : Prop :=
  ∀ T : Finset α, R ^ T.card * ((F.filter (fun A => T ⊆ A)).card : ℝ) ≤ F.card

/-- The link at a core consists of members containing that core, with the
core removed. -/
def link {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  (F.filter (fun A => S ⊆ A)).image (fun A => A \ S)

end Erdos20


