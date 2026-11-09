-- Prove2me | Definitions.Def_MoranYanPAC_Main_GoodFamily
-- name    : MoranYanPAC_Main_GoodFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:04:38.532344+00:00
-- url     : https://prove2.me/theorems/33037ead-b1ea-441c-be94-1b2e6757f819
-- title:
--   Good finite families and pointwise majority
-- statement:
--   Let $d\ge1$ be the fixed ambient dimension and $G$ a finite set of distinct binary predictors. Its pointwise majority $b_G$ chooses the label occurring more often, with ties toward zero. A nonempty $G$ is **good** if
--
--   $$\forall x\in X,\quad |\{g\in G:g(x)\ne b_G(x)\}|<\frac{|G|}{2(d+1)}.$$
--
--   The code uses the equivalent integer inequality after multiplying by the positive denominator. Good families have an unambiguous majority, so the total tie convention changes none of the source's instances. These families are the objects in Lemmas 5, 8 and 9; repeated training examples do not turn the family into a multiset.
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Section 7.2, p. 23 (PDF p. 23), paragraph before Lemma 8

import Mathlib

set_option autoImplicit false

namespace MoranYanPAC.Main

/-- Pointwise majority of distinct predictors; an irrelevant tie chooses zero. -/
noncomputable def majority {X : Type*} (G : Finset (X → Bool)) : X → Bool :=
  fun x => decide ((G.filter (fun h => h x = false)).card <
    (G.filter (fun h => h x = true)).card)

/-- Section 7.2, p. 23: good means nonempty and a strict pointwise minority
smaller than 1/[2(d+1)]. The multiplication form avoids division at an empty family. -/
def Good {X : Type*} (d : ℕ) (G : Finset (X → Bool)) : Prop :=
  G.Nonempty ∧ ∀ x : X,
    2 * (d + 1) * (G.filter (fun h => h x ≠ majority G x)).card < G.card

end MoranYanPAC.Main


