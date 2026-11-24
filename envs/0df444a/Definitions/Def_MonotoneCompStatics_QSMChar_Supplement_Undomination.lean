-- Prove2me | Definitions.Def_MonotoneCompStatics_QSMChar_Supplement_Undomination
-- name    : MonotoneCompStatics_QSMChar_Supplement_Undomination
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:07:44.819919+00:00
-- url     : https://prove2.me/theorems/edd07d94-8658-44a1-a79a-2f62fa21dcff
-- title:
--   Pure undomination, serial survivors, endpoint responses and interval hulls
-- statement:
--   For a set $T$ of opponent-compatible profiles define
--   $$U_i(T)=\{a\in S_i:\ \forall b\in S_i\ \exists x\in T,\ \pi_i(a,x_{-i})\ge\pi_i(b,x_{-i})\},\qquad U(T)=\prod_i U_i(T).$$
--   The serially undominated action sets are the greatest postfixed restriction of this simultaneous pure-elimination operator: $a\in R_i^{\infty}$ exactly when $a$ lies in some restriction $R_i$ with $R_j\subseteq U_j(\prod_k R_k)$ for all $j$. This is the stabilized transfinite iteration from the full action sets, rather than a fixed finite elimination depth. Pure alternatives range over the original $S_i$, as in the displayed definition of $U_i$.
--
--   Endpoint response profiles $b_*,b^*$ at $z$ are defined by actual least and greatest elements of each player's full best-response set. The interval hull is
--   $$\overline T=\{x:\ \exists l,u,\ l=\inf T,\ u=\sup T,\ l\le x\le u\}.$$
--   These definitions distinguish the possibly noninterval set $U(T)$ from its interval hull. **Formalization Note** All bounds are relational `IsGLB`/`IsLUB` and all response extrema are attained `IsLeast`/`IsGreatest`. Greatest postfixed restrictions implement unrestricted elimination without an arbitrary stopping date.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), DOI 10.2307/2951479, pp.175–176, PDF 20–21, serial undomination and response operators

import Mathlib
import Definitions.Def_MonotoneCompStatics_QSMChar_Supplement_NormalFormGame
import Definitions.Def_MonotoneCompStatics_Monotonicity_argmaxOn

namespace MonotoneCompStatics.QSMChar.Supplement

/-- Pure strategies not strictly dominated by any pure alternative against T. -/
def undominated {I : Type*} {S : I → Type*} (G : NormalFormGame I S)
    (T : Set ((i : I) → S i)) (i : I) : Set (S i) :=
  {a | ∀ b : S i, ∃ x ∈ T, G.payoff i b (opponents x i) ≤ G.payoff i a (opponents x i)}

def jointUndominated {I : Type*} {S : I → Type*} (G : NormalFormGame I S)
    (T : Set ((i : I) → S i)) : Set ((i : I) → S i) :=
  {x | ∀ i, x i ∈ undominated G T i}

/-- Greatest postfixed restriction of the simultaneous pure-elimination operator;
equivalently transfinite iteration from the full strategy spaces to stabilization.
All pure alternatives are tested, exactly as in the printed definition of U_n. -/
def serialActions {I : Type*} {S : I → Type*} (G : NormalFormGame I S) (i : I) : Set (S i) :=
  {a | ∃ R : (j : I) → Set (S j),
    (∀ j, R j ⊆ undominated G {x | ∀ k, x k ∈ R k} j) ∧ a ∈ R i}

def serialProfiles {I : Type*} {S : I → Type*} (G : NormalFormGame I S) :
    Set ((i : I) → S i) := {x | ∀ i, x i ∈ serialActions G i}

def EndpointResponses {I : Type*} {S : I → Type*} [∀ i, PartialOrder (S i)]
    (G : NormalFormGame I S) (z lo hi : (i : I) → S i) : Prop :=
  ∀ i,
    IsLeast (MonotoneCompStatics.Monotonicity.argmaxOn
      (fun a => G.payoff i a (opponents z i)) Set.univ) (lo i) ∧
    IsGreatest (MonotoneCompStatics.Monotonicity.argmaxOn
      (fun a => G.payoff i a (opponents z i)) Set.univ) (hi i)

def intervalHull {X : Type*} [PartialOrder X] (T : Set X) : Set X :=
  {x | ∃ lo hi, IsGLB T lo ∧ IsLUB T hi ∧ x ∈ Set.Icc lo hi}

end MonotoneCompStatics.QSMChar.Supplement


