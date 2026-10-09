-- Prove2me | Definitions.Def_OnlineCRS_Matroid_Polytope
-- name    : OnlineCRS_Matroid_Polytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:22.785399+00:00
-- url     : https://prove2.me/theorems/fbe1c02a-85f2-418f-8de9-f4475f33ae1f
-- title:
--   The matroid independence and base polytopes
-- statement:
--   Let $M$ be a matroid on a finite ground set $N$, and let $r(S)$ be the maximum size of an independent subset of $S$. The **matroid independence polytope** and **base polytope** are
--   $$P_{\mathcal F}=\{x\in\mathbb R^N_{\ge0}:x(S)\le r(S)\text{ for every }S\subseteq N\},\qquad P_B=\{x\in P_{\mathcal F}:x(N)=r(N)\},$$
--   where $x(S)=\sum_{e\in S}x_e$.
--
--   These are the relaxation and its maximal vectors used in the matroid OCRS analysis. On a finite matroid the rank is a finite natural number, represented as a real number in the inequalities.
-- source:
--   arXiv:1508.00142v2, §2.1, p. 9; §2.1.1, p. 11; Appendix A, pp. 31–32

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics

namespace OnlineCRS.Matroid

/-- Appendix A, pp. 31–32: rank of a finite subset of a finite matroid, viewed as a real number. -/
noncomputable def rank {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) (S : Finset α) : ℝ := ((M.eRk (S : Set α)).toNat : ℝ)

/-- §2.1, p. 9: the matroid independence polytope `P_F`. -/
def matroidPolytope {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) : Set (α → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ ∀ S : Finset α, ∑ e ∈ S, x e ≤ rank M S}

/-- §2.1.1, p. 11: the base polytope `P_B`. -/
def basePolytope {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) : Set (α → ℝ) :=
  {x | x ∈ matroidPolytope M ∧ (∑ e : α, x e) = rank M Finset.univ}

end OnlineCRS.Matroid


