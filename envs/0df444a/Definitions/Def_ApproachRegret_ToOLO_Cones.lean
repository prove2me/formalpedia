-- Prove2me | Definitions.Def_ApproachRegret_ToOLO_Cones
-- name    : ApproachRegret_ToOLO_Cones
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:41:42.786536+00:00
-- url     : https://prove2.me/theorems/763af6a5-eba8-4df3-8bf7-832f1d1c10a7
-- title:
--   Euclidean lift, generated cone, and polar cone (Definition 11)
-- statement:
--   Let $E_d=\mathbb R^d$ with its Euclidean inner product. The lift $a\oplus x\in E_{d+1}$ puts $a$ in coordinate zero and the coordinates of $x$ after it. For a set $K\subseteq E_d$, its generated cone and, for a set $C\subseteq E_d$, its polar are
--
--   $$\operatorname{cone}(K)=\{\alpha x:\alpha\ge0,\ x\in K\},\qquad C^0=\{\theta:\langle\theta,x\rangle\le0\text{ for every }x\in C\}.$$
--
--   These are the geometric objects used by the reduction and the cone distance statements.
--
--   **Formalization Note** The lift carries the Euclidean norm, including $\|a\oplus x\|^2=a^2+\|x\|^2$. The polar uses nonpositive inner products; an empty $K$ has an empty generated cone.
-- source:
--   Abernethy, Bartlett, Hazan, Blackwell Approachability and No-Regret Learning are Equivalent, COLT 2011, JMLR W&CP 19, https://proceedings.mlr.press/v19/abernethy11b.html, Definition 11, p. 34 (PDF p. 8)

import Mathlib

open scoped RealInnerProductSpace

namespace ApproachRegret.ToOLO

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The paper's Euclidean concatenation `a ⊕ x`. -/
noncomputable def lift {d : ℕ} (a : ℝ) (x : E d) : E (d + 1) :=
  (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm (fun i => Fin.cases a (fun j => x j) i)

/-- Definition 11: nonnegative multiples of members of a set. -/
def cone {d : ℕ} (K : Set (E d)) : Set (E d) :=
  {z | ∃ (α : ℝ), 0 ≤ α ∧ ∃ x ∈ K, z = α • x}

/-- Definition 11: the negative polar cone. -/
def polar {d : ℕ} (C : Set (E d)) : Set (E d) :=
  {θ | ∀ x ∈ C, ⟪θ, x⟫ ≤ 0}

end ApproachRegret.ToOLO


