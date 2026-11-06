-- Prove2me | Definitions.Def_PADMPriv_restrictedObj
-- name    : PADMPriv_restrictedObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:01.728025+00:00
-- url     : https://prove2.me/theorems/3fd3bd41-675c-416b-8070-13b00e60e7ef
-- title:
--   Restricted objective $J(u)=F(Vu)+g(U(c-u))$
-- statement:
--   For model (1) with $V = A^\top(AA^\top)^{-1}$ and $U = B^\top(BB^\top)^{-1}$, define
--   $$
--   J(u) := F(Vu) + g\big(U(c-u)\big),\qquad u\in\mathbb R^m,
--   $$
--   the objective of (1) restricted to feasible pairs in $\operatorname{range}(A^\top)\times\operatorname{range}(B^\top)$, parametrized by $u = Ax$.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), A.16, p.35

import Mathlib
import Definitions.Def_PADMPriv_pinvRight

namespace PADMPriv

/-- The objective of model (1) restricted to `range(Aᵀ) × range(Bᵀ)`, Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d),
A.16, p.35: `J(u) := F(Vu) + g(U(c − u))` with `V = Aᵀ(AAᵀ)⁻¹`, `U = Bᵀ(BBᵀ)⁻¹`. -/
noncomputable def restrictedObj {m p l : ℕ} (F : EuclideanSpace ℝ (Fin p) → ℝ)
    (g : EuclideanSpace ℝ (Fin l) → ℝ) (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m))
    (u : EuclideanSpace ℝ (Fin m)) : ℝ :=
  F (Matrix.toEuclideanLin (pinvRight A) u) + g (Matrix.toEuclideanLin (pinvRight B) (c - u))

end PADMPriv


