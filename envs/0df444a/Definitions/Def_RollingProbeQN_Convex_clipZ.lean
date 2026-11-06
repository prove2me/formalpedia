-- Prove2me | Definitions.Def_RollingProbeQN_Convex_clipZ
-- name    : RollingProbeQN_Convex_clipZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:00.572523+00:00
-- url     : https://prove2.me/theorems/7c5ed553-08d6-44b6-9a8f-a9aba694b3f5
-- title:
--   The eigenvalue clipping $\Pi_{\mathcal Z}$ to $[0,L_1]$
-- statement:
--   For a symmetric matrix $S=U\operatorname{diag}(s_1,\dots,s_d)U^\top$,
--
--   $$\Pi_{\mathcal Z}(S)=U\operatorname{diag}(\hat s_1,\dots,\hat s_d)U^\top,\qquad \hat s_i=\min\{\max\{s_i,0\},L_1\},$$
--
--   that is, $\Pi_{\mathcal Z}$ clips the eigenvalues of $S$ to $[0,L_1]$. It is the Frobenius projection onto $\mathcal Z$.
--
--   **Formalization Note** It is the functional calculus of the symmetric matrix applied to $t\mapsto\min\{\max\{t,0\},L_1\}$. The paper applies $\Pi_{\mathcal Z}$ to symmetric matrices only; on a non-symmetric matrix the Lean definition returns $0$, a value no statement uses.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, §2, p. 7; Lemma D.13, p. 42

import Mathlib

namespace RollingProbeQN.Convex

/-- **The clipping map `Π_Z`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, §2, p. 7: "the map `Π_Z` clips the eigenvalues of a symmetric matrix to `[0, L1]`";
Lemma D.13, p. 42: `Π_Z(S) = U diag(ŝ_1, …, ŝ_d) U^T` with `ŝ_i = min{max{s_i, 0}, L1}`.

**Formalization Note.** For a symmetric `M` this is the functional calculus of `M` applied to
`t ↦ min (max t 0) L₁` (reading R6). The paper applies `Π_Z` to symmetric matrices only; on a
non-symmetric matrix `clipZ` returns `0`, a value no statement of the mission uses. -/
noncomputable def clipZ {d : ℕ} (L₁ : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  open Classical in
  if hM : M.IsHermitian then hM.cfc (fun t => min (max t 0) L₁) else 0

end RollingProbeQN.Convex


