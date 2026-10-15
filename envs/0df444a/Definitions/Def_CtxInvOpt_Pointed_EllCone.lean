-- Prove2me | Definitions.Def_CtxInvOpt_Pointed_EllCone
-- name    : CtxInvOpt_Pointed_EllCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:11:49.230466+00:00
-- url     : https://prove2.me/theorems/5d2ebf50-527e-43a4-b559-3c5bcb7b3ed4
-- title:
--   Definitions 3–4, p. 17; §4.2, p. 15; (12), p. 19 — ellipsoidal cones E(W, U), effective difference, update test
-- statement:
--   Let $d=m+1\ge 2$, let $W=\operatorname{diag}(w_1,\dots,w_m)$ with $w_i>0$ (an element of $\mathbb D^{d-1}_{++}$) and let $U\in\mathbb R^{d\times d}$ be orthonormal. For $c\in\mathbb R^d$ write $\tilde c=U^{-1}c=U'c$ and split it as $\tilde c=(\tilde c_{[1]},\tilde c_{[2:d]})$.
--
--   1. The **ellipsoidal cone** (Definitions 3–4) is
--   $$E(W,U)=\Big\{c\in\mathbb R^d:\ \tilde c_{[1]}\ge 0,\ \ \tilde c_{[2:d]}'\,W^{-1}\,\tilde c_{[2:d]}\le \tilde c_{[1]}^2\Big\};$$
--   for $U=I$ this is the standard-position cone $E(W)$, whose axis is $e_1$. The axis of $E(W,U)$ is $Ue_1$, the first column of $U$, which is its circumcenter.
--   2. $\lambda_{\max}(W)=\max_i w_i$.
--   3. The **effective difference** (§4.2) of $u=f_t(x)-f_t(x^\star_t)$ is $\delta=u/\|u\|$, with $\delta=0$ if $u=0$.
--   4. The quantity of the update test (12) is $\bar\delta_{[2:d]}'\,W\,\bar\delta_{[2:d]}$ for $\bar\delta=U^{-1}\delta$.
--
--   These are the state and the cut vector of the EllipsoidalCones algorithm.
--
--   **Formalization Note** $W$ is stored as its diagonal $w$; $U^{-1}$ is written $U^\top$, which equals $U^{-1}$ for the orthonormal $U$ every statement assumes. Coordinate $0$ of $\tilde c$ is the paper's $[1]$, coordinate $i+1$ is the paper's $[i+2]$. The cone is defined for any $w$; statements assume $w>0$.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 15 (effective difference), p. 17 Definitions 3–4, p. 19 (12)

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry

namespace CtxInvOpt.Pointed

open Matrix

/-- **Definition 4, p. 17.** The coordinates `U⁻¹c` of a cost vector `c ∈ ℝ^{m+1}` in the frame of the
orthonormal matrix `U` (for orthonormal `U`, `U⁻¹ = Uᵀ`). Coordinate `0` is the paper's `[1]`, and
coordinate `Fin.succ i` is the paper's `[i+2]`. -/
noncomputable def rotCoord {m : ℕ} (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (c : EuclideanSpace ℝ (Fin (m + 1))) : Fin (m + 1) → ℝ :=
  Uᵀ *ᵥ (WithLp.ofLp c)

/-- The tail `v_{[2:d]}` of a vector `v ∈ ℝ^{m+1}`: its last `m` coordinates. -/
def tailVec {m : ℕ} (v : Fin (m + 1) → ℝ) : Fin m → ℝ :=
  fun i => v i.succ

/-- **Definitions 3–4, p. 17.** The ellipsoidal cone `E(W, U)` with `W = diag(w) ∈ D^{d−1}_{++}` and
orthonormal `U`, `d = m + 1`:
`c ∈ E(W, U) ⟺ U⁻¹c ∈ E(W) = {c ∈ ℝ₊ × ℝ^{d−1} : c′_{[2:d]} W⁻¹ c_{[2:d]} ≤ c²_{[1]}}`.
`U = 1` gives the standard-position cone `E(W)` of Definition 3. Statements assume `w > 0` and `U`
orthogonal. -/
def ellCone {m : ℕ} (w : Fin m → ℝ) (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  {c | 0 ≤ rotCoord U c 0 ∧ ∑ i, rotCoord U c i.succ ^ 2 / w i ≤ rotCoord U c 0 ^ 2}

/-- **p. 17.** The axis `U e₁` of `E(W, U)` (the first column of `U`), which is the circumcenter
`ĉ(E(W, U))`; EllipsoidalCones uses it as the proxy cost `c^π_t = U_t e₁` (Algorithm 2, p. 21). -/
def axisVec {m : ℕ} (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) : EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (fun i => U i 0)

/-- **p. 19.** `λ_max(W)` for `W = diag(w)`: the largest diagonal entry (for `m ≥ 1`). -/
noncomputable def lamMax {m : ℕ} (w : Fin m → ℝ) : ℝ :=
  ⨆ i, w i

/-- **§4.2, p. 15.** The effective difference `δ = u / ‖u‖` of `u = f_t(x) − f_t(x⋆_t)`, with `δ = 0`
if `u = 0`. -/
noncomputable def effDiff {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if u = 0 then 0 else ‖u‖⁻¹ • u

/-- **(12), p. 19.** The quadratic form `δ̄′_{[2:d]} W δ̄_{[2:d]}` of the update test, for
`W = diag(w)` and `δ̄ = U⁻¹δ` given by its coordinates `v`. -/
def tailQuad {m : ℕ} (w : Fin m → ℝ) (v : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i, w i * v i.succ ^ 2

end CtxInvOpt.Pointed


