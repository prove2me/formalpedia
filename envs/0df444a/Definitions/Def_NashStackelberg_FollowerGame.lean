-- Prove2me | Definitions.Def_NashStackelberg_FollowerGame
-- name    : NashStackelberg_FollowerGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:10.621093+00:00
-- url     : https://prove2.me/theorems/ea49aa16-33a0-4e4e-84f5-8f0821634255
-- title:
--   The followers' game with a simple parameterization in the leader's variables
-- statement:
--   Fix a leader whose variables are $w\in\mathbb R^{n_\ell}$. Its followers play a simultaneous game $P(w)$. There are $K$ followers; follower $k$ has variables $y_k\in\mathbb R^{d_k}$ and solves
--   $$
--   \min_{y_k}\ \tfrac12\,y_k^\top Q_k y_k + c_k^\top y_k + \Big(\sum_{k'\ne k} C_{kk'}\,y_{k'}\Big)^{\!\top} y_k + (H_k w)^\top y_k
--   \quad\text{s.t.}\quad A_k w + B_k y_k \le b_k ,
--   $$
--   where $Q_k$ is positive semidefinite and $A_k w+B_k y_k\le b_k$ has $r_k$ rows.
--
--   In the paper's terminology the followers' game is **simple** (convex quadratic objective plus a bilinear coupling with the other followers), **facile** (each feasible set is a polyhedron) and has a **simple parameterization with respect to $w$**: the leader enters only through the linear term $(H_k w)^\top y_k$ and the constraint term $A_k w$. This is the lower level of a simple Stackelberg game.
--
--   **Formalization Note** The page writes the feasible set as $y\in\mathcal F$ with $\mathcal F$ a polyhedron together with $Ax+By\le b$; both are folded into the single system $A_k w+B_k y_k\le b_k$ (the rows of $\mathcal F$ have zero $w$-part). Positive semidefiniteness is $v^\top Q_k v\ge0$ for all $v$, without requiring $Q_k$ symmetric. The block $C_{kk}$ is never used.
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, §3 p.6 (simple parameterization), Definition 1 pp.6–7 (simple and facile games), §3.2 and Definition 3, p.7

import Mathlib

open Matrix

namespace NashStackelberg

/-- **A followers' game with a simple parameterization** (Carvalho, Dragotto, Feijoo, Lodi &
Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, §3 p.6, Definition 1 (facile
game), §3.2 and Definition 3, p.7).

The data of the simultaneous game `P(w)` played by the followers of one leader whose variables are
`w ∈ ℝ^{nℓ}`. There are `K` followers; follower `k` has variables `yₖ ∈ ℝ^{d k}` and solves
`min_{yₖ} ½ yₖᵀ Qₖ yₖ + cₖᵀ yₖ + (Σ_{k' ≠ k} Cₖₖ' yₖ')ᵀ yₖ + (Hₖ w)ᵀ yₖ`
subject to `Aₖ w + Bₖ yₖ ≤ bₖ` (`r k` rows), with `Qₖ` positive semidefinite.

The game is *simple* (quadratic objective with PSD `Qₖ`, linear term, bilinear coupling
`(Cᵏ y⁻ᵏ)ᵀ yᵏ` with the other followers), *facile* (polyhedral feasible sets) and has a *simple
parameterization with respect to `w`* (the leader enters through `(Hₖ w)ᵀ yₖ` and `Aₖ w`).

**Formalization Note.** The page's `y ∈ 𝓕` with `𝓕` a polyhedron (facile game) and
`Ax + By ≤ b` are folded into one system `Aₖ w + Bₖ yₖ ≤ bₖ` (rows of `𝓕` have zero `w`-part).
Positive semidefiniteness is `0 ≤ vᵀ Qₖ v` for all `v` (no symmetry required; only the quadratic
form enters the objective). `Cₖₖ` is never used (the coupling sums over `k' ≠ k`). -/
structure FollowerGame (nl : ℕ) where
  /-- The number of followers. -/
  K : ℕ
  /-- Follower `k` has `d k` variables. -/
  d : Fin K → ℕ
  /-- The quadratic term `Qₖ` of follower `k`. -/
  Q : (k : Fin K) → Matrix (Fin (d k)) (Fin (d k)) ℝ
  /-- `Qₖ` is positive semidefinite. -/
  Q_psd : ∀ (k : Fin K) (v : Fin (d k) → ℝ), 0 ≤ v ⬝ᵥ (Q k *ᵥ v)
  /-- The linear term `cₖ`. -/
  c : (k : Fin K) → Fin (d k) → ℝ
  /-- The block `Cₖₖ'` of `Cᵏ` acting on follower `k'`'s variables. -/
  C : (k k' : Fin K) → Matrix (Fin (d k)) (Fin (d k')) ℝ
  /-- The matrix `Hₖ` of the simple parameterization `(Hₖ w)ᵀ yₖ`. -/
  H : (k : Fin K) → Matrix (Fin (d k)) (Fin nl) ℝ
  /-- The number of constraint rows of follower `k`. -/
  r : Fin K → ℕ
  /-- The leader part `Aₖ` of follower `k`'s constraints. -/
  A : (k : Fin K) → Matrix (Fin (r k)) (Fin nl) ℝ
  /-- The follower part `Bₖ` of follower `k`'s constraints. -/
  B : (k : Fin K) → Matrix (Fin (r k)) (Fin (d k)) ℝ
  /-- The right-hand side `bₖ`. -/
  b : (k : Fin K) → Fin (r k) → ℝ

end NashStackelberg


