-- Prove2me | Definitions.Def_SchattenSketch_Main_Path
-- name    : SchattenSketch_Main_Path
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:56:39.510193+00:00
-- url     : https://prove2.me/theorems/47181ca3-5158-4d1a-817e-9339da64accf
-- title:
--   Laws carried by at most $N$ points of $[0,B]$, paths piecewise $C^1$ after square roots, and the path length $L_K$ of (4.10)
-- statement:
--   A measure $\nu$ on $\mathbb R$ is **carried by at most $N$ points of $[0,B]$** if there is a finite set $S\subseteq[0,B]$ with $|S|\le N$ and $\nu(\mathbb R\setminus S)=0$.
--
--   A path $x:[0,1]\to[0,\infty)$ is **piecewise continuously differentiable after taking square roots** if there is a finite partition $0=t_0<t_1<\dots<t_r=1$ such that $t\mapsto\sqrt{x(t)}$ is continuously differentiable on every closed piece $[t_{l-1},t_l]$, with one-sided derivatives at the ends. In particular $\sqrt x$ is continuous on $[0,1]$.
--
--   For particle paths $x_1,\dots,x_n$ put $D_t=\mathrm{diag}(\sqrt{x_1(t)},\dots,\sqrt{x_n(t)})$. The **path length** (4.10) is
--   $$L_K=\int_0^1\Bigl(\frac1n\,\mathrm{tr}\,\dot D_t^2\Bigr)^{1/2}dt=\int_0^1\Bigl(\frac1n\sum_{i=1}^n\Bigl(\frac{d}{dt}\sqrt{x_i(t)}\Bigr)^2\Bigr)^{1/2}dt .$$
--
--   **Formalization Note.** The partition is `t : Fin (r + 1) → ℝ`, strictly increasing from `0` to `1`, with `ContDiffOn ℝ 1 (√x) (Icc t_{l-1} t_l)` on each piece. `pathLength x` is the interval integral over $[0,1]$ of the displayed integrand with Mathlib's `deriv`; for a piecewise-$C^1$ path the derivative exists except at the finitely many joining times, a null set, and the integrand is bounded, so the integral is the paper's $L_K$.
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 14, Proposition 4.2; p. 16, Lemma 4.4, (4.9a) and (4.10)

import Mathlib

open MeasureTheory

namespace SchattenSketch.Main

/-- `ν` is carried by at most `N` points of `[0, B]` (Yang, p. 14, Proposition 4.2 and p. 16,
Lemma 4.4): there is a finite set `S ⊆ [0, B]` with at most `N` elements and `ν(ℝ ∖ S) = 0`. -/
def IsSupportedOnAtMost (ν : Measure ℝ) (N : ℕ) (B : ℝ) : Prop :=
  ∃ S : Finset ℝ, S.card ≤ N ∧ (∀ y ∈ S, 0 ≤ y ∧ y ≤ B) ∧ ν (↑S)ᶜ = 0

/-- A path `x : [0, 1] → ℝ` is piecewise continuously differentiable after taking square roots
(Yang, p. 16, Lemma 4.4): there is a finite partition `0 = t₀ < t₁ < ⋯ < t_r = 1` such that
`t ↦ √(x t)` is `C¹` on every closed piece `[t_{l-1}, t_l]` (one-sided derivatives at the ends).
In particular `√x` is continuous on `[0, 1]`. -/
def SqrtPiecewiseC1 (x : ℝ → ℝ) : Prop :=
  ∃ r : ℕ, ∃ t : Fin (r + 1) → ℝ, t 0 = 0 ∧ t (Fin.last r) = 1 ∧ StrictMono t ∧
    ∀ l : Fin r, ContDiffOn ℝ 1 (fun s => Real.sqrt (x s)) (Set.Icc (t l.castSucc) (t l.succ))

/-- The path length (4.10) (Yang, p. 16) of `n` particle paths `x₁, …, xₙ`, with
`D_t = diag(√x₁(t), …, √xₙ(t))`: `L_K = ∫₀¹ ((1/n) tr Ḋ_t²)^{1/2} dt`, where
`(1/n) tr Ḋ_t² = (1/n) ∑ᵢ (d/dt √xᵢ(t))²`. The derivative is taken where it exists; for a
piecewise-`C¹` path that is every time except the finitely many joining times, a null set. -/
noncomputable def pathLength {n : ℕ} (x : Fin n → ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.sqrt ((1 / (n : ℝ)) * ∑ i : Fin n, (deriv (fun s => Real.sqrt (x i s)) t) ^ 2)

end SchattenSketch.Main


