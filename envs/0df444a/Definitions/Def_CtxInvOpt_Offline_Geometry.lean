-- Prove2me | Definitions.Def_CtxInvOpt_Offline_Geometry
-- name    : CtxInvOpt_Offline_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:16.083327+00:00
-- url     : https://prove2.me/theorems/7d79bc60-b5f8-4bf5-af64-15f153fc8bba
-- title:
--   §2–§3, pp. 7–12 — angle θ, uncertainty angle α (9), circumcenter, argmin set ψ (1), action sets 𝔅, contexts 𝔉
-- statement:
--   This module fixes the geometric vocabulary of contextual inverse optimization. Throughout, $\mathbb R^n$ (actions) and $\mathbb R^d$ (costs and contexts) carry the Euclidean norm $\|\cdot\|$ and inner product $c'x$.
--
--   1. **Angle.** For $c,\hat c\in\mathbb R^d$ the angle between them is
--   $$\theta(c,\hat c)=\arccos\frac{c'\hat c}{\|c\|\,\|\hat c\|},$$
--   with the convention $\theta(c,0)=\theta(0,\hat c)=0$.
--   2. **Unit sphere.** $S^d=\{c\in\mathbb R^d:\|c\|=1\}$.
--   3. **Uncertainty angle.** For a set $C\subseteq\mathbb R^d$,
--   $$\alpha(C)=\inf_{\hat c\in S^d}\ \sup_{c\in C}\ \theta(c,\hat c).$$
--   4. **Circumcenter.** A vector $\hat c$ is a circumcenter of $C$ if $\hat c\in S^d$ and $\sup_{c\in C}\theta(c,\hat c)=\alpha(C)$, i.e. $\hat c$ attains the infimum above.
--   5. **Forward problem.** For a cost vector $c\in\mathbb R^d$, a feasible set $\mathcal X\subseteq\mathbb R^n$ and a context function $f:\mathbb R^n\to\mathbb R^d$, the solution set is
--   $$\psi(c,\mathcal X,f)=\operatorname*{arg\,min}_{x\in\mathcal X} f(x)'c .$$
--   6. **Action sets.** $\mathcal X\in\mathcal B$ means $\mathcal X$ is a nonempty compact subset of $\mathbb R^n$ of diameter at most $1$.
--   7. **Context functions.** $f\in\mathcal F$ means $f:\mathbb R^n\to\mathbb R^d$ is $1$-Lipschitz.
--   8. **Regret level.** $g(a)=\sin a$ if $a<\pi/2$ and $g(a)=1$ otherwise, the function $\mathbf 1\{a<\pi/2\}\sin a+\mathbf 1\{a\ge\pi/2\}$ of Lemma 1 and Theorem 1.
--
--   These objects are shared by every statement of the paper's offline analysis: the uncertainty angle measures how much the data leave the cost direction undetermined, and the circumcenter is the proxy cost of the optimal offline policy.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin d)`, so norms, diameters and Lipschitz constants are Euclidean. The angle is defined directly rather than through Mathlib's `InnerProductGeometry.angle`, which equals $\pi/2$ at the zero vector; the paper sets it to $0$. The supremum and infimum in $\alpha$ are real `⨆`/`⨅`; the family of angles is bounded in $[0,\pi]$, so they are genuine suprema and infima whenever $C$ is nonempty and $d\ge1$. The nonemptiness of $\mathcal X$ is added to the paper's "compact subset of diameter at most 1": an empty feasible set admits no action.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 7, §2, (1); p. 11, §3.1 (definition of θ), Definition 2, (9); p. 12, Theorem 1

import Mathlib

namespace CtxInvOpt.Offline

open Real

/-- **arXiv:2106.14015v3, §3.1, p. 11.** The angle `θ(c, ĉ) = arccos (c′ĉ / (‖c‖‖ĉ‖))` between two
vectors, with the paper's convention `θ(c, 0) = 0` (p. 11) and `θ(0, ĉ) = 0` (proof of Lemma 2, App-5).
Mathlib's `InnerProductGeometry.angle` is `π/2` at `0`, so it is not used. -/
noncomputable def vecAngle {d : ℕ} (c chat : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if c = 0 ∨ chat = 0 then 0 else Real.arccos (inner ℝ c chat / (‖c‖ * ‖chat‖))

/-- **§2, p. 7.** `S^d`, the unit sphere of `ℝ^d`. -/
def unitSphere (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  Metric.sphere 0 1

/-- **Definition 2, (9), p. 11.** The uncertainty angle `α(C) = inf_{ĉ ∈ S^d} sup_{c ∈ C} θ(c, ĉ)`. -/
noncomputable def uncAngle {d : ℕ} (C : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ⨅ chat : unitSphere d, ⨆ c : C, vecAngle (c : EuclideanSpace ℝ (Fin d)) chat

/-- **Definition 2, p. 11.** `ĉ` is a circumcenter of `C`: a point of `S^d` attaining the infimum
in (9). -/
def IsCircumcenter {d : ℕ} (C : Set (EuclideanSpace ℝ (Fin d)))
    (chat : EuclideanSpace ℝ (Fin d)) : Prop :=
  chat ∈ unitSphere d ∧ (⨆ c : C, vecAngle (c : EuclideanSpace ℝ (Fin d)) chat) = uncAngle C

/-- **(1), p. 7.** The forward problem's solution set `ψ(c, X, f) = argmin_{x ∈ X} f(x)′c`. -/
def argminSet {n d : ℕ} (c : EuclideanSpace ℝ (Fin d)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ X ∧ ∀ y ∈ X, inner ℝ (f x) c ≤ inner ℝ (f y) c}

/-- **§2, p. 7.** `X ∈ 𝔅`: a (nonempty) compact subset of `ℝⁿ` with diameter at most `1`. -/
def IsActionSet {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  X.Nonempty ∧ IsCompact X ∧ Metric.diam X ≤ 1

/-- **§2, p. 7.** `f ∈ 𝔉`: a `1`-Lipschitz context function `ℝⁿ → ℝᵈ`. -/
def IsContext {n d : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d)) : Prop :=
  LipschitzWith 1 f

/-- **Lemma 1, p. 11; Theorem 1, p. 12.** The regret level `sin a` if `a < π/2`, and `1` otherwise. -/
noncomputable def regretCap (a : ℝ) : ℝ :=
  if a < π / 2 then Real.sin a else 1

end CtxInvOpt.Offline


