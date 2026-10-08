-- Prove2me | Definitions.Def_SelfScaledLongStep_Karmarkar_Defs
-- name    : SelfScaledLongStep_Karmarkar_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:52.510134+00:00
-- url     : https://prove2.me/theorems/2099444d-d1e4-4c9a-94c7-5a8ed88fe9a2
-- title:
--   §7.1, pp. 25–27 — Karmarkar-form problem, ζ∗, the potential Φ, ĉ, d̂, the projection (6.4)/(7.3), x̃(ζ) (7.4), the lower-bound update (7.6), the direction (7.5), K̄ and F̲
-- statement:
--   These definitions fix the objects of the conic Karmarkar method of Nesterov and Todd (1997, §7.1).
--
--   Let $E=\mathbb R^n$ with the Euclidean inner product $\langle\cdot,\cdot\rangle$ (the dual space $E^*$ is identified with $E$), let $K\subseteq E$ be a closed convex pointed cone with nonempty interior, $K^*$ its dual cone, and $F$ a barrier for $K$ with gradient $F'$ and Hessian $F''$. The data are a linear map $B:E\to\mathbb R^m$, a vector $c\in E$ and a vector $d\in E$ (in the theorems $d\in K^*$).
--
--   1. **Feasible and strictly feasible sets.** The problem is
--   $$(P)\qquad \min\ \langle c,x\rangle\quad\text{s.t.}\quad Bx=0,\ \ \langle d,x\rangle=1,\ \ x\in K.$$
--   A point is *feasible* if $x\in K$, $Bx=0$, $\langle d,x\rangle=1$, and *strictly feasible* ($x\in S^0(P)$) if moreover $x\in\operatorname{int}K$.
--   2. **Optimal value.** $\zeta^*=\inf\{\langle c,x\rangle : x \text{ feasible}\}$.
--   3. **Projection (6.4), (7.3).** For $w\in\operatorname{int}K$ and $u\in E$, a pair $(y,p)\in\mathbb R^m\times E$ is a *projection pair* if $Bp=0$ and $B^*y+F''(w)p=u$; then $p$ is the projection of $u$ into $\ker B$ with respect to $F''(w)$.
--   4. **Potential.** For $\nu>0$ and $\zeta\in\mathbb R$,
--   $$\Phi(x;\zeta)=\nu\ln\langle c-\zeta d,x\rangle+F(x).$$
--   5. **Modified objective vectors.** At the current iterate $\hat x$,
--   $$\hat c=c+\frac{\langle c,\hat x\rangle}{\nu}F'(\hat x),\qquad \hat d=d+\frac{\langle d,\hat x\rangle}{\nu}F'(\hat x),$$
--   so that $\Phi'(\hat x;\zeta)=\frac{\nu}{\langle c-\zeta d,\hat x\rangle}(\hat c-\zeta\hat d)$.
--   6. **Candidate dual slack direction (7.4).** With $p(c)$, $p(d)$ the projections of $\hat c$, $\hat d$,
--   $$\tilde x(\zeta)=\frac{\langle c-\zeta d,\hat x\rangle}{\nu}\hat x+\bigl(p(c)-\zeta p(d)\bigr).$$
--   7. **Lower-bound update (7.6).** Given a lower bound $\hat\zeta$, put $\zeta^+=\hat\zeta$ if $\tilde x(\hat\zeta)\notin\operatorname{int}K$, and otherwise
--   $$\zeta^+=\hat\zeta+\frac{1}{\sigma_{\tilde x(\hat\zeta)}(\tilde p)},\qquad \tilde p=p(d)+\hat x/\nu,$$
--   where $\sigma_x(p)=\min\{\beta\ge0:\beta x-p\in K\}$.
--   8. **Search direction (7.5).** $p=p(c)-\zeta p(d)$, used with $\zeta=\zeta^+$.
--   9. **The bounded set $\bar K$ and $\underline F$.** For an initial point $x_0$,
--   $$\bar K=\{x\in K: Bx=0,\ \langle c,x\rangle\le\gamma_0:=\max(\langle c,x_0\rangle,0)+1,\ \langle d,x\rangle\le1\},$$
--   and $\underline F$ is the infimum of $F$ over $\bar K\cap\operatorname{int}K$.
--
--   These objects are shared by Lemma 7.1, identity (7.8) and Theorems 7.1–7.2 of the paper.
--
--   **Formalization Note** The paper prints $\hat c := c-\frac{\langle c,\hat x\rangle}{\nu}F'(\hat x)$ and $\hat d := d-\frac{\langle d,\hat x\rangle}{\nu}F'(\hat x)$ on p. 27. The sign is a misprint: the identity $\Phi'(\hat x;\zeta)=\frac{\nu}{\langle c-\zeta d,\hat x\rangle}(\hat c-\zeta\hat d)$ printed directly above it, the identity $B^*(y(c)-\zeta y(d))+\tilde s(\zeta)=c-\zeta d$, and the relation $\langle\hat u,\hat x\rangle=0$ on p. 28 all require "$+$" (with "$-$", $\langle\hat c,\hat x\rangle=2\langle c,\hat x\rangle$ since $\langle F'(\hat x),\hat x\rangle=-\nu$). The definitions use "$+$". $E^*$ is identified with $E$; $F'$ is `gradient F` and $F''$ is `hess F`. $\zeta^*$ is a real `sInf`, finite only under the feasibility assumptions every theorem carries. When $\tilde x(\hat\zeta)\in\operatorname{int}K$ the paper's $\sigma_{\tilde x(\hat\zeta)}(\tilde p)$ is positive under those assumptions, so Lean's convention $1/0=0$ is never reached. $\underline F$ is taken over $\bar K\cap\operatorname{int}K$ because the barrier is $+\infty$ on $\partial K$ in the paper and has no meaningful value there in Lean; the paper calls it a minimum, and the infimum coincides with it.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, pp. 23, 25–27, (6.4), §7.1 (P), (D), Φ, ĉ, d̂, (7.3)–(7.6), K̄ and F̲ (p. 26); sign of ĉ, d̂ corrected

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PrimalDual_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.Karmarkar

/-- Feasible set of the Karmarkar-form problem (P), §7.1, p. 25:
`x ∈ K`, `B x = 0`, `⟨d, x⟩ = 1`. -/
def KarFeasible {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (d x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ K ∧ B x = 0 ∧ ⟪d, x⟫_ℝ = 1

/-- Strictly feasible set `S⁰(P)` of the Karmarkar-form problem (P), §7.1, p. 25:
`x ∈ int K`, `B x = 0`, `⟨d, x⟩ = 1`. -/
def KarStrict {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (d x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ interior K ∧ B x = 0 ∧ ⟪d, x⟫_ℝ = 1

/-- Optimal value `ζ*` of (P), §7.1, p. 25: the infimum of `⟨c, x⟩` over the feasible set.
It is a genuine (finite) infimum only when the feasible set is nonempty and the objective is
bounded below on it; every statement using it assumes strict primal and dual feasibility. -/
noncomputable def zetaStar {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (c d : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sInf ((fun x => ⟪c, x⟫_ℝ) '' {x | KarFeasible K B d x})

/-- Karmarkar potential, §7.1, p. 25: `Φ(x; ζ) = ν ln⟨c − ζ d, x⟩ + F(x)`, the potential (7.1)
with `µ = ν`, extended to `{x ∈ int K : B x = 0}`. -/
noncomputable def karPotential {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (c d : EuclideanSpace ℝ (Fin n)) (ζ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ν * Real.log ⟪c - ζ • d, x⟫_ℝ + F x

/-- `ĉ`, §7.1, p. 27: `ĉ = c + (⟨c, x̂⟩/ν) F'(x̂)`, so that
`Φ'(x̂; ζ) = (ν/⟨c − ζd, x̂⟩)(ĉ − ζ d̂)`. The page prints `−`; the sign `+` is forced by the
page's own identity for `Φ'(x̂; ζ)` and by `⟨ĉ, x̂⟩ = 0` (p. 28). -/
noncomputable def cHat {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (c xh : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  c + (⟪c, xh⟫_ℝ / ν) • gradient F xh

/-- `d̂`, §7.1, p. 27: `d̂ = d + (⟨d, x̂⟩/ν) F'(x̂)` (printed sign `−` corrected as for `cHat`). -/
noncomputable def dHat {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (d xh : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  d + (⟪d, xh⟫_ℝ / ν) • gradient F xh

/-- (7.4), p. 27: `x̃(ζ) = (⟨c − ζd, x̂⟩/ν) x̂ + (p(c) − ζ p(d))`, where `pc`, `pd` are the
projections of `ĉ`, `d̂`. -/
noncomputable def xTilde {n : ℕ} (ν : ℝ) (c d xh pc pd : EuclideanSpace ℝ (Fin n)) (ζ : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  (⟪c - ζ • d, xh⟫_ℝ / ν) • xh + (pc - ζ • pd)

open Classical in
/-- The lower-bound update of §7.1, p. 27: `ζ⁺ = ζ̂` if `x̃(ζ̂) ∉ int K`, and otherwise (7.6)
`ζ⁺ = ζ̂ + 1/σ_{x̃(ζ̂)}(p̃)` with `p̃ = p(d) + x̂/ν`. -/
noncomputable def zetaPlus {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (ν : ℝ)
    (c d xh pc pd : EuclideanSpace ℝ (Fin n)) (ζh : ℝ) : ℝ :=
  if xTilde ν c d xh pc pd ζh ∈ interior K then
    ζh + 1 / sigma K (xTilde ν c d xh pc pd ζh) (pd + (1 / ν) • xh)
  else ζh

/-- Search direction (7.5), p. 27: `p = p(c) − ζ p(d)` (used with `ζ = ζ⁺`). -/
def karDir {n : ℕ} (pc pd : EuclideanSpace ℝ (Fin n)) (ζ : ℝ) : EuclideanSpace ℝ (Fin n) :=
  pc - ζ • pd

/-- The bounded set `K̄` of §7.1, p. 26:
`K̄ = {x ∈ K : Bx = 0, ⟨c, x⟩ ≤ γ₀ := max(⟨c, x₀⟩, 0) + 1, ⟨d, x⟩ ≤ 1}`. -/
def kBar {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (c d x₀ : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ K ∧ B x = 0 ∧ ⟪c, x⟫_ℝ ≤ max ⟪c, x₀⟫_ℝ 0 + 1 ∧ ⟪d, x⟫_ℝ ≤ 1}

/-- `F̲`, §7.1, p. 26: the minimum of the barrier `F` over `K̄`, taken over the points of `K̄`
where `F` is finite, i.e. `K̄ ∩ int K`. -/
noncomputable def fLow {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (c d x₀ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sInf (F '' (kBar K B c d x₀ ∩ interior K))

end SelfScaledLongStep.Karmarkar


