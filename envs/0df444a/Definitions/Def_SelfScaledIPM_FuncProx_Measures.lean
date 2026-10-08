-- Prove2me | Definitions.Def_SelfScaledIPM_FuncProx_Measures
-- name    : SelfScaledIPM_FuncProx_Measures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:18:01.92881+00:00
-- url     : https://prove2.me/theorems/f728c1f9-e83e-4d25-a4fc-c5590ce1e992
-- title:
--   §3, p. 6 and §4, pp. 15–16 — local norms ‖u‖_v, σ_v(u), |u|_v, normalized gap µ, and proximity measures γ_F, γ_G, γ_∞, λ_∞, λ⁺_∞, λ₂, λ (4.8)–(4.14)
-- statement:
--   Let $K$, $F$, $F_*$ and $\nu$ be as in the setting file, with $E^*$ identified with $E$.
--
--   **Local norms** (§3). For $v\in\operatorname{int}K$: $\|u\|_v=\langle F''(v)u,u\rangle^{1/2}$ for $u\in E$, and $\|u\|_v=\langle u,[F''(v)]^{-1}u\rangle^{1/2}$ for $u\in E^*$. For $v\in\operatorname{int}K^*$ the same with $F_*$ in place of $F$ and the roles of $E$, $E^*$ exchanged.
--
--   **σ-measures** (§3). $\sigma_v(u)$ is the minimum $\beta\ge0$ such that $\beta v-u\in K$ (if $v\in\operatorname{int}K$, $u\in E$), $-\beta F'(v)-u\in K^*$ (if $v\in\operatorname{int}K$, $u\in E^*$), $\beta v-u\in K^*$ (if $v\in\operatorname{int}K^*$, $u\in E^*$), or $-\beta F_*'(v)-u\in K$ (if $v\in\operatorname{int}K^*$, $u\in E$). Further $|u|_v=\max\{\sigma_v(u),\sigma_v(-u)\}$.
--
--   **Proximity measures** (§4). For $x\in\operatorname{int}K$, $s\in\operatorname{int}K^*$, let $\mu(x,s)=\langle s,x\rangle/\nu$ and
--   $$\begin{aligned}
--   \gamma_F(x,s)&=F(x)+F_*(s)+\nu\ln\mu(x,s)+\nu, &(4.8)\\
--   \gamma_G(x,s)&=\mu(x,s)\langle F'(x),F_*'(s)\rangle-\nu, &(4.9)\\
--   \gamma_\infty(x,s)&=\mu(x,s)\,\sigma_s(-F'(x))-1, &(4.10)\\
--   \lambda_\infty(x,s)&=\Big|\tfrac{1}{\mu(x,s)}s+F'(x)\Big|_x, &(4.11)\\
--   \lambda^+_\infty(x,s)&=\sigma_s(x)/\mu(x,s)-1, &(4.12)\\
--   \lambda_2(x,s)&=\Big\|\tfrac{1}{\mu(x,s)}s+F'(x)\Big\|_x, &(4.13)\\
--   \lambda(x,s)&=\big(\nu-\nu^2\mu(x,s)^2/\|s\|_x^2\big)^{1/2}. &(4.14)
--   \end{aligned}$$
--   The first three are the global proximity measures, the last four the local ones; all vanish exactly on the central path $s=-\mu F'(x)$.
--
--   **Formalization Note** The paper's notation infers the meaning of $\|u\|_v$, $\sigma_v(u)$, $|u|_v$ from the spaces of $u$ and $v$. After identifying $E^*$ with $E$ this information is carried by the function used: `lnorm G v u` (same space) and `dnorm G v u` (other space) with $G=F$ or $G=F_*$; `sigma C c u` $=\min\{\beta\ge0:\beta c-u\in C\}$ with the cone $C\in\{K,K^*\}$ and the centre $c\in\{v,-F'(v),-F_*'(v)\}$ chosen as in the four cases above. Each measure uses the first of the two equal printed forms (their equality is Lemmas 3.2–3.3, not formalized). The inverse of $F''(v)$ is `ContinuousLinearMap.inverse`, nondegenerate by the barrier hypothesis.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 6 (§3 notation), p. 12 (µ), pp. 15–16, (4.8)–(4.14)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Functional proximity measure** (4.8): `γ_F(x, s) = F(x) + F*(s) + ν ln µ(x, s) + ν`. -/
noncomputable def gammaF {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  F x + SelfScaledIPM.ShortStep.conj K F s + ν * Real.log (SelfScaledIPM.ShortStep.mu ν x s) + ν

/-- **Gradient proximity measure** (4.9): `γ_G(x, s) = µ(x, s)⟨F'(x), F*'(s)⟩ − ν`. -/
noncomputable def gammaG {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  SelfScaledIPM.ShortStep.mu ν x s * ⟪gradient F x, gradient (SelfScaledIPM.ShortStep.conj K F) s⟫_ℝ - ν

/-- **Uniform proximity measure** (4.10), first printed form: `γ_∞(x, s) = µ(x, s) σ_s(−F'(x)) − 1`,
with `σ_s(·)` on `E*` at `s ∈ int K*`. (The second printed form `µ σ_x(−F*'(s)) − 1` is equal by
Lemma 3.3, not formalized here.) -/
noncomputable def gammaInf {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  SelfScaledIPM.ShortStep.mu ν x s * SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) s (-gradient F x) - 1

/-- **One-sided local measure** (4.12), first printed form: `λ⁺_∞(x, s) = σ_s(x)/µ(x, s) − 1`, with
`x ∈ E` and centre `s ∈ int K*`, i.e. `σ` relative to `K` centred at `−F*'(s)`. -/
noncomputable def lambdaPlusInf {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  SelfScaledIPM.ShortStep.sigma K (-gradient (SelfScaledIPM.ShortStep.conj K F) s) x / SelfScaledIPM.ShortStep.mu ν x s - 1

/-- **Local 2-norm measure** (4.13), first printed form: `λ₂(x, s) = ‖s/µ(x, s) + F'(x)‖_x`, the
argument in `E*`, so the dual local norm at `x`. -/
noncomputable def lambda2 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  SelfScaledIPM.ShortStep.dnorm F x ((SelfScaledIPM.ShortStep.mu ν x s)⁻¹ • s + gradient F x)

/-- **Measure λ** (4.14), first printed form: `λ(x, s) = (ν − ν² µ(x, s)² / ‖s‖_x²)^{1/2}`, with
`‖s‖_x` the dual local norm of `s ∈ E*` at `x ∈ int K`. -/
noncomputable def lambdaProx {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (ν - ν ^ 2 * SelfScaledIPM.ShortStep.mu ν x s ^ 2 / SelfScaledIPM.ShortStep.dnorm F x s ^ 2)

end SelfScaledIPM.FuncProx


