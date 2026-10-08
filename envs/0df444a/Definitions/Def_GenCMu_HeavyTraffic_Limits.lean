-- Prove2me | Definitions.Def_GenCMu_HeavyTraffic_Limits
-- name    : GenCMu_HeavyTraffic_Limits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:07.423984+00:00
-- url     : https://prove2.me/theorems/8e79a551-8164-4c82-87ab-f2e8369cde5b
-- title:
--   Assumptions 1–3, the reflection map, the limit workload $\tilde W^*_+=\varphi(\tilde L^*_++\tilde c^*)$, problem (43) and the lower bound $\tilde J^*$ (45)
-- statement:
--   **Assumption 1 (Main convergence).** There are continuous $\tilde A^*, \tilde S^*, \tilde c^*$ and continuously differentiable $\bar A^*, \bar S^*$ with positive derivatives $\lambda = \bar A^{*\prime}$ (18) and $\mu = \bar S^{*\prime}$ (19) such that, uniformly,
--   $$\bar A^n \to \bar A^*,\ \ \bar S^n \to \bar S^*,\ \ \tilde A^n \to \tilde A^*,\ \ \tilde S^n \to \tilde S^*,\ \ n^{1/2}(R^n_+ - e) \to \tilde c^* \qquad (15)\text{–}(17),$$
--   where $e(t) = t$, and moreover $\bar A^{n\prime} \to \lambda$, $\bar S^{n\prime} \to \mu$ uniformly. Put $R^*_k = (\bar S^*_k)^{-1}\circ\bar A^*_k$, $\mu_k(R^*_k(t))$ the service rate in real time, and $\rho_k(t) = \lambda_k(t)/\mu_k(R^*_k(t))$ (20). The limit of $\tilde L^n_k$ is (70)
--   $$\tilde L^*_k = \frac{\tilde A^*_k - \tilde S^*_k\circ R^*_k}{\mu_k\circ R^*_k},$$
--   and the limit total workload is $\tilde W^*_+ = \varphi(\tilde L^*_+ + \tilde c^*)$ (74), where $\varphi(x)(t) = x(t) + \sup_{0\le s\le t}\max(0, -x(s))$ is the one-dimensional reflection map.
--
--   **Assumption 2 (Cost convergence).** $C^* = (C^*_k)$ is nonnegative, nondecreasing and convex on $[0,\infty)$ and $C^n_k(n^{1/2}x) \to C^*_k(x)$ uniformly on every $[0,B]$ (38).
--
--   **Problem (43).** For rates $\lambda_k, \rho_k > 0$ and $y \ge 0$,
--   $$g\circ y = \arg\min_{x\in\Omega}\ \sum_{k=1}^d \lambda_k C^*_k\Big(\frac{x_k}{\rho_k}\Big), \qquad \Omega = \Big\{x \in \mathbb R^d_+ : \sum_k x_k = y\Big\}.$$
--   The lower bound (45) is $\tilde J^*(t) = \int_0^t V(s)\,ds$, where $V(s)$ is the optimal value of (43) with $\lambda(s)$, $\rho(s)$ and $y = \tilde W^*_+(s)$. The marginal cost is $c^*_k = C^{*\prime}_k$ (right derivative at $0$).
--
--   **Assumption 3 (Cost regularity).** Each $C^*_k$ is strictly convex and continuously differentiable on $[0,\infty)$, and at every $t \in [0,1]$ with $\tilde W^*_+(t) > 0$ every solution of (43) at $y = \tilde W^*_+(t)$ is interior.
--
--   These are the hypotheses and the limit objects of Propositions 2–7.
--
--   **Formalization Note** Every "→" is uniform convergence ((11), p. 816). The paper states (15) as convergence in $\mathcal C$; we add convergence of the derivatives of the trends, because without it $\bar A^n, \bar S^n$ may oscillate on the $n^{-1/2}$ time scale and (23)–(24), (33)–(34) and Proposition 3 fail. The service side ($\bar S^*, \tilde S^*, \mu$) is assumed on $[0,2]$, matching the sequence. The paper writes $\mu_k$ for $\bar S^{*\prime}_k$ (19) and uses $\mu_k(R^*_k(t))$ in (70), (77), (83); we read $\mu_k$ in (20), (36), (41), (46)–(51) as $\mu_k(R^*_k(t))$, which makes both equalities of (20) true. The paper states (38) without a mode; we state it uniformly on compacts. $\tilde J^*$ integrates the optimal value of (43), which equals the paper's integrand $\sum_k\lambda_k C^*_k([g\circ\tilde W^*_+]_k/\rho_k)$ for every minimizer, so no choice of $g$ is needed. The paper states Assumption 3's interior clause for all $t$ (p. 821); at $y = 0$ the only point of $\Omega$ is $0$, so read literally it would fail whenever $\tilde W^*_+$ vanishes (e.g. at $t = 0$); we impose it where $\tilde W^*_+(t) > 0$.
--
--   **Boundary convention** `PostHorizonRegular` requires the allocation over every bounded $O(\sqrt n)$ window after $n$ to advance at rate $\rho_k(1)$ for each class. The paper does not state this; it is needed for its delay claims at the right endpoint, since F1 constrains policies only through $n$.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), p. 817, Assumption 1 (Main convergence), (15)–(20); p. 819, Assumption 2 (Cost convergence), (38); p. 820, (43), (45); p. 822, Assumption 3 (Cost regularity); Appendix, (70)–(74), p. 827

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Sequence

namespace GenCMu.HeavyTraffic

open Filter Topology Finset

/-- The limit functions of Assumption 1 (p. 817): `Abs = Ā*`, `Sbs = S̄*` (first order),
`Ats = Ã*`, `Sts = S̃*` (second order), and `cs = c̃*` (heavy-traffic drift). -/
structure Limits (d : ℕ) where
  Abs : ℝ → Fin d → ℝ
  Sbs : ℝ → Fin d → ℝ
  Ats : ℝ → Fin d → ℝ
  Sts : ℝ → Fin d → ℝ
  cs : ℝ → ℝ

namespace Limits

variable {d : ℕ} (M : Limits d)

/-- (18): arrival rate `λ_k = Ā*_k′` on `[0, 1]`. -/
noncomputable def lam (k : Fin d) (t : ℝ) : ℝ :=
  derivWithin (fun s => M.Abs s k) (Set.Icc 0 1) t
/-- (19): service rate `μ_k = S̄*_k′`, a function of the server's class-`k` time `s ∈ [0, 2]`. -/
noncomputable def mu (k : Fin d) (s : ℝ) : ℝ :=
  derivWithin (fun s => M.Sbs s k) (Set.Icc 0 2) s
/-- `R*_k = (S̄*_k)⁻¹ ∘ Ā*_k`, the limit of `Rⁿ_k` and of `T̄ⁿ_k`. -/
noncomputable def Rstar (k : Fin d) (t : ℝ) : ℝ := genInv (fun s => M.Sbs s k) (M.Abs t k)
/-- `μ_k(R*_k(t))`: the service rate in real time; this is the `μ_k` of (20), (36), (41), (46),
(49), (51) (cf. (70), (77), (83), pp. 827–828). -/
noncomputable def muR (k : Fin d) (t : ℝ) : ℝ := M.mu k (M.Rstar k t)
/-- (20): traffic intensity `ρ_k = λ_k / μ_k`, with `μ_k` read at `R*_k(t)`; it equals `R*_k′`. -/
noncomputable def rho (k : Fin d) (t : ℝ) : ℝ := M.lam k t / M.muR k t
/-- (70), class by class: `L̃*_k = (Ã*_k − S̃*_k ∘ R*_k) / μ_k(R*_k)`, the limit of `L̃ⁿ_k`. -/
noncomputable def Lstar (k : Fin d) (t : ℝ) : ℝ :=
  (M.Ats t k - M.Sts (M.Rstar k t) k) / M.muR k t

end Limits

/-- The allocation continues with the first-order class rates on every bounded diffusion-scale
window after the nominal horizon. The paper's delay formula (9) reads beyond `n` for jobs arriving
near `n`, while F1 and Assumption 1 only constrain the processes through `n`. -/
def PostHorizonRegular {d : ℕ} (_H : HTSeq d) (M : Limits d) (T : ℕ → Alloc d) : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ k, ∀ s ∈ Set.Icc (0 : ℝ) B,
    |(T n ((n : ℝ) + Real.sqrt n * s) k - T n n k) / Real.sqrt n -
      M.rho k 1 * s| ≤ ε

/-- Assumption 1 (Main convergence), (15)–(17), p. 817, with the positive first derivatives
(18)–(19). Every convergence is uniform ((11), p. 816): on `[0, 1]` for the arrival side and the
heavy-traffic condition, on `[0, 2]` for the service side (see `HTSeq`).

The fields `conv_dAbar`, `conv_dSbar` (the first-order terms converge in `𝒞¹`, not only in `𝒞`) are
an explicit addition to the printed assumption: without them the trends `Āⁿ, S̄ⁿ` may oscillate on
the `n^{-1/2}` time scale, and then (23)–(24), (33)–(34) and Proposition 3 fail. -/
structure MainConvergence {d : ℕ} (H : HTSeq d) (M : Limits d) : Prop where
  Ats_cont : ContinuousOn M.Ats (Set.Icc 0 1)
  Sts_cont : ContinuousOn M.Sts (Set.Icc 0 2)
  cs_cont : ContinuousOn M.cs (Set.Icc 0 1)
  Abs_C1 : ∀ k, ContDiffOn ℝ 1 (fun t => M.Abs t k) (Set.Icc 0 1)
  Sbs_C1 : ∀ k, ContDiffOn ℝ 1 (fun t => M.Sbs t k) (Set.Icc 0 2)
  lam_pos : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < M.lam k t
  mu_pos : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) 2, 0 < M.mu k t
  /-- (15) -/
  conv_Abar : TendstoUniformlyOn H.Abar M.Abs atTop (Set.Icc 0 1)
  conv_Sbar : TendstoUniformlyOn H.Sbar M.Sbs atTop (Set.Icc 0 2)
  /-- (15) in `𝒞¹`: the derivatives of the trends converge too. -/
  conv_dAbar : TendstoUniformlyOn
    (fun n t k => derivWithin (fun s => H.Abar n s k) (Set.Icc 0 1) t)
    (fun t k => M.lam k t) atTop (Set.Icc 0 1)
  conv_dSbar : TendstoUniformlyOn
    (fun n t k => derivWithin (fun s => H.Sbar n s k) (Set.Icc 0 2) t)
    (fun t k => M.mu k t) atTop (Set.Icc 0 2)
  /-- (16) -/
  conv_Atil : TendstoUniformlyOn H.Atil M.Ats atTop (Set.Icc 0 1)
  conv_Stil : TendstoUniformlyOn H.Stil M.Sts atTop (Set.Icc 0 2)
  /-- (17), the heavy-traffic condition `n^{1/2}(Rⁿ_+ − e) → c̃*`. -/
  heavy : TendstoUniformlyOn (fun (n : ℕ) t => Real.sqrt n * (H.Rplus n t - t)) M.cs atTop
    (Set.Icc 0 1)

/-- Harrison's one-dimensional reflection map,
`φ(x)(t) = x(t) + sup_{0 ≤ s ≤ t} max(0, −x(s))`. -/
noncomputable def reflect (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  x t + max 0 (⨆ s : Set.Icc (0 : ℝ) t, -x s)

/-- (72), (74), p. 827: the limiting total workload `W̃*_+ = φ(L̃*_+ + c̃*)`. -/
noncomputable def Wstar {d : ℕ} (M : Limits d) : ℝ → ℝ :=
  reflect (fun t => ∑ k, M.Lstar k t + M.cs t)

/-- The objective of (43) at `x`, for rates `lam`, `rho` and costs `Cs` frozen at one time:
`Σ_k λ_k C*_k(x_k / ρ_k)`. -/
noncomputable def obj43 {d : ℕ} (lam rho : Fin d → ℝ) (Cs : Fin d → ℝ → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ k, lam k * Cs k (x k / rho k)

/-- `x` solves (43) for the total `y`: `x ∈ Ω = {x ∈ ℝ^d_+ : Σ_k x_k = y}` and `x` minimizes the
objective over `Ω`. -/
def IsMin43 {d : ℕ} (lam rho : Fin d → ℝ) (Cs : Fin d → ℝ → ℝ) (y : ℝ) (x : Fin d → ℝ) : Prop :=
  (∀ k, 0 ≤ x k) ∧ ∑ k, x k = y ∧
    ∀ x' : Fin d → ℝ, (∀ k, 0 ≤ x' k) → ∑ k, x' k = y →
      obj43 lam rho Cs x ≤ obj43 lam rho Cs x'

/-- The optimal value of (43): the infimum of the objective over `Ω`. -/
noncomputable def val43 {d : ℕ} (lam rho : Fin d → ℝ) (Cs : Fin d → ℝ → ℝ) (y : ℝ) : ℝ :=
  sInf {z | ∃ x : Fin d → ℝ, (∀ k, 0 ≤ x k) ∧ ∑ k, x k = y ∧ z = obj43 lam rho Cs x}

/-- (45): the lower bound `J̃*(t) = Σ_k ∫_0^t λ_k(s) C*_k([g ∘ W̃*_+]_k(s) / ρ_k(s)) ds`, written as
the integral over `[0, t]` of the optimal value of (43) at `y = W̃*_+(s)`. -/
noncomputable def Jstar {d : ℕ} (M : Limits d) (Cs : Fin d → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, val43 (fun k => M.lam k s) (fun k => M.rho k s) Cs (Wstar M s)

/-- Assumption 2 (Cost convergence), (38), p. 819: `C*` is nonnegative, nondecreasing and convex on
`[0, ∞)`, and `Cⁿ(n^{1/2} ·) → C*(·)` uniformly on every compact `[0, B]`. -/
structure CostConvergence {d : ℕ} (H : HTSeq d) (Cs : Fin d → ℝ → ℝ) : Prop where
  nonneg : ∀ k x, 0 ≤ x → 0 ≤ Cs k x
  mono : ∀ k, MonotoneOn (Cs k) (Set.Ici 0)
  convex : ∀ k, ConvexOn ℝ (Set.Ici 0) (Cs k)
  conv : ∀ k, ∀ B : ℝ, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ x ∈ Set.Icc (0 : ℝ) B,
    |(H.Q n).C k (Real.sqrt n * x) - Cs k x| ≤ ε

/-- The marginal cost `c*_k = C*_k′` on `[0, ∞)` (one-sided at `0`). -/
noncomputable def mc {d : ℕ} (Cs : Fin d → ℝ → ℝ) (k : Fin d) (x : ℝ) : ℝ :=
  derivWithin (Cs k) (Set.Ici 0) x

/-- Assumption 3 (Cost regularity), p. 822: `C*` is strictly convex and `𝒞¹` on `[0, ∞)`, and the
solution of (43) at `y = W̃*_+(t)` is interior. The interior clause is imposed at the times where
`W̃*_+(t) > 0`; at `W̃*_+(t) = 0` the only point of `Ω` is `0`, which is never interior. -/
structure CostRegularity {d : ℕ} (M : Limits d) (Cs : Fin d → ℝ → ℝ) : Prop where
  strict : ∀ k, StrictConvexOn ℝ (Set.Ici 0) (Cs k)
  smooth : ∀ k, ContDiffOn ℝ 1 (Cs k) (Set.Ici 0)
  interior : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < Wstar M t → ∀ x : Fin d → ℝ,
    IsMin43 (fun k => M.lam k t) (fun k => M.rho k t) Cs (Wstar M t) x → ∀ k, 0 < x k

end GenCMu.HeavyTraffic


