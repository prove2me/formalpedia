-- Prove2me | Definitions.Def_UninformedMG_Phi
-- name    : UninformedMG_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:48.463391+00:00
-- url     : https://prove2.me/theorems/d856ea1f-0cd6-452b-986a-8a2bd010042d
-- title:
--   Visitation $d^{z,q,T}$, drift, second-order cost $\bar{\mathcal J}$ (22), $\mathcal J$, feasible set $\mathcal Q(z)$ and the objective $\Phi(z,q)$
-- statement:
--   Fix a joint variable $z=w\pi$, a mixing table $q$ and an initial state $s_1\in S_1$. Let $\mathcal T_{\mathrm{all}}=\prod_{h,s,a}\Delta(S_{h+1})$ be the set of **effective transition kernels** $T_h(\cdot\mid s,a)$.
--
--   1. **Visitation** (11): $d_1(s)=\mathbf 1\{s=s_1\}$ and $d_{h+1}(s')=\sum_{s,v,a}d_h(s)q_h(v\mid s)\pi_h(a\mid s,v)T_h(s'\mid s,a)$.
--   2. **Drift** (12): $\mathrm{Drift}(z,q,T)=\sum_{h,s,v,a}d_h(s)q_h(v\mid s)\pi_h(a\mid s,v)\big(v_h(s)-\sum_{s'}T_h(s'\mid s,a)v_{h+1}(s')\big)$.
--   3. **Second-order cost for bandit feedback** (22): $\displaystyle\bar{\mathcal J}_h(z,s,q)=2\sum_v\frac{q_h(v\mid s)^2}{w(v)}\Big(1+\sum_{a\in A_h}\frac{\pi_h(a\mid s,v)}{\mu^{z,q}_h(a\mid s)}\Big)$.
--   4. **Total cost** (13): $\mathcal J(z,q,T)=\sum_{h,s}d_h(s)\bar{\mathcal J}_h(z,s,q)$.
--   5. **Feasible set** (17): $\mathcal Q(z)=\{q:\ q_h(\cdot\mid s)\in\Delta(\mathcal V)\ \forall h,s;\ q_1(\cdot\mid s)=w\ \forall s\in S_1;\ \lambda q_h(v\mid s)\le w(v)\ \forall h,s,v\}$.
--   6. **Objective** (16): $\displaystyle\Phi(z,q)=\sup_{T\in\mathcal T_{\mathrm{all}}}\big\{\mathrm{Drift}(z,q,T)+\lambda\mathcal J(z,q,T)\big\}$.
--   7. With a general local cost $R_h(s,p)$ (32): $\Phi_R(z,q)=\sup_{T}\big\{\mathrm{Drift}(z,q,T)+\sum_{h,s}d_h(s)R_h(s,q_h(\cdot\mid s))\big\}$.
--
--   Algorithm 1 chooses its mixing table by minimizing $\Phi(z^k,\cdot)$ over $\mathcal Q(z^k)$. The objective is robust over every effective kernel, so the opponent's unobserved actions do not enter it.
--
--   **Formalization Note** The initial state $s_1$ is an explicit argument. The divisions use Lean's convention $x/0=0$. On $\mathcal Q(z)$ the constraint forces $q_h(v\mid s)=0$ when $w(v)=0$, and actions with zero sampling probability contribute zero, as the paper states (p.24). The supremum is the real supremum over the kernel subtype. For fixed $(z,q,s_1)$ the family is bounded above, so this is the true supremum.
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Eqs. (11)–(13), (16)–(17), pp.8–9 (PDF pp.10–11); Eq. (22), p.11 (PDF p.13); Eq. (32), p.22 (PDF p.24)

import Mathlib
import Definitions.Def_UninformedMG_IsJoint

namespace UninformedMG

variable {H : ℕ}

/-- An effective transition kernel `T_h(s' | s, a)` on the learner's actions (p.8). -/
abbrev Kernel (G : Game H) := (h : Fin H) → G.St h.castSucc → G.Act h → G.St h.succ → ℝ

/-- `T ∈ T_all = ∏_{h,s,a} Δ(S_{h+1})` (p.8 = PDF p.10): every row is a distribution. -/
def IsKernel (G : Game H) (T : Kernel G) : Prop :=
  ∀ h s a, T h s a ∈ stdSimplex ℝ (G.St h.succ)

/-- **State visitation** (Eq. (11), p.8 = PDF p.10): for the initial state `s₁`,
`d_1(s) = 1{s = s₁}` and `d_{h+1}(s') = ∑_{s,v,a} d_h(s) q_h(v|s) π_h(a|s,v) T_h(s'|s,a)`.
Lean layer `h` is paper step `h + 1`. -/
noncomputable def visit {G : Game H} (V : CandClass G) (π : CPolicy V) (q : Mixing V)
    (T : Kernel G) (s₁ : G.St 0) : (h : Fin (H + 1)) → G.St h → ℝ :=
  Fin.induction (motive := fun h => G.St h → ℝ) (fun s => if s = s₁ then 1 else 0)
    (fun i d s' => ∑ s, ∑ v, ∑ a, d s * q i s v * π i s v a * T i s a s')

/-- **Drift** (Eq. (12), p.8 = PDF p.10):
`Drift(z,q,T) = ∑_{h,s,v,a} d_h(s) q_h(v|s) π_h(a|s,v) (v_h(s) − ∑_{s'} T_h(s'|s,a) v_{h+1}(s'))`,
with `d = d^{z,q,T}` started at `s₁`. -/
noncomputable def drift {G : Game H} (V : CandClass G) (π : CPolicy V) (q : Mixing V)
    (T : Kernel G) (s₁ : G.St 0) : ℝ :=
  ∑ h : Fin H, ∑ s, ∑ v, ∑ a, visit V π q T s₁ h.castSucc s * q h s v * π h s v a *
    (V.val v h.castSucc s - ∑ s', T h s a s' * V.val v h.succ s')

/-- **Second-order cost for bandit feedback** (Eq. (22), p.11 = PDF p.13):
`J̄_h(z,s,q) = 2 ∑_v (q_h(v|s)² / w(v)) (1 + ∑_{a ∈ A_h} π_h(a|s,v) / μ^{z,q}_h(a|s))`, with the
mixture policy `μ^{z,q}_h(a|s) = ∑_v q_h(v|s) π_h(a|s,v)`.

**Formalization Note.** Lean's `x / 0 = 0` is used for both divisions. For `q ∈ Q(z)` the
constraint `λ q_h(v|s) ≤ w(v)` forces `q_h(v|s) = 0` when `w(v) = 0`, and the paper states that
"actions with zero sampling probability contribute zero" (p.24), so this agrees with the paper. -/
noncomputable def Jbar {G : Game H} (V : CandClass G) (w : V.C → ℝ) (π : CPolicy V)
    (q : Mixing V) (h : Fin H) (s : G.St h.castSucc) : ℝ :=
  2 * ∑ v, q h s v ^ 2 / w v * (1 + ∑ a, π h s v a / mixPol V q π h s a)

/-- **Total second-order cost** (Eq. (13), p.8 = PDF p.10): `𝒥(z,q,T) = ∑_{h,s} d_h(s) J̄_h(z,s,q)`. -/
noncomputable def Jcost {G : Game H} (V : CandClass G) (w : V.C → ℝ) (π : CPolicy V)
    (q : Mixing V) (T : Kernel G) (s₁ : G.St 0) : ℝ :=
  ∑ h : Fin H, ∑ s, visit V π q T s₁ h.castSucc s * Jbar V w π q h s

/-- **Feasible mixing tables** `Q(z)` (Eq. (17), p.9 = PDF p.11):
`Q(z) = {q : q_h(·|s) ∈ Δ(V) ∀ h, s; q_1(·|s) = w ∀ s ∈ S_1; λ q_h(v|s) ≤ w(v) ∀ h, s, v}`.
Lean step `0` is paper step 1. -/
def feasibleMix {G : Game H} (V : CandClass G) (lam : ℝ) (w : V.C → ℝ) (q : Mixing V) : Prop :=
  (∀ h s, q h s ∈ stdSimplex ℝ V.C) ∧ (∀ (h : Fin H), h.val = 0 → ∀ s, q h s = w) ∧
    ∀ h s v, lam * q h s v ≤ w v

/-- **Robust drift–cost objective** (Eq. (16), p.9, with Eq. (22), p.11):
`Φ(z, q) = sup_{T ∈ T_all} {Drift(z,q,T) + λ 𝒥(z,q,T)}`, for the initial state `s₁`.

**Formalization Note.** The supremum is the real `⨆` over the subtype of kernels. For fixed
`(z, q, s₁)` the objective is a polynomial in the entries of `T`, which range over a compact
set, so the family is bounded above and `⨆` is the true supremum (checked in the mission's
verification file). The initial state, implicit in the paper, is an explicit argument. -/
noncomputable def Phi {G : Game H} (V : CandClass G) (lam : ℝ) (w : V.C → ℝ) (π : CPolicy V)
    (q : Mixing V) (s₁ : G.St 0) : ℝ :=
  ⨆ T : {T : Kernel G // IsKernel G T}, drift V π q T.1 s₁ + lam * Jcost V w π q T.1 s₁

/-- **Drift–cost objective with a general local cost** (Eq. (32), p.22 = PDF p.24):
`Φ_R(z, q) = sup_{T ∈ T_all} {Drift(z,q,T) + ∑_{h,s} d^{z,q,T}_h(s) R_h(s, q_h(·|s))}`. -/
noncomputable def PhiR {G : Game H} (V : CandClass G) (π : CPolicy V)
    (R : (h : Fin H) → G.St h.castSucc → (V.C → ℝ) → ℝ) (q : Mixing V) (s₁ : G.St 0) : ℝ :=
  ⨆ T : {T : Kernel G // IsKernel G T},
    drift V π q T.1 s₁ + ∑ h : Fin H, ∑ s, visit V π q T.1 s₁ h.castSucc s * R h s (q h s)

end UninformedMG


