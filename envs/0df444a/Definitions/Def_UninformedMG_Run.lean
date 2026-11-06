-- Prove2me | Definitions.Def_UninformedMG_Run
-- name    : UninformedMG_Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:04.380464+00:00
-- url     : https://prove2.me/theorems/9b7bbab5-e2b3-4289-b240-37b7e26510e7
-- title:
--   A run of Algorithm 1: estimators (21), (24) and the updates (23), (25)
-- statement:
--   A **run of Algorithm 1** with parameter $\lambda$ inside an interaction consists of iterates $z^k=w^k\pi^k$ ($k=1,\dots,K+1$) and mixing tables $q^k$ ($k=1,\dots,K$) such that:
--
--   1. $z^1$ is the uniform start (6);
--   2. $w^k$, $\pi^k$ and $q^k$ are $F^k$-measurable;
--   3. $q^k\in\arg\min_{q\in\mathcal Q(z^k)}\sup_{T\in\mathcal T_{\mathrm{all}}}\{\mathrm{Drift}(z^k,q,T)+\lambda\mathcal J(z^k,q,T)\}$ with initial state $s_1=s^k_1$ (23);
--   4. the learner plays $\mu^k_h(a\mid s)=\mu^{z^k,q^k}_h(a\mid s)=\sum_vq^k_h(v\mid s)\pi^k_h(a\mid s,v)$;
--   5. with $\eta^k_h(s,v)=\lambda q^k_h(v\mid s)/w^k(v)$ and the **implicit-exploration estimator** (21)
--   $$\widehat Y^k_{h,s,v,a}=\frac{\mathbf 1\{s^k_h=s,\ a^k_h=a\}}{\mu^k_h(a\mid s)+\eta^k_h(s,v)}\Big(\frac{\ell^k_h}{H}+v_{h+1}(s^k_{h+1})\Big),$$
--   the loss vector (24) is $g^k_{h,s,v,a}=\frac{q^k_h(v\mid s)\mathbf 1\{s^k_h=s\}}{w^k(v)}\big(\widehat Y^k_{h,s,v,a}-v_h(s)\big)$;
--   6. $z^{k+1}\in\arg\min_{z\in\mathcal Z}\{\lambda\langle z,g^k\rangle+D_{\mathcal H_{\mathrm{res}}}(z\|z^k)\}$ (25), with $\langle z,g\rangle=\sum_{h,s,v,a}z_{h,s,v,a}g_{h,s,v,a}$.
--
--   On the grid, $v_{H+1}=0$, as the paper sets at the terminal stage.
--
--   **Formalization Note** (23) and (25) are argmin conditions at every outcome. The closed form of (25) is a consequence (Lemma B.1). $q^k$ may be any $F^k$-measurable selection of the argmin of (23). Every selection the learner can compute from its own observations is such a selection, so statements about runs hold for every implementation of the learner. Lean iterate $k$ is the paper's $z^{k+1}$.
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Algorithm 1, p.12 (PDF p.14); Eqs. (21)–(22), p.11 (PDF p.13); Eq. (6), p.5 (PDF p.7)

import Mathlib
import Definitions.Def_UninformedMG_Interaction
import Definitions.Def_UninformedMG_Phi
import Definitions.Def_UninformedMG_divRes

namespace UninformedMG

open MeasureTheory

variable {H : ℕ}

/-- Implicit-exploration parameter `η_h(s, v) = λ q_h(v | s) / w(v)` (Eq. (21), p.11). -/
noncomputable def eta {G : Game H} (V : CandClass G) (lam : ℝ) (w : V.C → ℝ) (q : Mixing V)
    (h : Fin H) (s : G.St h.castSucc) (v : V.C) : ℝ :=
  lam * q h s v / w v

/-- **Implicit-exploration estimator** (Eq. (21), p.11 = PDF p.13), on the trajectory `τ`:
`Ŷ_{h,s,v,a} = 1{s_h = s, a_h = a} / (μ_h(a|s) + η_h(s,v)) · (ℓ_h / H + v_{h+1}(s_{h+1}))`, with the
played policy `μ = μ^{z,q}`. (On the grid `v_{H+1} = 0`, as the paper sets at `h = H`.) -/
noncomputable def Yhat {G : Game H} (V : CandClass G) (lam : ℝ) (w : V.C → ℝ) (π : CPolicy V)
    (q : Mixing V) (τ : Traj G) (h : Fin H) (s : G.St h.castSucc) (v : V.C) (a : G.Act h) : ℝ :=
  (if τ.st h.castSucc = s ∧ τ.act h = a then 1 else 0) /
      (mixPol V q π h s a + eta V lam w q h s v) *
    (τ.loss h / (H : ℝ) + V.val v h.succ (τ.st h.succ))

/-- **Loss vector of the OMD step** (Eq. (24), p.12 = PDF p.14):
`g_{h,s,v,a} = q_h(v|s) 1{s_h = s} / w(v) · (Ŷ_{h,s,v,a} − v_h(s))`. -/
noncomputable def gEst {G : Game H} (V : CandClass G) (lam : ℝ) (w : V.C → ℝ) (π : CPolicy V)
    (q : Mixing V) (τ : Traj G) (h : Fin H) (s : G.St h.castSucc) (v : V.C) (a : G.Act h) : ℝ :=
  q h s v * (if τ.st h.castSucc = s then 1 else 0) / w v *
    (Yhat V lam w π q τ h s v a - V.val v h.castSucc s)

/-- `⟨z, g⟩ = ∑_{h,s,v,a} z_{h,s,v,a} g_{h,s,v,a}` for `z = wπ`. -/
noncomputable def pairing {G : Game H} (V : CandClass G) (w : V.C → ℝ) (π : CPolicy V)
    (g : (h : Fin H) → G.St h.castSucc → V.C → G.Act h → ℝ) : ℝ :=
  ∑ h : Fin H, ∑ s, ∑ v, ∑ a, w v * π h s v a * g h s v a

/-- The OMD objective of Eq. (25), `λ⟨z', g⟩ + D_{ℋres}(z' ‖ z)`, at `z' = w'π'`, for the current
iterate `z = wπ`. -/
noncomputable def omdObj {G : Game H} (V : CandClass G) (lam : ℝ) (w : V.C → ℝ) (π : CPolicy V)
    (g : (h : Fin H) → G.St h.castSucc → V.C → G.Act h → ℝ) (w' : V.C → ℝ) (π' : CPolicy V) : ℝ :=
  lam * pairing V w' π' g + divRes V w' π' w π

/-- **A run of Algorithm 1** (p.12 = PDF p.14) with parameter `λ` on the candidate class `V`,
inside the interaction `I`. Iterates `z^k = w^k π^k` (Lean `w k`, `pi k`, `k = 0, …, K`; Lean
iterate `k` is the paper's `z^{k+1}`) and mixing tables `q^k` (Lean `q k`, `k = 0, …, K − 1`):

1. start: `z¹` uniform (Eq. (6));
2. `w^k, π^k, q^k` are `F^k`-measurable;
3. `q^k ∈ argmin_{q ∈ Q(z^k)} sup_{T ∈ T_all} {Drift(z^k,q,T) + λ𝒥(z^k,q,T)}` with
   `s₁ = s^k_1` (Eq. (23));
4. the learner plays `μ^k_h(a|s) = ∑_v q^k_h(v|s) π^k_h(a|s,v)`;
5. `z^{k+1} ∈ argmin_{z ∈ Z} {λ⟨z, g^k⟩ + D_{ℋres}(z ‖ z^k)}` (Eq. (25)), with `g^k` of Eq. (24)
   computed on the realized trajectory of episode `k`.

**Formalization Note.** (23) and (25) are kept as argmin conditions, at every outcome `ω`; the
closed form of (25) is Lemma B.1, a consequence. `q^k` may be any `F^k`-measurable selection of
the argmin of (23): every selection the learner can compute from its observations is one, so the
mission's statements hold for every learner implementation. -/
structure Run {G : Game H} (V : CandClass G) {K : ℕ} (lam : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (I : Interaction G K Ω P) where
  /-- Candidate weights `w^k`. -/
  w : Fin (K + 1) → Ω → V.C → ℝ
  /-- Candidate-conditional policies `π^k`. -/
  pi : Fin (K + 1) → Ω → CPolicy V
  /-- Mixing tables `q^k`. -/
  q : Fin K → Ω → Mixing V
  init_w : ∀ ω, w 0 ω = unifW V
  init_pi : ∀ ω, pi 0 ω = unifPi V
  w_meas : ∀ k : Fin K, Measurable[I.filt (toLex (k, 0))] (w k.castSucc)
  pi_meas : ∀ k : Fin K, Measurable[I.filt (toLex (k, 0))] (pi k.castSucc)
  q_meas : ∀ k : Fin K, Measurable[I.filt (toLex (k, 0))] (q k)
  q_feasible : ∀ (k : Fin K) ω, feasibleMix V lam (w k.castSucc ω) (q k ω)
  q_argmin : ∀ (k : Fin K) ω q', feasibleMix V lam (w k.castSucc ω) q' →
    Phi V lam (w k.castSucc ω) (pi k.castSucc ω) (q k ω) (I.st k 0 ω) ≤
      Phi V lam (w k.castSucc ω) (pi k.castSucc ω) q' (I.st k 0 ω)
  play : ∀ (k : Fin K) ω, I.lpol k ω = mixPol V (q k ω) (pi k.castSucc ω)
  update_joint : ∀ (k : Fin K) ω, IsJoint V (w k.succ ω) (pi k.succ ω)
  update_argmin : ∀ (k : Fin K) ω w' π', IsJoint V w' π' →
    omdObj V lam (w k.castSucc ω) (pi k.castSucc ω)
        (gEst V lam (w k.castSucc ω) (pi k.castSucc ω) (q k ω) (I.traj k ω))
        (w k.succ ω) (pi k.succ ω) ≤
      omdObj V lam (w k.castSucc ω) (pi k.castSucc ω)
        (gEst V lam (w k.castSucc ω) (pi k.castSucc ω) (q k ω) (I.traj k ω)) w' π'

/-- The loss vector `g^k` of episode `k` of a run at the outcome `ω` (Eq. (24)). -/
noncomputable def Run.g {G : Game H} {V : CandClass G} {K : ℕ} {lam : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {I : Interaction G K Ω P} (R : Run V lam I) (k : Fin K)
    (ω : Ω) : (h : Fin H) → G.St h.castSucc → V.C → G.Act h → ℝ :=
  gEst V lam (R.w k.castSucc ω) (R.pi k.castSucc ω) (R.q k ω) (I.traj k ω)

end UninformedMG


