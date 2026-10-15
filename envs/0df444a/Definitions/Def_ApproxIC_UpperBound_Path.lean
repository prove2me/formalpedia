-- Prove2me | Definitions.Def_ApproxIC_UpperBound_Path
-- name    : ApproxIC_UpperBound_Path
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:43.138834+00:00
-- url     : https://prove2.me/theorems/a707349c-2680-4fbc-a816-4d573be2e2a5
-- title:
--   §3.2.1, pp. 17–20 — the path relaxation M_path(ε), the dual (D) with Φ₁, Φ₂, ∆, the thresholds ν_k, the number of steps K and Lemma 2's λ^IC
-- statement:
--   This file defines the objects of the path-based duality approach of §3.2.1.
--
--   **Paths.** A path consists of numbers $0<\mu<\nu_0<\bar v$ and a candidate best response $v^\star:[\mu,\bar v]\to[0,\nu_0]$ that is strictly increasing and continuous, with $v^\star(\mu)=0$, $v^\star(\bar v)=\nu_0$ and $v^\star(v)<v$; $w:[0,\nu_0]\to[\mu,\bar v]$ is its inverse, and $\dot w$ its derivative.
--
--   **The relaxation $(P_{\text{path}})$.** $\mathcal M_{\text{path}}(\varepsilon)$ is the set of mechanisms $(x,t)$ with $x:S\to[0,1]$ such that
--   1. (IR$_\mu$) $v\,x(v)-t(v)\ge 0$ for $v\in[0,\mu]$;
--   2. (IC$_\mu$) $v\,x(v)-t(v)\ge v\,x(v^\star(v))-t(v^\star(v))-\varepsilon$ for $v\in[\mu,\bar v]$.
--
--   **The dual (D).** For $\lambda:[\mu,\bar v]\to\mathbb R$,
--   $$\Phi_1(\lambda)=\varepsilon\int_\mu^{\bar v}\lambda(v)\,dv,\qquad \Delta(v)=vf(v)-\dot w(v)\,(w(v)-v)\,\lambda(w(v))\,\mathbf 1_{\{v\in[0,\nu_0]\}},\qquad \Phi_2(\lambda)=\int_0^{\bar v}\Delta(v)^+\,dv .$$
--   $\lambda$ is dual feasible if $\lambda\ge 0$ on $[\mu,\bar v]$, $\lambda=f$ a.e. on $[\nu_0,\bar v]$ and $\lambda(v)=f(v)+\dot w(v)\lambda(w(v))$ a.e. on $[\mu,\nu_0]$.
--
--   **Steps.** The thresholds are $\nu_{-1}=\bar v$ and $\nu_k=v^\star(\nu_{k-1})$, equivalently $\nu_{k-1}=w(\nu_k)$; $K$ is the first index with $\nu_K\le\mu$. For $v\in[\mu,\bar v]$ lying in the step $[\nu_k,\nu_{k-1})$ (or $k=K$), Lemma 2's dual solution is
--   $$\lambda^{\star}(v)=\frac{d}{dv}\sum_{j=0}^{k}F(w^j(v)),$$
--   where $w^j$ is the $j$-th iterate of $w$.
--
--   These objects are used by Lemmas 1–4 and, through eq. (9), by the remaining milestones.
--
--   **Formalization Note** The thresholds form an $\mathbb N$-indexed sequence `nuSeq` with `nuSeq 0` $=\bar v$ (the paper's $\nu_{-1}$), so **the paper's $\nu_k$ is `nuSeq (k+1)`**. $\dot w$ is Lean's `deriv w`, which is $0$ where $w$ is not differentiable; since $w$ is assumed Lipschitz this is a null set. The Lipschitz property of $w$ on $[0,\nu_0]$ is an added, disclosed assumption (the paper only says $v^\star$ is continuous and increasing, but its change of variables needs absolute continuity; eq. (9)'s $w$ is Lipschitz). $\Phi_2$ uses the sign $(w(v)-v)$ of Lemma 4 and of the proof of Lemma 1; Lemma 1's printed $(v-w(v))$ is a slip. $\lambda^\star$ is $0$ off $[\mu,\bar v]$. The definitions `nuSeqOf`, `stepsOf`, `lamStarOf`, `DeltaOf` take the raw data $(\bar v,\mu,v^\star,w,\nu_0)$ so that eq. (9) can use them directly.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), pp. 17–20, §3.2.1, (P_path), Lemma 1 (D), thresholds ν_k and K (p. 19), Lemma 2, Lemma 4

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Setting

/-!
# The path relaxation, its dual and the step structure (arXiv:2103.03403v2, §3.2.1, pp. 17–20)

A path is a candidate best response `v⋆ : [µ, v̄] → [0, ν₀]` with inverse `w : [0, ν₀] → [µ, v̄]`.
The thresholds of p. 19 are "`ν_k = w(ν_{k+1})`, `k ≥ 0`, `ν_{−1} = v̄`"; here they form the
ℕ-indexed sequence `nuSeqOf vbar vstar` with `nuSeqOf … 0 = v̄` (the paper's `ν_{−1}`) and
`nuSeqOf … (k+1) = v⋆(nuSeqOf … k)`, so **the paper's `ν_k` is `nuSeqOf … (k+1)`**.
`K` ("the first index such that `ν_K ≤ µ`") is `stepsOf`.

The `…Of` definitions take the path's raw data, so that the explicit path of eq. (9) can use them
without a `Path` proof object; the `Path` versions below are abbreviations.
-/

namespace ApproxIC.UpperBound

open MeasureTheory

/-- A path (p. 17): `0 < µ < ν₀ < v̄`; `v⋆` strictly increasing and continuous on `[µ, v̄]` with
`v⋆(µ) = 0`, `v⋆(v̄) = ν₀`, values in `[0, ν₀]` and `v⋆(v) < v`; `w : [0, ν₀] → [µ, v̄]` its inverse.
Added (disclosed): `w` is Lipschitz on `[0, ν₀]`. -/
structure Path (M : Model) where
  /-- `µ`. -/
  mu : ℝ
  /-- `ν₀`. -/
  nu0 : ℝ
  /-- The candidate best response `v⋆`. -/
  vstar : ℝ → ℝ
  /-- The inverse `w` of `v⋆`. -/
  w : ℝ → ℝ
  mu_pos : 0 < mu
  mu_lt_nu0 : mu < nu0
  nu0_lt_vbar : nu0 < M.vbar
  vstar_strictMonoOn : StrictMonoOn vstar (Set.Icc mu M.vbar)
  vstar_continuousOn : ContinuousOn vstar (Set.Icc mu M.vbar)
  vstar_mu : vstar mu = 0
  vstar_vbar : vstar M.vbar = nu0
  vstar_mapsTo : Set.MapsTo vstar (Set.Icc mu M.vbar) (Set.Icc 0 nu0)
  vstar_lt : ∀ v ∈ Set.Icc mu M.vbar, vstar v < v
  w_mapsTo : Set.MapsTo w (Set.Icc 0 nu0) (Set.Icc mu M.vbar)
  w_vstar : ∀ v ∈ Set.Icc mu M.vbar, w (vstar v) = v
  vstar_w : ∀ u ∈ Set.Icc 0 nu0, vstar (w u) = u
  w_lipschitz : ∃ K, LipschitzOnWith K w (Set.Icc 0 nu0)

/-- `M_path(ε)` (p. 17): measurable mechanisms with `x : S → [0,1]`, (IR_µ) on `[0, µ]` and
(IC_µ) along the path on `[µ, v̄]`. -/
def MpathSet (M : Model) (P : Path M) (ε : ℝ) : Set Mech :=
  {m | IsMech M m ∧
    (∀ v ∈ Set.Icc 0 P.mu, 0 ≤ v * m.x v - m.t v) ∧
    (∀ v ∈ Set.Icc P.mu M.vbar,
      v * m.x (P.vstar v) - m.t (P.vstar v) - ε ≤ v * m.x v - m.t v)}

/-- `Φ₁(λ) = ε ∫_µ^{v̄} λ(v) dv` (Lemma 1, p. 18). -/
noncomputable def Phi1 (M : Model) (P : Path M) (ε : ℝ) (lam : ℝ → ℝ) : ℝ :=
  ε * ∫ v in P.mu..M.vbar, lam v

/-- The dual virtual value `∆(v) = v f(v) − ẇ(v)(w(v) − v) λ(w(v)) 1_{v ∈ [0, ν₀]}`
(Lemma 4, p. 20), with `ẇ = deriv w`, for raw path data `ν₀, w`. -/
noncomputable def DeltaOf (M : Model) (nu0 : ℝ) (w : ℝ → ℝ) (lam : ℝ → ℝ) (v : ℝ) : ℝ :=
  v * M.f v - deriv w v * (w v - v) * lam (w v) * (Set.Icc 0 nu0).indicator (fun _ => (1 : ℝ)) v

/-- `∆` for a path. -/
noncomputable def Delta (M : Model) (P : Path M) (lam : ℝ → ℝ) (v : ℝ) : ℝ :=
  DeltaOf M P.nu0 P.w lam v

/-- `Φ₂(λ) = ∫_0^{v̄} ∆(v)⁺ dv` (Lemma 1, p. 18, with the sign `(w(v) − v)` of Lemma 4). -/
noncomputable def Phi2 (M : Model) (P : Path M) (lam : ℝ → ℝ) : ℝ :=
  ∫ v in (0)..M.vbar, max 0 (Delta M P lam v)

/-- Feasibility for the dual problem (D) (Lemma 1, p. 18): `λ ≥ 0` on `[µ, v̄]`, `λ = f` a.e. on
`[ν₀, v̄]`, and `λ(v) = f(v) + ẇ(v) λ(w(v))` a.e. on `[µ, ν₀]`. -/
def DualFeasible (M : Model) (P : Path M) (lam : ℝ → ℝ) : Prop :=
  (∀ v ∈ Set.Icc P.mu M.vbar, 0 ≤ lam v) ∧
  (∀ᵐ v ∂(volume.restrict (Set.Icc P.nu0 M.vbar)), lam v = M.f v) ∧
  (∀ᵐ v ∂(volume.restrict (Set.Icc P.mu P.nu0)), lam v = M.f v + deriv P.w v * lam (P.w v))

/-- The thresholds (p. 19), ℕ-indexed: `nuSeqOf vbar vstar 0 = v̄` (the paper's `ν_{−1}`) and
`nuSeqOf vbar vstar (k+1) = v⋆(nuSeqOf vbar vstar k)`; the paper's `ν_k` is index `k + 1`. -/
def nuSeqOf (vbar : ℝ) (vstar : ℝ → ℝ) : ℕ → ℝ
  | 0 => vbar
  | k + 1 => vstar (nuSeqOf vbar vstar k)

/-- The number of steps `K` (p. 19): the least `k` with `ν_k ≤ µ`, i.e. `nuSeqOf … (k+1) ≤ µ`. -/
noncomputable def stepsOf (vbar mu : ℝ) (vstar : ℝ → ℝ) : ℕ :=
  sInf {k : ℕ | nuSeqOf vbar vstar (k + 1) ≤ mu}

/-- The step index of `v`: the least `k` with `ν_k ≤ v` (so `v ∈ [ν_k, ν_{k−1})`), capped at `K`. -/
noncomputable def stepIdxOf (vbar mu : ℝ) (vstar : ℝ → ℝ) (v : ℝ) : ℕ :=
  min (sInf {k : ℕ | nuSeqOf vbar vstar (k + 1) ≤ v}) (stepsOf vbar mu vstar)

/-- The dual solution of Lemma 2 (p. 20): for `v ∈ [µ, v̄]` with step index `k`,
`λ(v) = d/dv Σ_{j=0}^{k} F(w^j(v))`; `0` off `[µ, v̄]`. -/
noncomputable def lamStarOf (M : Model) (mu : ℝ) (vstar w : ℝ → ℝ) (v : ℝ) : ℝ :=
  if v ∈ Set.Icc mu M.vbar then
    deriv (fun u => ∑ j ∈ Finset.range (stepIdxOf M.vbar mu vstar v + 1), cdf M (w^[j] u)) v
  else 0

/-- `ν` for a path (the paper's `ν_k` is `nuSeq P (k+1)`). -/
def nuSeq {M : Model} (P : Path M) : ℕ → ℝ := nuSeqOf M.vbar P.vstar

/-- `K` for a path. -/
noncomputable def steps {M : Model} (P : Path M) : ℕ := stepsOf M.vbar P.mu P.vstar

/-- Lemma 2's `λ` for a path. -/
noncomputable def lamStar (M : Model) (P : Path M) : ℝ → ℝ := lamStarOf M P.mu P.vstar P.w

end ApproxIC.UpperBound


