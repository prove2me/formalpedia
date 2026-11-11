-- Prove2me | Definitions.Def_DPCutRelease_Main_Algorithms
-- name    : DPCutRelease_Main_Algorithms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:13:05.473491+00:00
-- url     : https://prove2.me/theorems/3b7b68ec-4bee-4b10-aa30-9b5e45002fe9
-- title:
--   Algorithms 1–4 (CutRelease, FindWitness, AggregateWitnesses, ClipEdgeWeights) as functions of an explicit noise source, with the Θ-constants as a parameter structure
-- statement:
--   **Randomness.** Each algorithm is a deterministic function of its input and of a noise source $\omega$ whose law makes a countable family of entries i.i.d. $N(0,1)$ and another, independent, i.i.d. $\mathrm{Lap}(1)$; every draw of the pseudocode reads its own entry, so all draws are independent. $\mathrm{Lap}(b)=b\cdot\mathrm{Lap}(1)$, and a draw from $N(0,X_D)$ is $X_D^{1/2}$ times a standard normal vector.
--
--   **Constants.** The $\Theta(\cdot)$ parameters are $k=\lceil c_k\log\frac n{\beta_\chi\delta_1}\rceil$, $K=\lceil c_K\log\frac n{\beta_{GE}}\rceil$, $\lambda=c_\lambda\frac1{\varepsilon_1}\log\frac n{\beta_{GE}\delta_{GE}}$, $T_1=\lceil c_{T_1}\log(nU)\rceil$, and $M_{stop}=c_{stop}\big(nUL+\frac n{\gamma\varepsilon}L^6\big)$ with $L=\log\frac{nU}{\delta\beta\gamma\varepsilon}$. A lemma with $\Theta$-parameters is stated for all constants in a region "$c_k,c_K,c_{T_1}\ge c_0$, then $c_\lambda\ge f(c_k,c_K,c_{T_1})$, then $c_{stop}\ge g(c_k,c_K,c_{T_1},c_\lambda)$".
--
--   **Algorithm 2, FindWitness$(D,r)$.** $\varepsilon_1=\frac{\varepsilon_{GE}}{320K(1+\log(2/\delta_{GE}))}$, $\delta_1=\frac{\delta_{GE}}{20n^2K}$, $\beta_1=\beta_\chi=\frac{\beta_{GE}}{4n^2K}$, $\tau_1=\log(1/\beta_1)/\varepsilon_1$. If $r=0$ return $\bot$. Otherwise compute $X_D$; for trials $1,\dots,K$: draw $Z^{(1..k)}\sim N(0,X_D)$, form $\hat g$, $Y=\langle D,\hat g\rangle+\mathrm{Lap}(1/\varepsilon_1)$, $\hat g_{\max}=\max\{\hat g(e):r(e)>0\}$; if $Y<\tau_1$ or $\hat g_{\max}=0$ continue, else return $g(e)=r(e)\hat g(e)/\hat g_{\max}$. After $K$ trials return $\bot$.
--
--   **Algorithm 3, AggregateWitnesses$(w,h,\gamma)$.** From $(g^+,g^-,r)=(0,0,\mathbf 1)$ loop: if $r=0$ return $(g^+,g^-,0)$; try FindWitness$(r\odot(h-(1+\gamma)w),r)$, on success add to $g^+$ and subtract from $r$; else try FindWitness$(r\odot((1-\gamma)w-h),r)$, on success add to $g^-$ and subtract from $r$; else return $(g^+,g^-,r)$.
--
--   **Algorithm 1, CutRelease$(w)$.** $T_2=1+\lceil64(1+\gamma)^2\log n/\gamma^2\rceil$, $\eta=\frac\gamma{8(1+\gamma)}$, $\varepsilon_2=\frac\varepsilon{2T_1}$, $\beta_2=\frac\beta{2T_1}$, $\tau_2=\frac{\log(1/\beta_2)}{\varepsilon_2}$, $\varepsilon_{GE}=\frac{\varepsilon}{4T_1\sqrt{2T_2\log(2T_1/\delta)}}$, $\delta_{GE}=\frac\delta{2T_1T_2}$, $\beta_{GE}=\frac\beta{2T_1T_2}$. From $a_1=\mathbf 1$, $\tilde w=0$, for $i=1..T_1$: $w_i=a_i\odot w$, $\tilde M_i=\max(0,\sum_ew_i(e)+\mathrm{Lap}(1/\varepsilon_2)+\tau_2)$; if $a_i=0$ or $\tilde M_i\le M_{stop}$ return $\tilde w$; $h_i=\tilde M_i a_i/\sum_ea_i(e)$, $a_{i+1}=a_i$; for $t=1..T_2$: $(g^+,g^-,r)\leftarrow$ AggregateWitnesses$(w_i,h_i,\gamma)$; if $\langle h_i,r\rangle\ge\max\{\langle h_i,g^+\rangle,\langle h_i,g^-\rangle\}$ then $\tilde w\mathrel{+}=h_i\odot r$, $a_{i+1}=a_i\odot(\mathbf 1-r)$, break; else $(\theta,g)=(1,g^+)$ if $\langle h_i,g^+\rangle\ge\langle h_i,g^-\rangle$, else $(-1,g^-)$, and $h_i(e)\leftarrow\tilde M_i\frac{h_i(e)e^{-\theta\eta g(e)}}{\sum_{e'}h_i(e')e^{-\theta\eta g(e')}}$. Return $\tilde w$.
--
--   **Algorithm 4, ClipEdgeWeights (Eqs. (5)–(6)).** $U=\frac8{\varepsilon_0\gamma}\log\frac n{\beta_0}$, $V=\frac2{\varepsilon_0}\log\frac n{\beta_0}$, $v_e=(w_e-U)_+$, $w'_e=\min\{w_e,U\}$, $Y_e=\max\{0,v_e+L_e-V\}$ with $L_e\sim\mathrm{Lap}(1/\varepsilon_0)$ i.i.d.
--
--   **Formalization Note.** `noiseLaw` is the product of `Measure.infinitePi` of `gaussianReal 0 1` and of `PrivLearn.Generic.laplace 1` over keys `List ℕ`; `ω.sub j` is the independent sub-source of keys starting with `j`. Trial $j$ of a FindWitness call reads Gaussian keys $[j,s,u]$ and Laplace key $[j]$; iteration $m$ of AggregateWitnesses uses sub-sources $2m$ and $2m+1$; step $t$ of round $i$ of CutRelease uses $i\to1\to t$ and the mass release key $[i,0]$; clipping reads Laplace key $[u,v]$. `aggLoop` has fuel $\binom n2+1$ (each success zeroes a positive coordinate of $r$, so the fuel never runs out). `cutReleaseStopped` records whether the run returned at line 7. $\hat g_{\max}$ is a fold of `max` from $0$.
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 13, Algorithm 1; p. 16, Algorithm 2; p. 17, Algorithm 3; p. 18, Algorithm 4 and Eqs. (5)–(6)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_SDP

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

namespace DPCutRelease.Main

/-!
# Algorithms 1–4 (CutRelease, FindWitness, AggregateWitnesses, ClipEdgeWeights)

Eliáš et al., arXiv:2611.06670v1, p. 13 (Algorithm 1), p. 16 (Algorithm 2), p. 17 (Algorithm 3),
p. 18 (Algorithm 4, Eqs. (5)–(6)).

**Randomness.** An algorithm is a deterministic function of its input and of a noise source
`ω : Noise = (List ℕ → ℝ) × (List ℕ → ℝ)`, whose law `noiseLaw` makes all entries independent,
the first family i.i.d. `N(0, 1)` and the second i.i.d. `Lap(1)` (`PrivLearn.Generic.laplace 1`).
Every random draw of the pseudocode reads its own key (a list of naturals), so distinct draws are
independent: `ω.sub j` restricts to the keys starting with `j` (an independent copy of `ω`).
A `Lap(b)` draw is `b · L` with `L ∼ Lap(1)`, and a draw of `N(0, X)` is `X^{1/2} Z` with
`Z ∼ N(0, I_n)` and `X^{1/2} = CFC.sqrt X` (as in Mathlib's `multivariateGaussian`).

**Θ-parameters.** `Consts` holds the universal constants hidden in the `Θ(·)` of Algorithms 1–2
(`k`, `K`, `λ`, `T₁`) and the constant `C` of `M_stop`: `k = ⌈c_k log(n/(β_χ δ₁))⌉`,
`K = ⌈c_K log(n/β_GE)⌉`, `λ = c_λ (1/ε₁) log(n/(β_GE δ_GE))`, `T₁ = ⌈c_{T₁} log(nU)⌉`,
`M_stop = c_stop (nU L + (n/(γε)) L⁶)` with `L = log(nU/(δβγε))`. Every other parameter is the
explicit formula of the pseudocode. `Consts.LargeEnough` is the region "constants sufficiently
large": `c_k, c_K, c_{T₁} ≥ c₀`, then `c_λ` above a threshold depending on them, then `c_stop`
above a threshold depending on all four. A lemma whose parameters are `Θ(·)` is stated for every
constant structure in such a region (with `c₀` and the thresholds existentially chosen first);
finitely many such regions always intersect, so the lemmas compose for one choice of constants.

**Loops.** `AggregateWitnesses` loops until `r = 0` or both searches fail; each success zeroes a
coordinate of `r` that was positive, so it runs at most `(n choose 2) + 1` iterations, which is
the fuel given to `aggLoop` (the fuel-exhausted branch is unreachable). `ĝ_max` is the maximum of
`ĝ` over `{e : r(e) > 0}` (computed as a fold of `max` from `0`, which is the maximum since
`ĝ ≥ 0`; `0` on the empty set, which never occurs when `r ≠ 0`, `r ≥ 0`).
-/

/-- The noise source: a family of `N(0,1)` entries and a family of `Lap(1)` entries, both indexed
by keys `List ℕ`. -/
abbrev Noise : Type := (List ℕ → ℝ) × (List ℕ → ℝ)

/-- The law of the noise: all entries independent, i.i.d. `N(0,1)` and i.i.d. `Lap(1)`. -/
noncomputable def noiseLaw : Measure Noise :=
  (Measure.infinitePi fun _ : List ℕ => gaussianReal 0 1).prod
    (Measure.infinitePi fun _ : List ℕ => PrivLearn.Generic.laplace 1)

/-- The sub-source of keys beginning with `j` (an independent copy of the source). -/
def Noise.sub (ω : Noise) (j : ℕ) : Noise := (fun l => ω.1 (j :: l), fun l => ω.2 (j :: l))

/-- The universal constants hidden in the `Θ(·)` parameters of Algorithms 1–2 and in `M_stop`. -/
structure Consts where
  /-- `k = ⌈c_k log(n/(β_χ δ₁))⌉` -/
  ck : ℝ
  /-- `K = ⌈c_K log(n/β_GE)⌉` -/
  cK : ℝ
  /-- `λ = c_λ (1/ε₁) log(n/(β_GE δ_GE))` -/
  clam : ℝ
  /-- `T₁ = ⌈c_{T₁} log(nU)⌉` -/
  cT1 : ℝ
  /-- `M_stop = c_stop (nU L + (n/(γε)) L⁶)` -/
  cStop : ℝ

/-- The constants are "sufficiently large": `c_k, c_K, c_{T₁} ≥ c₀`, `c_λ ≥ f(c_k, c_K, c_{T₁})`,
`c_stop ≥ g(c_k, c_K, c_{T₁}, c_λ)`. -/
def Consts.LargeEnough (θ : Consts) (c0 : ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (g : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  c0 ≤ θ.ck ∧ c0 ≤ θ.cK ∧ c0 ≤ θ.cT1 ∧ f θ.ck θ.cK θ.cT1 ≤ θ.clam ∧
    g θ.ck θ.cK θ.cT1 θ.clam ≤ θ.cStop

/-! ## Algorithm 2 (FindWitness) -/

/-- The parameters of Algorithm 2: `k` samples per trial, `K` trials, `λ`, the noise scale
`1/ε₁` and the threshold `τ₁`. -/
structure FWParams where
  k : ℕ
  K : ℕ
  lam : ℝ
  eps1 : ℝ
  tau1 : ℝ

/-- Algorithm 2, line 1, from `(ε_GE, δ_GE, β_GE)`: `K = Θ(log(n/β_GE))`,
`ε₁ = ε_GE/(320 K (1 + log(2/δ_GE)))`, `δ₁ = δ_GE/(20 n² K)`, `β₁ = β_χ = β_GE/(4 n² K)`,
`k = Θ(log(n/(β_χ δ₁)))`, `λ = Θ((1/ε₁) log(n/(β_GE δ_GE)))`, `τ₁ = log(1/β₁)/ε₁`. -/
noncomputable def fwParams (θ : Consts) (n : ℕ) (epsGE deltaGE betaGE : ℝ) : FWParams :=
  let K : ℕ := ⌈θ.cK * Real.log (n / betaGE)⌉₊
  let eps1 : ℝ := epsGE / (320 * K * (1 + Real.log (2 / deltaGE)))
  let delta1 : ℝ := deltaGE / (20 * (n : ℝ) ^ 2 * K)
  let betaChi : ℝ := betaGE / (4 * (n : ℝ) ^ 2 * K)
  { k := ⌈θ.ck * Real.log (n / (betaChi * delta1))⌉₊
    K := K
    lam := θ.clam * (1 / eps1) * Real.log (n / (betaGE * deltaGE))
    eps1 := eps1
    tau1 := Real.log (1 / betaChi) / eps1 }

/-- `max{v(e) : r(e) > 0}` (fold of `max` from `0`). -/
noncomputable def maxOnSupport {n : ℕ} (r v : EdgeVec n) : ℝ :=
  (Finset.univ.filter fun e => 0 < r e).fold max 0 v

/-- One trial (lines 7–15) of Algorithm 2 on the trial's noise: `k` vectors `Z^{(s)} = X^{1/2} G^{(s)}`
with `G^{(s)}` standard normal (keys `[j, s, u]`), `ĝ`, `Y = ⟨D, ĝ⟩ + L/ε₁` (key `[j]`);
`none` = "continue", else the witness `g(e) = r(e) ĝ(e)/ĝ_max`. -/
noncomputable def fwTrial {n : ℕ} (P : FWParams) (D r : EdgeVec n) (X : Mat n) (ω : Noise)
    (j : ℕ) : Option (EdgeVec n) :=
  let Z : Fin P.k → EuclideanSpace ℝ (Fin n) := fun s =>
    WithLp.toLp 2 (CFC.sqrt X *ᵥ fun u => ω.1 [j, s.val, u.val])
  let gh : EdgeVec n := ghat Z
  let Y : ℝ := dot D gh + ω.2 [j] / P.eps1
  let gmax : ℝ := maxOnSupport r gh
  if Y < P.tau1 ∨ gmax = 0 then none else some (fun e => r e * gh e / gmax)

/-- Algorithm 2, `FindWitness(D, r)`: `⊥` (`none`) if `r = 0`; otherwise compute `X_D` and run
trials `j = 0, …, K − 1`, returning the first witness found, or `⊥` after `K` trials. -/
noncomputable def findWitness {n : ℕ} (P : FWParams) (D r : EdgeVec n) (ω : Noise) :
    Option (EdgeVec n) :=
  if r = 0 then none else
    (List.range P.K).findSome? (fwTrial P D r (XD P.lam D) ω)

/-! ## Algorithm 3 (AggregateWitnesses) -/

/-- The loop of Algorithm 3 with `fuel` iterations left, iteration counter `m` and state
`(g⁺, g⁻, r)`; iteration `m` uses the noise `ω.sub (2m)` for the `D⁺` search and `ω.sub (2m+1)`
for the `D⁻` search. -/
noncomputable def aggLoop {n : ℕ} (P : FWParams) (w h : EdgeVec n) (γ : ℝ) (ω : Noise) :
    ℕ → ℕ → EdgeVec n × EdgeVec n × EdgeVec n → EdgeVec n × EdgeVec n × EdgeVec n
  | 0, _, s => s
  | fuel + 1, m, (gp, gm, r) =>
    if r = 0 then (gp, gm, 0) else
      match findWitness P (r * (h - (1 + γ) • w)) r (ω.sub (2 * m)) with
      | some g => aggLoop P w h γ ω fuel (m + 1) (gp + g, gm, r - g)
      | none =>
        match findWitness P (r * ((1 - γ) • w - h)) r (ω.sub (2 * m + 1)) with
        | some g => aggLoop P w h γ ω fuel (m + 1) (gp, gm + g, r - g)
        | none => (gp, gm, r)

/-- Algorithm 3, `AggregateWitnesses(w, h, γ)`: returns `(g⁺, g⁻, r)`, starting from
`(0, 0, 1)`. -/
noncomputable def aggregate {n : ℕ} (P : FWParams) (w h : EdgeVec n) (γ : ℝ) (ω : Noise) :
    EdgeVec n × EdgeVec n × EdgeVec n :=
  aggLoop P w h γ ω (Fintype.card (Pair n) + 1) 0 (0, 0, 1)

/-! ## Algorithm 1 (CutRelease) -/

/-- The parameters of Algorithm 1 (line 1) for `n, U, γ, ε, δ, β`. -/
structure A1Params where
  T1 : ℕ
  T2 : ℕ
  Mstop : ℝ
  eta : ℝ
  eps2 : ℝ
  beta2 : ℝ
  tau2 : ℝ
  epsGE : ℝ
  deltaGE : ℝ
  betaGE : ℝ
  gamma : ℝ
  fw : FWParams

/-- Algorithm 1, line 1: `T₁ = Θ(log(nU))`, `T₂ = 1 + ⌈64(1+γ)² log n/γ²⌉`,
`M_stop = C(nU log(nU/(δβγε)) + (n/(γε)) (log(nU/(δβγε)))⁶)`, `η = γ/[8(1+γ)]`, `ε₂ = ε/(2T₁)`,
`β₂ = β/(2T₁)`, `τ₂ = log(1/β₂)/ε₂`, `ε_GE = ε/(4T₁ √(2T₂ log(2T₁/δ)))`, `δ_GE = δ/(2T₁T₂)`,
`β_GE = β/(2T₁T₂)`, and Algorithm 2's parameters from `(ε_GE, δ_GE, β_GE)`. -/
noncomputable def a1Params (θ : Consts) (n : ℕ) (U γ ε δ β : ℝ) : A1Params :=
  let T1 : ℕ := ⌈θ.cT1 * Real.log (n * U)⌉₊
  let T2 : ℕ := 1 + ⌈64 * (1 + γ) ^ 2 * Real.log n / γ ^ 2⌉₊
  let L : ℝ := Real.log (n * U / (δ * β * γ * ε))
  let eps2 : ℝ := ε / (2 * T1)
  let beta2 : ℝ := β / (2 * T1)
  let epsGE : ℝ := ε / (4 * T1 * Real.sqrt (2 * T2 * Real.log (2 * T1 / δ)))
  let deltaGE : ℝ := δ / (2 * T1 * T2)
  let betaGE : ℝ := β / (2 * T1 * T2)
  { T1 := T1
    T2 := T2
    Mstop := θ.cStop * (n * U * L + n / (γ * ε) * L ^ 6)
    eta := γ / (8 * (1 + γ))
    eps2 := eps2
    beta2 := beta2
    tau2 := Real.log (1 / beta2) / eps2
    epsGE := epsGE
    deltaGE := deltaGE
    betaGE := betaGE
    gamma := γ
    fw := fwParams θ n epsGE deltaGE betaGE }

/-- Line 5: `M̃_i = max(0, M_i + Lap(1/ε₂) + τ₂)` with `M_i = Σ_e (a ⊙ w)(e)`, Laplace key `[0]`
of the round's noise. -/
noncomputable def massEstimate {n : ℕ} (P : A1Params) (w a : EdgeVec n) (ω : Noise) : ℝ :=
  max 0 (∑ e, (a * w) e + ω.2 [0] / P.eps2 + P.tau2)

/-- Lines 10–20: the MWU steps of one outer round on `w_i`, with `M̃_i` = `Mt`, `fuel` steps left,
step counter `t` and current `h_i`; step `t` calls AggregateWitnesses on `ω.sub t`. Returns
`some (h_i, r_i)` at the break of line 15, `none` if all `T₂` steps pass without a break. -/
noncomputable def innerLoop {n : ℕ} (P : A1Params) (wi : EdgeVec n) (Mt : ℝ) (ω : Noise) :
    ℕ → ℕ → EdgeVec n → Option (EdgeVec n × EdgeVec n)
  | 0, _, _ => none
  | fuel + 1, t, h =>
    let res := aggregate P.fw wi h P.gamma (ω.sub t)
    let gp := res.1
    let gm := res.2.1
    let r := res.2.2
    if max (dot h gp) (dot h gm) ≤ dot h r then some (h, r) else
      let θg : ℝ × EdgeVec n := if dot h gm ≤ dot h gp then (1, gp) else (-1, gm)
      let Wsum : ℝ := ∑ e, h e * Real.exp (-θg.1 * P.eta * θg.2 e)
      innerLoop P wi Mt ω fuel (t + 1) (fun e => Mt * (h e * Real.exp (-θg.1 * P.eta * θg.2 e)) / Wsum)

/-- Lines 9–20 of one outer round with mask `a` (round noise `ω`): `h_i = M̃_i a/Σ a`, then the MWU
steps on the noise `ω.sub 1`. -/
noncomputable def roundBreak {n : ℕ} (P : A1Params) (w a : EdgeVec n) (ω : Noise) :
    Option (EdgeVec n × EdgeVec n) :=
  let Mt := massEstimate P w a ω
  innerLoop P (a * w) Mt (ω.sub 1) P.T2 1 (fun e => Mt * a e / ∑ e', a e')

/-- Lines 3–22: the outer loop with `fuel` rounds left, round counter `i`, mask `a_i` and estimate
`w̃`; round `i` uses the noise `ω.sub i`. The flag is `true` when the run returned at line 7
(`a_i = 0` or `M̃_i ≤ M_stop`) and `false` when the `T₁` rounds ran out (line 22). -/
noncomputable def outerLoop {n : ℕ} (P : A1Params) (w : EdgeVec n) (ω : Noise) :
    ℕ → ℕ → EdgeVec n → EdgeVec n → EdgeVec n × Bool
  | 0, _, _, wt => (wt, false)
  | fuel + 1, i, a, wt =>
    if a = 0 ∨ massEstimate P w a (ω.sub i) ≤ P.Mstop then (wt, true) else
      match roundBreak P w a (ω.sub i) with
      | some (h, r) => outerLoop P w ω fuel (i + 1) (a * (1 - r)) (wt + h * r)
      | none => outerLoop P w ω fuel (i + 1) a wt

/-- Algorithm 1, `CutRelease(w)`: the released `w̃` (from `a₁ = 1`, `w̃ = 0`, `T₁` rounds). -/
noncomputable def cutRelease {n : ℕ} (P : A1Params) (w : EdgeVec n) (ω : Noise) : EdgeVec n :=
  (outerLoop P w ω P.T1 1 1 0).1

/-- Whether the run of Algorithm 1 returned at line 7 (`a_i = 0` or `M̃_i ≤ M_stop`) within its `T₁`
outer rounds. -/
noncomputable def cutReleaseStopped {n : ℕ} (P : A1Params) (w : EdgeVec n) (ω : Noise) : Bool :=
  (outerLoop P w ω P.T1 1 1 0).2

/-! ## Algorithm 4 (ClipEdgeWeights), Eqs. (5)–(6) -/

/-- `U = (8/(ε₀γ)) log(n/β₀)`. -/
noncomputable def clipU (n : ℕ) (γ ε0 β0 : ℝ) : ℝ := 8 / (ε0 * γ) * Real.log (n / β0)

/-- `V = (2/ε₀) log(n/β₀)`. -/
noncomputable def clipV (n : ℕ) (ε0 β0 : ℝ) : ℝ := 2 / ε0 * Real.log (n / β0)

/-- Eq. (5): the bounded part `w'_e = min{w_e, U}`. -/
noncomputable def clipW {n : ℕ} (γ ε0 β0 : ℝ) (w : EdgeVec n) : EdgeVec n :=
  fun e => min (w e) (clipU n γ ε0 β0)

/-- Eq. (5): the excess `v_e = (w_e − U)_+`. -/
noncomputable def clipExcess {n : ℕ} (γ ε0 β0 : ℝ) (w : EdgeVec n) : EdgeVec n :=
  fun e => max (w e - clipU n γ ε0 β0) 0

/-- Eq. (6): `Y_e = max{0, v_e + L_e − V}` with `L_e ∼ Lap(1/ε₀)` (Laplace key `[u, v]`). -/
noncomputable def clipY {n : ℕ} (γ ε0 β0 : ℝ) (w : EdgeVec n) (ω : Noise) : EdgeVec n :=
  fun e => max 0 (clipExcess γ ε0 β0 w e + ω.2 [e.1.1.val, e.1.2.val] / ε0 - clipV n ε0 β0)

end DPCutRelease.Main


