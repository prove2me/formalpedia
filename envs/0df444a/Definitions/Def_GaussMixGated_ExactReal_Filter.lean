-- Prove2me | Definitions.Def_GaussMixGated_ExactReal_Filter
-- name    : GaussMixGated_ExactReal_Filter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:25:25.429223+00:00
-- url     : https://prove2.me/theorems/70617dfc-996e-43fd-a1a6-4167b39d612d
-- title:
--   The weighted robust mean filter of §8.3, the spectral step, and the cover procedure of §8.4
-- statement:
--   For $x_1,\dots,x_n\in\mathbb R^d$, constants $K,B$ and a direction rule, the **filter** starts from $w_i=1/n$ and repeats at most $n$ times:
--
--   1. $W=\sum_iw_i$; if $W<1/2$ return $0$; otherwise $a=\sum_iw_ix_i/W$ and $M=\sum_iw_i(x_i-a)(x_i-a)^{\top}/W$.
--   2. If $M=0$ return $a$; otherwise take the rule's unit vector $v$ and $q=v^{\top}Mv$.
--   3. If $q\le100KB^2$ return $a$; otherwise $g_i=[v\cdot(x_i-a)]^2$, $g_{\max}=\max_{w_i>0}g_i$; if $g_{\max}=0$ return $a$, else replace each positive $w_i$ by $w_i(1-g_i/g_{\max})$.
--
--   If no round returns, the result is $0$. A **direction rule** must give, for every nonzero PSD $M$, a unit $v$ with $\lambda_{\max}(M)/2\le v^{\top}Mv\le\lambda_{\max}(M)$. The **spectral step** computes $y_j=M^re_j$, $r=\lceil\log(2d)/(2\log(4/3))\rceil$, and returns $y_j/\|y_j\|$ for the first nonzero $y_j$ of largest Rayleigh quotient.
--
--   The **cover procedure** of §8.4 with constants $C,K$: $N_{\mathrm{cov}}=\lceil(4k/\beta)\log(2k/\delta_{\mathrm{cov}})\rceil$, $n=\lceil C[d\log(2d)+\log(4N_{\mathrm{cov}}/\delta_{\mathrm{cov}})]\rceil$, $L=\log(2k/\beta)$, $B=4\sigma\sqrt L$. For each $t<N_{\mathrm{cov}}$ it forms $y_t=X_t+\sigma G_t$, draws $n$ posterior samples at $y_t$, runs the filter with the spectral step and returns $c_t=2a-y_t$. Its random inputs are the observations, the Gaussian tape (coordinates $td,\dots,td+d-1$ for $G_t$) and the posterior draws (draws $tn,\dots,tn+n-1$ for query $t$).
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF pp. 20–21, §8.3; PDF p. 22, deterministic spectral step and §8.4

import Mathlib
import Definitions.Def_GaussMixGated_ExactReal_Machine

open MeasureTheory ProbabilityTheory

noncomputable section

namespace GaussMixGated.ExactReal

/-!
# The weighted robust mean filter and the posterior cover procedure
(Zheng–Xie–He, STOC 2027 #36, §8.3–8.4, PDF pp. 20–22)

Vectors of `ℝ^d` are `EuclideanSpace ℝ (Fin d)`, `d × d` matrices are `Matrix (Fin d) (Fin d) ℝ`.
-/

/-- The quadratic form `vᵀ M v`. -/
def quadForm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ j, ∑ l, v j * M j l * v l

/-- `λ_max(M)`: the supremum of `vᵀ M v` over unit vectors. -/
def lamMax {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ v : {v : EuclideanSpace ℝ (Fin d) // ‖v‖ = 1}, quadForm M v.1

/-- The dot product `v · x` in coordinates. -/
def dotE {d : ℕ} (v x : EuclideanSpace ℝ (Fin d)) : ℝ := ∑ j, v j * x j

/-- The filter loop of §8.3 with `fuel` remaining rounds and current weights `w`. `choose` is the
rule producing the direction `v` of step 2. Each round:
1. `W = ∑ w_i`; if `W < 1/2` return `0`; otherwise `a = ∑ w_i x_i / W`,
   `M = ∑ w_i (x_i − a)(x_i − a)ᵀ / W`;
2. if `M = 0` return `a`; otherwise `v = choose M`, `q = vᵀ M v`;
3. if `q ≤ 100 K B²` return `a`; otherwise `g_i = (v · (x_i − a))²`,
   `g_max = max_{w_i > 0} g_i`; if `g_max = 0` return `a`; otherwise replace each positive `w_i` by
   `w_i (1 − g_i / g_max)`.
If no round returns, the result is `0`. -/
def filterLoop {n d : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) (K B : ℝ)
    (choose : Matrix (Fin d) (Fin d) ℝ → EuclideanSpace ℝ (Fin d)) :
    ℕ → (Fin n → ℝ) → EuclideanSpace ℝ (Fin d)
  | 0, _ => 0
  | fuel + 1, w =>
      open Classical in
      let W := ∑ i, w i
      if W < 1 / 2 then 0 else
      let a : EuclideanSpace ℝ (Fin d) := W⁻¹ • ∑ i, w i • x i
      let M : Matrix (Fin d) (Fin d) ℝ :=
        fun j l => (∑ i, w i * (x i j - a j) * (x i l - a l)) / W
      if M = 0 then a else
      let v := choose M
      let q := quadForm M v
      if q ≤ 100 * K * B ^ 2 then a else
      let g : Fin n → ℝ := fun i => dotE v (x i - a) ^ 2
      let gmax := Finset.univ.fold max 0 (fun i => if 0 < w i then g i else 0)
      if gmax = 0 then a else
      filterLoop x K B choose fuel (fun i => if 0 < w i then w i * (1 - g i / gmax) else w i)

/-- The weighted filter of §8.3: start from `w_i = 1/n` and run at most `n` rounds. -/
def robustFilter {n d : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) (K B : ℝ)
    (choose : Matrix (Fin d) (Fin d) ℝ → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  filterLoop x K B choose n (fun _ => 1 / (n : ℝ))

/-- The direction-choice requirement of step 2: for every nonzero positive semidefinite `M`,
`choose M` is a unit vector with `λ_max(M)/2 ≤ vᵀ M v ≤ λ_max(M)`. -/
def IsDirectionRule {d : ℕ} (choose : Matrix (Fin d) (Fin d) ℝ → EuclideanSpace ℝ (Fin d)) :
    Prop :=
  ∀ M : Matrix (Fin d) (Fin d) ℝ, M.PosSemidef → M ≠ 0 →
    ‖choose M‖ = 1 ∧ lamMax M / 2 ≤ quadForm M (choose M) ∧ quadForm M (choose M) ≤ lamMax M

/-- The power of the deterministic spectral step, `r = ⌈log(2d) / (2 log(4/3))⌉`. -/
def spectralPower (d : ℕ) : ℕ := ⌈Real.log (2 * d) / (2 * Real.log (4 / 3))⌉₊

/-- `y_j = M^r e_j`. -/
def spectralColumn {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun l => (M ^ spectralPower d) l j)

/-- The deterministic spectral step (PDF p. 22): among the nonzero `y_j = M^r e_j`, take one with
the largest Rayleigh quotient `y_jᵀ M y_j / ‖y_j‖²` (the smallest such index `j`), and return
`y_j / ‖y_j‖`, the norm computed as a square root. If every `y_j` is zero, return `0`. -/
def spectralStep {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : EuclideanSpace ℝ (Fin d) :=
  open Classical in
  let S := Finset.univ.filter (fun j => spectralColumn M j ≠ 0)
  let R : Fin d → ℝ := fun j =>
    quadForm M (spectralColumn M j) / ∑ l, (spectralColumn M j) l ^ 2
  let best := S.filter (fun j => ∀ j' ∈ S, R j' ≤ R j)
  if h : best.Nonempty then
    (Real.sqrt (∑ l, (spectralColumn M (best.min' h)) l ^ 2))⁻¹ • spectralColumn M (best.min' h)
  else 0

/-! ## The finite list of §8.4 -/

/-- `N_cov = ⌈(4k/β) log(2k/δ_cov)⌉` of (5). -/
def Ncov (k : ℕ) (β δ : ℝ) : ℕ := ⌈(4 * k / β) * Real.log (2 * k / δ)⌉₊

/-- The posterior batch size `n = ⌈C [d log(2d) + log(4 N_cov / δ_cov)]⌉` of §8.4. -/
def coverBatch (C : ℝ) (d k : ℕ) (β δ : ℝ) : ℕ :=
  ⌈C * (d * Real.log (2 * d) + Real.log (4 * Ncov k β δ / δ))⌉₊

/-- The cover procedure of §8.4 with the constants `C, K` of (49)–(50), as a function of its
random inputs: observations `obs t`, the Gaussian tape `g`, and the posterior draws, where
`post m y` is the `m`-th posterior draw (counting all draws) at query `y`. For query
`t < N_cov`: `y_t = obs t + σ G_t` with `G_t = (g(t d), …, g(t d + d − 1))`; the draws
`x_ℓ = post (t n + ℓ) y_t`, `ℓ < n`; the filter with `K` and `B = 4σ√L`, `L = log(2k/β)`, and the
spectral step; the center `c_t = 2a − y_t`. -/
def coverCenters (C K : ℝ) (d k : ℕ) (σ β δ : ℝ) (obs : ℕ → EuclideanSpace ℝ (Fin d))
    (g : ℕ → ℝ) (post : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Fin (Ncov k β δ) → EuclideanSpace ℝ (Fin d) :=
  fun t =>
    let n := coverBatch C d k β δ
    let B := 4 * σ * Real.sqrt (Real.log (2 * k / β))
    let y := obs t + σ • ofSeq d (fun i => g ((t : ℕ) * d + i))
    let xs : Fin n → EuclideanSpace ℝ (Fin d) := fun l => post ((t : ℕ) * n + l) y
    (2 : ℝ) • robustFilter xs K B spectralStep - y

/-- The cover program's initial configuration: cells `0–4` hold `d, k, σ, β, δ_cov`; pointer
registers `0, 1` hold `d, k`. -/
def coverStart (d k : ℕ) (σ β δ : ℝ) : State :=
  initState (listMem [(d : ℝ), (k : ℝ), σ, β, δ]) (listPtrs [(d : ℤ), (k : ℤ)])

/-- The posterior channel: the `m`-th call reads a query `y ∈ ℝ^d` and writes `resp y (ω m)`;
it is charged `c` extra units (the posterior sampling cost). -/
def kernelChannel {d : ℕ} {Ω : Type*} (resp : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (c : ℕ) (ω : ℕ → Ω) : Channel :=
  ⟨d, d, c, fun m x => toSeq (resp (ofSeq d x) (ω m))⟩

end GaussMixGated.ExactReal


