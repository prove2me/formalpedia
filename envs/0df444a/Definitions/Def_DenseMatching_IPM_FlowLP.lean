-- Prove2me | Definitions.Def_DenseMatching_IPM_FlowLP
-- name    : DenseMatching_IPM_FlowLP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:39:10.727289+00:00
-- url     : https://prove2.me/theorems/53b80817-4cd0-4d12-bf42-66cfb1e1aad4
-- title:
--   §4.1–§4.2 — flow LP on K_{n/2,n/2}, eligibility (Def. 4.1), ψ, Eq. (4), clipped direction (Def. 4.2), sparsity intensity (10), sampled correction (11), Newton adjustment, Eq. (12)
-- statement:
--   The objects of the interior-point method of §4.
--
--   **The linear program** (p. 24). On $K_{n/2,n/2}$ ($n=2k$, sides $L,R$, edges $(u,v)$ oriented from $L$ to $R$, $m=k^2$): $d_u=-1$ on $L$, $d_v=1$ on $R$, $B$ the $m\times n$ incidence matrix with $(Bu)_e=u_v-u_u$; $\min c^\top f$ s.t. $B^\top f=d$, $f\ge 0$. The residual is $r=B^\top f-d$. The tracked graph has weights $f/c$ and Laplacian $B^\top\mathrm{Diag}(f/c)B$; $\|v\|^2_{M^\dagger}=v^\top M^\dagger v$, $\|y\|_M^2=y^\top My$.
--
--   **Definition 4.1** (p. 26). $(f,c,\mu)$ is **eligible** if $\mu>0$, $f_e,c_e>0$, $\tfrac9{10}\mu\le f_ec_e\le\tfrac{11}{10}\mu$ for every edge, and $\|B^\top f-d\|^2_{(B^\top\mathrm{Diag}(f/c)B)^\dagger}\le 10^{-8}\mu$. `minPerfectMatchingCost k a` is the minimum over permutations $\sigma$ of $\sum_i a_{(i,\sigma(i))}$.
--
--   **Potential** (pp. 24–25). $\psi(\nu)=(1-\nu)^{-2}+(1+\nu)^{-2}$, $\psi'(\nu)=2(1-\nu)^{-3}-2(1+\nu)^{-3}$, $\psi''(\nu)=6(1-\nu)^{-4}+6(1+\nu)^{-4}$, $\psi(\boldsymbol\nu)=\sum_e\psi(\nu_e)$. The deviation is $\nu=10(\mu_e/\mu-1)$ with $\mu_e=f_ec_e$. Equation (4): $|\bar\nu_e-\nu_e|\le10^{-2}\min\{\eta,1-|\nu_e|\}$. Constants $\eta=10^{-5}$, $\alpha=10^7$.
--
--   **Definition 4.2** (p. 29). For representatives $\bar\nu$,
--   $$\Delta\mu=-\mathrm{Sgn}(\psi'(\bar\nu))\circ\min\{10^{-3}(1-|\bar\nu|),\,\theta|\psi'(\bar\nu)|\},\qquad \theta=\sup\{t\ge0:\|\min\{10^{-3}(1-|\bar\nu|),t|\psi'(\bar\nu)|\}\|_2\le\eta\},$$
--   $\theta=\infty$ allowed, $1/\theta:=0$; $E_{\rm clipped}=\{e:\psi'(\bar\nu)_e\ne0,\ \theta|\psi'(\bar\nu)_e|\ge10^{-3}(1-|\bar\nu_e|)\}$, $E_{\rm rest}=E\setminus E_{\rm clipped}$; the descent is $|\Delta\mu|^\top|\psi'(\bar\nu)|$.
--
--   **Equation (10)** (p. 30). The sparsity intensity is $p^s_e=1$ on $E_{\rm clipped}$ and on $E_{\rm rest}$
--   $$p^s_e=\min\Big\{1,\ \frac{\alpha|\tilde f_e|}{10^2\eta}+\frac{\alpha|\tilde\nu_e|}{2\cdot10^2\eta}+\frac{\alpha|\tilde\nu_e|}{1-|\bar\nu_e|}+10^2\alpha\frac{|\tilde\nu_e|\sqrt{\psi''(\bar\nu)_e\,\mathbb 1^\top_{E_{\rm rest}}\psi''(\bar\nu)}}{\eta(1/\theta+\sqrt m)}+\alpha\log n\frac{|\tilde\nu_e||\psi'(\bar\nu)_e|}{|\Delta\mu|^\top|\psi'(\bar\nu)|}\Big\}$$
--   with $0/0=0$ and $\log=\log_2$.
--
--   **Equation (11)** (p. 31). On an outcome $\omega$ of the independent coins, $f^{\rm sample}_e=\tilde f_e/p_e$ if $\omega_e$, else $0$; $f^\circ=f^{\rm sample}-\tilde f$, $\nu^\circ_e=\tilde\nu_ef^\circ_e/\tilde f_e$ ($0/0=0$).
--
--   **Lemma 4.6's Newton adjustment** (p. 35). $\tilde f=(B\Delta x)\circ(1+\Delta\mu/10)/(c+B\Delta x)$, $\tilde\nu=10(1+\nu/10)\circ(1+B\Delta x/c)\circ\tilde f$. The shrink is $\delta=10^{-3}\eta/\sqrt m$, and Equation (12) is $\hat\nu_e=\nu_e+\big((1+\nu_e/10)\Delta\mu_e-\nu^\circ_e+\delta(\nu_e+10)\big)/(1-\delta)$.
--
--   **Formalization Note.** The weights of the tracked graph are replaced by $1$ on an edge with $f_e/c_e\le0$, so that the published `WGraph` (which requires positive weights) is defined for all $f,c$; every statement assumes $f,c>0$. $\theta$ is a supremum in $[0,\infty]$ and the minimum in $\Delta\mu$ is taken there ($\infty\cdot0=0$). Real division by $0$ is $0$ in Lean, which is the paper's $0/0=0$; no other division by zero arises under the hypotheses of the lemmas.
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), pp. 24–31, 35, §4.1–§4.2

import Mathlib
import Definitions.Def_EffResSparsify_Sampling_Defs

namespace DenseMatching.IPM

open EffResSparsify.Sampling Matrix

/-!
# The flow LP of §4 and the objects of one interior-point step

Dai, Peng, Sleator, Stepin, Yang, *Approaching Optimality for Dense Bipartite Matching*, STOC 2027
submission (manuscript sha256 0bdeb447…), §4.1–§4.2, pp. 24–31.

**Formalization Note.**
* The instance of §4 is the complete bipartite graph `K_{n/2,n/2}` with `n = 2k`: vertices
  `Sum.inl i ∈ L` and `Sum.inr j ∈ R` (`i, j : Fin k`), edges `(i, j)`, oriented from `L` to `R`, so
  that `(B u)_e = u_v − u_u` for `e = (u, v)`; `m = k²`. Demands `d_u = −1` on `L`, `d_v = 1` on `R`.
* The tracked graph `B⊤ Diag(f/c) B` is the published `WGraph` Laplacian with weights `f/c`; the
  weight of an edge with `f_e / c_e ≤ 0` is replaced by `1` so that the graph is defined for every
  `f, c` (every statement assumes `f, c > 0`, where the weights are exactly `f/c`).
  `‖r‖²_{M†} = r⊤ M† r` uses the published Moore–Penrose pseudoinverse `lapPinv`.
* The objects of a step (`ψ`, Definition 4.2, Equation (10), Equation (11), the Newton adjustment
  of Lemma 4.6 and Equation (12)) are defined over an arbitrary finite edge set `E`.
* `θ` of Definition 4.2 is a supremum in `[0, ∞]` (`ℝ≥0∞`), `θ = ∞` allowed; `1/θ` is
  `(θ⁻¹).toReal`, which is `0` at `θ = ∞` as the paper sets (`θ > 0` always, since the set
  contains a neighbourhood of `0` when `η > 0`).
* Real divisions by zero are `0` in Lean; this is the paper's convention `0/0 = 0` in Equation (10)
  and in `ν°` (p. 31), and no other division by zero occurs under the hypotheses of the lemmas.
-/

/-- The step size `η = 10⁻⁵` (p. 26). -/
noncomputable def eta : ℝ := 1 / 10 ^ 5

/-- The amplification `α = 10⁷` of the sampling probabilities (p. 26). -/
noncomputable def alpha : ℝ := 10 ^ 7

/-- The vertices of `K_{k,k}`: `Sum.inl i` is in `L`, `Sum.inr j` in `R`. -/
abbrev KV (k : ℕ) := Fin k ⊕ Fin k

/-- The edges of `K_{k,k}`: `(i, j)` joins `Sum.inl i ∈ L` to `Sum.inr j ∈ R`. -/
abbrev KE (k : ℕ) := Fin k × Fin k

/-- `K_{k,k}` with positive edge weights `w`, edge `(i, j)` oriented from `inl i` (tail) to
`inr j` (head), so the incidence row of `e = (u, v)` is `χ_e = 1_v − 1_u`. -/
def kGraph (k : ℕ) (w : KE k → ℝ) (hw : ∀ e, 0 < w e) : WGraph (KV k) (KE k) where
  head e := Sum.inr e.2
  tail e := Sum.inl e.1
  w := w
  head_ne_tail _ := Sum.inr_ne_inl
  w_pos := hw

/-- The tracked graph of §4.1 (p. 25): `K_{k,k}` with weights `f/c` (replaced by `1` on an edge
where `f_e / c_e ≤ 0`, a case excluded by every statement). Its Laplacian is `B⊤ Diag(f/c) B`. -/
noncomputable def trackedGraph (k : ℕ) (f c : KE k → ℝ) : WGraph (KV k) (KE k) :=
  kGraph k (fun e => if 0 < f e / c e then f e / c e else 1)
    (fun e => by
      split_ifs with h
      · exact h
      · exact one_pos)

/-- The `m × n` incidence matrix `B` of `K_{k,k}` (it does not depend on the weights). -/
def incK (k : ℕ) : Matrix (KE k) (KV k) ℝ :=
  (kGraph k (fun _ => 1) (fun _ => one_pos)).incidence

/-- The demand vector `d`: `d_u = −1` for `u ∈ L`, `d_v = 1` for `v ∈ R` (p. 24). -/
def demand (k : ℕ) : KV k → ℝ := Sum.elim (fun _ => -1) (fun _ => 1)

/-- The residual `r = B⊤ f − d` (p. 24). -/
def residual (k : ℕ) (f : KE k → ℝ) : KV k → ℝ := (incK k)ᵀ *ᵥ f - demand k

/-- `‖v‖²_{(B⊤ Diag(f/c) B)†} = v⊤ (B⊤ Diag(f/c) B)† v`. -/
noncomputable def pinvNormSq (k : ℕ) (f c : KE k → ℝ) (v : KV k → ℝ) : ℝ :=
  v ⬝ᵥ ((trackedGraph k f c).lapPinv *ᵥ v)

/-- `‖y‖²_{B⊤ Diag(f/c) B} = y⊤ (B⊤ Diag(f/c) B) y`. -/
noncomputable def lapNormSq (k : ℕ) (f c : KE k → ℝ) (y : KV k → ℝ) : ℝ :=
  y ⬝ᵥ ((trackedGraph k f c).laplacian *ᵥ y)

/-- `(B⊤ Diag(f/c) B)† v`. -/
noncomputable def pinvApply (k : ℕ) (f c : KE k → ℝ) (v : KV k → ℝ) : KV k → ℝ :=
  (trackedGraph k f c).lapPinv *ᵥ v

/-- Definition 4.1 (p. 26): `(f, c, μ)` is *eligible* if `μ > 0`, `f_e, c_e > 0`,
`(9/10) μ ≤ f_e c_e ≤ (11/10) μ` for every edge, and `‖B⊤f − d‖²_{(B⊤Diag(f/c)B)†} ≤ 10⁻⁸ μ`. -/
def Eligible (k : ℕ) (f c : KE k → ℝ) (μ : ℝ) : Prop :=
  0 < μ ∧ (∀ e, 0 < f e) ∧ (∀ e, 0 < c e) ∧
    (∀ e, 9 / 10 * μ ≤ f e * c e ∧ f e * c e ≤ 11 / 10 * μ) ∧
    pinvNormSq k f c (residual k f) ≤ 1 / 10 ^ 8 * μ

/-- The minimum cost of a perfect matching of `K_{k,k}` under the edge costs `a`: the minimum of
`∑_i a(i, σ i)` over the permutations `σ` of `Fin k`. -/
noncomputable def minPerfectMatchingCost (k : ℕ) (a : KE k → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun σ : Equiv.Perm (Fin k) => ∑ i, a (i, σ i))

/-- `ψ(ν) = (1 − ν)⁻² + (1 + ν)⁻²` (p. 24). -/
noncomputable def psi (v : ℝ) : ℝ := 1 / (1 - v) ^ 2 + 1 / (1 + v) ^ 2

/-- `ψ′(ν) = 2/(1 − ν)³ − 2/(1 + ν)³` (p. 25). -/
noncomputable def dpsi (v : ℝ) : ℝ := 2 / (1 - v) ^ 3 - 2 / (1 + v) ^ 3

/-- `ψ″(ν) = 6/(1 − ν)⁴ + 6/(1 + ν)⁴` (p. 25). -/
noncomputable def ddpsi (v : ℝ) : ℝ := 6 / (1 - v) ^ 4 + 6 / (1 + v) ^ 4

variable {E : Type*} [Fintype E]

/-- The potential `ψ(ν) = ∑_e ψ(ν_e)` (p. 25). -/
noncomputable def potential (ν : E → ℝ) : ℝ := ∑ e, psi (ν e)

/-- The Euclidean norm `‖v‖₂` of a vector on `E`. -/
noncomputable def l2norm (v : E → ℝ) : ℝ := Real.sqrt (∑ e, v e ^ 2)

/-- The centrality deviation `ν = 10(μ/μ − 1)` of the centrality vector `μ_e = f_e c_e` from the
scalar target `μ` (p. 24). -/
noncomputable def deviation (μ : ℝ) (f c : E → ℝ) : E → ℝ := fun e => 10 * (f e * c e / μ - 1)

/-- Equation (4) (p. 25): every representative `ν̄_e` satisfies
`|ν̄_e − ν_e| ≤ 10⁻² min{η, 1 − |ν_e|}`. -/
def RepresentativesClose (η : ℝ) (ν νbar : E → ℝ) : Prop :=
  ∀ e, |νbar e - ν e| ≤ 1 / 100 * min η (1 - |ν e|)

/-- The cap `10⁻³ (1 − |ν̄_e|)` of Definition 4.2. -/
noncomputable def residueCap (νbar : E → ℝ) (e : E) : ℝ := 1 / 1000 * (1 - |νbar e|)

/-- `‖min{10⁻³(1 − |ν̄|), t |ψ′(ν̄)|}‖₂` (Definition 4.2). -/
noncomputable def clipNorm (νbar : E → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (∑ e, (min (residueCap νbar e) (t * |dpsi (νbar e)|)) ^ 2)

/-- The clipping parameter `θ = sup{t ≥ 0 : ‖min{10⁻³(1 − |ν̄|), t |ψ′(ν̄)|}‖₂ ≤ η}` of
Definition 4.2 (p. 29), in `[0, ∞]`. -/
noncomputable def clipTheta (η : ℝ) (νbar : E → ℝ) : ENNReal :=
  ⨆ (t : NNReal) (_ : clipNorm νbar (t : ℝ) ≤ η), (t : ENNReal)

/-- `1/θ`, with `1/∞ = 0` (Definition 4.2). -/
noncomputable def invTheta (η : ℝ) (νbar : E → ℝ) : ℝ := (clipTheta η νbar)⁻¹.toReal

/-- The clipped centrality direction `Δμ = −Sgn(ψ′(ν̄)) ∘ min{10⁻³(1 − |ν̄|), θ |ψ′(ν̄)|}` of
Definition 4.2 (the minimum is taken in `[0, ∞]`, where `∞ · 0 = 0`). -/
noncomputable def clippedDir (η : ℝ) (νbar : E → ℝ) : E → ℝ := fun e =>
  -Real.sign (dpsi (νbar e)) *
    (min (ENNReal.ofReal (residueCap νbar e))
      (clipTheta η νbar * ENNReal.ofReal |dpsi (νbar e)|)).toReal

open Classical in
/-- The clipped edges `E_clipped = {e : ψ′(ν̄)_e ≠ 0, θ |ψ′(ν̄)_e| ≥ 10⁻³(1 − |ν̄_e|)}`
(Definition 4.2). -/
noncomputable def clippedEdges (η : ℝ) (νbar : E → ℝ) : Finset E :=
  Finset.univ.filter (fun e => dpsi (νbar e) ≠ 0 ∧
    ENNReal.ofReal (residueCap νbar e) ≤ clipTheta η νbar * ENNReal.ofReal |dpsi (νbar e)|)

open Classical in
/-- `E_rest = E \ E_clipped` (Definition 4.2). -/
noncomputable def restEdges (η : ℝ) (νbar : E → ℝ) : Finset E :=
  Finset.univ \ clippedEdges η νbar

/-- The descent `|Δμ|⊤ |ψ′(ν̄)|`. -/
noncomputable def descent (η : ℝ) (νbar : E → ℝ) : ℝ :=
  ∑ e, |clippedDir η νbar e| * |dpsi (νbar e)|

open Classical in
/-- The sparsity intensity `pˢ` of Equation (10) (Lemma 4.4, p. 30), for `n` vertices
(`log n = log₂ n`) and `m = |E|`: `1` on `E_clipped` and, on `E_rest`,
`min{1, α|f̃_e|/(10²η) + α|ν̃_e|/(2·10²η) + α|ν̃_e|/(1 − |ν̄_e|)
 + 10²α |ν̃_e| √(ψ″(ν̄)_e 1⊤_{E_rest} ψ″(ν̄)) / (η(1/θ + √m))
 + α log n |ν̃_e| |ψ′(ν̄)_e| / (|Δμ|⊤|ψ′(ν̄)|)}` (with `0/0 = 0`). -/
noncomputable def sparsityIntensity (n : ℕ) (η α : ℝ) (νbar ft νt : E → ℝ) (e : E) : ℝ :=
  if e ∈ clippedEdges η νbar then 1 else
    min 1 (α * |ft e| / (10 ^ 2 * η) + α * |νt e| / (2 * 10 ^ 2 * η)
      + α * |νt e| / (1 - |νbar e|)
      + 10 ^ 2 * α * |νt e| *
          Real.sqrt (ddpsi (νbar e) * ∑ e' ∈ restEdges η νbar, ddpsi (νbar e')) /
          (η * (invTheta η νbar + Real.sqrt (Fintype.card E)))
      + α * Real.logb 2 n * |νt e| * |dpsi (νbar e)| / descent η νbar)

/-- The sampled correction of Equation (11) (p. 31) on the outcome `ω` (`ω e` = the coin of `e`
came up): `f^sample_e = f̃_e / p_e` if `ω e`, `0` otherwise. -/
noncomputable def sampledCorrection (ft p : E → ℝ) (ω : E → Bool) : E → ℝ := fun e =>
  if ω e then ft e / p e else 0

/-- The sampling error of the centrality deviations (p. 31): `ν°_e = ν̃_e f°_e / f̃_e` with
`f° = f^sample − f̃` (and `0/0 = 0`). -/
noncomputable def samplingErrorNu (ft νt p : E → ℝ) (ω : E → Bool) : E → ℝ := fun e =>
  νt e * (sampledCorrection ft p ω e - ft e) / ft e

/-- The Newton adjustment of Lemma 4.6 (p. 35): `f̃ = (BΔx) ∘ (1 + Δμ/10) / (c + BΔx)`, given the
edge vector `BΔx`. -/
noncomputable def newtonFlow (Bdx c dmu : E → ℝ) : E → ℝ := fun e =>
  Bdx e * (1 + dmu e / 10) / (c e + Bdx e)

/-- `ν̃ = 10 (1 + ν/10) ∘ (1 + BΔx/c) ∘ f̃` (Lemma 4.6, p. 35). -/
noncomputable def newtonNu (ν Bdx c ft : E → ℝ) : E → ℝ := fun e =>
  10 * (1 + ν e / 10) * (1 + Bdx e / c e) * ft e

/-- The shrink factor `δ = 10⁻³ η / √m` (Lemma 4.5, p. 31). -/
noncomputable def shrink (η m : ℝ) : ℝ := 1 / 1000 * η / Real.sqrt m

/-- The new deviations of Equation (12) (p. 31):
`ν̂_e = ν_e + ((1 + ν_e/10) Δμ_e − ν°_e + δ(ν_e + 10)) / (1 − δ)`. -/
noncomputable def newDeviation (δ : ℝ) (ν dmu νcirc : E → ℝ) : E → ℝ := fun e =>
  ν e + ((1 + ν e / 10) * dmu e - νcirc e + δ * (ν e + 10)) / (1 - δ)

end DenseMatching.IPM


