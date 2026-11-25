-- Prove2me | Definitions.Def_Arxiv2412_03183_Basic
-- name    : Arxiv2412_03183_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T13:39:23.628488+00:00
-- url     : https://prove2.me/theorems/a989b22b-f091-51eb-91f2-a8ef23cb75be
-- title:
--   Visibilities, gains, imaging and self-calibration objectives (Ikeda et al. 2024)
-- statement:
--   Objects of Sections 2-3 and Appendix 1 of Ikeda, Nakazato, Tsukagoshi, Takeuchi and Yamaguchi (2024).
--
--   1. **Stations and gains.** A finite set of stations $\alpha$. Station $\alpha$ has $N_\alpha$ complex gains $g_{\alpha 0},\dots,g_{\alpha,N_\alpha-1}$, one per integration in which it observes, at strictly increasing times $t_{\alpha 0}<t_{\alpha 1}<\cdots$. A gain vector is $g=(g_{\alpha l})\in\mathbb{C}^{\sum_\alpha N_\alpha}$.
--   2. **Observation setup (eqs. (1)-(4)).** There are $M$ observed visibilities $\tilde v_k\in\mathbb{C}$. Visibility $k$ corresponds to a time $t_l$ and an ordered pair $(\alpha,\beta)$ of distinct stations, through the gains $g_{\alpha l}$ and $g_{\beta l}$ taken at that time. The map $k\mapsto(t_l,\alpha,\beta)$ is one-to-one. Each visibility has a noise standard deviation $\sigma_k>0$ and a u-v point $(u_k,v_k)$.
--   3. **Image and Fourier transform.** An image is $x=(x_{ij})\in\mathbb{R}^{N_x\times N_y}$. Pixel $(i,j)$ sits at sky position $(\xi_i,\eta_j)$, and $\mathcal{F}_k(x)=\sum_{i,j}x_{ij}\,e^{-2\pi\mathrm{i}(u_k\xi_i+v_k\eta_j)}$. The feasible images are those with $x\ge0$.
--   4. **Data term (eq. (8)).** $L_{\tilde v}(x,g)=\sum_k\frac{1}{2\sigma_k^2}|\tilde v_kg_{\alpha l}g_{\beta l}^*-\mathcal{F}_k(x)|^2$.
--   5. **Image regulariser (eq. (11)).** $R_{\lambda_1,\lambda_2}(x)=\lambda_1\|x\|_1+\lambda_2\mathrm{TSV}(x)$, where $\|x\|_1=\sum_{ij}|x_{ij}|$ and $\mathrm{TSV}(x)=\sum_{ij}(x_{ij}-x_{i-1,j})^2+(x_{ij}-x_{i,j-1})^2$. A difference is included only when the neighbouring pixel exists.
--   6. **Gain regulariser and constraint (eqs. (12)-(13)).** $S_{\mu_1,\mu_2}(g)=\mu_1\sum_{\alpha,l\ge1}w_{\alpha l}|g_{\alpha l}-g_{\alpha,l-1}|^2+\mu_2\sum_{\alpha,l\ge1}w_{\alpha l}(|g_{\alpha l}|-|g_{\alpha,l-1}|)^2$ with $w_{\alpha l}=1/(t_{\alpha l}-t_{\alpha,l-1})$. The constraint is $\sum_l|g_{\alpha l}|=N_\alpha$ for every station $\alpha$.
--   7. **Objectives.** The imaging objective (eq. (10)) is $L_{\tilde v}(x,\hat g)+R_{\lambda_1,\lambda_2}(x)$. The gain objective (eq. (12)) is $L_{\tilde v}(\hat x,g)+S_{\mu_1,\mu_2}(g)$. The joint objective (eq. (14)) is $L_{\tilde v}(x,g)+R_{\lambda_1,\lambda_2}(x)+S_{\mu_1,\mu_2}(g)$. The real coordinates of $g$ are $(\operatorname{Re}g_{\alpha l},\operatorname{Im}g_{\alpha l})$.
--   8. **Extended functions and subproblem (eqs. (A1)-(A3)).** $\mathcal{L}_{\tilde v}(x,g,h)=\sum_k\frac{1}{4\sigma_k^2}\big[|\tilde v_kg_{\alpha l}h_{\beta l}^*-\mathcal{F}_k(x)|^2+|\tilde v_kh_{\alpha l}g_{\beta l}^*-\mathcal{F}_k(x)|^2\big]$, and $\mathcal{S}_{\mu_1,\mu_2}(g,h)$ is as in eq. (A2), summed over $l\ge1$. The subproblem objective is $\mathcal{L}_{\tilde v}(x,g,\hat h)+\mathcal{S}_{\mu_1,\mu_2}(g,\hat h)+\frac\rho2\sum_{\alpha,l}|g_{\alpha l}-\hat h_{\alpha l}|^2$.
--   9. **Closed form (eqs. (A4)-(A5)).** $\mathcal{N}(\alpha l)$ is the set of visibilities $k\leftrightarrow(t_l,\alpha,\beta)$ whose first gain is $g_{\alpha l}$; for such $k$, $h_{\beta l}$ is the second gain. With $y_k=\mathcal{F}_k(x)$ the coefficients $a_{\alpha l},b_{\alpha l},c_{\alpha l},\eta_\alpha,r_{\alpha l}$ are as printed in eq. (A5), and $\hat g_{\alpha l}=r_{\alpha l}b_{\alpha l}/|b_{\alpha l}|$. A setup is *conjugate-duplicated* if every visibility $k\leftrightarrow(t_l,\alpha,\beta)$ also appears as some $k'\leftrightarrow(t_l,\beta,\alpha)$ with $\tilde v_{k'}=\tilde v_k^*$, $\sigma_{k'}=\sigma_k$ and $(u_{k'},v_{k'})=(-u_k,-v_k)$.
--
--   **Formalization Note** The paper does not give $\mathcal{F}_k$ explicitly. It is written as the Fourier sum above, with the pixel positions and u-v points as free data. The sign convention of the exponent does not matter, because the statements quantify over all u-v points. Terms of eqs. (11), (13), (A2) and (A5) that involve a non-existent neighbour (pixel $i-1$ or $j-1$, gain $l-1$ or $l+1$) are omitted; the paper does not say how it treats them. $y_k$, which the paper never defines, is taken as $\mathcal{F}_k(x)$. A gain index $l$ is the position of the gain among station $\alpha$'s own $N_\alpha$ gains, which is what allows $N_\alpha$ to differ between stations.
-- source:
--   Ikeda, Nakazato, Tsukagoshi, Takeuchi and Yamaguchi, Solving Self-calibration of ALMA Data with an Optimization Method, arXiv:2412.03183v1 (2024), Section 2.1 (eqs. (1)-(4), (8)), Sections 3.1-3.3 (eqs. (10)-(14)), Appendix 1 (eqs. (A1)-(A5)), PDF pp. 2-3, 9

import Mathlib

/-!
Ikeda, Nakazato, Tsukagoshi, Takeuchi and Yamaguchi, *Solving Self-calibration of ALMA Data with an
Optimization Method*, arXiv:2412.03183v1 (2024): the observation model of Section 2 (eqs. (1)-(9)),
the imaging, gain-correction and joint problems of Section 3 (eqs. (10)-(14)), and the extended
functions, subproblem and closed-form update of Appendix 1 (eqs. (A1)-(A5)).
-/

open Finset

noncomputable section

namespace Arxiv2412_03183

/-- Section 2.1, eq. (3) and the sentence before eq. (4): station `α` has `N α` gains
`g_{α 0}, …, g_{α (N α - 1)}`, one per integration in which it observes. A gain is indexed by the
pair `(α, l)`. -/
abbrev GainIdx {S : Type*} (N : S → ℕ) := Σ α : S, Fin (N α)

/-- Section 2.1: a collection of complex gains `g = {g_{α l}}`. -/
abbrev Gains {S : Type*} (N : S → ℕ) := GainIdx N → ℂ

/-- Section 2.1, before eq. (3): an `N_x × N_y` pixelated (Stokes I) image `x = (x_{ij})`. -/
abbrev Image (Nx Ny : ℕ) := Fin Nx → Fin Ny → ℝ

/-- Section 2.1, eqs. (1)-(4), and eq. (8): the observation setup. `M` visibilities `ṽ_k`;
visibility `k` belongs to the integration time `t_l` and the ordered pair of distinct stations
`(α, β)` (eq. (3)), recorded as the gain `first k = (α, l)` and the gain `second k = (β, l)` taken
at that same time; the correspondence `k ↦ (t_l, α, β)` is one-to-one. `time (α, l)` is the time
`t_l` of the gain `g_{α l}`, increasing in `l` for each station. `σ_k > 0` is the noise standard
deviation of visibility `k` (eq. (8)); `(u_k, v_k)` is its u-v point and `(pixX i, pixY j)` the sky
position of pixel `(i, j)`, which define the Fourier transform `F_k` of eq. (1). -/
structure ObsSetup (S : Type*) (N : S → ℕ) (M Nx Ny : ℕ) where
  time : GainIdx N → ℝ
  time_lt : ∀ (α : S) (i j : Fin (N α)), i < j → time ⟨α, i⟩ < time ⟨α, j⟩
  first : Fin M → GainIdx N
  second : Fin M → GainIdx N
  first_ne_second : ∀ k, (first k).1 ≠ (second k).1
  same_time : ∀ k, time (first k) = time (second k)
  injective : Function.Injective fun k => (time (first k), (first k).1, (second k).1)
  vobs : Fin M → ℂ
  sigma : Fin M → ℝ
  sigma_pos : ∀ k, 0 < sigma k
  u : Fin M → ℝ
  v : Fin M → ℝ
  pixX : Fin Nx → ℝ
  pixY : Fin Ny → ℝ

variable {S : Type*} [Fintype S] [DecidableEq S] {N : S → ℕ} {M Nx Ny : ℕ}

/-- Eqs. (1) and (4): `F_k(x)`, the two-dimensional Fourier transform of the pixelated image `x`
at the u-v point of visibility `k`. -/
def visFT (D : ObsSetup S N M Nx Ny) (x : Image Nx Ny) (k : Fin M) : ℂ :=
  ∑ i, ∑ j, (x i j : ℂ) *
    Complex.exp (-(2 * Real.pi * Complex.I) * ((D.u k * D.pixX i + D.v k * D.pixY j : ℝ) : ℂ))

/-- Eq. (8): the weighted squared error
`L_ṽ(x, g) = ∑_k |ṽ_k g_{α l} g*_{β l} - F_k(x)|² / (2 σ_k²)`. -/
def dataLoss (D : ObsSetup S N M Nx Ny) (x : Image Nx Ny) (g : Gains N) : ℝ :=
  ∑ k, ‖D.vobs k * g (D.first k) * starRingEnd ℂ (g (D.second k)) - visFT D x k‖ ^ 2 /
    (2 * D.sigma k ^ 2)

/-- Section 3.1, after eq. (10): `‖x‖₁ = ∑_{ij} |x_{ij}|`. -/
def l1Norm (x : Image Nx Ny) : ℝ := ∑ i, ∑ j, |x i j|

/-- Section 3.1, after eq. (10): `TSV(x) = ∑_{ij} (x_{ij} - x_{i-1 j})² + (x_{ij} - x_{i j-1})²`,
a difference being present when the neighbouring pixel `(i-1, j)`, resp. `(i, j-1)`, exists. -/
def tsv (x : Image Nx Ny) : ℝ :=
  ∑ i : Fin Nx, ∑ j : Fin Ny,
    ((if 0 < i.val then (x i j - x ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ j) ^ 2 else 0) +
      (if 0 < j.val then (x i j - x i ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩) ^ 2 else 0))

/-- Eq. (11): `R_{λ₁,λ₂}(x) = λ₁ ‖x‖₁ + λ₂ TSV(x)`. -/
def imgReg (lam1 lam2 : ℝ) (x : Image Nx Ny) : ℝ := lam1 * l1Norm x + lam2 * tsv x

/-- Eq. (10) and Section 2.1 ("`x` is non-negative"): the feasible images `x ≥ 0`. -/
def nonnegImages : Set (Image Nx Ny) := {x | ∀ i j, 0 ≤ x i j}

/-- Eq. (10): the imaging objective `L_ṽ(x, ĝ) + R_{λ₁,λ₂}(x)` for fixed gains `ĝ`. -/
def imagingObjective (D : ObsSetup S N M Nx Ny) (lam1 lam2 : ℝ) (g : Gains N)
    (x : Image Nx Ny) : ℝ :=
  dataLoss D x g + imgReg lam1 lam2 x

/-- Eq. (13): the previous gain `(α, l-1)` of station `α`, for `l ≥ 1`. -/
def predIdx (p : GainIdx N) (_h : 0 < p.2.val) : GainIdx N := ⟨p.1, ⟨p.2.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) p.2.isLt⟩⟩

/-- Eq. (A5): the next gain `(α, l+1)` of station `α`, when it exists. -/
def succIdx (p : GainIdx N) (h : p.2.val + 1 < N p.1) : GainIdx N := ⟨p.1, ⟨p.2.val + 1, h⟩⟩

/-- Eq. (13): `w_{α l} = 1 / (t_l - t_{l-1})`, for `l ≥ 1`. -/
def stepWeight (D : ObsSetup S N M Nx Ny) (p : GainIdx N) (h : 0 < p.2.val) : ℝ :=
  1 / (D.time p - D.time (predIdx p h))

/-- Eq. (12): the gain-correction constraint `∑_l |g_{α l}| = N_α` for every station `α`. -/
def gainFeasible (N : S → ℕ) : Set (Gains N) :=
  {g | ∀ α : S, ∑ i : Fin (N α), ‖g ⟨α, i⟩‖ = (N α : ℝ)}

/-- Eq. (13): `S_{μ₁,μ₂}(g) = μ₁ ∑_{α,l} w_{α l} |g_{α l} - g_{α l-1}|²
+ μ₂ ∑_{α,l} w_{α l} (|g_{α l}| - |g_{α l-1}|)²`, the sums running over `l ≥ 1`. -/
def gainReg (D : ObsSetup S N M Nx Ny) (mu1 mu2 : ℝ) (g : Gains N) : ℝ :=
  ∑ p : GainIdx N, if h : 0 < p.2.val then
    stepWeight D p h * (mu1 * ‖g p - g (predIdx p h)‖ ^ 2 +
      mu2 * (‖g p‖ - ‖g (predIdx p h)‖) ^ 2) else 0

/-- Eq. (12): the gain-correction objective `L_ṽ(x̂, g) + S_{μ₁,μ₂}(g)` for a fixed image `x̂`. -/
def gainObjective (D : ObsSetup S N M Nx Ny) (x : Image Nx Ny) (mu1 mu2 : ℝ) (g : Gains N) : ℝ :=
  dataLoss D x g + gainReg D mu1 mu2 g

/-- Eq. (14): the joint objective `L_ṽ(x, g) + R_{λ₁,λ₂}(x) + S_{μ₁,μ₂}(g)`. -/
def jointObjective (D : ObsSetup S N M Nx Ny) (lam1 lam2 mu1 mu2 : ℝ)
    (xg : Image Nx Ny × Gains N) : ℝ :=
  dataLoss D xg.1 xg.2 + imgReg lam1 lam2 xg.1 + gainReg D mu1 mu2 xg.2

/-- Section 3.2 ("quartic ... w.r.t. `g`"): the real coordinates of the gains, `(Re g_{α l})` for
the index `0` and `(Im g_{α l})` for the index `1`. -/
def gainCoords (g : Gains N) (q : GainIdx N × Fin 2) : ℝ :=
  if q.2 = 0 then (g q.1).re else (g q.1).im

/-- Eq. (A1): `𝓛_ṽ(x, g, h) = ∑_k (1 / (4 σ_k²)) [|ṽ_k g_{α l} h*_{β l} - F_k(x)|²
+ |ṽ_k h_{α l} g*_{β l} - F_k(x)|²]`. -/
def extDataLoss (D : ObsSetup S N M Nx Ny) (x : Image Nx Ny) (g h : Gains N) : ℝ :=
  ∑ k, (1 / (4 * D.sigma k ^ 2)) *
    (‖D.vobs k * g (D.first k) * starRingEnd ℂ (h (D.second k)) - visFT D x k‖ ^ 2 +
      ‖D.vobs k * h (D.first k) * starRingEnd ℂ (g (D.second k)) - visFT D x k‖ ^ 2)

/-- Eq. (A2): `𝒮_{μ₁,μ₂}(g, h) = (μ₁/2) ∑_{α,l} w_{α l} [|g_{α l} - h_{α l-1}|² + |h_{α l} - g_{α l-1}|²]
+ (μ₂/2) ∑_{α,l} w_{α l} [(|g_{α l}| - |h_{α l-1}|)² + (|h_{α l}| - |g_{α l-1}|)²]`, over `l ≥ 1`. -/
def extGainReg (D : ObsSetup S N M Nx Ny) (mu1 mu2 : ℝ) (g h : Gains N) : ℝ :=
  ∑ p : GainIdx N, if hp : 0 < p.2.val then
    stepWeight D p hp *
      (mu1 / 2 * (‖g p - h (predIdx p hp)‖ ^ 2 + ‖h p - g (predIdx p hp)‖ ^ 2) +
        mu2 / 2 * ((‖g p‖ - ‖h (predIdx p hp)‖) ^ 2 + (‖h p‖ - ‖g (predIdx p hp)‖) ^ 2)) else 0

/-- Eq. (A3): the subproblem objective
`𝓛_ṽ(x, g, ĥ) + 𝒮_{μ₁,μ₂}(g, ĥ) + (ρ/2) ∑_{α,l} |g_{α l} - ĥ_{α l}|²`, minimised over `g` subject
to the constraint of eq. (12). -/
def subproblemObjective (D : ObsSetup S N M Nx Ny) (x : Image Nx Ny) (mu1 mu2 rho : ℝ)
    (h g : Gains N) : ℝ :=
  extDataLoss D x g h + extGainReg D mu1 mu2 g h + rho / 2 * ∑ p, ‖g p - h p‖ ^ 2

/-- Eq. (A5): `w_{α l}`, taken as `0` when `l = 0` (no previous gain). -/
def prevWeight (D : ObsSetup S N M Nx Ny) (p : GainIdx N) : ℝ :=
  if h : 0 < p.2.val then stepWeight D p h else 0

/-- Eq. (A5): `w_{α l+1}`, taken as `0` when `l` is the last gain of station `α`. -/
def nextWeight (D : ObsSetup S N M Nx Ny) (p : GainIdx N) : ℝ :=
  if h : p.2.val + 1 < N p.1 then stepWeight D (succIdx p h) (Nat.succ_pos _) else 0

/-- Eq. (A5): `h_{α l-1}`, taken as `0` when `l = 0`. -/
def prevVal (h : Gains N) (p : GainIdx N) : ℂ :=
  if hp : 0 < p.2.val then h (predIdx p hp) else 0

/-- Eq. (A5): `h_{α l+1}`, taken as `0` when `l` is the last gain of station `α`. -/
def nextVal (h : Gains N) (p : GainIdx N) : ℂ :=
  if hp : p.2.val + 1 < N p.1 then h (succIdx p hp) else 0

/-- Appendix 1, after eq. (A5): `𝒩(α l)`, the visibilities `k ↔ (t_l, α, β)` containing the gain
`g_{α l}` (as the first factor of eq. (4)); for such `k`, `β` is the station of `second k`. -/
def visOf (D : ObsSetup S N M Nx Ny) (p : GainIdx N) : Finset (Fin M) :=
  univ.filter fun k => D.first k = p

/-- Eq. (A5): `a_{α l} = ∑_{k ∈ 𝒩(α l)} |ṽ_k|² |h_{β l}|² / σ_k² + ρ + (μ₁ + μ₂)(w_{α l} + w_{α l+1})`. -/
def coefA (D : ObsSetup S N M Nx Ny) (mu1 mu2 rho : ℝ) (h : Gains N) (p : GainIdx N) : ℝ :=
  (∑ k ∈ visOf D p, ‖D.vobs k‖ ^ 2 * ‖h (D.second k)‖ ^ 2 / D.sigma k ^ 2) + rho +
    (mu1 + mu2) * (prevWeight D p + nextWeight D p)

/-- Eq. (A5): `b_{α l} = ∑_{k ∈ 𝒩(α l)} y_k ṽ*_k h_{β l} / σ_k² + ρ h_{α l}
+ μ₁ (w_{α l} h_{α l-1} + w_{α l+1} h_{α l+1})`, with `y_k = F_k(x)` the model visibility. -/
def coefB (D : ObsSetup S N M Nx Ny) (x : Image Nx Ny) (mu1 rho : ℝ) (h : Gains N)
    (p : GainIdx N) : ℂ :=
  (∑ k ∈ visOf D p, visFT D x k * starRingEnd ℂ (D.vobs k) * h (D.second k) /
      ((D.sigma k ^ 2 : ℝ) : ℂ)) + (rho : ℂ) * h p +
    (mu1 : ℂ) * ((prevWeight D p : ℂ) * prevVal h p + (nextWeight D p : ℂ) * nextVal h p)

/-- Eq. (A5): `c_{α l} = μ₂ (w_{α l} |h_{α l-1}| + w_{α l+1} |h_{α l+1}|)`. -/
def coefC (D : ObsSetup S N M Nx Ny) (mu2 : ℝ) (h : Gains N) (p : GainIdx N) : ℝ :=
  mu2 * (prevWeight D p * ‖prevVal h p‖ + nextWeight D p * ‖nextVal h p‖)

/-- Eq. (A5): the Lagrange multiplier
`η_α = (∑_l (|b_{α l}| + c_{α l}) / a_{α l} - N_α) / ∑_l 1 / a_{α l}`. -/
def etaMult (D : ObsSetup S N M Nx Ny) (x : Image Nx Ny) (mu1 mu2 rho : ℝ) (h : Gains N)
    (α : S) : ℝ :=
  ((∑ i : Fin (N α), (‖coefB D x mu1 rho h ⟨α, i⟩‖ + coefC D mu2 h ⟨α, i⟩) /
      coefA D mu1 mu2 rho h ⟨α, i⟩) - N α) /
    ∑ i : Fin (N α), 1 / coefA D mu1 mu2 rho h ⟨α, i⟩

/-- Eq. (A5): `r_{α l} = (|b_{α l}| + c_{α l} - η_α) / a_{α l}`. -/
def coefR (D : ObsSetup S N M Nx Ny) (x : Image Nx Ny) (mu1 mu2 rho : ℝ) (h : Gains N)
    (p : GainIdx N) : ℝ :=
  (‖coefB D x mu1 rho h p‖ + coefC D mu2 h p - etaMult D x mu1 mu2 rho h p.1) /
    coefA D mu1 mu2 rho h p

/-- Eq. (A4): the closed-form update `ĝ_{α l} = r_{α l} b_{α l} / |b_{α l}|`. -/
def closedFormGain (D : ObsSetup S N M Nx Ny) (x : Image Nx Ny) (mu1 mu2 rho : ℝ) (h : Gains N)
    (p : GainIdx N) : ℂ :=
  (coefR D x mu1 mu2 rho h p : ℂ) * (coefB D x mu1 rho h p / (‖coefB D x mu1 rho h p‖ : ℂ))

/-- Eqs. (3) and (A5), the convention under which `𝒩(α l)` collects every visibility containing
`g_{α l}`: each visibility `k ↔ (t_l, α, β)` is also recorded as `k' ↔ (t_l, β, α)` with
`ṽ_{k'} = ṽ_k*`, `σ_{k'} = σ_k` and u-v point `(-u_k, -v_k)` (Hermitian symmetry of
visibilities). -/
def IsConjDuplicated (D : ObsSetup S N M Nx Ny) : Prop :=
  ∃ dup : Fin M → Fin M, ∀ k, D.first (dup k) = D.second k ∧ D.second (dup k) = D.first k ∧
    D.vobs (dup k) = starRingEnd ℂ (D.vobs k) ∧ D.sigma (dup k) = D.sigma k ∧
    D.u (dup k) = -D.u k ∧ D.v (dup k) = -D.v k

end Arxiv2412_03183


