-- Prove2me | Definitions.Def_GoodViewsNotEnough_Basic
-- name    : GoodViewsNotEnough_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T18:48:56.049558+00:00
-- url     : https://prove2.me/theorems/ae669ebf-c6e6-4a6c-bde6-d3f37c0f9d51
-- title:
--   Good Views Are Not Enough: Epps–Pulley discrepancy, four-state scalar model and 512-dimensional whitened model
-- statement:
--   Objects of Sections 3–5 and Appendices A–E of Xu (2026), *Good Views Are Not Enough*.
--
--   1. **Characteristic-function discrepancy (eq. 6).** For a law $\mu$ on $\mathbb{R}$ with characteristic function $\varphi_\mu(t)=\mathbb{E}_\mu e^{itX}$, the standard Gaussian characteristic function $g(t)=e^{-t^2/2}$ and a finite frequency measure $\nu$ on $\mathbb{R}$: $D_\nu(\mu)=\int|\varphi_\mu(t)-g(t)|^2\,d\nu(t)$, $A_\nu=\nu(\mathbb{R})$ and $J_\nu(\mu)=\int|\varphi_\mu(t)|^2\,d\nu(t)$.
--   2. **Epps–Pulley statistic.** For a batch $y\in\mathbb{R}^N$ with empirical law $\hat\mu_N=\frac1N\sum_n\delta_{y_n}$, the statistic is $N\,D_\nu(\hat\mu_N)$. Its expectation over an i.i.d. batch from $\mu$ is $R_{N,\nu}(\mu)$.
--   3. **Frequency measures.** The analytic measure is $d\nu=e^{-t^2/2}\,dt$. The scalar grid is $\nu_{\rm gr}=\sum_{j=-8}^{8}\omega_j\delta_{t_j}$ with $t_j=5j/8$, $\omega_j=\frac58c_je^{-t_j^2/2}$, $c_{\pm8}=\frac12$ and $c_j=1$ otherwise (eq. 11).
--   4. **Four-state scalar model (Section 4).** There are four observations $(S,U)=(1,1),(1,-1),(-1,1),(-1,-1)$ with uniform law, scene signs $s=(1,1,-1,-1)$ and the pair law $\pi_{ij}=(1+s_is_j/2)/16$. A scalar encoder is $x\in\mathbb{R}^4$ with output law $\mu_x=\frac14\sum_i\delta_{x_i}$. The prediction term is $P_\pi(x)=\frac14\sum_{i,j}\pi_{ij}(x_i-x_j)^2$ and the centred domain is $X_0=\{x:\sum_ix_i=0\}$. The objectives are $F_\pi(x)=P_\pi(x)+\frac1{49}R_{1024,\rm gr}(\mu_x)$ (eq. 1), $P_\pi+\gamma D_\nu(\mu_x)$ and $P_\pi+\alpha R_{N,\nu}(\mu_x)$. The within-scene swaps are $T_+=(12)$ and $T_-=(34)$. The comparator is $w=(1/10,13/10,-1/10,-13/10)$, and $d_*=\frac{\sqrt{2\pi}}2+\sqrt{\frac{2\pi}3}-\frac74\sqrt\pi\,2^{-3/14}$. Further: $\|x\|_p^2=\frac14\sum_ix_i^2$, $d_\pm(x,z)=\min\{\|x-z\|_p,\|x+z\|_p\}$, $\mathbb{E}[x\mid S]$ is the scene average, and $u(x)=\mathbb{E}\operatorname{Var}(x\mid S)$. A pair law with uniform marginals is a symmetric nonnegative $\pi'$ with $\sum_j\pi'_{ij}=\frac14$.
--   5. **512-dimensional model (Section 5).** The scene $S$ takes 513 values with $p_1=p_2=\frac14$ and $p_s=\frac1{1022}$ otherwise. The nuisance $U$ is uniform on $\{-1,1\}^{512}$, independent of $S$. An encoder is any map $h(S,U)\in\mathbb{R}^{512}$. It is whitened if $\mathbb{E}h=0$ and $\mathbb{E}hh^\top=I_{512}$, and its nuisance fraction is $u(h)=\frac1{512}\mathbb{E}\|h-\mathbb{E}[h\mid S]\|^2$.
--   6. **Pooled statistic (eqs. 19–21).** The nodes are $t_j=3j/16$, $0\le j\le16$, with weights $\omega_j=\frac3{16}d_jg_j$, where $d_0=d_{16}=1$ and $d_j=2$ otherwise. A batch $\mathcal B$ has $N=256$ i.i.d. scenes and $V=8$ independent nuisances per scene, giving $M=2048$ outputs. For a direction $\theta$ uniform on $\mathbb{S}^{511}$, $\widehat R_{\mathcal B,\theta}(h)=M\sum_j\omega_j\big|\frac1M\sum_{i,v}e^{it_j\theta^\top h(S_i,U_{iv})}-g_j\big|^2$. Then $\bar R(h)=\mathbb{E}_{\mathcal B,\theta}\widehat R_{\mathcal B,\theta}(h)$ and $F(h)=\frac54u(h)+\frac1{50}\bar R(h)$. The direction-averaged terms are $J$, $J_c$ and $X$ of Appendix D.2.
--   7. **Single batch (eq. 28).** $\widehat F_{\mathcal B}(h)=\frac1{NVk}\sum_{i,v}\|h_{iv}-\bar h_{i,G}\|^2+\frac1{50}\mathbb{E}_\theta\widehat R_{\mathcal B,\theta}(h)$, where $\bar h_{i,G}$ averages the first $G=2$ views.
--   8. **Alignment and the linear class.** The alignment error is $\frac1{512}\mathbb{E}\|h_1(S,U_1)-Qh_2(S,U_2)\|^2$ with $U_1,U_2$ independent. Here $r$ is a centred orthonormal scene basis ($\mathbb{E}r=0$, $\mathbb{E}rr^\top=I$), and $h_W(S,U)=W(r(S),U)$ with $W\in\mathbb{R}^{512\times1024}$ and $WW^\top=I$.
--
--   **Formalization Note** Observation $(S,U)$ of the scalar model is index $i\in\{0,1,2,3\}$ in the listed order, and scenes $1,2$ of the 512-dimensional model are indices $0,1$. A cube point is a Boolean vector, mapped to $\pm1$. All expectations over the finite observation spaces are finite weighted sums. The uniform law on $\mathbb{S}^{511}$ is Mathlib's surface measure on the sphere, normalised to total mass one.
-- source:
--   Anran Xu, Good Views Are Not Enough: Global Counterexamples for Gaussian-Regularized JEPAs, arXiv:2611.12137v1 (2026), Section 3, Section 4 (eq. 1), Section 5 (eq. 2), Appendix A (eqs. 6-7), Appendix B.1-B.2 (eqs. 8, 11), Appendix C, Appendix D.1-D.2 (eqs. 16, 17, 19-21), Appendix E (eq. 28)

import Mathlib

/-!
Anran Xu, *Good Views Are Not Enough: Global Counterexamples for Gaussian-Regularized JEPAs*,
arXiv:2611.12137v1 (2026): the characteristic-function discrepancy and the expected Epps–Pulley
statistic of Section 3 and Appendix A, the four-state scalar model of Section 4 and Appendices B–C,
and the 512-dimensional whitened model with pooled Epps–Pulley regularization of Section 5 and
Appendices D–E.
-/

open MeasureTheory Complex
open scoped ENNReal

noncomputable section

namespace GoodViewsNotEnough

/-! ### Characteristic-function discrepancy and the Epps–Pulley statistic -/

/-- Section 3 and Appendix A, eq. (6): the standard Gaussian characteristic function
`g(t) = exp(-t²/2)`. -/
def gaussCF (t : ℝ) : ℝ := Real.exp (-t ^ 2 / 2)

/-- Appendix A, eq. (6): the weighted characteristic-function discrepancy
`D_ν(μ) = ∫ |φ_μ(t) - g(t)|² dν(t)` of a law `μ` on `ℝ` for a frequency measure `ν`. -/
def discrepancy (ν μ : Measure ℝ) : ℝ := ∫ t, ‖charFun μ t - (gaussCF t : ℂ)‖ ^ 2 ∂ν

/-- Appendix A, eq. (6): the total mass `A_ν = ∫ dν` of a frequency measure. -/
def freqMass (ν : Measure ℝ) : ℝ := (ν Set.univ).toReal

/-- Appendix A, eq. (6): the self term `J_ν(μ) = ∫ |φ_μ(t)|² dν(t)`. -/
def selfTerm (ν μ : Measure ℝ) : ℝ := ∫ t, ‖charFun μ t‖ ^ 2 ∂ν

/-- Appendix A: the empirical law `(1/N) ∑_n δ_{y_n}` of a batch `y` of size `N`. -/
def empiricalLaw {N : ℕ} (y : Fin N → ℝ) : Measure ℝ :=
  ∑ n, (N : ℝ≥0∞)⁻¹ • Measure.dirac (y n)

/-- Section 3 and Appendix A: the Epps–Pulley statistic of a batch of size `N`, which is `N` times
the empirical discrepancy, `N · D_ν(μ̂_N)`. -/
def epStat {N : ℕ} (ν : Measure ℝ) (y : Fin N → ℝ) : ℝ := N * discrepancy ν (empiricalLaw y)

/-- Section 4 and Appendix A, before eq. (7): `R_{N,ν}(μ)`, the exact expectation of the
Epps–Pulley statistic on an i.i.d. batch of size `N` drawn from `μ`. -/
def iidEP (N : ℕ) (ν μ : Measure ℝ) : ℝ := ∫ y, epStat ν y ∂(Measure.pi fun _ : Fin N => μ)

/-- Appendix B.2: the analytic frequency measure `dν = e^{-t²/2} dt` on `ℝ`. -/
def analyticFreq : Measure ℝ := volume.withDensity fun t => ENNReal.ofReal (gaussCF t)

/-- Section 4 and Appendix B.2, eq. (11): the scalar grid nodes `t_j = 5j/8`, `-8 ≤ j ≤ 8`, indexed
by `j + 8 ∈ {0, …, 16}`. -/
def scalarNode (j : Fin 17) : ℝ := 5 * (((j : ℕ) : ℝ) - 8) / 8

/-- Section 4 and Appendix B.2, eq. (11): the grid weights `ω_j = (5/8) c_j e^{-t_j²/2}` with
`c_{±8} = 1/2` and `c_j = 1` otherwise. -/
def scalarWeight (j : Fin 17) : ℝ :=
  5 / 8 * (if (j : ℕ) = 0 ∨ (j : ℕ) = 16 then 1 / 2 else 1) * gaussCF (scalarNode j)

/-- Section 4 and Appendix B.2, eq. (11): the grid frequency measure `∑_j ω_j δ_{t_j}`, for which
`D_ν = D_gr = ∑_j ω_j |φ(t_j) - g_j|²`. -/
def gridFreq : Measure ℝ :=
  ∑ j, ENNReal.ofReal (scalarWeight j) • Measure.dirac (scalarNode j)

/-! ### The four-state scalar model (Section 4, Appendices B and C) -/

/-- Section 4 and Appendix B.1: the scene sign `s = (1, 1, -1, -1)` of the four observations
`(S,U) = (1,1), (1,-1), (-1,1), (-1,-1)`. -/
def scalarScene : Fin 4 → ℝ := ![1, 1, -1, -1]

/-- Section 4 and Appendix B.1, eq. (8): the positive-pair law `π_ij = (1 + s_i s_j / 2) / 16`. -/
def scalarPairLaw (i j : Fin 4) : ℝ := (1 + scalarScene i * scalarScene j / 2) / 16

/-- Appendix C, Corollary 6: `π` is a symmetric pair law on the four observations with uniform
marginals `∑_j π_ij = 1/4`. -/
def IsUniformPairLaw (π : Fin 4 → Fin 4 → ℝ) : Prop :=
  (∀ i j, 0 ≤ π i j) ∧ (∀ i j, π i j = π j i) ∧ ∀ i, ∑ j, π i j = 1 / 4

/-- Section 4: the prediction term `P_π(x) = (1/4) ∑_{i,j} π_ij (x_i - x_j)²` of a scalar
encoder `x ∈ ℝ⁴`. -/
def scalarPred (π : Fin 4 → Fin 4 → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  1 / 4 * ∑ i, ∑ j, π i j * (x i - x j) ^ 2

/-- Section 4, eq. (1): the output law `μ_x = (1/4) ∑_i δ_{x_i}` of a scalar encoder. -/
def scalarLaw (x : Fin 4 → ℝ) : Measure ℝ := ∑ i, (4 : ℝ≥0∞)⁻¹ • Measure.dirac (x i)

/-- Appendix B.2, Lemma 3: the equally weighted two-atom law `(δ_b + δ_c)/2`. -/
def twoAtomLaw (b c : ℝ) : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac b + Measure.dirac c)

/-- Section 4: the centred domain `X₀ = {x ∈ ℝ⁴ : ∑_i x_i = 0}` (that is, `E_p x = 0`). -/
def centeredDomain : Set (Fin 4 → ℝ) := {x | ∑ i, x i = 0}

/-- Section 4, eq. (1), and Appendix C, Lemma 5: `F_π(x) = P_π(x) + R_{1024,gr}(μ_x)/49`. -/
def scalarObjective (π : Fin 4 → Fin 4 → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  scalarPred π x + 1 / 49 * iidEP 1024 gridFreq (scalarLaw x)

/-- Appendix B.3, Theorem 4: the deterministic objective `P_π + γ D_ν(μ_x)`. -/
def detObjective (ν : Measure ℝ) (γ : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  scalarPred scalarPairLaw x + γ * discrepancy ν (scalarLaw x)

/-- Appendix B.3, Theorem 4: the i.i.d. objective `P_π + α R_{N,ν}(μ_x)`. -/
def iidObjective (ν : Measure ℝ) (N : ℕ) (α : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  scalarPred scalarPairLaw x + α * iidEP N ν (scalarLaw x)

/-- Appendix B.1: the within-scene swaps `T₊ = (12)` and `T₋ = (34)` (0-indexed: `(0 1)`, `(2 3)`). -/
def sceneSwaps : Set (Equiv.Perm (Fin 4)) := {Equiv.swap 0 1, Equiv.swap 2 3}

/-- Appendix B.3, Theorem 4: the conclusion of the theorem for an objective `F` on a domain `X`.
`F` attains its minimum on `X`, and for every global minimiser `x` some within-scene swap `x ∘ T`
lies in `X`, has the same value, and lies outside the sign orbit `{x, -x}`. -/
def SwapNonuniqueness (F : (Fin 4 → ℝ) → ℝ) (X : Set (Fin 4 → ℝ)) : Prop :=
  (∃ x ∈ X, IsMinOn F X x) ∧
    ∀ x ∈ X, IsMinOn F X x →
      ∃ T ∈ sceneSwaps, x ∘ ⇑T ∈ X ∧ F (x ∘ ⇑T) = F x ∧ x ∘ ⇑T ≠ x ∧ x ∘ ⇑T ≠ -x

/-- Section 4 and Appendix B.2, Lemma 3: the rational comparator `w = (1/10, 13/10, -1/10, -13/10)`. -/
def scalarComparator : Fin 4 → ℝ := ![1 / 10, 13 / 10, -1 / 10, -13 / 10]

/-- Appendix B.2, eq. (12): `d_* = √(2π)/2 + √(2π/3) - (7/4) √π 2^{-3/14}`. -/
def analyticTwoAtomMin : ℝ :=
  Real.sqrt (2 * Real.pi) / 2 + Real.sqrt (2 * Real.pi / 3) -
    7 / 4 * Real.sqrt Real.pi * (2 : ℝ) ^ (-(3 : ℝ) / 14)

/-- Appendix A: the norm `‖x‖_p = (E_p x²)^{1/2}` under the uniform law `p` on four observations. -/
def pNorm (x : Fin 4 → ℝ) : ℝ := Real.sqrt (1 / 4 * ∑ i, x i ^ 2)

/-- Appendix A: the scalar sign-orbit distance `d_±(x,z) = min{‖x - z‖_p, ‖x + z‖_p}`. -/
def signOrbitDist (x z : Fin 4 → ℝ) : ℝ := min (pNorm (x - z)) (pNorm (x + z))

/-- Appendix C: the conditional scene mean `E[x | S]` of a scalar encoder. -/
def sceneCondMean (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => if (i : ℕ) < 2 then (x 0 + x 1) / 2 else (x 2 + x 3) / 2

/-- Appendix C: the within-scene variance `u(x) = E Var(x | S)`. -/
def scalarNuisance (x : Fin 4 → ℝ) : ℝ := 1 / 4 * ∑ i, (x i - sceneCondMean x i) ^ 2

/-! ### The 512-dimensional whitened model (Section 5, Appendices D and E) -/

/-- Section 5 and Appendix D.1, eq. (16): the scene law on 513 scenes, `p₁ = p₂ = 1/4` and
`p_s = 1/1022` otherwise (scenes 1, 2 of the paper are indices 0, 1). -/
def hdSceneProb (s : Fin 513) : ℝ := if (s : ℕ) < 2 then 1 / 4 else 1 / 1022

/-- Section 5: the probability `2^{-512}` of each nuisance `U ∈ {-1,1}^{512}`, drawn uniformly. -/
def cubeProb : ℝ := ((2 : ℝ) ^ 512)⁻¹

/-- Section 5: the nuisance vector `U ∈ {-1,1}^{512}` encoded by a Boolean vector. -/
def cubeVec (U : Fin 512 → Bool) : Fin 512 → ℝ := fun a => if U a then 1 else -1

/-- Section 5: the population expectation `E f(S,U)` with `S ∼ p` and `U` uniform on the cube,
independent. -/
def popMean (f : Fin 513 → (Fin 512 → Bool) → ℝ) : ℝ :=
  ∑ s, ∑ U, hdSceneProb s * cubeProb * f s U

/-- Section 5 and Appendix D.1, eq. (17): an encoder `h(S,U) ∈ ℝ^{512}` is exactly whitened,
`E h = 0` and `E h hᵀ = I_{512}`. -/
def IsWhitenedHD (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) : Prop :=
  (∀ a, popMean (fun s U => h s U a) = 0) ∧
    ∀ a b, popMean (fun s U => h s U a * h s U b) = if a = b then 1 else 0

/-- Section 5: the conditional scene mean `E[h | S = s]`. -/
def hdCondMean (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) (s : Fin 513) : Fin 512 → ℝ :=
  fun a => ∑ U, cubeProb * h s U a

/-- Section 5 and eq. (17): the nuisance fraction `u(h) = (1/512) E ‖h - E[h | S]‖²`. -/
def nuisanceFrac (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) : ℝ :=
  1 / 512 * popMean (fun s U => ∑ a, (h s U a - hdCondMean h s a) ^ 2)

/-- Section 5 and Appendix D.2, eq. (19): the pooled nodes `t_j = 3j/16`, `0 ≤ j ≤ 16`. -/
def pooledNode (j : Fin 17) : ℝ := 3 * ((j : ℕ) : ℝ) / 16

/-- Section 5 and Appendix D.2, eq. (19): the pooled weights `ω_j = (3/16) d_j g_j` with
`d_0 = d_16 = 1`, `d_j = 2` otherwise, and `g_j = e^{-t_j²/2}`. -/
def pooledWeight (j : Fin 17) : ℝ :=
  3 / 16 * (if (j : ℕ) = 0 ∨ (j : ℕ) = 16 then 1 else 2) * gaussCF (pooledNode j)

/-- Section 5 and Appendix D.2: a batch of `N = 256` examples, each a scene `S_i` and `V = 8`
nuisances `U_{i1}, …, U_{i8}` (one per view). -/
abbrev HDBatch := Fin 256 → Fin 513 × (Fin 8 → Fin 512 → Bool)

/-- Section 5 and Appendix E: the probability of a batch; scenes are i.i.d. `∼ p` and the
`8 · 256` nuisances are i.i.d. uniform on the cube, independent of the scenes. -/
def batchProb (B : HDBatch) : ℝ := ∏ i, (hdSceneProb (B i).1 * cubeProb ^ 8)

/-- Appendix E: the law of a batch, as a measure on batches. -/
def batchLaw : Measure HDBatch := ∑ B, ENNReal.ofReal (batchProb B) • Measure.dirac B

/-- Section 5 and Appendix A: the uniform probability measure on the unit sphere `𝕊^{511}`. -/
def sphereDir : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin 512)) 1) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin 512))).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin 512))).toSphere

/-- Section 5: the projection `θᵀ v` of an embedding onto a direction `θ ∈ 𝕊^{511}`. -/
def dirProj (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 512)) 1) (v : Fin 512 → ℝ) : ℝ :=
  ∑ a, (θ : EuclideanSpace ℝ (Fin 512)) a * v a

/-- Appendix D.2: the pooled statistic `R̂_{B,θ}(h) = M ∑_j ω_j |M⁻¹ ∑_{i,v} e^{i t_j θᵀ h(S_i,U_iv)} - g_j|²`
with `M = NV = 2048`. -/
def pooledStat (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) (B : HDBatch)
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 512)) 1) : ℝ :=
  2048 * ∑ j, pooledWeight j *
    ‖(1 / 2048 : ℂ) * (∑ i, ∑ v, Complex.exp ((pooledNode j * dirProj θ (h (B i).1 ((B i).2 v)) : ℝ) * I)) -
      (gaussCF (pooledNode j) : ℂ)‖ ^ 2

/-- Appendix E, eq. (28): the direction-averaged pooled statistic `E_θ R̂_{B,θ}(h)` of one batch. -/
def dirAvgPooledStat (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) (B : HDBatch) : ℝ :=
  ∫ θ, pooledStat h B θ ∂sphereDir

/-- Section 5, eq. (2), and Appendix D.2: the expected pooled statistic `R̄(h) = E_{B,θ} R̂_{B,θ}(h)`. -/
def pooledEP (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) : ℝ :=
  ∑ B, batchProb B * dirAvgPooledStat h B

/-- Section 5, eq. (2), and Appendix D.2, eq. (21): `F(h) = (5/4) u(h) + R̄(h)/50`. -/
def highObjective (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) : ℝ :=
  5 / 4 * nuisanceFrac h + 1 / 50 * pooledEP h

/-- Appendix D.2: the characteristic function `φ_{h,θ}(t) = E e^{i t θᵀ h(S,U)}` of the projected
output. -/
def hdCF (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ)
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 512)) 1) (t : ℝ) : ℂ :=
  ∑ s, ∑ U, ((hdSceneProb s * cubeProb : ℝ) : ℂ) * Complex.exp ((t * dirProj θ (h s U) : ℝ) * I)

/-- Appendix D.2: the conditional characteristic function `φ_{h|S=s,θ}(t) = E[e^{i t θᵀ h} | S = s]`. -/
def hdCondCF (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) (s : Fin 513)
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 512)) 1) (t : ℝ) : ℂ :=
  ∑ U, ((cubeProb : ℝ) : ℂ) * Complex.exp ((t * dirProj θ (h s U) : ℝ) * I)

/-- Appendix D.2: the direction-averaged marginal self term `J(h) = ∑_j ω_j E_θ |φ_{h,θ}(t_j)|²`. -/
def pooledJ (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) : ℝ :=
  ∑ j, pooledWeight j * ∫ θ, ‖hdCF h θ (pooledNode j)‖ ^ 2 ∂sphereDir

/-- Appendix D.2: the direction-averaged conditional self term
`J_c(h) = ∑_j ω_j E_{S,θ} |φ_{h|S,θ}(t_j)|²`. -/
def pooledJc (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) : ℝ :=
  ∑ j, pooledWeight j * ∑ s, hdSceneProb s * ∫ θ, ‖hdCondCF h s θ (pooledNode j)‖ ^ 2 ∂sphereDir

/-- Appendix D.2: the direction-averaged target cross term
`X(h) = ∑_j ω_j g_j E_θ Re φ_{h,θ}(t_j)`. -/
def pooledX (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) : ℝ :=
  ∑ j, pooledWeight j * gaussCF (pooledNode j) * ∫ θ, (hdCF h θ (pooledNode j)).re ∂sphereDir

/-- Appendix E, eq. (28): the single-batch prediction term
`(1/(NVk)) ∑_{i,v} ‖h_{iv} - h̄_{i,G}‖²`, where `h̄_{i,G}` averages the `G = 2` global views
(the first two views). -/
def batchPred (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) (B : HDBatch) : ℝ :=
  1 / (256 * 8 * 512) * ∑ i, ∑ v, ∑ a,
    (h (B i).1 ((B i).2 v) a - (h (B i).1 ((B i).2 0) a + h (B i).1 ((B i).2 1) a) / 2) ^ 2

/-- Appendix E, eq. (28): the single-batch objective `F̂_B(h)`. -/
def batchObjective (B : HDBatch) (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) : ℝ :=
  batchPred h B + 1 / 50 * dirAvgPooledStat h B

/-- Appendix A and Theorem 2: the cross-modal alignment error `E ‖h₁ - Q h₂‖² / k`, the two
encoders seeing the same scene `S ∼ p` with independent nuisances `U₁, U₂`. -/
def alignErr (h₁ h₂ : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) (Q : Matrix (Fin 512) (Fin 512) ℝ) :
    ℝ :=
  1 / 512 * ∑ s, ∑ U₁, ∑ U₂, hdSceneProb s * cubeProb * cubeProb *
    ∑ a, (h₁ s U₁ a - Q.mulVec (h₂ s U₂) a) ^ 2

/-- Section 5 and Appendix D.1: `r` is a complete centred orthonormal basis of the scene functions
in `L²(p)`, that is, `E r(S) = 0` and `E r(S) r(S)ᵀ = I_{512}`. -/
def IsCenteredOrthonormalBasis (r : Fin 513 → Fin 512 → ℝ) : Prop :=
  (∀ a, ∑ s, hdSceneProb s * r s a = 0) ∧
    ∀ a b, ∑ s, hdSceneProb s * r s a * r s b = if a = b then 1 else 0

/-- Theorem 2 and Appendix D.4, Theorem 8: the linear encoder `h_W(S,U) = W (r(S), U)` with
`W = [A, B] ∈ ℝ^{512 × 1024}`. -/
def linEncoder (r : Fin 513 → Fin 512 → ℝ) (W : Matrix (Fin 512) (Fin 512 ⊕ Fin 512) ℝ) :
    Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ :=
  fun s U a => ∑ b, W a (Sum.inl b) * r s b + ∑ b, W a (Sum.inr b) * cubeVec U b

/-- Theorem 2 and Appendix D.4: the Stiefel constraint `W Wᵀ = I_{512}`. -/
def IsStiefel (W : Matrix (Fin 512) (Fin 512 ⊕ Fin 512) ℝ) : Prop := W * W.transpose = 1

end GoodViewsNotEnough


