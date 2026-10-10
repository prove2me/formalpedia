-- Prove2me | Definitions.Def_RieszMF_Global_Setting
-- name    : RieszMF_Global_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:01.009115+00:00
-- url     : https://prove2.me/theorems/bb5657e6-5f21-4023-93a0-1212385c381e
-- title:
--   §1.1–1.3, §2, §3, §5, pp. 1–6, 10–14, 21–28 — admissible potentials (i)–(x), global superharmonicity, the systems (1.1) and (1.5), the modulated energy (1.6)
-- statement:
--   This module fixes the objects of Rosenzweig and Serfaty's mean-field analysis of singular diffusive flows in $\mathbb R^d$.
--
--   1. **Admissible potentials.** A potential $\mathsf g:\mathbb R^d\to\mathbb R$ of order $s$ is *admissible* (pp. 5–6) if it satisfies ten assumptions, each recorded as its own predicate: (i) $\mathsf g(x)=\mathsf g(-x)$; (ii) $\mathsf g(x)\to\infty$ as $x\to0$; (iii) there is $r_0>0$ with $\Delta\mathsf g\le0$ on $B(0,r_0)\setminus\{0\}$; (iv) $\mathsf g\in C^\infty(\mathbb R^d\setminus\{0\})$ and, for every $k\ge0$, $|\nabla^{\otimes k}\mathsf g(x)|\le C_k\big(|x|^{-s-k}+|\log|x||\mathbf 1_{s=k=0}\big)$; (v) $|x||\nabla\mathsf g(x)|+|x|^2|\nabla^{\otimes2}\mathsf g(x)|\le C\mathsf g(x)$ on $B(0,r_0)\setminus\{0\}$; (vi) the Fourier transform satisfies $C_1|\xi|^{-(d-s)}\le\hat{\mathsf g}(\xi)\le C_2|\xi|^{-(d-s)}$ for $\xi\ne0$; (vii) the doubling conditions: for $x,y\in B(0,r_0)$, $x\ne0$, with $|y|\ge2|x|$, there is $c_s<1$ with $\mathsf g(y)<c_s\mathsf g(x)$ ($s>0$), resp. $c_0>0$ with $\mathsf g(x)-\mathsf g(y)\ge c_0$ ($s=0$); (viii) if $d-4<s$, an extension $\mathsf G:\mathbb R^{d+m}\to\mathbb R$, $m\ge1$, with $-\Delta\mathsf g(x)=\mathsf G(x,0)$, $\mathsf G$ even, smooth, superharmonic and with $|\nabla^{\otimes k}\mathsf G(X)|\le C_k|X|^{-(s+2+k)}$ on $B(0,r_0)\setminus\{0\}$ and $\hat{\mathsf G}\ge0$; (ix) if $s=d-2k$ for a positive integer $k$, the kernel $x\otimes\nabla^{\otimes(2k+1)}\mathsf g(x)$ is associated to a Calderón–Zygmund operator; (x) $\mathbb M:\nabla^{\otimes2}\mathsf g(x)\ge0$ for $x\ne0$, where $\mathbb M$ is a $d\times d$ matrix with $\mathbb M\xi\cdot\xi\le0$ (condition (1.2)).
--
--   2. **Global superharmonicity** (p. 7, "$r_0=\infty$ in (iii)"): $\Delta\mathsf g\le0$ on all of $\mathbb R^d\setminus\{0\}$, and the variant of (viii) in which (1.15)–(1.16) hold on all of $\mathbb R^{d+m}\setminus\{0\}$.
--
--   3. **The particle system (1.1).** For independent standard Brownian motions $W_1,\dots,W_N$ in $\mathbb R^d$ and pairwise distinct $x^0_1,\dots,x^0_N$, a solution is a family of processes with continuous paths that almost surely never collide and satisfy
--   $$x^t_i=x^0_i+\int_0^t\frac1N\sum_{j\ne i}\mathbb M\nabla\mathsf g(x^\tau_i-x^\tau_j)\,d\tau+\sqrt{2\sigma}\,W^t_i .$$
--
--   4. **The mean-field PDE (1.5)** $\partial_t\mu=-\operatorname{div}(\mu\,\mathbb M\nabla\mathsf g*\mu)+\sigma\Delta\mu$, in the mild form (3.1)
--   $$\mu^t=e^{t\sigma\Delta}\mu^0-\int_0^te^{(t-\kappa)\sigma\Delta}\operatorname{div}(\mu^\kappa\,\mathbb M\nabla\mathsf g*\mu^\kappa)\,d\kappa,$$
--   for paths $\mu\in C([0,\infty);L^1\cap L^\infty)$; the probability-density condition $\mu^t\in\mathcal P(\mathbb R^d)$ is a separate predicate.
--
--   5. **The modulated energy (1.6)**
--   $$F_N(x_N,\mu)=\int_{(\mathbb R^d)^2\setminus\triangle}\mathsf g(x-y)\,d\Big(\frac1N\sum_{i=1}^N\delta_{x_i}-\mu\Big)^{\otimes2}(x,y),$$
--   and the same off-diagonal pairing for any kernel $K(x,y)$, together with the smeared potentials $\mathsf g_\eta=\mathsf g*\delta^{(\eta)}_0$ ($\delta^{(\eta)}_0$ the uniform probability measure on $\partial B(0,\eta)$), the Riesz potential $\mathcal I_s$ of (2.3), the exponents $\gamma_{s,p},\lambda_{s,p}$ of (5.21), the constant $K(r)$ of (3.23), and the fractional derivative $|\nabla|^a$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Derivatives are Mathlib's `iteratedFDeriv` (operator norm), `gradient` and `Laplacian.laplacian`. The Fourier transforms in (vi) and (1.17) are read away from the origin: there is a function $\hat{\mathsf g}$ with $\int\mathsf g\,\mathcal F\varphi=\int\hat{\mathsf g}\,\varphi$ for every Schwartz $\varphi$ vanishing near $0$ (Mathlib's normalization $e^{-2\pi i\langle x,\xi\rangle}$). Quantities singular at $0$ are required for $x\ne0$ only. (iv) has a constant $C_k$ for each $k$. (ix) is stated componentwise: each scalar component of the tensor kernel is associated to an operator bounded on $L^2$ that is given by the kernel integral off the support of bounded compactly supported data. One radius $r_0$ serves (iii), (v), (vii) and (viii). In (vii) for $s>0$ the page prints $\mathsf g(x)<c_s\mathsf g(y)$; with $|y|\ge2|x|$ this contradicts (ii) as $x\to0$ (no admissible potential would exist), so the clause is read with $x$ and $y$ exchanged, $\mathsf g(y)<c_s\mathsf g(x)$: the far point has the smaller value, as in the $s=0$ clause. The model potential $|x|^{-s}$ satisfies it with $c_s=(1+2^{-s})/2$. The SDE needs no Itô integral because the noise is additive; the no-collision clause is the conclusion of the paper's Proposition 4.5, so it does not narrow the class of solutions. The mild formulation requires every integral in (3.1), including the velocity $u^\kappa(y)$ for a.e. $y$, to converge absolutely, so a divergent integral is never read as $0$; likewise both pairings in the off-zero Fourier identity converge absolutely.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, pp. 1–7, 10–14, 21–28: (1.1), (1.2), (1.5), (1.6), assumptions (i)–(x) and (1.14)–(1.17), (2.3), (3.1), (3.23), (5.2), (5.12), (5.21)

import Mathlib
import Definitions.Def_RieszMF_Linear_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal FourierTransform SchwartzMap

namespace RieszMF.Global

noncomputable section

/-! ### Space, derivatives, the matrix 𝕄 -/

/-- The standard basis vector `e_i` of `ℝ^n`. -/
def basisVec (n : ℕ) (i : Fin n) : RieszMF.Linear.E n := EuclideanSpace.single i 1

/-- The embedding `ℝ^d → ℝ^{d+m}`, `x ↦ (x, 0)`. -/
def embed (d m : ℕ) (x : RieszMF.Linear.E d) : RieszMF.Linear.E (d + m) :=
  WithLp.toLp 2 (Fin.append (WithLp.ofLp x) (0 : Fin m → ℝ))

/-- The Laplacian `Δf(x)` (trace of the Hessian, Mathlib's `Laplacian` instance). -/
def lap {n : ℕ} (f : RieszMF.Linear.E n → ℝ) (x : RieszMF.Linear.E n) : ℝ := Laplacian.laplacian f x

/-- The vector field `𝕄∇g(z)`. -/
def mGrad {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (g : RieszMF.Linear.E d → ℝ) (z : RieszMF.Linear.E d) : RieszMF.Linear.E d :=
  Matrix.toEuclideanLin M (gradient g z)

/-! ### Fourier transforms away from the origin -/

/-! ### Assumptions (i)–(x) on the potential (pp. 5–6) -/

/-- (iii) `Δg ≤ 0` on `B(0, r₀) ∖ {0}`, with `r₀ > 0`. -/
def AssumpIII {n : ℕ} (g : RieszMF.Linear.E n → ℝ) (r₀ : ℝ) : Prop :=
  0 < r₀ ∧ ∀ x : RieszMF.Linear.E n, x ≠ 0 → ‖x‖ < r₀ → lap g x ≤ 0

/-- (iii) with `r₀ = ∞`: `g` is globally superharmonic, `Δg ≤ 0` on `ℝ^n ∖ {0}`. -/
def GloballySuperharmonic {n : ℕ} (g : RieszMF.Linear.E n → ℝ) : Prop :=
  ∀ x : RieszMF.Linear.E n, x ≠ 0 → lap g x ≤ 0

/-- `G : ℝ^{d+m} → ℝ` is an extension of `h : ℝ^d → ℝ` of order `a` on `B(0, r₀)`:
`h(x) = G(x, 0)` for `x ≠ 0`, (1.14) `G(X) = G(-X)`, (1.15) `ΔG ≤ 0` on `B(0, r₀) ∖ {0}`,
`G ∈ C^∞(B(0, r₀) ∖ {0})`, (1.16) `|∇^{⊗k}G(X)| ≤ C_k |X|^{-(a+k)}` on `B(0, r₀) ∖ {0}`,
(1.17) `Ĝ ≥ 0` away from the origin. -/
def IsExtension (d m : ℕ) (h : RieszMF.Linear.E d → ℝ) (a r₀ : ℝ) (G : RieszMF.Linear.E (d + m) → ℝ) : Prop :=
  (∀ x : RieszMF.Linear.E d, x ≠ 0 → h x = G (embed d m x)) ∧
  (∀ X, G (-X) = G X) ∧
  (∀ X : RieszMF.Linear.E (d + m), X ≠ 0 → ‖X‖ < r₀ → lap G X ≤ 0) ∧
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (Metric.ball 0 r₀ \ {0}) ∧
  (∀ k : ℕ, ∃ C : ℝ, ∀ X : RieszMF.Linear.E (d + m), X ≠ 0 → ‖X‖ < r₀ →
      ‖iteratedFDeriv ℝ k G X‖ ≤ C / ‖X‖ ^ (a + k)) ∧
  ∃ Ghat : RieszMF.Linear.E (d + m) → ℝ, (∀ Ξ : RieszMF.Linear.E (d + m), Ξ ≠ 0 → 0 ≤ Ghat Ξ) ∧ RieszMF.Linear.FTOffZero G Ghat

/-- The same with `r₀ = ∞` in (1.15) and (1.16). -/
def IsGlobalExtension (d m : ℕ) (h : RieszMF.Linear.E d → ℝ) (a : ℝ) (G : RieszMF.Linear.E (d + m) → ℝ) : Prop :=
  (∀ x : RieszMF.Linear.E d, x ≠ 0 → h x = G (embed d m x)) ∧
  (∀ X, G (-X) = G X) ∧
  (∀ X : RieszMF.Linear.E (d + m), X ≠ 0 → lap G X ≤ 0) ∧
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G {0}ᶜ ∧
  (∀ k : ℕ, ∃ C : ℝ, ∀ X : RieszMF.Linear.E (d + m), X ≠ 0 →
      ‖iteratedFDeriv ℝ k G X‖ ≤ C / ‖X‖ ^ (a + k)) ∧
  ∃ Ghat : RieszMF.Linear.E (d + m) → ℝ, (∀ Ξ : RieszMF.Linear.E (d + m), Ξ ≠ 0 → 0 ≤ Ghat Ξ) ∧ RieszMF.Linear.FTOffZero G Ghat

/-- (viii) If `d - 4 < s`, there are `m ≥ 1` and an extension `G` of `-Δg` of order `s + 2`. -/
def AssumpVIII (d : ℕ) (s : ℝ) (g : RieszMF.Linear.E d → ℝ) (r₀ : ℝ) : Prop :=
  (d : ℝ) - 4 < s → ∃ m : ℕ, 0 < m ∧ ∃ G : RieszMF.Linear.E (d + m) → ℝ,
    IsExtension d m (fun x => -lap g x) (s + 2) r₀ G

/-- (viii) with `r₀ = ∞` in (1.15)–(1.16). -/
def HasExtensionGlobal (d : ℕ) (s : ℝ) (g : RieszMF.Linear.E d → ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ G : RieszMF.Linear.E (d + m) → ℝ, IsGlobalExtension d m (fun x => -lap g x) (s + 2) G

/-- A scalar convolution kernel `K` is associated to a Calderón–Zygmund operator: there is a
bounded linear operator `T` on `L²(ℝ^d)` such that for every bounded measurable compactly
supported `f`, `(Tf)(x) = ∫ K(x - y) f(y) dy` for a.e. `x` outside the support of `f`. -/
def IsCZKernel (d : ℕ) (K : RieszMF.Linear.E d → ℝ) : Prop :=
  ∃ T : Lp ℝ 2 (volume : Measure (RieszMF.Linear.E d)) →L[ℝ] Lp ℝ 2 (volume : Measure (RieszMF.Linear.E d)),
    ∀ (f : RieszMF.Linear.E d → ℝ) (hf : MemLp f 2 volume), Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      HasCompactSupport f →
        ∀ᵐ x ∂volume, x ∉ tsupport f → T (hf.toLp f) x = ∫ y, K (x - y) * f y

/-- (ix) If `s = d - 2k` for a positive integer `k`, every component
`x_j · ∂_{i_1} ⋯ ∂_{i_{2k+1}} g(x)` of the `(ℝ^d)^{⊗(2k+2)}`-valued kernel `x ⊗ ∇^{⊗(2k+1)} g(x)`
is associated to a Calderón–Zygmund operator. -/
def AssumpIX (d : ℕ) (s : ℝ) (g : RieszMF.Linear.E d → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → s = (d : ℝ) - 2 * k →
    ∀ (j : Fin d) (α : Fin (2 * k + 1) → Fin d),
      IsCZKernel d (fun x => inner ℝ x (basisVec d j) *
        iteratedFDeriv ℝ (2 * k + 1) g x (fun l => basisVec d (α l)))

/-- An admissible potential (assumptions (i)–(x), pp. 5–6), with the radius `r₀` of (iii),
(v), (vii), (viii). -/
structure Admissible (d : ℕ) (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (g : RieszMF.Linear.E d → ℝ) (r₀ : ℝ) :
    Prop where
  i_symm : RieszMF.Linear.AssumpI g
  ii_blowup : RieszMF.Linear.AssumpII g
  iii_superharmonic : AssumpIII g r₀
  iv_derivatives : RieszMF.Linear.AssumpIV d s g
  v_doubling_derivs : RieszMF.Linear.AssumpV g r₀
  vi_fourier : RieszMF.Linear.AssumpVI d s g
  vii_doubling : RieszMF.Linear.AssumpVII s g r₀
  viii_extension : AssumpVIII d s g r₀
  ix_calderon_zygmund : AssumpIX d s g
  x_frobenius : RieszMF.Linear.AssumpX M g

/-! ### Exponents and thresholds of §5.2 -/

/-- `γ_{s,p} = (2p + sp - s)/(dp + 2p - d)` of (5.21); for `p = ∞` its limit `(2 + s)/(d + 2)`. -/
def gam (d : ℕ) (s : ℝ) (p : ℝ≥0∞) : ℝ :=
  if p = ⊤ then (2 + s) / ((d : ℝ) + 2)
  else (2 * p.toReal + s * p.toReal - s) / ((d : ℝ) * p.toReal + 2 * p.toReal - d)

/-- `λ_{s,p} = 2p(d - s)/(dp + 2p - d)` of (5.21); for `p = ∞` its limit `2(d - s)/(d + 2)`. -/
def lam (d : ℕ) (s : ℝ) (p : ℝ≥0∞) : ℝ :=
  if p = ⊤ then 2 * ((d : ℝ) - s) / ((d : ℝ) + 2)
  else 2 * p.toReal * ((d : ℝ) - s) / ((d : ℝ) * p.toReal + 2 * p.toReal - d)

/-- The upper end `2^{-(dp-d+2p)/(d(p-1))} L^{-1/d}` of the range of `η_i` in Proposition 5.8;
for `p = ∞` the exponent is its limit `(d + 2)/d`. -/
def etaMax (d : ℕ) (p : ℝ≥0∞) (L : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(if p = ⊤ then ((d : ℝ) + 2) / d
      else ((d : ℝ) * p.toReal - d + 2 * p.toReal) / ((d : ℝ) * (p.toReal - 1)))) *
    L ^ (-(1 / (d : ℝ)))

/-- The exponent `(dp - d + p)/(p - 1)` of the threshold of Proposition 5.15; for `p = ∞` its
limit `d + 1`. -/
def thrExp (d : ℕ) (p : ℝ≥0∞) : ℝ :=
  if p = ⊤ then (d : ℝ) + 1 else ((d : ℝ) * p.toReal - d + p.toReal) / (p.toReal - 1)

/-! ### The constants of Proposition 3.8 -/

/-- The middle factor `(4πσt / (1/p - 1/q))^{-(d/2)(1/p - 1/q)}` of (3.22); for `p = q` it is
`1` (its limit as `1/p - 1/q → 0`). -/
def decayFactor (d : ℕ) (σ t : ℝ) (p q : ℝ≥0∞) : ℝ :=
  if p = q then 1
  else (4 * Real.pi * σ * t / (p⁻¹.toReal - q⁻¹.toReal)) ^
    (-((d : ℝ) / 2) * (p⁻¹.toReal - q⁻¹.toReal))

/-! ### Densities, Riesz potentials, smearing -/

/-- `μ ∈ 𝒫(ℝ^d) ∩ L^∞(ℝ^d)`: an essentially bounded probability density. -/
def IsProbDensity {d : ℕ} (μ : RieszMF.Linear.E d → ℝ) : Prop :=
  MemLp μ ⊤ volume ∧ Integrable μ volume ∧ (∀ᵐ x ∂volume, 0 ≤ μ x) ∧ ∫ x, μ x = 1

/-- `‖f‖_{L^∞}` as a real number. -/
def supNorm {d : ℕ} (f : RieszMF.Linear.E d → ℝ) : ℝ := (eLpNorm f ⊤ volume).toReal

/-- The uniform probability measure on the unit sphere of `ℝ^n`. -/
def sphereMeasure (n : ℕ) : Measure (Metric.sphere (0 : RieszMF.Linear.E n) 1) :=
  ((volume : Measure (RieszMF.Linear.E n)).toSphere Set.univ)⁻¹ • (volume : Measure (RieszMF.Linear.E n)).toSphere

/-- The smeared potential `f_η = f ∗ δ^{(η)}_0` ((5.2), (5.12)), `δ^{(η)}_0` the uniform
probability measure on the sphere `∂B(0, η)`. -/
def smear (n : ℕ) (f : RieszMF.Linear.E n → ℝ) (η : ℝ) (X : RieszMF.Linear.E n) : ℝ :=
  ∫ ϖ, f (X - η • (ϖ : RieszMF.Linear.E n)) ∂(sphereMeasure n)

/-- `w = |∇|^a v` for vector fields `v, w : ℝ^d → ℝ^d`, in the sense of distributions modulo
polynomials: for every complex Schwartz `ψ` vanishing near the origin and every component `j`,
`∫ w_j 𝓕⁻ψ = ∫ v_j 𝓕⁻((2π|ξ|)^a ψ)` (Mathlib's Fourier normalization, in which `|∇|` has symbol
`2π|ξ|`). -/
def IsFracGrad (d : ℕ) (a : ℝ) (v w : RieszMF.Linear.E d → RieszMF.Linear.E d) : Prop :=
  ∀ ψ : 𝓢(RieszMF.Linear.E d, ℂ), (∀ᶠ ξ in 𝓝 (0 : RieszMF.Linear.E d), ψ ξ = 0) → ∀ j : Fin d,
    ∫ x, ((inner ℝ (w x) (basisVec d j) : ℝ) : ℂ) * 𝓕⁻ (⇑ψ) x =
      ∫ x, ((inner ℝ (v x) (basisVec d j) : ℝ) : ℂ) *
        𝓕⁻ (fun ξ : RieszMF.Linear.E d => ((2 * Real.pi * ‖ξ‖) ^ a : ℝ) * ψ ξ) x

/-! ### Modulated energy -/

/-- `(1/N²) ∑_{i ≠ j} (h(x_j - x_i) - h_{η_i}(x_j - x_i))_+`, the left side of (5.33). -/
def smearGap {d : ℕ} (N : ℕ) (h : RieszMF.Linear.E d → ℝ) (x : Fin N → RieszMF.Linear.E d) (η : Fin N → ℝ) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
    max (h (x j - x i) - smear d h (η i) (x j - x i)) 0

/-- `(1/N²) ∑_{i ≠ j} (h(x_j - x_i) - G_{η_i}(x_j - x_i, 0))_+`, the left side of (5.34). -/
def smearGapExt {d m : ℕ} (N : ℕ) (h : RieszMF.Linear.E d → ℝ) (G : RieszMF.Linear.E (d + m) → ℝ) (x : Fin N → RieszMF.Linear.E d)
    (η : Fin N → ℝ) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
    max (h (x j - x i) - smear (d + m) G (η i) (embed d m (x j - x i))) 0

/-! ### The PDE (1.5) in mild form (3.1) -/

/-- `∂_jΦ_τ(x) = -(x_j/(2τ)) Φ_τ(x)`. -/
def heatKernelDeriv (d : ℕ) (τ : ℝ) (j : Fin d) (x : RieszMF.Linear.E d) : ℝ :=
  -(inner ℝ x (basisVec d j) / (2 * τ)) * RieszMF.Linear.heatKernel d τ x

/-- The velocity field `u = 𝕄∇g ∗ μ`. -/
def velocity {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (g : RieszMF.Linear.E d → ℝ) (μ : RieszMF.Linear.E d → ℝ) (x : RieszMF.Linear.E d) :
    RieszMF.Linear.E d :=
  ∫ y, μ y • mGrad M g (x - y)

/-- `μ : [0, ∞) → L¹ ∩ L^∞` is a mild solution (3.1) of (1.5) with initial datum `μ0`:
`μ ∈ C([0, ∞); L¹ ∩ L^∞)`, `μ^0 = μ0`, and for every `t > 0`, for a.e. `x`,
`μ^t(x) = (Φ_{σt} ∗ μ^0)(x) - ∫_0^t ∑_j ((∂_jΦ_{σ(t-κ)}) ∗ (μ^κ u^κ_j))(x) dκ`,
with every integral in this identity (including the velocity `u^κ(y)` for a.e. `y`) absolutely
convergent. -/
def IsMildSolution (d : ℕ) (σ : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (g : RieszMF.Linear.E d → ℝ)
    (μ0 : RieszMF.Linear.E d → ℝ) (μ : ℝ≥0 → RieszMF.Linear.E d → ℝ) : Prop :=
  (∀ t, MemLp (μ t) 1 volume ∧ MemLp (μ t) ⊤ volume) ∧
  (∀ t, Tendsto (fun t' => eLpNorm (μ t' - μ t) 1 volume + eLpNorm (μ t' - μ t) ⊤ volume)
      (𝓝 t) (𝓝 0)) ∧
  (μ 0 =ᵐ[volume] μ0) ∧
  (∀ κ : ℝ≥0, ∀ᵐ y ∂volume, Integrable (fun z => μ κ z • mGrad M g (y - z)) volume) ∧
  ∀ t : ℝ≥0, 0 < t → ∀ᵐ x ∂volume,
    Integrable (fun y => RieszMF.Linear.heatKernel d (σ * t) (x - y) * μ0 y) volume ∧
    (∀ κ : ℝ, κ ∈ Ioo (0 : ℝ) t → ∀ j : Fin d,
      Integrable (fun y => heatKernelDeriv d (σ * (t - κ)) j (x - y) *
        (μ κ.toNNReal y * inner ℝ (velocity M g (μ κ.toNNReal) y) (basisVec d j))) volume) ∧
    IntervalIntegrable (fun κ : ℝ => ∑ j : Fin d, ∫ y, heatKernelDeriv d (σ * (t - κ)) j (x - y) *
        (μ κ.toNNReal y * inner ℝ (velocity M g (μ κ.toNNReal) y) (basisVec d j))) volume 0 t ∧
    μ t x = (∫ y, RieszMF.Linear.heatKernel d (σ * t) (x - y) * μ0 y) -
      ∫ κ in (0 : ℝ)..t, ∑ j : Fin d, ∫ y, heatKernelDeriv d (σ * (t - κ)) j (x - y) *
        (μ κ.toNNReal y * inner ℝ (velocity M g (μ κ.toNNReal) y) (basisVec d j))

/-! ### Brownian motions and the particle system (1.1) -/

/-- `W_1, …, W_N` are independent standard Brownian motions in `ℝ^d`: every coordinate is a
standard real Brownian motion and the `N·d` coordinate processes are jointly independent. -/
def IsBrownianFamily {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N d : ℕ}
    (W : Fin N → ℝ≥0 → Ω → RieszMF.Linear.E d) : Prop :=
  (∀ i k, IsBrownianReal (fun t ϖ => inner ℝ (W i t ϖ) (basisVec d k)) P) ∧
  iIndepFun (fun (ik : Fin N × Fin d) (ϖ : Ω) (t : ℝ≥0) => inner ℝ (W ik.1 t ϖ) (basisVec d ik.2)) P

/-- The drift `(1/N) ∑_{j ≠ i} 𝕄∇g(x_i - x_j)` of particle `i`. -/
def drift {d N : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (g : RieszMF.Linear.E d → ℝ) (y : Fin N → RieszMF.Linear.E d)
    (i : Fin N) : RieszMF.Linear.E d :=
  (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, mGrad M g (y i - y j)

/-- `x` is a solution of (1.1) driven by `W` from `x0`: each `x^t_i` is measurable and, almost
surely, the paths are continuous, the particles never collide, the drift is integrable in time
and `x^t_i = x^0_i + ∫_0^t (1/N) ∑_{j ≠ i} 𝕄∇g(x^τ_i - x^τ_j) dτ + √(2σ) W^t_i` for all `t ≥ 0`. -/
def IsParticleSolution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N d : ℕ} (σ : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (g : RieszMF.Linear.E d → ℝ) (x0 : Fin N → RieszMF.Linear.E d)
    (W : Fin N → ℝ≥0 → Ω → RieszMF.Linear.E d) (x : Fin N → ℝ≥0 → Ω → RieszMF.Linear.E d) : Prop :=
  (∀ i t, Measurable (x i t)) ∧
  ∀ᵐ ϖ ∂P,
    (∀ i, Continuous (fun t => x i t ϖ)) ∧
    (∀ t, Pairwise (fun i j => x i t ϖ ≠ x j t ϖ)) ∧
    ∀ i (t : ℝ≥0),
      IntervalIntegrable (fun τ : ℝ => drift M g (fun j => x j τ.toNNReal ϖ) i) volume 0 t ∧
      x i t ϖ = x0 i + (∫ τ in (0 : ℝ)..t, drift M g (fun j => x j τ.toNNReal ϖ) i) +
        Real.sqrt (2 * σ) • W i t ϖ

end

end RieszMF.Global


