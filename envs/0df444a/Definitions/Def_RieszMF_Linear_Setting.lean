-- Prove2me | Definitions.Def_RieszMF_Linear_Setting
-- name    : RieszMF_Linear_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:11.24424+00:00
-- url     : https://prove2.me/theorems/184f64b0-004b-41cf-8660-b930383fc344
-- title:
--   §1.1–1.3, §2, §3.1, §4, §5 — admissible potentials (i)–(x), the particle system (1.1), the mild PDE (3.1), the modulated energy (1.6)
-- statement:
--   This module fixes the objects of Rosenzweig–Serfaty's mean-field problem on $\mathbb R^d$ (Euclidean space, Lebesgue measure).
--
--   **Potentials.** Fix $d\in\mathbb N$, $s\in\mathbb R$, a $d\times d$ real matrix $\mathbb M$, a potential $\mathsf g:\mathbb R^d\to\mathbb R$ (its value at $0$ is irrelevant) and a radius $r_0$. Condition (1.2) on $\mathbb M$ is $\mathbb M\xi\cdot\xi\le 0$ for all $\xi$. The potential is **admissible** when it satisfies:
--
--   1. (i) $\mathsf g(x)=\mathsf g(-x)$;
--   2. (ii) $\mathsf g(x)\to+\infty$ as $x\to 0$;
--   3. (iii) $r_0>0$ and $\Delta\mathsf g(x)\le 0$ for $0<|x|<r_0$;
--   4. (iv) $\mathsf g\in C^\infty(\mathbb R^d\setminus\{0\})$ and for every $k\ge0$ there is $C_k$ with $|\nabla^{\otimes k}\mathsf g(x)|\le C_k\big(|x|^{-(s+k)}+|\log|x||\mathbf 1_{s=k=0}\big)$ for $x\ne0$;
--   5. (v) $|x||\nabla\mathsf g(x)|+|x|^2|\nabla^{\otimes2}\mathsf g(x)|\le C\,\mathsf g(x)$ for $0<|x|<r_0$;
--   6. (vi) there are $C_1,C_2>0$ and a function $\hat{\mathsf g}$ with $C_1|\xi|^{-(d-s)}\le\hat{\mathsf g}(\xi)\le C_2|\xi|^{-(d-s)}$ for $\xi\ne0$, which is the Fourier transform of $\mathsf g$ away from the origin: $\int\mathsf g\,\widehat\varphi=\int\hat{\mathsf g}\,\varphi$ for every Schwartz $\varphi$ vanishing near $0$;
--   7. (vii) if $s>0$, some $c_s<1$ has $\mathsf g(y)<c_s\,\mathsf g(x)$, and if $s=0$, some $c_0>0$ has $\mathsf g(x)-\mathsf g(y)\ge c_0$, whenever $x\neq0$, $|x|,|y|<r_0$ and $|y|\ge2|x|$;
--   8. (viii) if $d-4<s$: there are $m\ge1$ and $\mathsf G:\mathbb R^{d+m}\to\mathbb R$ with $-\Delta\mathsf g(x)=\mathsf G(x,0)$ for $x\ne0$, $\mathsf G$ even, smooth and superharmonic on $B(0,r_0)\setminus\{0\}$, $|\nabla^{\otimes k}\mathsf G(X)|\le C_k|X|^{-(s+2+k)}$ there, and $\hat{\mathsf G}\ge0$ away from $0$ (conditions (1.14)–(1.17));
--   9. (ix) whenever $s=d-2k$ for a positive integer $k$, the tensor kernel $x\otimes\nabla^{\otimes(2k+1)}\mathsf g(x)$ is associated to a Calderón–Zygmund operator: some bounded operator $T$ on $L^2$ satisfies $Tf(x)=\int\mathsf k(x-y)f(y)\,dy$ for a.e. $x$ outside the support of every bounded, measurable, compactly supported $f$;
--   10. (x) $\mathbb M:\nabla^{\otimes2}\mathsf g(x)=\sum_{i,j}\mathbb M_{ij}\partial_i\partial_j\mathsf g(x)\ge0$ for $x\ne0$.
--
--   **Densities and energies.** $\mathcal P(\mathbb R^d)\cap L^\infty$ is the set of integrable, essentially bounded, a.e. nonnegative $\mu$ with $\int\mu=1$; the log moment is $\int\log(1+|x|)\mu(x)\,dx<\infty$. For a configuration $x_N=(x_1,\dots,x_N)$ and a kernel $K(x,y)$,
--   $$\iint_{(\mathbb R^d)^2\setminus\triangle}K\,d(\mu_N-\mu)^{\otimes2}=\frac1{N^2}\sum_{i\ne j}K(x_i,x_j)-\frac1N\sum_i\int\big(K(x_i,y)+K(y,x_i)\big)\mu(y)\,dy+\iint K(x,y)\mu(x)\mu(y)\,dx\,dy,$$
--   with $\mu_N=\frac1N\sum_i\delta_{x_i}$, and the **modulated energy** (1.6) is $F_N(x_N,\mu)$, the case $K(x,y)=\mathsf g(x-y)$. The Riesz potential is $\mathcal I_s f(x)=\frac{\Gamma(\frac{d-s}2)}{2^s\pi^{d/2}\Gamma(\frac s2)}\int f(y)|x-y|^{s-d}\,dy$, and $\mathsf g_\eta(x)=\int\mathsf g(x-\eta\omega)\,d\sigma(\omega)$ averages $\mathsf g$ over the sphere of radius $\eta$ ($\sigma$ the uniform probability on the unit sphere).
--
--   **The PDE (1.5)** $\partial_t\mu=-\operatorname{div}(\mu\,\mathbb M\nabla\mathsf g*\mu)+\sigma\Delta\mu$ is taken in the mild form (3.1)
--   $$\mu^t=e^{t\sigma\Delta}\mu^0-\int_0^te^{(t-\kappa)\sigma\Delta}\operatorname{div}(\mu^\kappa\,\mathbb M\nabla\mathsf g*\mu^\kappa)\,d\kappa,$$
--   with $e^{\tau\Delta}$ convolution by $\Phi_\tau(x)=(4\pi\tau)^{-d/2}e^{-|x|^2/4\tau}$; a solution lies in $C([0,\infty);L^1\cap L^\infty)$ (continuity in the norm $\|\cdot\|_{L^1}+\|\cdot\|_{L^\infty}$), starts at $\mu^0$, and every integral in (3.1) converges. The path stays in $\mathcal P(\mathbb R^d)$ when each $\mu^t$ is a nonnegative density of mass one.
--
--   **The particle system (1.1).** $W_1,\dots,W_N$ are independent standard $d$-dimensional Brownian motions (all $Nd$ coordinates jointly independent real Brownian motions). A solution of (1.1) from $x^0_N$ is a measurable process whose paths are almost surely continuous, collision-free, and satisfy
--   $$x^t_i=x^0_i+\int_0^t\frac1N\sum_{j\ne i}\mathbb M\nabla\mathsf g(x^\tau_i-x^\tau_j)\,d\tau+\sqrt{2\sigma}\,W^t_i\qquad\text{for all }t\ge0.$$
--   For §4, a **bump function** is $\chi\in C^\infty_c(\mathbb R^d)$ with $\chi\ge0$, $\chi(x)=1$ for $|x|\le1/2$ and $\chi(x)=0$ for $|x|\ge1$ (4.1), and the **truncated potential** is $\mathsf g_{(\varepsilon)}(x)=\mathsf g(x)(1-\chi(x/\varepsilon))$ (4.2). A solution is **strong** when each $x^t_i$ agrees almost surely with a random variable measurable for $\mathcal F^W_t=\sigma(W^\tau_j:1\le j\le N,\ 0\le\tau\le t)$ (adaptedness to the completed Brownian filtration).
--
--   **Fractional derivatives.** For a vector field $v$ and $\alpha\in\mathbb R$, $w=|\nabla|^\alpha v$ with $|\nabla|^\alpha=(-\Delta)^{\alpha/2}$ ((2.1)) is understood weakly: for every coordinate $j$ and every complex Schwartz $\varphi$ whose Fourier transform vanishes near $0$, $\int w_j\varphi=\int v_j\,(-\Delta)^{\alpha/2}\varphi$, both integrals converging absolutely. This fixes $w$ only up to a polynomial; the statements that use it pin $w$ down by an $L^p$ condition with $p<\infty$. The integrability of the three terms of the off-diagonal energy above is a separate predicate, and $\|f\|_{L^p}$ is written as a real number.
--
--   Finally $K(r)=r'^{1/r'}/r^{1/r}$ of (3.23), $1\le r\le\infty$, with the limiting values $K(1)=K(\infty)=1$.
--
--   **Formalization Note.** Derivatives are Fréchet derivatives (`iteratedFDeriv`, operator norms; any tensor norm changes constants only), $\Delta$ is Mathlib's Laplacian, and the Fourier transform is Mathlib's $\widehat\varphi(\xi)=\int e^{-2\pi i x\cdot\xi}\varphi(x)\,dx$ (the constants $C_1,C_2$ absorb the normalization). Condition (vii) for $s>0$ is printed as $\mathsf g(x)<c_s\mathsf g(y)$; together with (ii) that is impossible (fix $y$, let $x\to0$), so the roles of $x$ and $y$ are exchanged, which is the inequality the model potential $|x|^{-s}$ satisfies. One radius $r_0$ serves (iii), (v), (vii) and (viii) (the printed (1.15) introduces its own radius; shrinking to the minimum gives an equivalent class). Because the noise is additive, the pathwise integral equation is the strong formulation of (1.1); absence of collisions is proved in the paper (Proposition 4.5) and so does not narrow the solution class. Superharmonicity (iii) is read pointwise on the punctured ball; for $s<d-2$ this is equivalent to the paper's distributional reading (footnote 2) under (iv). Several objects take Lean's default value on bad input, and every statement that uses them supplies the guard: an integral of a non-integrable function is $0$ (hence the integrability conjuncts in the mild-solution predicate, the Fourier pairings and the energy predicate), $\|f\|_{L^p}$ is $0$ when $f\notin L^p$, $\Phi_\tau$ is $0$ at $\tau=0$, $\sqrt{2\sigma}=0$ for $\sigma<0$, $\mathsf g_{(\varepsilon)}=0$ at $\varepsilon=0$, and the off-diagonal energy with $N=0$ particles is the self-energy of $\mu$; the theorems assume $\sigma>0$, $N\ge1$, $\varepsilon>0$ and the relevant integrability.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, pp. 1–6, 9–11, 14, 17, 20–23, 30, (1.1), (1.2), (1.5), (1.6), (6.4)–(6.6), assumptions (i)–(x), (2.1), (2.3), (3.1), (3.23), (4.1), (4.2), (5.2), (5.12)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal FourierTransform Laplacian

namespace RieszMF.Linear

/-! ## Space, matrix, derivatives -/

/-- Euclidean space `ℝ^d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The standard basis vector `e_i` of `ℝ^d`. -/
noncomputable def ebasis (d : ℕ) (i : Fin d) : E d := EuclideanSpace.single i 1

/-- The embedding `x ↦ (x, 0)` of `ℝ^d` into `ℝ^{d+m}`. -/
noncomputable def embed (d m : ℕ) (x : E d) : E (d + m) :=
  WithLp.toLp 2 (fun i : Fin (d + m) => if h : (i : ℕ) < d then x ⟨i, h⟩ else 0)

/-- Condition (1.2): `𝕄ξ · ξ ≤ 0` for every `ξ ∈ ℝ^d`. -/
def NegSemidef {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ ξ : E d, inner ℝ (Matrix.toEuclideanLin M ξ) ξ ≤ 0

/-- The Frobenius product `𝕄 : ∇^{⊗2}g(x) = Σ_{i,j} 𝕄_{ij} ∂_i∂_j g(x)`. -/
noncomputable def frob {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (g : E d → ℝ) (x : E d) : ℝ :=
  ∑ i, ∑ j, M i j * iteratedFDeriv ℝ 2 g x ![ebasis d i, ebasis d j]

/-- `ĝ` is the Fourier transform of `g` away from the origin: for every complex Schwartz
function `φ` vanishing on a neighbourhood of `0`, `∫ g · 𝓕φ = ∫ ĝ · φ`, both integrals
converging absolutely (Mathlib's normalization `𝓕φ(ξ) = ∫ e^{-2πi⟨x,ξ⟩} φ(x) dx`). -/
def FTOffZero {n : ℕ} (g ĝ : E n → ℝ) : Prop :=
  ∀ φ : SchwartzMap (E n) ℂ, (∀ᶠ x in 𝓝 (0 : E n), φ x = 0) →
    Integrable (fun x => (g x : ℂ) * 𝓕 (⇑φ) x) ∧
    Integrable (fun ξ => (ĝ ξ : ℂ) * φ ξ) ∧
    ∫ x, (g x : ℂ) * 𝓕 (⇑φ) x = ∫ ξ, (ĝ ξ : ℂ) * φ ξ

/-! ## The assumptions (i)–(x) on the potential (pp. 5–6) -/

/-- (i) `g(x) = g(-x)`. -/
def AssumpI {d : ℕ} (g : E d → ℝ) : Prop := ∀ x, g (-x) = g x

/-- (ii) `lim_{x → 0} g(x) = ∞`. -/
def AssumpII {d : ℕ} (g : E d → ℝ) : Prop := Tendsto g (𝓝[≠] 0) atTop

/-- (iii) `Δg ≤ 0` in `B(0, r₀) ∖ {0}`, `r₀ > 0`. -/
def AssumpIII {d : ℕ} (g : E d → ℝ) (r₀ : ℝ) : Prop :=
  0 < r₀ ∧ ∀ x : E d, x ≠ 0 → ‖x‖ < r₀ → Δ g x ≤ 0

/-- (iv) `g ∈ C^∞(ℝ^d ∖ {0})` and for every `k ≥ 0` there is `C_k` with
`|∇^{⊗k} g(x)| ≤ C_k (|x|^{-(s+k)} + |log |x|| 1_{s=k=0})` for `x ≠ 0`. -/
def AssumpIV (d : ℕ) (s : ℝ) (g : E d → ℝ) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g {0}ᶜ ∧
  ∀ k : ℕ, ∃ C : ℝ, ∀ x : E d, x ≠ 0 →
    ‖iteratedFDeriv ℝ k g x‖ ≤
      C * (‖x‖ ^ (-(s + k)) + |Real.log ‖x‖| * (if s = 0 ∧ k = 0 then 1 else 0))

/-- (v) `|x||∇g(x)| + |x|²|∇^{⊗2}g(x)| ≤ C g(x)` in `B(0, r₀) ∖ {0}`. -/
def AssumpV {d : ℕ} (g : E d → ℝ) (r₀ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x : E d, x ≠ 0 → ‖x‖ < r₀ →
    ‖x‖ * ‖gradient g x‖ + ‖x‖ ^ 2 * ‖iteratedFDeriv ℝ 2 g x‖ ≤ C * g x

/-- (vi) `C₁ |ξ|^{-(d-s)} ≤ ĝ(ξ) ≤ C₂ |ξ|^{-(d-s)}` for `ξ ≠ 0`, `ĝ` the Fourier transform
of `g` away from `0`. -/
def AssumpVI (d : ℕ) (s : ℝ) (g : E d → ℝ) : Prop :=
  ∃ C₁ C₂ : ℝ, ∃ ĝ : E d → ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    (∀ ξ : E d, ξ ≠ 0 →
      C₁ / ‖ξ‖ ^ ((d : ℝ) - s) ≤ ĝ ξ ∧ ĝ ξ ≤ C₂ / ‖ξ‖ ^ ((d : ℝ) - s)) ∧
    FTOffZero g ĝ

/-- (vii), read with the roles of `x` and `y` as forced by (ii) for `s > 0`:
for `s > 0` there is `c_s < 1` with `g(y) < c_s g(x)`, and for `s = 0` there is `c₀ > 0` with
`g(x) - g(y) ≥ c₀`, for all `x ≠ 0`, `x, y ∈ B(0, r₀)`, `|y| ≥ 2|x|`. -/
def AssumpVII {d : ℕ} (s : ℝ) (g : E d → ℝ) (r₀ : ℝ) : Prop :=
  (0 < s → ∃ c : ℝ, c < 1 ∧ ∀ x y : E d, x ≠ 0 → ‖x‖ < r₀ → ‖y‖ < r₀ →
      2 * ‖x‖ ≤ ‖y‖ → g y < c * g x) ∧
  (s = 0 → ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x y : E d, x ≠ 0 → ‖x‖ < r₀ → ‖y‖ < r₀ →
      2 * ‖x‖ ≤ ‖y‖ → c₀ ≤ g x - g y)

/-- Conditions (1.14)–(1.17) on a function `G : ℝ^n → ℝ` of order `σ'`, with radius `r₀`:
`G` even, superharmonic and smooth in `B(0, r₀) ∖ {0}`, `|∇^{⊗k}G(X)| ≤ C_k |X|^{-(σ'+k)}`
there, and `Ĝ ≥ 0` away from `0`. In (viii), `σ' = s + 2`. -/
def ExtensionConds (n : ℕ) (σ' : ℝ) (G : E n → ℝ) (r₀ : ℝ) : Prop :=
  0 < r₀ ∧
  (∀ X : E n, G (-X) = G X) ∧
  (∀ X : E n, X ≠ 0 → ‖X‖ < r₀ → Δ G X ≤ 0) ∧
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (ball 0 r₀ \ {0}) ∧
  (∀ k : ℕ, ∃ C : ℝ, ∀ X : E n, X ≠ 0 → ‖X‖ < r₀ →
      ‖iteratedFDeriv ℝ k G X‖ ≤ C / ‖X‖ ^ (σ' + k)) ∧
  ∃ Ĝ : E n → ℝ, (∀ Ξ : E n, Ξ ≠ 0 → 0 ≤ Ĝ Ξ) ∧ FTOffZero G Ĝ

/-- (viii) If `d - 4 < s`, there are `m ∈ ℕ`, `m ≥ 1`, and `G : ℝ^{d+m} → ℝ` with
`-Δg(x) = G(x, 0)` for `x ≠ 0` and (1.14)–(1.17) at order `s + 2`. -/
def AssumpVIII (d : ℕ) (s : ℝ) (g : E d → ℝ) (r₀ : ℝ) : Prop :=
  (d : ℝ) - 4 < s → ∃ m : ℕ, 0 < m ∧ ∃ G : E (d + m) → ℝ,
    (∀ x : E d, x ≠ 0 → -Δ g x = G (embed d m x)) ∧ ExtensionConds (d + m) (s + 2) G r₀

/-- The tensor kernel `𝗄(x) = x ⊗ ∇^{⊗(2k+1)} g(x)`, as the multilinear form
`(v₀, …, v_{2k+1}) ↦ ⟨x, v₀⟩ · ∇^{2k+1}g(x)(v₁, …, v_{2k+1})`. -/
noncomputable def czKernel {d : ℕ} (g : E d → ℝ) (k : ℕ) (x : E d) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (2 * k + 1 + 1) => E d) ℝ :=
  ((innerSL ℝ x).smulRight (iteratedFDeriv ℝ (2 * k + 1) g x)).uncurryLeft

/-- A kernel `K` is associated to a Calderón–Zygmund operator: there is a bounded linear
operator `T : L²(ℝ^d) → L²(ℝ^d; V)` such that for every bounded measurable compactly
supported `f`, `(Tf)(x) = ∫ K(x - y) f(y) dy` for a.e. `x` outside the support of `f`. -/
def IsCZKernel {d : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (K : E d → V) : Prop :=
  ∃ T : Lp ℝ 2 (volume : Measure (E d)) →L[ℝ] Lp V 2 (volume : Measure (E d)),
    ∀ (f : E d → ℝ) (hf : MemLp f 2 volume), Measurable f → HasCompactSupport f →
      (∃ B : ℝ, ∀ x, |f x| ≤ B) →
      ∀ᵐ x ∂volume, x ∉ tsupport f → (T (hf.toLp f)) x = ∫ y, f y • K (x - y)

/-- (ix) For every positive integer `k` with `s = d - 2k`, the kernel
`x ⊗ ∇^{⊗(2k+1)}g(x)` is associated to a Calderón–Zygmund operator. -/
def AssumpIX (d : ℕ) (s : ℝ) (g : E d → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → s = (d : ℝ) - 2 * k → IsCZKernel (czKernel g k)

/-- (x) `𝕄 : ∇^{⊗2} g(x) ≥ 0` for `x ≠ 0`. -/
def AssumpX {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (g : E d → ℝ) : Prop :=
  ∀ x : E d, x ≠ 0 → 0 ≤ frob M g x

/-- An admissible potential (pp. 5–6): assumptions (i)–(x), with `r₀` the radius of (iii),
also used in (v), (vii), (viii). -/
structure Admissible (d : ℕ) (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (g : E d → ℝ) (r₀ : ℝ) :
    Prop where
  i_symm : AssumpI g
  ii_blowup : AssumpII g
  iii_superharm : AssumpIII g r₀
  iv_deriv : AssumpIV d s g
  v_ratio : AssumpV g r₀
  vi_fourier : AssumpVI d s g
  vii_doubling : AssumpVII s g r₀
  viii_extension : AssumpVIII d s g r₀
  ix_cz : AssumpIX d s g
  x_frobenius : AssumpX M g

/-! ## Riesz potential, densities, smearing -/

/-- The constant of the kernel of `𝓘_s = (-Δ)^{-s/2}` ((2.3) with `s ↦ -s`). -/
noncomputable def rieszConst (d : ℕ) (s : ℝ) : ℝ :=
  Real.Gamma (((d : ℝ) - s) / 2) / (2 ^ s * Real.pi ^ ((d : ℝ) / 2) * Real.Gamma (s / 2))

/-- The Riesz potential `𝓘_s f(x) = c_{d,s} ∫ f(y) |x - y|^{-(d-s)} dy`. -/
noncomputable def rieszPot (d : ℕ) (s : ℝ) (f : E d → ℝ) (x : E d) : ℝ :=
  rieszConst d s * ∫ y, f y / ‖x - y‖ ^ ((d : ℝ) - s)

/-- `‖f‖_{L^p}` as a real number. -/
noncomputable def lpNorm {d : ℕ} (f : E d → ℝ) (p : ℝ≥0∞) : ℝ :=
  (eLpNorm f p volume).toReal

/-- `μ ∈ 𝒫(ℝ^d) ∩ L^∞(ℝ^d)`: a bounded probability density. -/
def IsProbDensityLinfty {d : ℕ} (μ : E d → ℝ) : Prop :=
  Integrable μ volume ∧ MemLp μ ⊤ volume ∧ (∀ᵐ x ∂volume, 0 ≤ μ x) ∧ ∫ x, μ x = 1

/-- The logarithmic moment condition `∫ log(1 + |x|) dμ(x) < ∞`. -/
def LogMoment {d : ℕ} (μ : E d → ℝ) : Prop :=
  Integrable (fun x => Real.log (1 + ‖x‖) * μ x) volume

/-- The uniform probability measure on the unit sphere of `ℝ^n`. -/
noncomputable def unitSphereProb (n : ℕ) : Measure (sphere (0 : E n) 1) :=
  ((volume : Measure (E n)).toSphere univ)⁻¹ • (volume : Measure (E n)).toSphere

/-- The smeared potential `g_η = g ∗ δ_0^{(η)}`, `δ_0^{(η)}` the uniform probability measure on
the sphere `∂B(0, η)` ((5.2), (5.12)). -/
noncomputable def smear {n : ℕ} (g : E n → ℝ) (η : ℝ) (x : E n) : ℝ :=
  ∫ ω, g (x - η • (ω : E n)) ∂(unitSphereProb n)

/-- `w = |∇|^α v` (componentwise, `|∇|^α = (-Δ)^{α/2}`, Fourier multiplier `(2π|ξ|)^α`):
for every coordinate `j` and every complex Schwartz `φ` whose Fourier transform vanishes near
`0`, `∫ w_j φ = ∫ v_j · 𝓕⁻¹((2π|ξ|)^α 𝓕φ)`, both integrals converging absolutely. -/
def IsFracGrad {d : ℕ} (α : ℝ) (v w : E d → E d) : Prop :=
  ∀ j : Fin d, ∀ φ : SchwartzMap (E d) ℂ, (∀ᶠ ξ in 𝓝 (0 : E d), 𝓕 (⇑φ) ξ = 0) →
    Integrable (fun x => ((w x j : ℝ) : ℂ) * φ x) volume ∧
    Integrable (fun x => ((v x j : ℝ) : ℂ) *
      𝓕⁻ (fun ξ : E d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x) volume ∧
    ∫ x, ((w x j : ℝ) : ℂ) * φ x =
      ∫ x, ((v x j : ℝ) : ℂ) *
        𝓕⁻ (fun ξ : E d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x

/-! ## The modulated energy (1.6) -/

/-- `∫∫_{(ℝ^d)² ∖ △} K(x, y) d(μ_N - μ)^{⊗2}(x, y)` for `μ_N = (1/N) Σ δ_{x_i}`. -/
noncomputable def offDiag {d : ℕ} (N : ℕ) (K : E d → E d → ℝ) (x : Fin N → E d)
    (μ : E d → ℝ) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, K (x i) (x j)
    - (1 / (N : ℝ)) * ∑ i, (∫ y, (K (x i) y + K y (x i)) * μ y)
    + ∫ x', ∫ y, K x' y * μ x' * μ y

/-- The integrals in `offDiag N K x μ` converge absolutely. -/
def OffDiagIntegrable {d : ℕ} (N : ℕ) (K : E d → E d → ℝ) (x : Fin N → E d)
    (μ : E d → ℝ) : Prop :=
  (∀ i, Integrable (fun y => K (x i) y * μ y) volume ∧
      Integrable (fun y => K y (x i) * μ y) volume) ∧
  Integrable (fun p : E d × E d => K p.1 p.2 * μ p.1 * μ p.2) (volume.prod volume)

/-- The modulated energy `F_N(x_N, μ)` of (1.6). -/
noncomputable def modEnergy {d : ℕ} (N : ℕ) (g : E d → ℝ) (x : Fin N → E d)
    (μ : E d → ℝ) : ℝ :=
  offDiag N (fun a b => g (a - b)) x μ

/-! ## The mean-field PDE (1.5) in mild form (3.1) -/

/-- The heat kernel `Φ_τ(x) = (4πτ)^{-d/2} e^{-|x|²/(4τ)}` of `e^{τΔ}`. -/
noncomputable def heatKernel (d : ℕ) (τ : ℝ) (x : E d) : ℝ :=
  (4 * Real.pi * τ) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * τ))

/-- `e^{τΔ} f = Φ_τ ∗ f`. -/
noncomputable def heatFlow (d : ℕ) (τ : ℝ) (f : E d → ℝ) (x : E d) : ℝ :=
  ∫ y, heatKernel d τ (x - y) * f y

/-- The velocity field `u = 𝕄∇g ∗ ν`, `u(y) = ∫ 𝕄∇g(y - z) ν(z) dz`. -/
noncomputable def velocity {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (g : E d → ℝ)
    (ν : E d → ℝ) (y : E d) : E d :=
  ∫ z, ν z • Matrix.toEuclideanLin M (gradient g (y - z))

/-- The integrand of `e^{τΔ} div F (x) = Σ_j (∂_jΦ_τ ∗ F_j)(x)` with `F = ν u`,
`∂_jΦ_τ(z) = -(z_j / 2τ) Φ_τ(z)`: the function
`y ↦ -(1/(2τ)) Φ_τ(x - y) ⟨x - y, u(y)⟩ ν(y)`. -/
noncomputable def heatDivIntegrand {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (g : E d → ℝ)
    (τ : ℝ) (ν : E d → ℝ) (x y : E d) : ℝ :=
  -(1 / (2 * τ)) * heatKernel d τ (x - y) * inner ℝ (x - y) (velocity M g ν y) * ν y

/-- `μ ∈ C([0, ∞); X)`, `X = L¹ ∩ L^∞`, is a mild solution (3.1) of (1.5) with data `μ⁰`:
`μ^t = e^{tσΔ}μ⁰ - ∫_0^t e^{(t-κ)σΔ} div(μ^κ 𝕄∇g ∗ μ^κ) dκ`, every integral converging. -/
def IsMildSolution (d : ℕ) (σ : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (g : E d → ℝ)
    (μ0 : E d → ℝ) (μ : ℝ≥0 → E d → ℝ) : Prop :=
  (∀ t, MemLp (μ t) 1 volume ∧ MemLp (μ t) ⊤ volume) ∧
  (∀ t, Tendsto (fun t' => eLpNorm (μ t' - μ t) 1 volume + eLpNorm (μ t' - μ t) ⊤ volume)
      (𝓝 t) (𝓝 0)) ∧
  (μ 0 =ᵐ[volume] μ0) ∧
  (∀ κ : ℝ≥0, ∀ᵐ y ∂volume,
      Integrable (fun z => μ κ z • Matrix.toEuclideanLin M (gradient g (y - z))) volume) ∧
  ∀ t : ℝ≥0, 0 < t → ∀ᵐ x ∂volume,
    Integrable (fun y => heatKernel d (σ * t) (x - y) * μ0 y) volume ∧
    (∀ κ : ℝ, 0 < κ → κ < t →
      Integrable (heatDivIntegrand M g (σ * (t - κ)) (μ κ.toNNReal) x) volume) ∧
    IntervalIntegrable
      (fun κ : ℝ => ∫ y, heatDivIntegrand M g (σ * (t - κ)) (μ κ.toNNReal) x y) volume 0 t ∧
    μ t x = heatFlow d (σ * t) μ0 x
      - ∫ κ in (0 : ℝ)..(t : ℝ), ∫ y, heatDivIntegrand M g (σ * (t - κ)) (μ κ.toNNReal) x y

/-- The path stays in `𝒫(ℝ^d)`: each `μ^t` is a nonnegative density of mass one. -/
def IsProbPath {d : ℕ} (μ : ℝ≥0 → E d → ℝ) : Prop :=
  ∀ t, (∀ᵐ x ∂volume, 0 ≤ μ t x) ∧ ∫ x, μ t x = 1

/-! ## Brownian motions and the particle system (1.1) -/

/-- `W_1, …, W_N` are independent standard `d`-dimensional Brownian motions: each coordinate
is a real Brownian motion and the `N·d` coordinate processes are jointly independent. -/
def IsBrownianFamily {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {d N : ℕ}
    (W : Fin N → ℝ≥0 → Ω → E d) : Prop :=
  (∀ i k, IsBrownianReal (fun t ω => W i t ω k) P) ∧
  iIndepFun (fun (ik : Fin N × Fin d) (ω : Ω) (t : ℝ≥0) => W ik.1 t ω ik.2) P

/-- `x` is a global solution of (1.1) driven by `W` from `x⁰`: measurable, and almost surely
the paths are continuous, never collide, and satisfy for all `t ≥ 0`
`x_i^t = x_i^0 + ∫_0^t (1/N) Σ_{j ≠ i} 𝕄∇g(x_i^τ - x_j^τ) dτ + √(2σ) W_i^t`. -/
def IsParticleSolution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {d N : ℕ} (σ : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (g : E d → ℝ) (x0 : Fin N → E d)
    (W : Fin N → ℝ≥0 → Ω → E d) (x : Fin N → ℝ≥0 → Ω → E d) : Prop :=
  (∀ i t, Measurable (x i t)) ∧
  ∀ᵐ ω ∂P, (∀ i, Continuous (fun t => x i t ω)) ∧
    (∀ t, Pairwise (fun i j => x i t ω ≠ x j t ω)) ∧
    ∀ i (t : ℝ≥0), x i t ω = x0 i
      + (∫ τ in (0 : ℝ)..(t : ℝ), (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
          Matrix.toEuclideanLin M (gradient g (x i τ.toNNReal ω - x j τ.toNNReal ω)))
      + Real.sqrt (2 * σ) • W i t ω

/-- The σ-algebra `𝓕^W_t = σ(W_j^τ : 1 ≤ j ≤ N, 0 ≤ τ ≤ t)` generated by the Brownian motions
up to time `t`. -/
abbrev bmSigma {Ω : Type} {d N : ℕ} (W : Fin N → ℝ≥0 → Ω → E d) (t : ℝ≥0) :
    MeasurableSpace Ω :=
  ⨆ (j : Fin N) (τ : ℝ≥0) (_ : τ ≤ t), MeasurableSpace.comap (W j τ) inferInstance

/-- `x` is a strong solution: each `x_i^t` agrees `P`-a.s. with a `𝓕^W_t`-measurable random
variable (adaptedness to the `P`-completed filtration generated by `W`). -/
def IsAdaptedToBM {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {d N : ℕ}
    (W : Fin N → ℝ≥0 → Ω → E d) (x : Fin N → ℝ≥0 → Ω → E d) : Prop :=
  ∀ i t, ∃ y : Ω → E d, Measurable[bmSigma W t] y ∧ x i t =ᵐ[P] y

/-- A bump function as in (4.1): `χ ∈ C_c^∞(ℝ^d)`, `χ ≥ 0`, `χ(x) = 1` for `|x| ≤ 1/2` and
`χ(x) = 0` for `|x| ≥ 1`. -/
def IsBump {d : ℕ} (χ : E d → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x, 0 ≤ χ x) ∧
    (∀ x : E d, ‖x‖ ≤ 1 / 2 → χ x = 1) ∧ (∀ x : E d, 1 ≤ ‖x‖ → χ x = 0)

/-- The truncated potential (4.2): `g_(ε)(x) = g(x)(1 - χ(x/ε))`. -/
noncomputable def truncPot {d : ℕ} (g χ : E d → ℝ) (ε : ℝ) (x : E d) : ℝ :=
  g x * (1 - χ (ε⁻¹ • x))

/-! ## Constants of Proposition 3.8 -/

/-- `K(r) = r'^{1/r'} / r^{1/r}` of (3.23), `r'` the Hölder conjugate, `1 ≤ r ≤ ∞`, with the
limiting values `K(1) = K(∞) = 1`. -/
noncomputable def carlenLossK (r : ℝ≥0∞) : ℝ :=
  if r = 1 ∨ r = ⊤ then 1
  else
    let ρ := r.toReal
    let ρ' := ρ / (ρ - 1)
    ρ' ^ (1 / ρ') / ρ ^ (1 / ρ)

end RieszMF.Linear


