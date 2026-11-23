-- Prove2me | Definitions.Def_LeJEPAWorldModel_Basic
-- name    : LeJEPAWorldModel_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T17:14:09.193806+00:00
-- url     : https://prove2.me/theorems/4d3cb5cf-0b20-4384-9cc0-e555d6842bef
-- title:
--   Gaussian world, LeJEPA alignment loss, Hermite basis, and latent planning
-- statement:
--   Objects of Klindt, LeCun and Balestriero (2026), *When Does LeJEPA Learn a World Model?*
--
--   1. **Gaussian world (Section 2.1.1, eq. 1).** The latent is $z\sim\gamma_N=\mathcal N(0,I_N)$ on $\mathbb R^N$, the law with independent standard normal coordinates. For $\rho\in(0,1)$ a positive pair is $(z,z')$ with $z'=\rho z+\sqrt{1-\rho^2}\,\eta$, where $\eta\sim\mathcal N(0,I_N)$ is independent of $z$. Its law on $\mathbb R^N\times\mathbb R^N$ is the image of $\gamma_N\otimes\gamma_N$ under $(z,\eta)\mapsto(z,\rho z+\sqrt{1-\rho^2}\eta)$. Here $\|v\|^2=\sum_iv_i^2$.
--   2. **LeJEPA objective (Section 2.2, eq. 2).** For $h:\mathbb R^N\to\mathbb R^N$, the alignment loss is $\mathcal L(h)=\mathbb E\|h(z')-h(z)\|^2$.
--   3. **Second-order quantities (Theorem 3, Appendix C).** $\mathrm{Cov}(h(z))_{ij}=\mathbb E[(h_i(z)-\mathbb Eh_i(z))(h_j(z)-\mathbb Eh_j(z))]$, and $\|A\|_F=(\sum_{ij}A_{ij}^2)^{1/2}$. The linear part of $h$ is the matrix $M_{ij}=\mathbb E[h_i(z)z_j]$ (eq. 36), and the nonlinear energy is $W_{\mathrm{nl}}=\mathbb E\|h(z)-Mz\|^2$ (eq. 37).
--   4. **Hermite polynomials (Appendix A.2).** $\mathrm{He}_k$ is the probabilists' Hermite polynomial of degree $k$ (eq. 7), $\hat h_k=\mathrm{He}_k/\sqrt{k!}$, and for a multi-index $\alpha\in\mathbb N^N$, $H_\alpha(z)=\prod_j\hat h_{\alpha_j}(z_j)$ (eq. 10).
--   5. **Sturm–Liouville generator (Appendix B.1, eq. 30).** For a diffusion constant $K$ and a density $p$ on $\mathbb R$, $\mathcal D\varphi=\frac1p\frac{d}{dz}\big[Kp\,\varphi'\big]$.
--   6. **Planning (Section 4.4, Appendix D).** States lie in $\mathbb R^N$ and actions in a set $\mathcal A$. The transition $z_t\sim P(z_{t-1},a_t)$ is given by a probability measure $P(z,a)$ for each state and action. The stage cost is $\ell(z,a)$ and the terminal cost is $\ell_T(z)$. The expected cost of a plan $a_{1:T}$ from $z_0$ is $J(a_{1:T};z_0)=\mathbb E[\ell_T(z_T)+\sum_{t=1}^T\ell(z_{t-1},a_t)]$, computed backwards: $J(\varnothing;z)=\ell_T(z)$ and $J(a\,a_{2:T};z)=\ell(z,a)+\int J(a_{2:T};z')\,P(z,a)(dz')$. The value is $V^*(z_0)=\inf_{a_{1:T}}J(a_{1:T};z_0)$ over plans of length $T$ (by convention it is $0$ if this set of costs is empty or unbounded below). A plan of length $T$ is optimal if its cost is at most the cost of every plan of length $T$. For $Q\in O(N)$, the learned-latent transitions are $\hat P(\hat z,a)$, the image of $P(Q^\top\hat z,a)$ under $z\mapsto Qz$.
--   7. **Dirichlet-energy setting (Appendix E.1).** A $C^1$ diffeomorphism is a $C^1$ bijection of $\mathbb R^N$ with a $C^1$ inverse. For $\varepsilon>0$, the quotient is $\frac1\varepsilon\,\mathbb E\|h(z+\sqrt\varepsilon\,\eta)-h(z)\|^2\in[0,\infty]$, where $z,\eta\sim\mathcal N(0,I_N)$ are independent. Its limit as $\varepsilon\to0^+$ is the loss $\mathcal L(h)$ of Appendix E.
--
--   **Formalization Note** Vectors in $\mathbb R^N$ are functions $\mathrm{Fin}\,N\to\mathbb R$, and the squared norm is written out as a sum of squares. The Hermite polynomials are Mathlib's `Polynomial.hermite`, which Mathlib proves equal to the Rodrigues formula (7). The expected cost of a plan is defined by the backward recursion, which equals the trajectory expectation by the tower property. The Dirichlet quotient is a lower Lebesgue integral with values in $[0,\infty]$, so it is defined for every $h$.
-- source:
--   Klindt, LeCun and Balestriero, When Does LeJEPA Learn a World Model?, arXiv:2605.26379v2 (2026), Sections 2.1.1, 2.2, 4.4 (eqs. (1)-(2), (6)), Appendix A.2 (eqs. (7), (10)), Appendix B.1 (eq. (30)), Appendix C (eqs. (36)-(37)), Appendix D, Appendix E.1

import Mathlib

/-!
Klindt, LeCun and Balestriero, *When Does LeJEPA Learn a World Model?*, arXiv:2605.26379v2
(2026): the Gaussian world and the LeJEPA objective of Section 2, the Hermite basis of
Appendix A.2, the Sturm–Liouville generator of Appendix B.1, the linear part and nonlinear energy
of Appendix C, the planning problem of Section 4.4 and Appendix D, and the Dirichlet-energy
objective of Appendix E.1.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace LeJEPAWorldModel

/-- Squared Euclidean norm `‖v‖² = ∑ᵢ vᵢ²` of a vector `v ∈ ℝ^N` (Section 2.2). -/
def sqNorm {N : ℕ} (v : Fin N → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Section 2.1.1: the standard Gaussian `γ_N = N(0, I_N)` on `ℝ^N`, the law of the latent `z`
(independent standard normal coordinates). -/
def stdGaussian (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- Eq. (1): the law of a positive pair `(z, z')` of the Gaussian world, where `z ∼ N(0, I_N)`,
`η ∼ N(0, I_N)` is independent of `z`, and `z' = ρ z + √(1 - ρ²) η`. -/
def ouPairLaw (N : ℕ) (ρ : ℝ) : Measure ((Fin N → ℝ) × (Fin N → ℝ)) :=
  ((stdGaussian N).prod (stdGaussian N)).map
    (fun p => (p.1, ρ • p.1 + Real.sqrt (1 - ρ ^ 2) • p.2))

/-- Eq. (2), Section 2.2: the LeJEPA alignment loss `𝓛(h) = E ‖h(z') - h(z)‖²` over positive
pairs of the Gaussian world. -/
def alignLoss (N : ℕ) (ρ : ℝ) (h : (Fin N → ℝ) → Fin N → ℝ) : ℝ :=
  ∫ p, sqNorm (h p.2 - h p.1) ∂ouPairLaw N ρ

/-- Section 2.2 and Theorem 3: the covariance matrix `Cov(h(z))`, `z ∼ N(0, I_N)`. -/
def covMat (N : ℕ) (h : (Fin N → ℝ) → Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∫ z, (h z i - ∫ y, h y i ∂stdGaussian N) * (h z j - ∫ y, h y j ∂stdGaussian N)
    ∂stdGaussian N

/-- Frobenius norm `‖A‖_F = (∑ᵢⱼ Aᵢⱼ²)^{1/2}` (Theorem 3). -/
def frobNorm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- Eq. (36), Appendix C: the linear part `M` of `h`, `M_ij = E[h_i(z) z_j]`, `z ∼ N(0, I_N)`. -/
def linearPart (N : ℕ) (h : (Fin N → ℝ) → Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∫ z, h z i * z j ∂stdGaussian N

/-- Eq. (37), Appendix C: the nonlinear energy `W_nl = E ‖ν(z)‖²` of the residual
`ν(z) = h(z) - M z`. -/
def nonlinearEnergy (N : ℕ) (h : (Fin N → ℝ) → Fin N → ℝ) : ℝ :=
  ∫ z, sqNorm (h z - (linearPart N h).mulVec z) ∂stdGaussian N

/-- Eq. (7), Appendix A.2: the probabilists' Hermite polynomial `He_k`, evaluated at `x`
(Mathlib's `Polynomial.hermite`, which equals the Rodrigues formula (7) by
`Polynomial.hermite_eq_deriv_gaussian`). -/
def hermiteHe (k : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval x (Polynomial.hermite k)

/-- Appendix A.2: the normalized Hermite polynomial `ĥ_k(x) = He_k(x) / √(k!)`. -/
def hermiteNormalized (k : ℕ) (x : ℝ) : ℝ :=
  hermiteHe k x / Real.sqrt (k.factorial : ℝ)

/-- Eq. (10), Appendix A.2: the multivariate Hermite function `H_α(z) = ∏ⱼ ĥ_{αⱼ}(zⱼ)` for a
multi-index `α ∈ ℕ^N`. -/
def multiHermite {N : ℕ} (α : Fin N → ℕ) (z : Fin N → ℝ) : ℝ :=
  ∏ j, hermiteNormalized (α j) (z j)

/-- Eq. (30), Appendix B.1: the Sturm–Liouville generator of a scalar latent with constant
diffusion `K` and stationary density `p`, `𝒟φ = (1/p) d/dz [K p φ']`. -/
def slGenerator (K : ℝ) (p φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / p x) * deriv (fun y => K * p y * deriv φ y) x

section Planning

variable {N : ℕ} {A : Type*}

/-- Section 4.4: the expected cost `E[ℓ_T(z_T) + ∑_{t=1}^T ℓ(z_{t-1}, a_t) | z_0]` of the plan
`[a_1, …, a_T]` started at `z_0`, where `z_t ∼ P(z_{t-1}, a_t)`, computed backwards:
the empty plan costs `ℓ_T(z)` and the plan `a :: as` costs `ℓ(z, a) + ∫ cost(as, z') dP(z, a)(z')`. -/
def planCost (P : (Fin N → ℝ) → A → Measure (Fin N → ℝ)) (c : (Fin N → ℝ) → A → ℝ)
    (cT : (Fin N → ℝ) → ℝ) : List A → (Fin N → ℝ) → ℝ
  | [], z => cT z
  | a :: as, z => c z a + ∫ z', planCost P c cT as z' ∂(P z a)

/-- Section 4.4: the minimal cost `V*(z_0)` over plans `a_{1:T}` of length `T`. -/
def optimalValue (P : (Fin N → ℝ) → A → Measure (Fin N → ℝ)) (c : (Fin N → ℝ) → A → ℝ)
    (cT : (Fin N → ℝ) → ℝ) (T : ℕ) (z0 : Fin N → ℝ) : ℝ :=
  ⨅ as : {l : List A // l.length = T}, planCost P c cT as.1 z0

/-- Section 4.4: `as` is an optimal plan `a*_{1:T}(z_0)`: it has length `T` and its cost is at
most the cost of every plan of length `T`. -/
def IsOptimalPlan (P : (Fin N → ℝ) → A → Measure (Fin N → ℝ)) (c : (Fin N → ℝ) → A → ℝ)
    (cT : (Fin N → ℝ) → ℝ) (T : ℕ) (z0 : Fin N → ℝ) (as : List A) : Prop :=
  as.length = T ∧ ∀ bs : List A, bs.length = T → planCost P c cT as z0 ≤ planCost P c cT bs z0

/-- Theorem 4 and Appendix D: the transitions `p̂(· | ẑ, a)` of the learned latent `ẑ = h(z) = Q z`,
the pushforward under `h` of `p(· | h⁻¹(ẑ), a)`, with `h⁻¹(ẑ) = Qᵀ ẑ` for orthogonal `Q`. -/
def pushDynamics (Q : Matrix (Fin N) (Fin N) ℝ) (P : (Fin N → ℝ) → A → Measure (Fin N → ℝ)) :
    (Fin N → ℝ) → A → Measure (Fin N → ℝ) :=
  fun zh a => (P (Q.transpose.mulVec zh) a).map (fun z => Q.mulVec z)

end Planning

/-- Appendix E.1: `h : ℝ^N → ℝ^N` is a `C¹` diffeomorphism (a `C¹` bijection with `C¹` inverse). -/
def IsC1Diffeo {N : ℕ} (h : (Fin N → ℝ) → Fin N → ℝ) : Prop :=
  ContDiff ℝ 1 h ∧ ∃ g : (Fin N → ℝ) → Fin N → ℝ,
    ContDiff ℝ 1 g ∧ Function.LeftInverse g h ∧ Function.RightInverse g h

/-- Appendix E.1: the quotient `(1/ε) E ‖h(z + √ε η) - h(z)‖²`, `z, η ∼ N(0, I_N)` independent,
whose limit as `ε → 0⁺` is the normalized loss `𝓛(h)`; valued in `[0, ∞]`. -/
def dirichletQuotient (N : ℕ) (h : (Fin N → ℝ) → Fin N → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / ε) *
    ∫⁻ p, ENNReal.ofReal (sqNorm (h (p.1 + Real.sqrt ε • p.2) - h p.1))
      ∂((stdGaussian N).prod (stdGaussian N))

end LeJEPAWorldModel


