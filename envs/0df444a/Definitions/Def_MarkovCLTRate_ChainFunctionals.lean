-- Prove2me | Definitions.Def_MarkovCLTRate_ChainFunctionals
-- name    : MarkovCLTRate_ChainFunctionals
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:27:04.555923+00:00
-- url     : https://prove2.me/theorems/aa1c6264-727d-4a96-9b26-07ad4c74cdcd
-- title:
--   Chain functionals of Theorem 3: $g$, $U_n$, the Poisson equation, $m_k$, $W_n$, $v$, $\Sigma_\infty$, $B$, $\Psi$, $\tilde\Psi_k$, $\Gamma_k$ and the proof setting
-- statement:
--   Let $X=(X_0,X_1,\dots)$ be the Markov chain with kernel $P$ and initial distribution $\eta$, realized on the path space with $\mathcal F_k=\sigma(X_0,\dots,X_k)$. For a reward $r:\mathcal S\to\Re^d$ with $\pi\|r\|<\infty$:
--
--   1. $\bar r=\pi r$, $g=r-\bar r$ and $U_n=\frac1{\sqrt n}\sum_{k=1}^n g(X_{k-1})$.
--   2. $V_r$ solves the **Poisson equation** $V_r-PV_r=g$, where $PV_r(x)=\int V_r(y)P(x,dy)$; a **growth bound** with exponent $a$ is $\|V_r(x)\|\le C(1+\mathcal V(x)^a)$.
--   3. $m_k=V_r(X_k)-E[V_r(X_k)\mid X_{k-1}]$ for $k\ge1$, and $W_n=\frac1{\sqrt n}\sum_{k=1}^nm_k$.
--   4. $v(x)=E[m_1m_1^\top\mid X_0=x]$, $\Sigma_\infty=E_\pi[m_1m_1^\top]$ (the chain started from $\pi$), and $B(x)=\Sigma_\infty-v(x)$.
--   5. $\Psi$ solves the matrix **Poisson equation** $\Psi-P\Psi=B$ componentwise; $\tilde\Psi_k=\Psi(X_k)-E[\Psi(X_k)]$ and $\Gamma_k=\Psi(X_k)-E[\Psi(X_k)\mid\mathcal F_{k-1}]$.
--
--   The **proof setting** for an exponent $2<p\le4$ collects: the standing assumptions of Theorem 3; $r$ measurable and $\pi$-integrable with $\|g(x)\|^p\le C_r\mathcal V(x)$; and $V_r$ a solution of the Poisson equation with $\|V_r(x)\|\le C(1+\mathcal V(x)^{1/p})$ (the bound (10)). Item 1 of Theorem 3 is the case $p=2+\beta$, item 2 the case $p=4$.
--
--   **Formalization Note** The chain's law is `MarkovChainCLT.chainMeasure P η` on $\mathcal S^{\mathbb N}$ and $X_k(\omega)=\omega_k$; the filtration is `Filtration.piLE`. By the Markov property $E[V_r(X_k)\mid X_{k-1}]=PV_r(X_{k-1})$, and $m_k$ is written that way. Matrix-valued objects are handled entrywise.
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, Theorem 3, pp.17–18; proof of Theorem 3, pp.18–20 ((10), v, Σ∞, B, (16), Ψ̃_k, Γ_k)

import Mathlib
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_MartingaleCLT
import Definitions.Def_MarkovCLTRate_GeneralChain

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

variable {S : Type*} [MeasurableSpace S] {d : ℕ}

/-- The filtration `𝓕_k = σ(X_0, …, X_k)` of the coordinate process `X_k(ω) = ω k` on the path
space `ℕ → S`. -/
noncomputable abbrev pathFiltration (S : Type*) [MeasurableSpace S] :
    Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → S)) :=
  Filtration.piLE (X := fun _ : ℕ => S)

/-- The centered reward `g = r − r̄`, `r̄ = πr = ∫ r dπ`, arXiv:2401.15719v5, Theorem 3, p.17. -/
noncomputable def centered (π : Measure S) (r : S → Vec d) (x : S) : Vec d :=
  r x - ∫ y, r y ∂π

/-- `U_n = (1/√n) Σ_{k=1}^n g(X_{k−1})` on the path `ω = (X_0, X_1, …)`, arXiv:2401.15719v5,
Theorem 3, p.17. -/
noncomputable def Usum (g : S → Vec d) (n : ℕ) (ω : ℕ → S) : Vec d :=
  (Real.sqrt n)⁻¹ • ∑ k ∈ Finset.range n, g (ω k)

/-- The kernel acting on a vector-valued function: `Pf(x) = E[f(X_{k+1}) | X_k = x] = ∫ f dP(x)`. -/
noncomputable def kerApply (P : Kernel S S) (f : S → Vec d) (x : S) : Vec d :=
  ∫ y, f y ∂(P x)

/-- `V` solves the Poisson equation `V − PV = g` pointwise, arXiv:2401.15719v5, Theorem 3, p.18:
`V` is measurable, integrable against every `P(x, ·)`, and `V(x) − PV(x) = g(x)` for all `x`. -/
def IsPoissonSolution (P : Kernel S S) (g V : S → Vec d) : Prop :=
  Measurable V ∧ ∀ x, Integrable V (P x) ∧ V x - kerApply P V x = g x

/-- The growth bound `‖f(x)‖ ≤ C(1 + 𝒱(x)^a)` for some constant `C`, the form of (10), p.18 of
arXiv:2401.15719v5. -/
def GrowthBound (lyap : S → ℝ) (a : ℝ) (f : S → Vec d) : Prop :=
  ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C * (1 + lyap x ^ a)

/-- The martingale increment `m_k = V_r(X_k) − E[V_r(X_k) | X_{k−1}]`, arXiv:2401.15719v5,
Theorem 3, p.18, for `k ≥ 1`.

**Formalization Note.** By the Markov property `E[V_r(X_k) | X_{k−1}] = PV_r(X_{k−1})`; the
increment is written with `PV_r(X_{k−1})`. -/
noncomputable def mChain (P : Kernel S S) (V : S → Vec d) (k : ℕ) (ω : ℕ → S) : Vec d :=
  V (ω k) - kerApply P V (ω (k - 1))

/-- `W_n = (1/√n) Σ_{k=1}^n m_k`, arXiv:2401.15719v5, p.19. -/
noncomputable def Wsum (P : Kernel S S) (V : S → Vec d) (n : ℕ) (ω : ℕ → S) : Vec d :=
  (Real.sqrt n)⁻¹ • ∑ k ∈ Finset.Icc 1 n, mChain P V k ω

/-- The conditional covariance function `v(x) = E[m_1 m_1ᵀ | X_0 = x]`, arXiv:2401.15719v5, p.19:
`v(x)_{ij} = ∫ (V(y) − PV(x))_i (V(y) − PV(x))_j P(x, dy)`. -/
noncomputable def vCov (P : Kernel S S) (V : S → Vec d) (x : S) : Mat d :=
  Matrix.of fun i j => ∫ y, (V y - kerApply P V x) i * (V y - kerApply P V x) j ∂(P x)

/-- `Σ_∞ = E_π[m_1 m_1ᵀ]`, arXiv:2401.15719v5, Theorem 3, p.18: the second moment of `m_1` when the
chain starts from its invariant distribution `π`, entrywise. -/
noncomputable def sigmaInf (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) (V : S → Vec d) :
    Mat d :=
  Matrix.of fun i j =>
    ∫ ω, mChain P V 1 ω i * mChain P V 1 ω j ∂(MarkovChainCLT.chainMeasure P π)

/-- `B(x) = Σ_∞ − v(x)`, arXiv:2401.15719v5, p.20. -/
noncomputable def Bmat (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) (V : S → Vec d)
    (x : S) : Mat d :=
  sigmaInf P π V - vCov P V x

/-- `Ψ` solves the matrix-valued Poisson equation `Ψ − PΨ = B` componentwise, arXiv:2401.15719v5,
(16), p.20: every entry is measurable, integrable against every `P(x, ·)`, and
`Ψ(x)_{ij} − ∫ Ψ(y)_{ij} P(x, dy) = B(x)_{ij}`. -/
def IsMatPoissonSolution (P : Kernel S S) (B Ψ : S → Mat d) : Prop :=
  (∀ i j, Measurable fun x => Ψ x i j) ∧
    ∀ x i j, Integrable (fun y => Ψ y i j) (P x) ∧ Ψ x i j - ∫ y, Ψ y i j ∂(P x) = B x i j

/-- `Ψ̃_k = Ψ(X_k) − E[Ψ(X_k)]`, arXiv:2401.15719v5, p.20, entrywise, under the law `μ` of the
path. -/
noncomputable def psiTilde (μ : Measure (ℕ → S)) (Ψ : S → Mat d) (k : ℕ) (ω : ℕ → S) : Mat d :=
  Matrix.of fun i j => Ψ (ω k) i j - ∫ ω', Ψ (ω' k) i j ∂μ

/-- `Γ_k = Ψ(X_k) − E[Ψ(X_k) | 𝓕_{k−1}]`, arXiv:2401.15719v5, p.20, entrywise. -/
noncomputable def gammaMat (μ : Measure (ℕ → S)) (Ψ : S → Mat d) (k : ℕ) (ω : ℕ → S) : Mat d :=
  Matrix.of fun i j =>
    Ψ (ω k) i j - (μ[fun ω' => Ψ (ω' k) i j | pathFiltration S (k - 1)]) ω

/-- The setting of the proof of Theorem 3, arXiv:2401.15719v5, pp.18–22, for an exponent
`2 < p ≤ 4`: the standing assumptions of Theorem 3; the reward `r` is measurable and
`π`-integrable (`π‖r‖ < ∞`) with `‖g(x)‖^p ≤ C_r 𝒱(x)` for `g = r − πr`; and `V` solves the
Poisson equation `V − PV = g` with the growth bound (10), `‖V(x)‖ ≤ C(1 + 𝒱(x)^a)`, `a = 1/p`.

**Formalization Note.** The proof of item 1 has `p = 2 + β`; p.22 repeats it for item 2 with
`p = 4`. One parameter `2 < p ≤ 4` covers both. -/
structure ProofSetting (P : Kernel S S) (π η : Measure S) (lyap : S → ℝ) (lam L : ℝ)
    (r : S → Vec d) (p Cr : ℝ) (V : S → Vec d) : Prop where
  chain : GeoDriftChain P π η lyap lam L
  two_lt_p : 2 < p
  p_le_four : p ≤ 4
  measurable_r : Measurable r
  integrable_r : Integrable r π
  reward_growth : ∀ x, ‖centered π r x‖ ^ p ≤ Cr * lyap x
  poisson : IsPoissonSolution P (centered π r) V
  poisson_growth : GrowthBound lyap (1 / p) V

end MarkovCLTRate


