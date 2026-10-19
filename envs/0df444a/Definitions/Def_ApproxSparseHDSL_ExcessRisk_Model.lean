-- Prove2me | Definitions.Def_ApproxSparseHDSL_ExcessRisk_Model
-- name    : ApproxSparseHDSL_ExcessRisk_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:27.273616+00:00
-- url     : https://prove2.me/theorems/93747b82-6f77-4229-93d9-f45fd9baaa05
-- title:
--   (1)–(3), (5), (11), (12), Assumptions 1–4, Definition 1, pp. 2–15 — MCP-regularized M-estimation, A-sparsity and the S³ONC
-- statement:
--   This file sets up the high-dimensional M-estimation problem of Liu, Ye & Lee.
--
--   **Data and risks** (pp. 2–3). On a probability space $(\Omega, \mathbb P)$, the observations $Z_1, \dots, Z_n$ are independent random elements of a measurable space $\mathcal W$, each with law $\mu$ (the i.i.d. copies of $Z$). A loss $L : \mathbb R^p \times \mathcal W \to \mathbb R$ is measurable and $\mu$-integrable in $z$ for every $\beta$, and
--
--   $$
--   \mathbb L(\beta) = \mathbb E[L(\beta, Z)], \qquad \mathcal L_n(\beta, Z_1^n) = \frac1n\sum_{i=1}^n L(\beta, Z_i), \qquad \mathcal L_{n,\lambda}(\beta, Z_1^n) = \mathcal L_n(\beta, Z_1^n) + \sum_{j=1}^p P_\lambda(|\beta_j|),
--   $$
--
--   with $\inf_\beta \mathbb L(\beta) > -\infty$ and $p, n \ge 1$. The Lasso objective of (5) is $\mathcal L_n(\beta, Z_1^n) + \lambda|\beta|$.
--
--   **Smoothness (11)** (p. 13). $U_L > 0$ and, for almost every $z$, each partial derivative $\partial L(\beta, z)/\partial \beta_j$ exists and satisfies $|\partial_j L(\tilde\beta + \delta e_j, z) - \partial_j L(\tilde\beta, z)| \le U_L|\delta|$ for all $\tilde\beta, \delta, j$.
--
--   **Assumption 3** (p. 13). $\sigma \ge 1$ and $\|L(\beta, Z_i) - \mathbb E L(\beta, Z_i)\|_{\psi_1} \le \sigma$ for all $\beta$ with $\|\beta\|_\infty \le R$ and all $i$.
--
--   **Assumption 4** (p. 14). A measurable integrable $\mathcal C : \mathcal W \to \mathbb R_+$ with $\|\mathcal C(Z_i) - \mathbb E\mathcal C(Z_i)\|_{\psi_1} \le \sigma_L$ ($\sigma_L \ge 1$), $|L(\beta_1, z) - L(\beta_2, z)| \le \mathcal C(z)\|\beta_1 - \beta_2\|$ on the box for a.e. $z$, and $\mathbb E\mathcal C(Z_i) \le \mathcal C_\mu$ with $\mathcal C_\mu \ge 1$.
--
--   **Bernstein inequalities.** (12) with constant $c$: for $\|\beta\|_\infty \le R$, $t \ge 0$, $a \in \mathbb R^n$,
--
--   $$
--   \mathbb P\Big(\Big|\sum_{i=1}^n a_i\{L(\beta, Z_i) - \mathbb E L(\beta, Z_i)\}\Big| > \sigma(\|a\|\sqrt t + \|a\|_\infty t)\Big) \le 2e^{-ct},
--   $$
--
--   and the analogous bound $\mathbb P(|\frac1n\sum_i(\mathcal C(Z_i) - \mathbb E\mathcal C(Z_i))| > \sigma_L(t/n + \sqrt{t/n})) \le 2e^{-ct}$ used in Lemma EC.1.
--
--   **A-sparsity** (p. 5). Assumption 1: $\varepsilon_A \ge 0$, $R \ge 1$, $\|\beta^*_{\varepsilon_A}\|_\infty \le R$ and $\mathbb L(\beta^*_{\varepsilon_A}) - \inf_\beta\mathbb L(\beta) \le \varepsilon_A$. Assumption 2 replaces $\inf_\beta \mathbb L$ by some $L^*_g \le \inf_\beta \mathbb L(\beta)$. The sparsity level is $s = \|\beta^*_{\varepsilon_A}\|_0$.
--
--   **S³ONC** (Definition 1, pp. 14–15). Given a sample $Z_1^n$, $\hat\beta$ satisfies the S³ONC if (a) there are $\kappa_j \in \partial|\hat\beta_j|$ with $\nabla\mathcal L_n(\hat\beta, Z_1^n) + (P'_\lambda(|\hat\beta_j|)\kappa_j)_j = 0$, and (b) $U_L + P''_\lambda(|\hat\beta_j|) \ge 0$ whenever $|\hat\beta_j| \in (0, a\lambda)$.
--
--   **Constants.** $\tilde\zeta = \ln(3eR(\sigma_L + \mathcal C_\mu))$, $\zeta_1(\epsilon) = \ln(3(\sigma_L + \mathcal C_\mu)peR/\epsilon)$, and the tuning parameters $\lambda = \sqrt{8\sigma/(c a n^{2\varrho})\,[\ln(n^\varrho p) + \tilde\zeta]}$ (Propositions 1, 5) and $\lambda = \sqrt{8\sigma/(c a n^{2/3})\,[\ln(n^{2/3} p) + \tilde\zeta]}$ (Theorem 1).
--
--   This is the model layer every theorem of the mission states its hypotheses in; it is reusable for the paper's nonsmooth and neural-network applications.
--
--   **Formalization Note** $\|\cdot\|_{\psi_1}$ is the published Orlicz norm `HighDimProb.Concentration.subexponentialNorm` (Vershynin 2018), always paired with an explicit witness $t > 0$ with $\mathbb E e^{|X|/t} \le 2$, so the junk value of an empty infimum never enters. The paper cites Vershynin (2012)'s moment form of $\psi_1$; the two are equivalent up to absolute constants, absorbed by the universal constants of the theorems. (12) and the $\mathcal C$-bound are hypotheses with their constant $c$ (Remark 1 derives (12) from Assumption 3 for an absolute $c \in (0, 1/2]$; the platform's proved `bernstein_weighted` shows such a $c$ exists). The paper's gradient is encoded through coordinate partial derivatives, which is all (11), (13) and (14) use; Definition 1 (a) also records that these partial derivatives of $\mathcal L_n$ exist. "$s \ll p$" has no formal content and is dropped. $\mathcal W \subseteq \mathbb R^q$ is an abstract measurable space: the embedding plays no role.
-- source:
--   Liu, Ye & Lee, High-dimensional learning under approximate sparsity with applications to nonsmooth estimation and regularized neural networks, arXiv:1903.00616v2, pp. 2–15, (1)–(3), (5), (11), (12), Assumptions 1–4, Definition 1

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubexponentialNorm
import Definitions.Def_ApproxSparseHDSL_ExcessRisk_Penalty

open MeasureTheory ProbabilityTheory

namespace ApproxSparseHDSL.ExcessRisk

section Risks

variable {E : Type} {p n : ℕ}

/-- The sample `Zⁿ₁ = (Z₁(ω), …, Zₙ(ω))` at the outcome `ω`. -/
def sample {Ω : Type} (Z : Fin n → Ω → E) (ω : Ω) : Fin n → E := fun i => Z i ω

/-- The population risk `𝕃(β) = E[L(β, Z)] = ∫ L(β, z) dμ(z)`, (1), p. 2, where `μ` is the law
of `Z`. -/
noncomputable def popRisk [MeasurableSpace E] (μ : Measure E) (L : (Fin p → ℝ) → E → ℝ) (β : Fin p → ℝ) : ℝ :=
  ∫ z, L β z ∂μ

/-- The empirical risk `ℒₙ(β, Zⁿ₁) = (1/n) Σᵢ L(β, Zᵢ)`, (2), p. 2. -/
noncomputable def empRisk (L : (Fin p → ℝ) → E → ℝ) (z : Fin n → E) (β : Fin p → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, L β (z i)

/-- The MCP-regularized empirical risk `ℒₙ,λ(β, Zⁿ₁) = ℒₙ(β, Zⁿ₁) + Σⱼ P_λ(|βⱼ|)`, (3), p. 3. -/
noncomputable def regRisk (a lam : ℝ) (L : (Fin p → ℝ) → E → ℝ) (z : Fin n → E)
    (β : Fin p → ℝ) : ℝ :=
  empRisk L z β + ∑ j, mcp a lam |β j|

/-- The Lasso objective `ℒₙ(β, Zⁿ₁) + λ|β|` of (5), p. 6 (`|·|` is the ℓ₁ norm). -/
noncomputable def lassoObj (lam : ℝ) (L : (Fin p → ℝ) → E → ℝ) (z : Fin n → E)
    (β : Fin p → ℝ) : ℝ :=
  empRisk L z β + lam * l1 β

/-- Definition 1, pp. 14–15: `β` satisfies the S³ONC of Problem (3) at the sample `z`.
(a) the coordinate partial derivatives of `ℒₙ(·, z)` exist at `β`, and there are
`κⱼ ∈ ∂|βⱼ|` with `∂ℒₙ/∂βⱼ(β) + P′_λ(|βⱼ|) κⱼ = 0` for all `j` (13);
(b) for all `j` with `|βⱼ| ∈ (0, aλ)`, `U_L + P″_λ(|βⱼ|) ≥ 0` (14). -/
def S3ONC (UL a lam : ℝ) (L : (Fin p → ℝ) → E → ℝ) (z : Fin n → E) (β : Fin p → ℝ) : Prop :=
  (∀ j, DifferentiableAt ℝ (fun t => empRisk L z (Function.update β j t)) (β j)) ∧
  (∃ κ : Fin p → ℝ, (∀ j, κ j ∈ absSubdiff (β j)) ∧
    ∀ j, partialJ (empRisk L z) β j + deriv (mcp a lam) |β j| * κ j = 0) ∧
  (∀ j, |β j| ∈ Set.Ioo 0 (a * lam) → 0 ≤ UL + deriv (deriv (mcp a lam)) |β j|)

end Risks

section Assumptions

variable {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] {p n : ℕ}

/-- The standing sampling setting, pp. 2–3 and 12: `p, n ≥ 1`; `P` is a probability measure;
`Z₁, …, Zₙ` are measurable, independent, each with law `μ` (i.i.d. copies of `Z`);
`L(β, ·)` is measurable and `μ`-integrable for every `β` (so `E[L(β, Z)]` is well defined
and finite); and `inf_β 𝕃(β) > −∞`, i.e. `𝕃` is bounded below. -/
structure IIDSample (P : Measure Ω) (μ : Measure E) (Z : Fin n → Ω → E)
    (L : (Fin p → ℝ) → E → ℝ) : Prop where
  p_pos : 0 < p
  n_pos : 0 < n
  isProb : IsProbabilityMeasure P
  meas_Z : ∀ i, Measurable (Z i)
  indep : iIndepFun Z P
  law : ∀ i, P.map (Z i) = μ
  meas_L : ∀ β, Measurable (L β)
  int_L : ∀ β, Integrable (L β) μ
  bddBelow : BddBelow (Set.range (popRisk μ L))

/-- The smoothness condition (11), p. 13: `U_L > 0` and, for `μ`-almost every `z`, every
coordinate section `t ↦ L(β + (t − βⱼ)eⱼ, z)` is differentiable at `βⱼ`, and the partial
derivative `∂L(β, z)/∂βⱼ` is `U_L`-Lipschitz along the `j`-th coordinate:
`|∂ⱼL(β̃ + δeⱼ, z) − ∂ⱼL(β̃, z)| ≤ U_L|δ|` for all `β̃, δ, j`. -/
def Smooth11 (μ : Measure E) (L : (Fin p → ℝ) → E → ℝ) (UL : ℝ) : Prop :=
  0 < UL ∧
  (∀ᵐ z ∂μ, ∀ (β : Fin p → ℝ) (j : Fin p),
      DifferentiableAt ℝ (fun t => L (Function.update β j t) z) (β j)) ∧
  (∀ᵐ z ∂μ, ∀ (β : Fin p → ℝ) (δ : ℝ) (j : Fin p),
      |partialJ (fun b => L b z) (Function.update β j (β j + δ)) j
        - partialJ (fun b => L b z) β j| ≤ UL * |δ|)

/-- `X` is sub-exponential with `‖X‖ψ₁ ≤ K`: some `t > 0` has `E exp(|X|/t)` finite and `≤ 2`
(so the Orlicz norm is a genuine infimum, not the junk value `sInf ∅ = 0`), and the published
`ψ₁` norm `subexponentialNorm P X` is at most `K`. -/
def SubexpBounded (P : Measure Ω) (X : Ω → ℝ) (K : ℝ) : Prop :=
  (∃ t : ℝ, 0 < t ∧ Integrable (fun ω => Real.exp (|X ω| / t)) P ∧
      ∫ ω, Real.exp (|X ω| / t) ∂P ≤ 2) ∧
  HighDimProb.Concentration.subexponentialNorm P X ≤ K

/-- Assumption 3, p. 13: `σ ≥ 1` and, for all `β` with `‖β‖∞ ≤ R` and all `i`,
`‖L(β, Zᵢ) − E[L(β, Zᵢ)]‖ψ₁ ≤ σ`. (`E[L(β, Zᵢ)] = ∫ L(β, ·) dμ` is finite by `IIDSample`.) -/
def Assumption3 (P : Measure Ω) (μ : Measure E) (Z : Fin n → Ω → E)
    (L : (Fin p → ℝ) → E → ℝ) (R σ : ℝ) : Prop :=
  1 ≤ σ ∧
  ∀ β : Fin p → ℝ, InBox R β → ∀ i : Fin n,
    SubexpBounded P (fun ω => L β (Z i ω) - ∫ z, L β z ∂μ) σ

/-- Assumption 4, p. 14, together with the convention `E[𝒞(Zᵢ)] ≤ C_µ`, `C_µ ≥ 1` stated right
after it: `𝒞 : 𝒲 → ℝ₊` is measurable and integrable, `‖𝒞(Zᵢ) − E[𝒞(Zᵢ)]‖ψ₁ ≤ σ_L` for all `i`
with `σ_L ≥ 1`, and `|L(β₁, z) − L(β₂, z)| ≤ 𝒞(z)‖β₁ − β₂‖` (Euclidean norm) for all `β₁, β₂`
in the box `‖·‖∞ ≤ R` and `μ`-almost every `z`. -/
def Assumption4 (P : Measure Ω) (μ : Measure E) (Z : Fin n → Ω → E)
    (L : (Fin p → ℝ) → E → ℝ) (R : ℝ) (Cfn : E → ℝ) (sigL Cmu : ℝ) : Prop :=
  Measurable Cfn ∧ (∀ z, 0 ≤ Cfn z) ∧ Integrable Cfn μ ∧
  1 ≤ sigL ∧
  (∀ i : Fin n, SubexpBounded P (fun ω => Cfn (Z i ω) - ∫ z, Cfn z ∂μ) sigL) ∧
  (∀ᵐ z ∂μ, ∀ β₁ β₂ : Fin p → ℝ, InBox R β₁ → InBox R β₂ →
      |L β₁ z - L β₂ z| ≤ Cfn z * eucl (β₁ - β₂)) ∧
  ∫ z, Cfn z ∂μ ≤ Cmu ∧ 1 ≤ Cmu

/-- The Bernstein-like inequality (12) of Remark 1, p. 13, with constant `c`: for all `β` with
`‖β‖∞ ≤ R`, all `t ≥ 0` and all `a ∈ ℝⁿ`,
`P(|Σᵢ aᵢ (L(β, Zᵢ) − E L(β, Zᵢ))| > σ(‖a‖√t + ‖a‖∞ t)) ≤ 2 exp(−ct)`. -/
def Bernstein12 (P : Measure Ω) (μ : Measure E) (Z : Fin n → Ω → E)
    (L : (Fin p → ℝ) → E → ℝ) (R σ c : ℝ) : Prop :=
  ∀ β : Fin p → ℝ, InBox R β → ∀ t : ℝ, 0 ≤ t → ∀ a : Fin n → ℝ,
    P {ω | σ * (eucl a * Real.sqrt t + supNorm a * t) <
        |∑ i, a i * (L β (Z i ω) - ∫ z, L β z ∂μ)|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(c * t)))

/-- The Bernstein-like inequality for `𝒞(Zᵢ)` invoked in the proof of Lemma EC.1, p. ec41, with
constant `c`: for all `t ≥ 0`,
`P(|Σᵢ (1/n)(𝒞(Zᵢ) − E 𝒞(Zᵢ))| > σ_L(t/n + √(t/n))) ≤ 2 exp(−ct)`. -/
def BernsteinC (P : Measure Ω) (μ : Measure E) (Z : Fin n → Ω → E) (Cfn : E → ℝ)
    (sigL c : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    P {ω | sigL * (t / n + Real.sqrt (t / n)) <
        |∑ i, (1 / (n : ℝ)) * (Cfn (Z i ω) - ∫ z, Cfn z ∂μ)|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(c * t)))

/-- Assumption 1 (A-sparsity), p. 5: `εA ≥ 0`, `R ≥ 1`, `‖β*_εA‖∞ ≤ R` and
`𝕃(β*_εA) − inf_β 𝕃(β) ≤ εA`. (`s := ‖β*_εA‖₀`; "`s ≪ p`" has no formal content.) -/
def Assumption1 (μ : Measure E) (L : (Fin p → ℝ) → E → ℝ) (R epsA : ℝ)
    (betaStar : Fin p → ℝ) : Prop :=
  0 ≤ epsA ∧ 1 ≤ R ∧ InBox R betaStar ∧
  popRisk μ L betaStar - ⨅ β, popRisk μ L β ≤ epsA

/-- Assumption 2, p. 5: `εA ≥ 0`, `R ≥ 1`, `‖β*_εA‖∞ ≤ R`, `L*_g ≤ inf_β 𝕃(β)` and
`𝕃(β*_εA) − L*_g ≤ εA`. -/
def Assumption2 (μ : Measure E) (L : (Fin p → ℝ) → E → ℝ) (R epsA Lg : ℝ)
    (betaStar : Fin p → ℝ) : Prop :=
  0 ≤ epsA ∧ 1 ≤ R ∧ InBox R betaStar ∧
  Lg ≤ ⨅ β, popRisk μ L β ∧ popRisk μ L betaStar - Lg ≤ epsA

end Assumptions

/-- `ζ̃ := ln(3eR(σ_L + C_µ))`, pp. 15 and ec24. -/
noncomputable def zetaT (R sigL Cmu : ℝ) : ℝ :=
  Real.log (3 * Real.exp 1 * R * (sigL + Cmu))

/-- `ζ₁(ϵ) := ln(3(σ_L + C_µ) p e R / ϵ)`, Propositions 3 and 4, pp. ec20, ec22. -/
noncomputable def zeta1 (p : ℕ) (R sigL Cmu ε : ℝ) : ℝ :=
  Real.log (3 * (sigL + Cmu) * p * Real.exp 1 * R / ε)

/-- The tuning parameter of Propositions 1 and 5:
`λ := √(8σ/(c a n^{2ϱ}) [ln(n^ϱ p) + ζ̃])`. -/
noncomputable def lamRho (σ c a : ℝ) (n p : ℕ) (rho zT : ℝ) : ℝ :=
  Real.sqrt (8 * σ / (c * a * (n : ℝ) ^ (2 * rho)) * (Real.log ((n : ℝ) ^ rho * p) + zT))

/-- The tuning parameter of Theorem 1: `λ := √(8σ/(c a n^{2/3}) [ln(n^{2/3} p) + ζ̃])`. -/
noncomputable def lamThm1 (σ c a : ℝ) (n p : ℕ) (zT : ℝ) : ℝ :=
  Real.sqrt (8 * σ / (c * a * (n : ℝ) ^ (2 / 3 : ℝ)) *
    (Real.log ((n : ℝ) ^ (2 / 3 : ℝ) * p) + zT))

end ApproxSparseHDSL.ExcessRisk


