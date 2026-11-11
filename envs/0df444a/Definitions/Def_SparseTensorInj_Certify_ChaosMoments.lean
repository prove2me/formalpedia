-- Prove2me | Definitions.Def_SparseTensorInj_Certify_ChaosMoments
-- name    : SparseTensorInj_Certify_ChaosMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:38:18.514182+00:00
-- url     : https://prove2.me/theorems/0878b979-0c71-4d88-9898-97a7f9043590
-- title:
--   Expected trace moments of $M$, $M_{\mathrm{dec}}$, $M_{\mathrm{sym}}$, $M_{\mathrm{comp}}$, the independent chaos $Z$ and the Gaussian chaos $G_s$ (Lemmas 57, 64, Definitions 59, 65, 68, 79)
-- statement:
--   Let $E=[n]_{2q+1}$ and $\chi=\{\chi_e\}_{e\in E}$ be the coefficients of Definition 3. The expected trace moments of §4.3.3 are:
--
--   - $\mathbb E[\Phi_t(M)]$ for $M$ of Construction 47 built from the random tensor;
--   - $\mathbb E[\Phi_t(M_{\mathrm{dec}})]$, $M_{\mathrm{dec}}=\sum_{e\ne f,\min e=\min f}\chi_e\chi'_f(P_e\otimes P_f)$ with $\chi'$ an independent copy (Lemma 57);
--   - $\mathbb E[\Phi_t(M_{\mathrm{sym}})]$, $M_{\mathrm{sym}}=\sum_{e\ne f,\min e=\min f}\zeta_e\eta_f(P_e\otimes P_f)$, $\zeta_e=(\chi_e-\hat\chi_e)/\sqrt2$, $\eta_e=(\chi'_e-\hat\chi'_e)/\sqrt2$, with $\chi,\chi',\hat\chi,\hat\chi'$ four mutually independent copies (Definition 59, Lemma 64);
--   - $\mathbb E[\Phi_t(M_{\mathrm{comp}})]$, $M_{\mathrm{comp}}=\sum_{e\ne f,\min e=\min f}\mu_e\nu_f(P_e\otimes P_f)$ with $\mu,\nu$ two independent families of independent variables with law $D$ (Definition 65);
--   - $\mathbb E[\Phi_t(Z)]$, $Z=\sum_{i\in[n]}X_i\otimes Y_i$ where all entries of $X_i,Y_i\in\mathbb R^{N_q\times N_q}$ (over all $i$ and both families) are mutually independent with law $D$ (Definition 68; $X_i,Y_i$ need not be symmetric);
--   - $\mathbb E[\Phi_t(G_s)]$, $G_s=\sum_{i=1}^sG_i\otimes H_i\in\mathbb R^{s^{2q}\times s^{2q}}$ with all entries of $G_i,H_i\in\mathbb R^{s^q\times s^q}$ mutually independent standard Gaussians (Definition 79).
--
--   **Formalization Note.** Each expectation is the lower Lebesgue integral $\int^-\Phi_t$ of the non-negative trace moment, so it is the expectation in $[0,\infty]$ and needs no integrability side condition. Independent copies of $\chi$ are realized on product spaces: $\chi(\omega_1),\chi(\omega_2)$ on $(\Omega\times\Omega,P\otimes P)$ for $M_{\mathrm{dec}}$, and $\chi(\omega_1),\chi(\omega_2),\chi(\omega_3),\chi(\omega_4)$ for $\chi,\chi',\hat\chi,\hat\chi'$ on $((\Omega\times\Omega)\times(\Omega\times\Omega))$ for $M_{\mathrm{sym}}$. The $D$- and Gaussian families are product measures `Measure.pi`. The law $D$ is `sparseRademacher ρ` for a parameter $\rho$ (the paper's $\rho_t$). The rows and columns of $G_i,H_i$ are indexed by `Fin (s^q)`.
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), pp. 34–38, 44, Lemma 57, Definition 59, Lemma 64, Definitions 65, 68 and 79

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_RandomModel
import Definitions.Def_SparseTensorInj_Certify_OddCertificate
import Definitions.Def_SparseTensorInj_Certify_MomentParams

open MeasureTheory Matrix

namespace SparseTensorInj.Certify

/-! Expected trace moments `E[Φ_t(·)]` of the matrix chaoses of §4.3.3 (pp. 33–46). Each
expectation is the Lebesgue integral of the non-negative quantity `Φ_t` (possibly `+∞`), so no
integrability side condition is hidden. Independent copies are realized on product spaces. -/

/-- `E[Φ_t(M)]` for the matrix `M` of Construction 47 built from the random tensor of
Definition 3 with coefficients `χ` on `(Ω, P)`, `k = 2q + 1`. -/
noncomputable def expPhiM {n q : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : KSubset n (2 * q + 1) → Ω → ℝ) (t : ℕ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (traceMoment t (oddM (modelTensor χ ω))) ∂P

/-- `E[Φ_t(M_dec)]` (Lemma 57, p. 34): `M_dec = Σ_{e ≠ f, min e = min f} χ_e χ'_f (P_e ⊗ P_f)`
with `χ'` an independent copy of `χ`, realized on `(Ω × Ω, P ⊗ P)` as `χ = χ(ω₁)`, `χ' = χ(ω₂)`. -/
noncomputable def expPhiMdec {n q : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : KSubset n (2 * q + 1) → Ω → ℝ) (t : ℕ) : ENNReal :=
  ∫⁻ p : Ω × Ω, ENNReal.ofReal
    (traceMoment t (chaosMatrix (q := q) (fun e => χ e p.1) (fun e => χ e p.2))) ∂(P.prod P)

/-- `E[Φ_t(M_sym)]` (Definition 59 and Lemma 64, pp. 35–36):
`M_sym = Σ_{e ≠ f, min e = min f} ζ_e η_f (P_e ⊗ P_f)` with `ζ_e = (χ_e − χ̂_e)/√2` and
`η_e = (χ'_e − χ̂'_e)/√2`, where `χ, χ', χ̂, χ̂'` are four mutually independent copies, realized
on `((Ω × Ω) × (Ω × Ω), (P ⊗ P) ⊗ (P ⊗ P))` as `χ = χ(ω₁)`, `χ' = χ(ω₂)`, `χ̂ = χ(ω₃)`,
`χ̂' = χ(ω₄)` for the point `((ω₁, ω₂), (ω₃, ω₄))`. -/
noncomputable def expPhiMsym {n q : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : KSubset n (2 * q + 1) → Ω → ℝ) (t : ℕ) : ENNReal :=
  ∫⁻ p : (Ω × Ω) × (Ω × Ω), ENNReal.ofReal
    (traceMoment t (chaosMatrix (q := q)
      (fun e => (χ e p.1.1 - χ e p.2.1) / Real.sqrt 2)
      (fun e => (χ e p.1.2 - χ e p.2.2) / Real.sqrt 2))) ∂((P.prod P).prod (P.prod P))

/-- `E[Φ_t(M_comp)]` (Definition 65, p. 37): `M_comp = Σ_{e ≠ f, min e = min f} μ_e ν_f (P_e ⊗ P_f)`
where `(μ_e)`, `(ν_e)` are two independent families of independent variables with law
`D = sparseRademacher ρ`, i.e. the product law `D^{⊗E} ⊗ D^{⊗E}`. -/
noncomputable def expPhiMcomp (n q t : ℕ) (ρ : ℝ) : ENNReal :=
  ∫⁻ p : (KSubset n (2 * q + 1) → ℝ) × (KSubset n (2 * q + 1) → ℝ),
    ENNReal.ofReal (traceMoment t (chaosMatrix (q := q) p.1 p.2))
    ∂((Measure.pi fun _ => sparseRademacher ρ).prod (Measure.pi fun _ => sparseRademacher ρ))

/-- The independent matrix chaos `Z = Σ_{i ∈ [n]} X_i ⊗ Y_i` (Definition 68, p. 38), from the
entries `x (i, a, c) = X_i[a, c]` and `y (i, b, d) = Y_i[b, d]`, `X_i, Y_i ∈ ℝ^{N_q × N_q}`. -/
def Zmat {n q : ℕ} (x y : Fin n × QSet n q × QSet n q → ℝ) :
    Matrix (QSet n q × QSet n q) (QSet n q × QSet n q) ℝ :=
  ∑ i : Fin n, kronecker (fun a c => x (i, a, c)) (fun b d => y (i, b, d))

/-- `E[Φ_t(Z)]` (Definition 68): all entries of all `X_i, Y_i` mutually independent with law
`D = sparseRademacher ρ`, i.e. the product law over both entry families. -/
noncomputable def expPhiZ (n q t : ℕ) (ρ : ℝ) : ENNReal :=
  ∫⁻ p : (Fin n × QSet n q × QSet n q → ℝ) × (Fin n × QSet n q × QSet n q → ℝ),
    ENNReal.ofReal (traceMoment t (Zmat p.1 p.2))
    ∂((Measure.pi fun _ => sparseRademacher ρ).prod (Measure.pi fun _ => sparseRademacher ρ))

/-- The Gaussian reference chaos `G_s = Σ_{i=1}^s G_i ⊗ H_i ∈ ℝ^{s^{2q} × s^{2q}}`
(Definition 79, p. 44), from the entries `g (i, a, c) = G_i[a, c]`, `h (i, b, d) = H_i[b, d]`,
`G_i, H_i ∈ ℝ^{s^q × s^q}` (row and column indices in `[s^q]`). -/
def Gmat (s q : ℕ) (g h : Fin s × Fin (s ^ q) × Fin (s ^ q) → ℝ) :
    Matrix (Fin (s ^ q) × Fin (s ^ q)) (Fin (s ^ q) × Fin (s ^ q)) ℝ :=
  ∑ i : Fin s, kronecker (fun a c => g (i, a, c)) (fun b d => h (i, b, d))

/-- `E[Φ_t(G_s)]`: all entries of `G_1, …, G_s, H_1, …, H_s` mutually independent standard
Gaussians `N(0, 1)`. -/
noncomputable def expPhiG (s q t : ℕ) : ENNReal :=
  ∫⁻ p : (Fin s × Fin (s ^ q) × Fin (s ^ q) → ℝ) × (Fin s × Fin (s ^ q) × Fin (s ^ q) → ℝ),
    ENNReal.ofReal (traceMoment t (Gmat s q p.1 p.2))
    ∂((Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 1).prod
      (Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 1))

end SparseTensorInj.Certify


