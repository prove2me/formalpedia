-- Prove2me | Definitions.Def_PassiveIndexing_PriceEfficiency_Model
-- name    : PassiveIndexing_PriceEfficiency_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:14.562455+00:00
-- url     : https://prove2.me/theorems/8ebcda08-9fed-4d9d-a633-6472b7b5fa3a
-- title:
--   §2 and (3)–(4), (7)–(8), (19)–(20): Gaussian signal economy and public statistic
-- statement:
--   **Gaussian signal economy.** There are $n$ risky assets and $m$ investors. The payoff vector $v$ has multivariate normal law $N(\mu_v,\Sigma_{vv})$. Investor $k$ sees $s_k=v+\varepsilon_k$, where every noise vector has law $N(0,\Sigma_{\varepsilon\varepsilon})$. The payoff and all noise vectors are mutually independent. Both covariance matrices are positive definite. A portfolio $x\in\mathbb R^n$ pays $x'v$, and $\mathbf 1$ is the all-ones market portfolio.
--
--   For a nonindexer set $NI$, with $1\le |NI|<m$, equations (3) and (4) define
--   $$
--   g=(m\Sigma_{vv}+\Sigma_{\varepsilon\varepsilon})^{-1}\Sigma_{vv}\mathbf 1,
--   \qquad y=\left(\frac1{|NI|}\sum_{k\in NI}s_k,\;g'\sum_{k=1}^m s_k\right).
--   $$
--   The final coordinate of $y$ follows the first $n$ coordinates. The definition file also names the matrices $\Sigma_{vy}$ and $\Sigma_{yy}(N)$ from (7)–(8), the coefficient row $(\theta',q)=x'\Sigma_{vy}\Sigma_{yy}(N)^{-1}$ from (19), and the Schur-complement expression from (20). These are derived objects of the model, not free parameters.
--
--   This interface makes the Gaussian model and its public statistic reusable for the price-efficiency statements.
--
--   **Formalization Note** Investors and assets are indexed from zero. The law lives on Mathlib's Euclidean space; the statistic has coordinates indexed by $\mathrm{Fin}(n)\oplus\mathrm{Unit}$. Measurability of payoffs and noises is stated explicitly so conditioning on $\sigma(y)$ is valid. Conditional variance is Mathlib's $\operatorname{Var}[x'v\mid\sigma(y)]$; the Schur expression has a separate name and is connected to it by milestone (20). The inverse matrices are used only under the positivity and cardinality conditions in the theorems.
-- source:
--   Baruch & Zhang, The Distortion in Prices Due to Passive Investing, Management Science 68(8), 2022, pp. 6221–6223 and 6226, §2, equations (3), (4), (7), (8), (19), (20); https://doi.org/10.1287/mnsc.2021.4114

import Mathlib

namespace PassiveIndexing.PriceEfficiency

open MeasureTheory ProbabilityTheory Matrix

/-- The paper's Gaussian payoff and private-noise model (§2, p. 6221). The `none` member
of the independence family is the payoff vector; `some k` is investor `k`'s noise. -/
structure SignalModel {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}
    (P : Measure Ω) (muv : EuclideanSpace ℝ (Fin n))
    (Svv See : Matrix (Fin n) (Fin n) ℝ)
    (v : Ω → EuclideanSpace ℝ (Fin n))
    (eps : Fin m → Ω → EuclideanSpace ℝ (Fin n)) : Prop where
  payoff_posDef : Svv.PosDef
  noise_posDef : See.PosDef
  payoff_measurable : Measurable v
  noise_measurable : ∀ k, Measurable (eps k)
  payoff_law : HasLaw v (multivariateGaussian muv Svv) P
  noise_law : ∀ k, HasLaw (eps k) (multivariateGaussian 0 See) P
  independent : iIndepFun
    (fun (i : Option (Fin m)) (ω : Ω) => i.elim (v ω) (fun k => eps k ω)) P

/-- Investor `k`'s private signal, `sₖ = v + εₖ` (§2, p. 6221). -/
def signal {Ω : Type*} {n m : ℕ}
    (v : Ω → EuclideanSpace ℝ (Fin n))
    (eps : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (k : Fin m) (ω : Ω) : EuclideanSpace ℝ (Fin n) := v ω + eps k ω

/-- The risky payoff `x′v` of a stock portfolio (§2, p. 6221). -/
def payoff {Ω : Type*} {n : ℕ} (v : Ω → EuclideanSpace ℝ (Fin n))
    (x : Fin n → ℝ) (ω : Ω) : ℝ := ∑ i, x i * v ω i

/-- The market portfolio `1` (§2, p. 6221). -/
def marketPortfolio (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- Equation (3): `g = (m Σvv + Σεε)⁻¹ Σvv 1`. -/
noncomputable def gvec {n : ℕ} (m : ℕ)
    (Svv See : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  (((m : ℝ) • Svv + See)⁻¹) *ᵥ (Svv *ᵥ marketPortfolio n)

/-- Equation (4): first `n` coordinates average the nonindexers' signals, and the final
coordinate is the scalar statistic of all signals. The final coordinate is `Sum.inr ()`. -/
noncomputable def yStat {Ω : Type*} {n m : ℕ}
    (Svv See : Matrix (Fin n) (Fin n) ℝ)
    (v : Ω → EuclideanSpace ℝ (Fin n))
    (eps : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (NI : Finset (Fin m)) (ω : Ω) : (Fin n ⊕ Unit) → ℝ :=
  Sum.elim
    (fun i => (NI.card : ℝ)⁻¹ * ∑ k ∈ NI, signal v eps k ω i)
    (fun _ => ∑ i, gvec m Svv See i * ∑ k : Fin m, signal v eps k ω i)

/-- The standing condition that both kinds of investor are present (§2, p. 6222). -/
def Admissible {m : ℕ} (NI : Finset (Fin m)) : Prop :=
  1 ≤ NI.card ∧ NI.card < m

/-- Conditional variance of `x′v` given the public statistic `y`, as in (16) and (20).
This is Mathlib's genuine conditional variance, not the matrix formula from (20). -/
noncomputable def cv {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}
    (P : Measure Ω) (Svv See : Matrix (Fin n) (Fin n) ℝ)
    (v : Ω → EuclideanSpace ℝ (Fin n))
    (eps : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (x : Fin n → ℝ) (NI : Finset (Fin m)) : Ω → ℝ :=
  Var[payoff v x; P | MeasurableSpace.comap (yStat Svv See v eps NI) inferInstance]

/-- Equation (7), the covariance matrix of `v` and `y`. -/
noncomputable def Svy {n : ℕ} (m : ℕ)
    (Svv See : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromCols Svv (fun i _ => (m : ℝ) * (Svv *ᵥ gvec m Svv See) i)

/-- Equation (8), the covariance matrix of `y`, extended to real `N = |NI|`. -/
noncomputable def Syy {n : ℕ} (m : ℕ)
    (Svv See : Matrix (Fin n) (Fin n) ℝ) (N : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks
    (Svv + N⁻¹ • See)
    (fun i _ => (Svv *ᵥ marketPortfolio n) i)
    (fun _ j => (marketPortfolio n ᵥ* Svv) j)
    (fun _ _ => (m : ℝ) * (marketPortfolio n ⬝ᵥ (Svv *ᵥ gvec m Svv See)))

/-- The portfolio version of the Schur complement on the right of (20). -/
noncomputable def condVarFormula {n : ℕ} (m : ℕ)
    (Svv See : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (N : ℝ) : ℝ :=
  x ⬝ᵥ (Svv *ᵥ x) -
    x ⬝ᵥ ((Svy m Svv See * (Syy m Svv See N)⁻¹ * (Svy m Svv See)ᵀ) *ᵥ x)

/-- Equation (19), the row vector `[θ′ q] = x′ Σvy Σyy⁻¹`. -/
noncomputable def rowCoef {n : ℕ} (m : ℕ)
    (Svv See : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (N : ℝ) : (Fin n ⊕ Unit) → ℝ :=
  (x ᵥ* Svy m Svv See) ᵥ* (Syy m Svv See N)⁻¹

/-- The first `n` coefficients `θ` of (19). -/
noncomputable def thetaVec {n : ℕ} (m : ℕ)
    (Svv See : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (N : ℝ) : Fin n → ℝ :=
  fun i => rowCoef m Svv See x N (Sum.inl i)

/-- The final coefficient `q` of (19). -/
noncomputable def qCoef {n : ℕ} (m : ℕ)
    (Svv See : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (N : ℝ) : ℝ :=
  rowCoef m Svv See x N (Sum.inr ())

/-- Block matrix with `Σεε` in the upper-left corner, used for the derivatives of (8). -/
def Dblk {n : ℕ} (See : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks See 0 0 0

end PassiveIndexing.PriceEfficiency


