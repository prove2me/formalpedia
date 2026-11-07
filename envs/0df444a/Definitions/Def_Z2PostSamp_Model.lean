-- Prove2me | Definitions.Def_Z2PostSamp_Model
-- name    : Z2PostSamp_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:14.278195+00:00
-- url     : https://prove2.me/theorems/43be5680-d70e-46b2-aafa-9421d6971e89
-- title:
--   The $\mathbb Z_2$ synchronization model, its posterior $\mu_J$, and the planted law
-- statement:
--   Let $\theta$ be uniform on $\{-1,1\}^n$ and, independently, let $Z$ be the real symmetric Gaussian matrix with $(Z_{ij})_{i<j}$ i.i.d. $\mathcal N(0,1)$ and $(Z_{ii})$ i.i.d. $\mathcal N(0,2)$, the two families independent. The observation is
--
--   $$Y=\frac{\lambda}{\sqrt n}\,\theta\theta^\top+Z .$$
--
--   For a matrix $J$ the **Ising law** on $\{\pm1\}^n$ is
--
--   $$\mu_J(x)=\frac{\exp(H_J(x))}{\sum_{z}\exp(H_J(z))},\qquad H_J(x)=\tfrac12\langle x,Jx\rangle ,$$
--
--   and the posterior of $\theta$ given $Y$ is $\mu_Y=\mu_J$ with $J=\frac{\lambda}{\sqrt n}Y=\frac{\lambda^2}{n}\theta\theta^\top+\lambda W$, $W=Z/\sqrt n$. The **planted law** is the joint law of $(\theta,Z,I)$, where $I$ is an independent uniform permutation of $[n]$ (the revealing order). The module also fixes the Frobenius norm $\|J\|_F$ and the $\ell^2\to\ell^2$ operator norm $\|J\|_{\mathrm{op}}$.
--
--   These are the objects of every statement of the mission: the goal compares a sampler's output law with $\mu_Y$ under the law of $(\theta,Z)$, and the milestones average over the planted law.
--
--   **Formalization Note** A configuration is `x : Spin n = Fin n → Bool` (published `OAI.CriticalSK`), with $\pm1$ values `spinValue`. The matrix $Z$ is generated from its free entries $E_{ij}$, $i\le j$, and symmetrized; the noise law is the product of the Gaussian laws of the free entries. The order is a permutation with the discrete σ-algebra, and `I a` (0-based) is the paper's $I_{a+1}$.
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), §1, p.2 (model, (1.1)); §2 preamble, p.5 and §2.2, p.7 (planted law, uniform order)

import Mathlib
import Definitions.Def_CriticalSK

set_option autoImplicit false

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory OAI.CriticalSK

namespace Z2PostSamp

noncomputable section

/-!
# The ℤ₂ synchronization model, its posterior, and the planted law

Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), §1, p.2: `Y = (λ/√n) θθᵀ + Z`, θ uniform on `{−1,1}ⁿ`, independent of the real
symmetric Gaussian `Z` with `(Z_ij)_{i<j}` iid `N(0,1)` and `Z_ii` iid `N(0,2)`; (1.1):
`μ_J(x) ∝ exp(H_J(x))`, `H_J(x) = ½⟨x, Jx⟩`, `J = (λ/√n) Y = (λ²/n) θθᵀ + λW`, `W = Z/√n`;
`μ_Y = μ_J`. §2 preamble, p.5: probabilities in the analysis are under the joint planted law with an
independent uniform revealing order `I`.

**Formalization Note.** A configuration is `x : Spin n = Fin n → Bool` (published `OAI.CriticalSK`),
with value `spinValue (x i) ∈ {1, −1}` (`true ↦ 1`). The Gaussian matrix is generated from its free
entries `E : Free n → ℝ`, indexed by pairs `i ≤ j`, with independent `N(0, 2)` diagonal and `N(0, 1)`
off-diagonal laws, and symmetrized by `Zmat`; this avoids a measurable structure on `Matrix`. The
posterior is the paper's Gibbs formula (1.1), diagonal included. The revealing order is a uniform
permutation `I` of `Fin n` (discrete σ-algebra); `I a` is the paper's `I_{a+1}` (0-based).
-/

/-- The spin vector `s = (spinValue (x i))_i ∈ {±1}ⁿ` of a configuration. -/
def spinVec {n : ℕ} (x : Spin n) : Fin n → ℝ := fun i => spinValue (x i)

/-- The Hamiltonian `H_J(x) = ½⟨x, Jx⟩ = ½ Σ_{i,j} J_ij x_i x_j` of (1.1). -/
def hamJ {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, J i j * spinValue (x i) * spinValue (x j)

/-- The Ising law `μ_J(x) = exp(H_J(x)) / Σ_z exp(H_J(z))` on `{±1}ⁿ`, (1.1). -/
def isingLaw {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) : ℝ :=
  Real.exp (hamJ J x) / ∑ z : Spin n, Real.exp (hamJ J z)

/-- The posterior `μ_Y = μ_J` with `J = (λ/√n) Y`, (1.1). -/
def postY (n : ℕ) (lam : ℝ) (Y : Matrix (Fin n) (Fin n) ℝ) : Spin n → ℝ :=
  isingLaw ((lam / Real.sqrt n) • Y)

/-- The free entries of a symmetric `n × n` matrix: pairs `(i, j)` with `i ≤ j`. -/
abbrev Free (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}

/-- The symmetric matrix `Z` with free entries `E`: `Z_ij = Z_ji = E_(min, max)`. -/
def Zmat {n : ℕ} (E : Free n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if h : i ≤ j then E ⟨(i, j), h⟩ else E ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩

/-- The law of the free entries of `Z`: independent, `N(0, 2)` on the diagonal, `N(0, 1)` above it. -/
def noiseLaw (n : ℕ) : Measure (Free n → ℝ) :=
  Measure.pi fun p : Free n => gaussianReal 0 (if p.1.1 = p.1.2 then 2 else 1)

/-- The prior of `θ`: uniform on `{±1}ⁿ`. -/
def signalLaw (n : ℕ) : Measure (Spin n) :=
  (PMF.uniformOfFintype (Spin n)).toMeasure

/-- The observation `Y = (λ/√n) θθᵀ + Z`, p.2. -/
def obsY (n : ℕ) (lam : ℝ) (θ : Spin n) (Z : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (lam / Real.sqrt n) • Matrix.vecMulVec (spinVec θ) (spinVec θ) + Z

/-- The discrete σ-algebra on permutations of `Fin n` (the revealing orders). -/
instance instMeasurableSpacePerm (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- The law of the revealing order: uniform on permutations of `Fin n` (p.7). -/
def permLaw (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure

/-- The planted sample space: the signal `θ`, the free noise entries, and the revealing order. -/
abbrev PΩ (n : ℕ) := Spin n × (Free n → ℝ) × Equiv.Perm (Fin n)

/-- The joint planted law of `(θ, Z, I)`, all independent (p.5, p.7). -/
def plantedLaw (n : ℕ) : Measure (PΩ n) :=
  (signalLaw n).prod ((noiseLaw n).prod (permLaw n))

/-- The interaction matrix `J = (λ/√n) Y = (λ²/n) θθᵀ + (λ/√n) Z` of a planted sample, (1.1). -/
def Jof (n : ℕ) (lam : ℝ) (ω : PΩ n) : Matrix (Fin n) (Fin n) ℝ :=
  (lam / Real.sqrt n) • obsY n lam ω.1 (Zmat ω.2.1)

/-- The Frobenius norm `‖J‖_F = (Σ_{i,j} J_ij²)^{1/2}`. -/
def frobNorm {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, J i j ^ 2)

/-- The `ℓ²→ℓ²` operator norm `‖J‖_op`. -/
def opNorm {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin J).toContinuousLinearMap‖

end

end Z2PostSamp


