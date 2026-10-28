-- Prove2me | Definitions.Def_NechitaRDM_MP_Basic
-- name    : NechitaRDM_MP_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:04.200476+00:00
-- url     : https://prove2.me/theorems/f6a6f52f-381c-4fc1-9930-c1a56b1387b5
-- title:
--   §2–§3.1, Definitions 1–5, pp. 3–7 — complex Gaussian matrices, Wishart matrices, pure states, the induced measure μ_{n,k}, the empirical spectral measure and the Marchenko–Pastur law μ_c
-- statement:
--   This file fixes the objects of Nechita's *Asymptotics of random density matrices* (§2 and §3.1).
--
--   1. **Complex Gaussians** (p. 4). $\mathcal N_{\mathbb C}(0,1)$ is the law of $Z = X + iY$ with $X, Y$ independent real Gaussians of mean $0$ and variance $1/2$ (so $\mathbb E|Z|^2 = 1$). A random vector $g \in \mathbb C^N$ has law $\mathcal N^N_{\mathbb C}(0, I_N)$ when its coordinates are independent with law $\mathcal N_{\mathbb C}(0,1)$; a random $n\times k$ matrix $X$ has i.i.d. $\mathcal N_{\mathbb C}(0,1)$ entries when its $nk$ entries are independent with that law.
--   2. **Wishart matrices** (Definition 4, p. 7). For an $n \times k$ complex matrix $X$, $W = X X^*$.
--   3. **Pure states** (Definition 1, p. 3; eq. (5), p. 5). A pure state of $\mathbb C^m$ is a ray $|\psi\rangle$, i.e. a nonzero vector up to a nonzero scalar factor. Its pure density matrix is
--   $$|\psi\rangle\langle\psi| = \frac{\psi\,\psi^*}{\operatorname{Tr}(\psi\,\psi^*)} = \frac{\psi\,\psi^*}{\|\psi\|^2},$$
--   a Hermitian, idempotent, trace-one matrix (a rank-one orthogonal projection). The map $|\psi\rangle \mapsto |\psi\rangle\langle\psi|$ identifies the space $E_m$ of pure states with the set of such projections.
--   4. **Unitarily invariant law on pure states** (Definition 2, p. 3). A probability measure $\nu$ on matrices, carried by the pure density matrices, that is invariant under every unitary conjugation $\rho \mapsto U\rho U^*$, $U \in U(m)$ (the image of the action $|\psi\rangle \mapsto |U\psi\rangle$).
--   5. **The induced measure $\mu_{n,k}$** (Definition 3, p. 5). For $\mathcal H \otimes \mathcal K = \mathbb C^n \otimes \mathbb C^k$, a random $n\times n$ matrix $\rho$ has law $\mu_{n,k}$ when its law is the image, under the partial trace $\operatorname{Tr}_{\mathcal K}$ over the environment $\mathcal K$, of a unitarily invariant law $\nu_{nk}$ on the pure states of $\mathbb C^n \otimes \mathbb C^k$.
--   6. **Eigenvalues and empirical spectral measure** (eqs. (19), (49), (50)). For an $n\times n$ matrix $A$, its eigenvalues $\lambda_1(A), \dots, \lambda_n(A)$ are counted with multiplicity, and for a scale $s \in \mathbb R$
--   $$L^s(A) = \frac1n \sum_{i=1}^n \delta_{s\,\lambda_i(A)} .$$
--   7. **The Marchenko–Pastur law** (Definition 5, eq. (20), p. 7). For $c > 0$, with $a = (\sqrt c - 1)^2$ and $b = (\sqrt c + 1)^2$,
--   $$\mu_c = \max\{1-c, 0\}\,\delta_0 + \frac{\sqrt{(x-a)(b-x)}}{2\pi x}\,\mathbf 1_{[a,b]}(x)\,dx .$$
--
--   These objects state Theorem 5 (the almost sure Marchenko–Pastur limit of $L^{cn}(\rho_n)$ for $\rho_n \sim \mu_{n,k(n)}$) and every step of its proof: Propositions 1–2, Lemma 1, eqs. (12) and (24), Theorem 2 and Lemma 2.
--
--   **Formalization Note** The complex Gaussian law reuses the published `SpikedWishart.SoftEdge.stdComplexGaussian` (real and imaginary parts independent $N(0,1/2)$), and the partial trace reuses the published `WildeQIT.partialTraceRight`; $\mathbb C^n \otimes \mathbb C^k$ is indexed by `Fin n × Fin k` with the environment as the right factor. Pure states (rays) are represented by their rank-one projections, so a law on $E_m$ is a law on $m\times m$ matrices carried by the set `IsPureDensity`. The induced law is the predicate `HasInducedLaw` ("there is a unitarily invariant law on pure states whose partial trace has the law of $\rho$"); it is well defined because that law is unique (Proposition 1). For $n = 0$ or $k = 0$ there are no pure states and `HasInducedLaw` is false. Eigenvalues are the real parts of the roots, with multiplicity, of the characteristic polynomial (for a Hermitian matrix these are its real eigenvalues); for $n = 0$, $L^s$ is the zero measure. The pinned Mathlib has no measurable structure on matrices, so the file declares the entrywise (product, equivalently Borel) σ-algebra as an instance scoped to `NechitaRDM.MP`. In $\mu_c$, `x / 0 = 0` at $x = 0$ only touches a Lebesgue-null set.
-- source:
--   Nechita, Asymptotics of random density matrices, arXiv:quant-ph/0702154v3, pp. 3–7, Definitions 1–5, eqs. (5), (19), (20)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_SpikedWishart_SoftEdge_Model

namespace NechitaRDM.MP

open MeasureTheory ProbabilityTheory

/-- The Borel σ-algebra on complex (or real) matrices, i.e. the product σ-algebra on the
entries. Scoped to `NechitaRDM.MP`, since the pinned Mathlib has no `MeasurableSpace` instance
on `Matrix`. -/
scoped instance instMeasurableSpaceMatrix {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs (MeasurableSpace (m → n → α))

/-- `N_ℂ(0,1)` (p. 4): `Z = X + iY` with `X, Y` independent real Gaussians of mean `0` and
variance `1/2`. This is the published `SpikedWishart.SoftEdge.stdComplexGaussian`. -/
noncomputable abbrev complexGaussian : Measure ℂ :=
  SpikedWishart.SoftEdge.stdComplexGaussian

/-- A random complex vector `g` has law `N^n_ℂ(0, I_n)` (p. 4): its coordinates are
measurable, mutually independent, and each has law `N_ℂ(0,1)`. -/
def IsComplexGaussianVector {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ}
    (g : Ω → (Fin N → ℂ)) : Prop :=
  (∀ i, Measurable fun ω => g ω i) ∧
  iIndepFun (fun i ω => g ω i) P ∧
  ∀ i, P.map (fun ω => g ω i) = complexGaussian

/-- A random `n × k` complex matrix `X` has i.i.d. `N_ℂ(0,1)` entries (Lemma 1, Definition 4):
its entries are measurable, mutually independent (indexed by `Fin n × Fin k`), and each has
law `N_ℂ(0,1)`. -/
def IsComplexGaussianMatrix {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n k : ℕ}
    (X : Ω → Matrix (Fin n) (Fin k) ℂ) : Prop :=
  (∀ i j, Measurable fun ω => X ω i j) ∧
  iIndepFun (fun (p : Fin n × Fin k) ω => X ω p.1 p.2) P ∧
  ∀ i j, P.map (fun ω => X ω i j) = complexGaussian

/-- The Wishart matrix `W = X · X*` of Definition 4 (p. 7). -/
def wishart {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  X * X.conjTranspose

/-- The pure density matrix of eq. (5), p. 5: `|ψ⟩⟨ψ| = ψ ψ* / Tr(ψ ψ*)`, with
`Tr(ψ ψ*) = ‖ψ‖²`. Entry `(i, j)` is `ψ i * conj (ψ j) / ‖ψ‖²`. (At `ψ = 0` it is `0`.) -/
noncomputable def pureState {ι : Type*} [Fintype ι] (ψ : ι → ℂ) : Matrix ι ι ℂ :=
  (((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ))⁻¹ • Matrix.vecMulVec ψ (star ψ)

/-- `ρ` is a pure density matrix: a rank-one orthogonal projection (Hermitian, idempotent,
trace one). These are exactly the matrices `|ψ⟩⟨ψ|` of eq. (5), and `|ψ⟩ ↦ |ψ⟩⟨ψ|` identifies
the space `E_n` of pure states (rays, Definition 1) with this set. -/
def IsPureDensity {ι : Type*} [Fintype ι] (ρ : Matrix ι ι ℂ) : Prop :=
  ρ.IsHermitian ∧ ρ * ρ = ρ ∧ ρ.trace = 1

/-- A unitarily invariant probability measure on pure states (Definition 2, p. 3), carried by
the pure density matrices: `ν` is a probability measure, almost every `ρ` is a pure density
matrix, and `ν` is invariant under every unitary conjugation `ρ ↦ U ρ U*` (the image of the
action `|ψ⟩ ↦ |Uψ⟩`). -/
def IsPureStateLaw {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : Measure (Matrix ι ι ℂ)) :
    Prop :=
  IsProbabilityMeasure ν ∧ (∀ᵐ ρ ∂ν, IsPureDensity ρ) ∧
  ∀ U ∈ Matrix.unitaryGroup ι ℂ, ν.map (fun ρ => U * ρ * star U) = ν

/-- `ρ` has the induced law `μ_{n,k}` (Definition 3, p. 5): the law of `ρ` is the image of a
unitarily invariant law `ν_{nk}` on pure states of `H ⊗ K = ℂⁿ ⊗ ℂᵏ` (indexed by
`Fin n × Fin k`) under the partial trace over the environment `K` (the right factor). -/
def HasInducedLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (ρ : Ω → Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : Prop :=
  ∃ ν : Measure (Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ),
    IsPureStateLaw ν ∧ P.map ρ = ν.map WildeQIT.partialTraceRight

/-- The eigenvalues of a square complex matrix, with multiplicity: the real parts of the roots
of its characteristic polynomial. For a Hermitian matrix these are its `n` real eigenvalues. -/
noncomputable def eigs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Multiset ℝ :=
  A.charpoly.roots.map Complex.re

/-- The rescaled empirical spectral measure `(1/n) Σᵢ δ_{s λᵢ(A)}` (eqs. (19), (49), (50)). -/
noncomputable def esd {n : ℕ} (s : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) : Measure ℝ :=
  ((n : ENNReal)⁻¹) • ((eigs A).map (fun x => Measure.dirac (s * x))).sum

/-- The left edge `a = (√c − 1)²` of the Marchenko–Pastur law (Definition 5). -/
noncomputable def mpLeft (c : ℝ) : ℝ := (Real.sqrt c - 1) ^ 2

/-- The right edge `b = (√c + 1)²` of the Marchenko–Pastur law (Definition 5). -/
noncomputable def mpRight (c : ℝ) : ℝ := (Real.sqrt c + 1) ^ 2

/-- The Marchenko–Pastur law of Definition 5, eq. (20), p. 7:
`μ_c = max{1 − c, 0} δ₀ + √((x − a)(b − x)) / (2πx) · 1_{[a,b]}(x) dx`. -/
noncomputable def marchenkoPastur (c : ℝ) : Measure ℝ :=
  ENNReal.ofReal (max (1 - c) 0) • Measure.dirac 0 +
    (volume.restrict (Set.Icc (mpLeft c) (mpRight c))).withDensity
      (fun x => ENNReal.ofReal
        (Real.sqrt ((x - mpLeft c) * (mpRight c - x)) / (2 * Real.pi * x)))

end NechitaRDM.MP


