-- Prove2me | Definitions.Def_SYKCavity_Supplement_IsingModel
-- name    : SYKCavity_Supplement_IsingModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:46:22.111196+00:00
-- url     : https://prove2.me/theorems/39f091cd-cefc-4f32-9863-a7da4918d608
-- title:
--   Ising mixtures (7.1), $Z_N(\beta,J)$ and $\langle\sigma_A\rangle_{\beta,J}$ (7.2), the static transition $\beta^*$, and the SK model
-- statement:
--   Let $P$ be a finite set of interaction orders and $\lambda_p$, $p\in P$, real coefficients. For spins $\sigma\in\{-1,1\}^N$ write $\sigma_A=\prod_{i\in A}\sigma_i$, with $\sigma_\emptyset=1$. The **mixture Hamiltonian** (7.1) is
--   $$H_N(\sigma)=\sum_{p\in P}a_{p,N}\sum_{E\in\binom{[N]}{p}}J_{p,E}\sigma_E,\qquad a_{p,N}=\lambda_p\sqrt{\frac{p!}{2N^{p-1}}},$$
--   with independent standard Gaussian couplings $J_{p,E}$, one for each order $p$ and each $p$-subset $E$ of distinct sites. The partition function and the Gibbs averages (7.2) are
--   $$Z_N(\beta,J)=\sum_{\sigma}e^{\beta H_N(\sigma)},\qquad \langle\sigma_A\rangle_{\beta,J}=\frac{\sum_\sigma\sigma_Ae^{\beta H_N(\sigma)}}{Z_N(\beta,J)}.$$
--   Let $\xi(q)=\tfrac12\sum_{p\in P}\lambda_p^2q^p$ (7.3). The **static transition** $\beta^*$ is the endpoint of the interval, starting at $0$, on which the limiting pressure $\lim_N\frac1N\mathbb E_J\log Z_N(\beta,J)$ equals $\log2+\beta^2\xi(1)/2$. The condition $\beta<\beta^*$ is encoded as: there is $b>\beta$ such that for every $\beta'\in[0,b]$,
--   $$\frac1N\mathbb E_J\log Z_N(\beta',J)\longrightarrow\log2+\frac{\beta'^2\xi(1)}2\qquad(N\to\infty).$$
--   The **Sherrington–Kirkpatrick model** $H_N(\sigma)=N^{-1/2}\sum_{i<j}J_{ij}\sigma_i\sigma_j$ is the instance $P=\{2\}$, $\lambda_2=1$, since $a_{2,N}=N^{-1/2}$.
--
--   These are the models of Theorems 26 and 31.
--
--   **Formalization Note** Spins are Booleans (true $=+1$). The exponent $p-1$ is a natural number, and every order used is at least $2$. The encoding of $\beta<\beta^*$ is equivalent to it and has no junk value when the interval is unbounded.
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), (7.1)–(7.3) and the definition of β*, p.59; SK model, p.66 and (8.5), p.67

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace SYKCavity.Supplement

/-!
# Ising mixtures (7.1), Gibbs averages (7.2), the static transition, and the SK model

A. Schmidhuber, A. Zlokapa, *Polynomial-time algorithms for mean-field models up to the glass
transition*, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5): (7.1)–(7.3) and the definition
of `β*`, p.59; the SK model, p.66 and (8.5), p.67.

**Formalization Note.**
* Spins: `σ : Fin N → Bool`, `true ↦ +1`, `false ↦ −1`; `σ_A = ∏_{i∈A} σ_i`, `σ_∅ = 1`.
* A mixture is a finite set `P ⊆ ℕ` of interaction orders and coefficients `lam : ℕ → ℝ` (only
  `lam p`, `p ∈ P`, are used). Couplings are indexed by `(p, E)` with `p ∈ P` and `E` a `p`-subset
  of distinct sites (`CIdx P N`), with law `⊗ N(0,1)` (`couplingLaw`).
* `coef lam p N = a_{p,N} = λ_p √(p!/(2N^{p−1}))` (natural-number exponent `p − 1`; every order
  used is `≥ 2`). `hamiltonian = H_N(σ) = Σ_e a_e J_e σ_e`, `partitionFn = Z_N(β,J) = Σ_σ e^{βH_N(σ)}`
  (unnormalized, as (7.2)), `gibbsAvg A = ⟨σ_A⟩_{β,J}`.
* `xi P lam q = ξ(q) = ½ Σ_{p∈P} λ_p² q^p`. `meanPressure = (1/N) E_J log Z_N(β,J)`.
* `β*` is the endpoint of the interval (starting at `0`) on which the limiting pressure equals
  `log 2 + β²ξ(1)/2`. `BelowStaticTransition P lam β` encodes `β < β*` as: there is `b > β` such
  that for every `β' ∈ [0, b]`, `(1/N) E_J log Z_N(β', J) → log 2 + β'²ξ(1)/2`. This is
  equivalent to `β < β*` and has no junk value when the interval is unbounded.
* The SK model (`H_N = N^{−1/2} Σ_{i<j} J_ij σ_iσ_j`) is the instance `skOrders = {2}`,
  `skCoeff = 1`: `a_{2,N} = √(2!/(2N)) = N^{−1/2}`.
-/

/-- The value `±1` of a spin (`true ↦ 1`, `false ↦ −1`). -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- `σ_A = ∏_{i∈A} σ_i` (`σ_∅ = 1`). -/
def spinProd {N : ℕ} (σ : Fin N → Bool) (A : Finset (Fin N)) : ℝ :=
  ∏ i ∈ A, spin (σ i)

/-- Coupling indices `(p, E)`: an order `p ∈ P` and a `p`-subset `E` of distinct sites. -/
abbrev CIdx (P : Finset ℕ) (N : ℕ) := Σ p : P, {E : Finset (Fin N) // E.card = p.1}

/-- `a_{p,N} = λ_p √(p!/(2N^{p−1}))`, (7.1). -/
noncomputable def coef (lam : ℕ → ℝ) (p N : ℕ) : ℝ :=
  lam p * Real.sqrt ((p.factorial : ℝ) / (2 * (N : ℝ) ^ (p - 1)))

/-- The mixture Hamiltonian (7.1): `H_N(σ) = Σ_{p∈P} a_{p,N} Σ_{E} J_{p,E} σ_E`. -/
noncomputable def hamiltonian (P : Finset ℕ) (lam : ℕ → ℝ) (N : ℕ) (J : CIdx P N → ℝ)
    (σ : Fin N → Bool) : ℝ :=
  ∑ e : CIdx P N, coef lam e.1.1 N * J e * spinProd σ e.2.1

/-- `Z_N(β, J) = Σ_σ e^{βH_N(σ)}`, (7.2). -/
noncomputable def partitionFn (P : Finset ℕ) (lam : ℕ → ℝ) (N : ℕ) (β : ℝ)
    (J : CIdx P N → ℝ) : ℝ :=
  ∑ σ : Fin N → Bool, Real.exp (β * hamiltonian P lam N J σ)

/-- `⟨σ_A⟩_{β,J} = Σ_σ σ_A e^{βH_N(σ)} / Z_N(β, J)`, (7.2). -/
noncomputable def gibbsAvg (P : Finset ℕ) (lam : ℕ → ℝ) (N : ℕ) (β : ℝ) (J : CIdx P N → ℝ)
    (A : Finset (Fin N)) : ℝ :=
  (∑ σ : Fin N → Bool, spinProd σ A * Real.exp (β * hamiltonian P lam N J σ)) /
    partitionFn P lam N β J

/-- The coupling law: independent standard Gaussians `J_{p,E} ~ N(0,1)`. -/
noncomputable def couplingLaw (P : Finset ℕ) (N : ℕ) : Measure (CIdx P N → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- `ξ(q) = ½ Σ_{p∈P} λ_p² q^p`, (7.3). -/
noncomputable def xi (P : Finset ℕ) (lam : ℕ → ℝ) (q : ℝ) : ℝ :=
  (1 / 2) * ∑ p ∈ P, lam p ^ 2 * q ^ p

/-- The mean pressure `(1/N) E_J log Z_N(β, J)`. -/
noncomputable def meanPressure (P : Finset ℕ) (lam : ℕ → ℝ) (N : ℕ) (β : ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ J, Real.log (partitionFn P lam N β J) ∂couplingLaw P N

/-- `β < β*` (p.59): for some `b > β`, the limiting pressure equals `log 2 + β'²ξ(1)/2` at every
`β' ∈ [0, b]`. -/
def BelowStaticTransition (P : Finset ℕ) (lam : ℕ → ℝ) (β : ℝ) : Prop :=
  ∃ b : ℝ, β < b ∧ ∀ β' ∈ Set.Icc (0 : ℝ) b,
    Tendsto (fun N : ℕ => meanPressure P lam N β') atTop
      (𝓝 (Real.log 2 + β' ^ 2 * xi P lam 1 / 2))

/-- The SK model's single interaction order, `2`. -/
def skOrders : Finset ℕ := {2}

/-- The SK model's coefficient `λ_2 = 1`. -/
def skCoeff : ℕ → ℝ := fun _ => 1

end SYKCavity.Supplement


