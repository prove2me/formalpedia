-- Prove2me | Definitions.Def_GraphonLabelGame_Kernel
-- name    : GraphonLabelGame_Kernel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:51.149+00:00
-- url     : https://prove2.me/theorems/ee6a694f-f1e2-4e92-9862-de731ba7d944
-- title:
--   Kernels, step kernels $W_\xi$, the strong operator topology, the operator $\mathsf W m(u)$, $\mathcal P_{\mathrm{Unif}}$ and neighborhood empirical measures
-- statement:
--   This module fixes the measure-theoretic layer of Lacker–Soret's label-state graphon games.
--
--   1. **Intervals and step kernels** (2.1). For $n\in\mathbb N$ the unit interval is split into $I^n_i=[(i-1)/n,i/n)$, $i<n$, and $I^n_n=[(n-1)/n,1]$. An $n\times n$ matrix $\xi$ defines the step kernel $W_\xi(u,v)=\xi_{ij}$ for $(u,v)\in I^n_i\times I^n_j$.
--   2. **Kernels.** $W\in L^1_+[0,1]^2$ is a nonnegative, Borel, integrable function on $[0,1]^2$; it need be neither bounded nor symmetric. An **interaction matrix** has nonnegative entries and zero diagonal.
--   3. **Strong operator topology** (§2.2). With $\mathsf W\varphi(u)=\int_0^1W(u,v)\varphi(v)\,dv$ (2.3), kernels $W_n\to W$ in the strong operator topology if $\|\mathsf W_n\varphi-\mathsf W\varphi\|_{L^1[0,1]}\to0$ for every $\varphi\in L^\infty[0,1]$.
--   4. **Uniform first marginal.** $\mathcal P_{\mathrm{Unif}}([0,1]\times E)$ is the set of probability measures on $[0,1]\times E$ whose first marginal is $\mathrm{Unif}[0,1]$, with the topology of weak convergence.
--   5. **The operator on measures** (2.6). For a probability measure $m$ on $[0,1]\times E$,
--   $$\mathsf Wm(u)=\int_{[0,1]\times E}W(u,v)\,\delta_x\,m(dv,dx)\in\mathcal M_+(E),$$
--   so that $\langle\mathsf Wm(u),\varphi\rangle=\int W(u,v)\varphi(x)\,m(dv,dx)$.
--   6. **Neighborhood empirical measures** (3.2), (6.2): $M_i=\frac1n\sum_j\xi_{ij}\delta_{x_j}$.
--   7. The **outer integral** $\mathbb E^*[F]=\inf\{\int g\,d\nu: g\text{ measurable},\ F\le g\ \nu\text{-a.e.}\}$, used to read expectations of possibly non-measurable errors, and the uniform law on the box $I^n_1\times\dots\times I^n_n$.
--   8. The sampling of §6.1: independent pairs $(U^n_i,X^n_i)$ whose law is the conditional law of $(U,X)\sim\mu$ given $\{U\in I^n_i\}$, i.e. $n\,\mu|_{I^n_i\times E}$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Labels are real numbers and kernels are functions on $\mathbb R^2$; only values on $[0,1]$ resp. $[0,1]^2$ enter. $\mathcal M_+(E)$ is Mathlib's `FiniteMeasure E`. $\mathsf Wm(u)$ is set to $0$ at the labels $u$ where its total mass $\int W(u,v)\,m(dv,dx)$ is infinite; for $m\in\mathcal P_{\mathrm{Unif}}$ this is a Lebesgue-null set of labels. The pair $(U,X)$ of §6.1 is not carried by the sampling structure, since the statements depend on it only through its law.
-- source:
--   Lacker, Soret, A Label-State Formulation of Stochastic Graphon Games and Approximate Equilibria on Large Networks, arXiv:2204.09642v1, §1 p.4 (notation, P_Unif), §2 pp.4–5 ((2.1), (2.3), strong operator topology, (2.6)), §3.1 p.7 ((3.2), interaction matrix), §6.1 p.24 ((6.2), the sampling), Theorem 3.6 p.11 (Uⁿᵢ ∼ Unif(Iⁿᵢ))

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GraphonLabelGame

/-- The interval `Iⁿᵢ` of (2.1), with the player index `i : Fin n` counted from `0`:
`Iⁿ_{i+1} = [i/n, (i+1)/n)` for `i + 1 < n`, and the last one is closed,
`Iⁿₙ = [(n−1)/n, 1]`.
Lacker–Soret, arXiv:2204.09642v1, (2.1), p.4.

**Formalization Note** The paper numbers players `1, …, n`; here `i : Fin n` is the paper's
`i + 1`. -/
def I (n : ℕ) (i : Fin n) : Set ℝ :=
  if (i : ℕ) + 1 = n then Icc ((i : ℝ) / n) 1 else Ico ((i : ℝ) / n) (((i : ℝ) + 1) / n)

/-- The step kernel `W_ξ(u, v) := ξᵢⱼ` for `(u, v) ∈ Iⁿᵢ × Iⁿⱼ` of an `n × n` matrix `ξ`
(2.1), p.4.

**Formalization Note** Kernels are functions `ℝ → ℝ → ℝ`; only their values on `[0, 1]²`
enter any statement. Off `[0, 1]²` the step kernel is `0`. -/
noncomputable def stepKernel {n : ℕ} (ξ : Matrix (Fin n) (Fin n) ℝ) (u v : ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ j, if u ∈ I n i ∧ v ∈ I n j then ξ i j else 0

/-- `W ∈ L¹₊[0, 1]²` (§2, p.4): a Borel measurable, nonnegative kernel, integrable on
`[0, 1]²`. Neither boundedness nor symmetry is required.

**Formalization Note** A kernel is a representative `W : ℝ → ℝ → ℝ`; it is taken nonnegative
everywhere (every a.e.-nonnegative element of `L¹` has such a representative, and values
outside `[0, 1]²` never enter). -/
def IsKernelL1Plus (W : ℝ → ℝ → ℝ) : Prop :=
  Measurable (Function.uncurry W) ∧ (∀ u v, 0 ≤ W u v) ∧
    IntegrableOn (Function.uncurry W) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)

/-- The interaction matrix of §3.1 (p.7): nonnegative entries and zero diagonal,
`ξᵢᵢ = 0`. No upper bound is imposed. -/
def IsInteractionMatrix {n : ℕ} (ξ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ ξ i j) ∧ ∀ i, ξ i i = 0

/-- The operator `𝐖φ(u) := ∫₀¹ W(u, v) φ(v) dv` of (2.3), p.5. -/
noncomputable def kernelOp (W : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ v in Icc (0 : ℝ) 1, W u v * φ v

/-- Convergence of kernels `Wₙ → W` in the strong operator topology (§2.2, p.5):
`‖𝐖ₙφ − 𝐖φ‖_{L¹[0,1]} → 0` for every `φ ∈ L^∞[0, 1]`.

**Formalization Note** `φ ∈ L^∞[0, 1]` is a bounded Borel function `ℝ → ℝ` (every essentially
bounded function has a bounded representative, and only its values on `[0, 1]` enter). -/
def SOTConv (Wn : ℕ → ℝ → ℝ → ℝ) (W : ℝ → ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, Measurable φ → (∃ C : ℝ, ∀ v, |φ v| ≤ C) →
    Tendsto (fun n => ∫ u in Icc (0 : ℝ) 1, |kernelOp (Wn n) φ u - kernelOp W φ u|) atTop
      (𝓝 0)

/-- Lebesgue measure on `[0, 1]`, i.e. `Unif[0, 1]` (p.4), as a measure on `ℝ`. -/
noncomputable def lebUnit : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

/-- A measure on `[0, 1] × E` has uniform first marginal (p.4). Labels live in `ℝ`; a measure
whose first marginal is `Unif[0, 1]` is concentrated on `[0, 1] × E`. -/
def IsUnifFirst {E : Type*} [MeasurableSpace E] (m : Measure (ℝ × E)) : Prop :=
  m.map Prod.fst = lebUnit

/-- `P_Unif([0, 1] × E)` (p.4): Borel probability measures on `[0, 1] × E` with uniform first
marginal, with the topology of weak convergence (the subspace topology of
`ProbabilityMeasure (ℝ × E)`). -/
abbrev PUnif (E : Type*) [MeasurableSpace E] :=
  {μ : ProbabilityMeasure (ℝ × E) // IsUnifFirst (μ : Measure (ℝ × E))}

/-- The measure `∫ W(u, v) δₓ m(dv, dx)` of (2.6), p.5, as an (a priori infinite) measure:
the image under `(v, x) ↦ x` of `W(u, v) m(dv, dx)`. -/
noncomputable def WopMeasure {E : Type*} [MeasurableSpace E] (W : ℝ → ℝ → ℝ)
    (m : Measure (ℝ × E)) (u : ℝ) : Measure E :=
  (m.withDensity fun p => ENNReal.ofReal (W u p.1)).map Prod.snd

/-- The measure-valued operator `𝐖m(u) := ∫_{[0,1]×E} W(u, v) δₓ m(dv, dx) ∈ M₊(E)` of (2.6),
p.5, acting by `⟨𝐖m(u), φ⟩ = ∫ W(u, v) φ(x) m(dv, dx)`.

**Formalization Note** `M₊(E)` is Mathlib's `FiniteMeasure E` (weak topology). `𝐖m(u)` is a
finite measure exactly when `∫ W(u, v) m(dv, dx) < ∞`; at the other labels `u` it is set to `0`.
For `m` with uniform first marginal these labels form a Lebesgue-null set (Fubini, p.15), so no
expectation over a uniform label sees the convention. -/
noncomputable def Wop {E : Type*} [MeasurableSpace E] (W : ℝ → ℝ → ℝ) (m : Measure (ℝ × E))
    (u : ℝ) : FiniteMeasure E := by
  classical
  exact if h : IsFiniteMeasure (WopMeasure W m u) then ⟨WopMeasure W m u, h⟩ else 0

/-- The Dirac mass `δₓ` as a finite measure. -/
noncomputable def diracFM {E : Type*} [MeasurableSpace E] (x : E) : FiniteMeasure E :=
  ⟨Measure.dirac x, inferInstance⟩

/-- The neighborhood empirical measure `Mᵢ = (1/n) Σⱼ ξᵢⱼ δ_{xⱼ} ∈ M₊(E)` ((3.2), p.7;
(6.2), p.24).

**Formalization Note** The weights are `Real.toNNReal (ξᵢⱼ / n)`, which equals `ξᵢⱼ / n` for the
nonnegative matrices of the paper. -/
noncomputable def nbhdEmp {E : Type*} [MeasurableSpace E] {n : ℕ}
    (ξ : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → E) (i : Fin n) : FiniteMeasure E :=
  ∑ j, (Real.toNNReal (ξ i j / n)) • diracFM (x j)

/-- The **outer integral** `E*[F] := inf {∫ g dν : g measurable, F ≤ g ν-a.e.}` of a possibly
non-measurable `F ≥ 0`. It equals `∫⁻ F dν` when `F` is measurable and dominates every other
value one could assign to `E[F]`.

**Formalization Note** Used to read `E[εⁿᵢ(Uⁿ)]` in Theorem 3.6 (p.11), whose integrand the
paper never shows to be measurable. -/
noncomputable def outerLIntegral {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (F : X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (g : X → ℝ≥0∞) (_ : Measurable g) (_ : ∀ᵐ x ∂ν, F x ≤ g x), ∫⁻ x, g x ∂ν

/-- The law of `Uⁿ = (Uⁿ₁, …, Uⁿₙ)` with independent `Uⁿᵢ ∼ Unif(Iⁿᵢ)` (Theorem 3.6, p.11):
the uniform probability measure on the box `Iⁿ₁ × ⋯ × Iⁿₙ`. -/
noncomputable def unifBox (n : ℕ) : Measure (Fin n → ℝ) :=
  ((n : ℝ≥0∞) ^ n) • Measure.pi (fun i : Fin n => volume.restrict (I n i))

/-- The sampling of §6.1 (p.24) at stage `n`: random variables `(Uⁿᵢ, Xⁿᵢ)`, `i ∈ [n]`, on one
probability space, mutually independent, with `L(Uⁿᵢ, Xⁿᵢ)` the conditional law of
`(U, X) ∼ μ` given `{U ∈ Iⁿᵢ}`, i.e. `n · μ|_{Iⁿᵢ × E}`.

**Formalization Note** The pair `(U, X) ∼ μ` of §6.1, independent of the sample, is not
carried: the statements of §6 depend on it only through its law `μ`, and an independent copy
can always be adjoined by a product extension. -/
structure Sampling (E : Type*) [MeasurableSpace E] (μ : Measure (ℝ × E)) (n : ℕ) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  Y : Fin n → Ω → ℝ × E
  measY : ∀ i, Measurable (Y i)
  law : ∀ i, P.map (Y i) = (n : ℝ≥0∞) • μ.restrict (I n i ×ˢ univ)
  indep : iIndepFun Y P

attribute [instance] Sampling.mΩ

end GraphonLabelGame


