-- Prove2me | Definitions.Def_QAlgorithms_Defs_Ensemble
-- name    : QAlgorithms_Defs_Ensemble
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:51:07.830212+00:00
-- url     : https://prove2.me/theorems/f2892e8c-9ad5-4517-aaa3-84172597503c
-- title:
--   POVMs, tensor powers, state identification, von Neumann entropy (shared definition layer)
-- statement:
--   POVMs, tensor powers, state identification, von Neumann entropy (shared definition layer)
--
--   ### QAlgorithms.IsPOVM
--
--   This is a predicate on a family $M = (M_o)_{o \in O}$ of complex square matrices indexed by $\iota \times \iota$. Here $O$ (the outcome set) and $\iota$ (the basis index set) are arbitrary finite types, and $\iota$ has decidable equality.
--
--   $\mathrm{IsPOVM}(M)$ holds exactly when both of the following are true:
--
--   1. Every $M_o$ is positive semidefinite in Mathlib's sense, which includes being Hermitian: $M_o^* = M_o$ and $\langle v, M_o v\rangle \ge 0$ for all $v \in \mathbb{C}^\iota$.
--   2. The matrices sum to the identity:
--   $$\sum_{o \in O} M_o = I_\iota.$$
--
--   Edge cases:
--
--   - If $O$ is empty and $\iota$ is nonempty, the sum is the zero matrix, so the predicate cannot hold.
--   - If $\iota$ is empty, every family satisfies it trivially.
--
--   ### QAlgorithms.povmEventProb
--
--   Inputs:
--
--   - finite types $O$ and $\iota$;
--   - an arbitrary family of complex matrices $M = (M_o)_{o\in O}$ on $\iota\times\iota$;
--   - an arbitrary complex matrix $\rho$ on $\iota \times \iota$;
--   - a decidable predicate $P$ on $O$.
--
--   The value is the real number
--   $$\sum_{o \in O,\ P(o)} \operatorname{Re}\operatorname{tr}(M_o\,\rho).$$
--   Each summand is $\mathrm{effectProb}(M_o,\rho) = \operatorname{Re}\operatorname{tr}(M_o \rho)$.
--
--   No hypothesis is imposed: $M$ need not be a POVM and $\rho$ need not be a density matrix. If no outcome satisfies $P$, the value is $0$.
--
--   ### QAlgorithms.tensorPow
--
--   Given a natural number $T$ and a vector $\psi \in \mathbb{C}^\iota$ (any index type $\iota$, no normalization assumed), $\psi^{\otimes T}$ is the vector indexed by tuples $z = (z_0,\dots,z_{T-1}) \in \iota^T$ with coordinates
--   $$\big(\psi^{\otimes T}\big)_z = \prod_{i=0}^{T-1} \psi_{z_i}.$$
--
--   For $T = 0$, the index set $\iota^0$ has a single element, and the unique coordinate is the empty product $1$.
--
--   ### QAlgorithms.ensembleSuccess
--
--   Inputs:
--
--   - finite types $O$ and $\iota$;
--   - real weights $p = (p_i)_{i\in O}$;
--   - vectors $\psi = (\psi_i)_{i \in O}$ in $\mathbb{C}^\iota$;
--   - matrices $M = (M_i)_{i\in O}$ on $\iota\times\iota$.
--
--   The ensemble and the measurement share the same index set $O$; outcome $i$ is paired with state $i$. The value is
--   $$\sum_{i \in O} p_i \,\operatorname{Re}\operatorname{tr}\!\big(M_i\, |\psi_i\rangle\langle\psi_i|\big).$$
--   Here $|\psi_i\rangle\langle\psi_i|$ is $\mathrm{pureDensity}(\psi_i)$, the matrix with $(a,b)$ entry $\psi_i(a)\,\overline{\psi_i(b)}$.
--
--   No hypotheses are imposed: the $p_i$ need not be nonnegative or sum to $1$, the $\psi_i$ need not be unit vectors, and $M$ need not be a POVM.
--
--   ### QAlgorithms.optSuccess
--
--   The inputs are the same as for $\mathrm{ensembleSuccess}$ minus the measurement: finite types $O$ and $\iota$ (with decidable equality on $\iota$), real weights $(p_i)_{i\in O}$, and vectors $(\psi_i)_{i\in O}$ in $\mathbb{C}^\iota$. The value is the real supremum
--   $$\sup_{M \,:\, \mathrm{IsPOVM}(M)} \ \sum_{i\in O} p_i\,\operatorname{Re}\operatorname{tr}\!\big(M_i\,|\psi_i\rangle\langle\psi_i|\big).$$
--
--   - The supremum ranges over all POVMs $M = (M_i)_{i\in O}$: each $M_i$ positive semidefinite and $\sum_i M_i = I$.
--   - The outcome set of the POVM equals the index set $O$ of the ensemble.
--   - This is the supremum of reals in Mathlib's convention. It equals $0$ when no POVM exists, which happens when $O$ is empty and $\iota$ is nonempty. It would also equal $0$ for a set unbounded above.
--   - No constraints are placed on $p$ or $\psi$.
--
--   ### QAlgorithms.pgmSuccess
--
--   The inputs are finite types $O$ and $\iota$ (with decidable equality on $\iota$), real weights $(p_i)_{i\in O}$, and vectors $(\psi_i)_{i\in O}$ in $\mathbb{C}^\iota$. Construct the following:
--
--   - The rescaled vectors $\psi'_i = \sqrt{p_i}\,\psi_i$, where $\sqrt{\cdot}$ is the real square root with $\sqrt{x} = 0$ for $x < 0$.
--   - The Hermitian matrix
--   $$\rho = \sum_{i\in O} |\psi'_i\rangle\langle\psi'_i|, \qquad \text{with } (a,b) \text{ entry } \sum_i \psi'_i(a)\,\overline{\psi'_i(b)}.$$
--   - The matrix $\rho^{-1/2}$, obtained by applying $g(x) = (\sqrt{x})^{-1}$ to the eigenvalues of $\rho$ via the continuous functional calculus. Because $\sqrt{x} = 0$ for $x \le 0$ and $0^{-1} = 0$, $g$ sends eigenvalue $0$ to $0$. So $\rho^{-1/2}$ is the inverse square root on the support of $\rho$ and zero on its kernel.
--
--   The value is
--   $$\sum_{i\in O} p_i\,\big|\langle \rho^{-1/2}\psi'_i,\ \psi_i\rangle\big|^2.$$
--   The inner product $\langle u, v\rangle = \sum_a \overline{u_a}\,v_a$ is conjugate-linear in the first argument.
--
--   No hypotheses are imposed on $p$ or $\psi$: no nonnegativity, normalization or linear independence.
--
--   ### QAlgorithms.vnEntropy
--
--   For a finite type $\iota$ with decidable equality and a complex matrix $\rho$ on $\iota\times\iota$, the value is
--   $$S(\rho) = -\operatorname{Re}\operatorname{tr}\big(h(\rho)\big),$$
--   where $h(x) = x\log_2 x$ is applied through the continuous functional calculus.
--
--   The function $h$ uses Mathlib's real logarithm, which has $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$. Hence:
--
--   - $h(0) = 0$;
--   - $h(x) = x\log_2 x$ for $x>0$;
--   - $h(x) = x\log_2|x|$ for $x<0$.
--
--   The value depends on whether $\rho$ is Hermitian:
--
--   - **Hermitian $\rho$:** with eigenvalues $\lambda_1,\dots,\lambda_{|\iota|}$ counted with multiplicity,
--   $$S(\rho) = -\sum_k h(\lambda_k).$$
--   - **Non-Hermitian $\rho$:** the functional calculus returns the zero matrix by convention, so $S(\rho) = 0$.
--
--   No hypothesis that $\rho$ is a density matrix is imposed.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Ensemble.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Adiabatic
/-!
# POVMs, tensor powers, state identification, von Neumann entropy (shared definition layer)

S. Arunachalam, *Quantum Algorithms and Learning Theory* (PhD thesis, 2018), cited
"Arunachalam p.N" (PDF pages), and S. Arunachalam, R. de Wolf, *A survey of quantum learning
theory* (2017), cited "survey p.N" (PDF pages).

Conventions: a measurement with finite outcome set `O` is a family of positive semidefinite
matrices summing to the identity (`IsPOVM`); outcome `o` on a density matrix `ρ` has probability
`Re Tr(M_o ρ)` (frozen `effectProb`), and a pure state `ψ` enters as `pureDensity ψ = |ψ⟩⟨ψ|`.
Matrix functions of Hermitian matrices are Mathlib's continuous functional calculus `cfc` (a real
function applied to the eigenvalues; every function is continuous on the finite spectrum).
-/

namespace QAlgorithms

open scoped ComplexConjugate ComplexOrder

/-- Survey p.3 (§2.1), Arunachalam p.159 (§7.3.2): an `O`-outcome POVM on the space indexed by
`ι` is a family `{M_o}_{o ∈ O}` of positive semidefinite matrices with `∑_o M_o = I`. -/
def IsPOVM {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι] (M : O → Matrix ι ι ℂ) : Prop :=
  (∀ o, (M o).PosSemidef) ∧ ∑ o, M o = 1

/-- Survey p.3 and p.7 (§3.2), Arunachalam p.128 (§6.3.2): the probability that measuring the
density matrix `ρ` with the POVM `M` gives an outcome in the event `P`,
`∑_{o ∈ P} Tr(M_o ρ)` (real part, frozen `effectProb`). -/
noncomputable def povmEventProb {O ι : Type*} [Fintype O] [Fintype ι] (M : O → Matrix ι ι ℂ)
    (ρ : Matrix ι ι ℂ) (P : O → Prop) [DecidablePred P] : ℝ :=
  ∑ o ∈ Finset.univ.filter P, effectProb (M o) ρ

/-- Arunachalam p.163 (§7.4.1), survey pp.13–14 (§4.2): the `T`-fold tensor power
`|ψ⟩^{⊗T}` of a vector `ψ` indexed by `ι`, as the vector indexed by `Fin T → ι` (copy `i` is the
`i`-th factor) with coordinates `z ↦ ∏_i ψ(z_i)`. At `T = 0` it is the unit vector of the
one-point space. -/
noncomputable def tensorPow {ι : Type*} (T : ℕ) (ψ : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (Fin T → ι) :=
  WithLp.toLp 2 fun z => ∏ i, ψ (z i)

/-- Arunachalam p.159 (§7.3.2), survey p.5 (§2.3): the average success probability
`P_M(E) = ∑_i p_i ⟨ψ_i|M_i|ψ_i⟩` of the POVM `M` (indexed by the same finite set `O` as the
ensemble) in identifying the states of the ensemble `E = {(p_i, |ψ_i⟩)}_{i ∈ O}`. -/
noncomputable def ensembleSuccess {O ι : Type*} [Fintype O] [Fintype ι] (p : O → ℝ)
    (ψ : O → EuclideanSpace ℂ ι) (M : O → Matrix ι ι ℂ) : ℝ :=
  ∑ i, p i * effectProb (M i) (pureDensity (ψ i))

/-- Arunachalam p.159 (§7.3.2), survey p.5 (§2.3): `P^opt(E) = max_M P_M(E)`, the optimal
average success probability over all `|O|`-outcome POVMs `M`. The set of values is bounded
(each `⟨ψ_i|M_i|ψ_i⟩ ∈ [0, ‖ψ_i‖²]`), and nonempty whenever `O` is nonempty (put `I` on one
outcome); the junk value `0` occurs only for an empty ensemble, which `∑ p_i = 1` excludes. -/
noncomputable def optSuccess {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι] (p : O → ℝ)
    (ψ : O → EuclideanSpace ℂ ι) : ℝ :=
  ⨆ M : {M : O → Matrix ι ι ℂ // IsPOVM M}, ensembleSuccess p ψ M.1

/-- Arunachalam p.159 (§7.3.2): the success probability of the pretty good measurement,
`P^PGM(E) = ∑_i p_i |⟨ν_i|ψ_i⟩|²`, where `ψ'_i = √p_i ψ_i`, `ρ = ∑_i |ψ'_i⟩⟨ψ'_i|` and
`ν_i = ρ^{−1/2} ψ'_i`, the inverse square root taken over the non-zero eigenvalues of `ρ`
(here `cfc (x ↦ (√x)⁻¹) ρ`, which sends the eigenvalue `0` to `0` since `(√0)⁻¹ = 0` in Lean).
The PGM's operators are `|ν_i⟩⟨ν_i|`. -/
noncomputable def pgmSuccess {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι] (p : O → ℝ)
    (ψ : O → EuclideanSpace ℂ ι) : ℝ :=
  let ψ' : O → EuclideanSpace ℂ ι := fun i => (Real.sqrt (p i) : ℂ) • ψ i
  let ρ : Matrix ι ι ℂ := ∑ i, pureDensity (ψ' i)
  ∑ i, p i * ‖inner ℂ (act (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) ρ) (ψ' i)) (ψ i)‖ ^ 2

/-- Arunachalam p.159 (§7.3.1): the von Neumann entropy in bits, `S(ρ) = −Tr(ρ log ρ)` with
`log` to base 2 (so that the uniform distribution on `{0,1}^d` has entropy `d`, p.156), computed
as `−Re Tr(f(ρ))` for `f(x) = x log₂ x` (`0 log 0 = 0`, since `Real.logb 2 0 = 0`). Junk: `cfc`
returns `0` on a non-Hermitian argument; statements carry `IsDensityMatrix`. -/
noncomputable def vnEntropy {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) : ℝ :=
  -(cfc (fun x : ℝ => x * Real.logb 2 x) ρ).trace.re

/-! ### Sanity tests -/

example : IsPOVM (fun _ : Unit => (1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
  ⟨fun _ => Matrix.PosSemidef.one, by simp⟩

example {ι : Type*} (ψ : EuclideanSpace ℂ ι) (z : Fin 0 → ι) : tensorPow 0 ψ z = 1 := by
  simp [tensorPow]

example {ι : Type*} (ψ : EuclideanSpace ℂ ι) (z : Fin 1 → ι) : tensorPow 1 ψ z = ψ (z 0) := by
  simp [tensorPow]

theorem povmEventProb_true {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι]
    {M : O → Matrix ι ι ℂ} (hM : IsPOVM M) {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    povmEventProb M ρ (fun _ => True) = 1 := by
  have h : ∑ o, effectProb (M o) ρ = ((∑ o, M o) * ρ).trace.re := by
    simp only [effectProb, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  simp only [povmEventProb, Finset.filter_true, h, hM.2, one_mul, hρ.2, Complex.one_re]

example {O ι : Type*} [Fintype O] [Fintype ι] (p : O → ℝ) (ψ : O → EuclideanSpace ℂ ι) :
    ensembleSuccess p ψ 0 = 0 := by
  simp [ensembleSuccess, effectProb]

example {O ι : Type*} [Fintype O] [Fintype ι] [DecidableEq ι] (ψ : O → EuclideanSpace ℂ ι) :
    pgmSuccess 0 ψ = 0 := by
  simp [pgmSuccess]

example {ι : Type*} [Fintype ι] [DecidableEq ι] : vnEntropy (1 : Matrix ι ι ℂ) = 0 := by
  simp [vnEntropy, cfc_one]

end QAlgorithms


