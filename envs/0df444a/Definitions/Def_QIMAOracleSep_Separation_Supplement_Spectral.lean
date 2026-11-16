-- Prove2me | Definitions.Def_QIMAOracleSep_Separation_Supplement_Spectral
-- name    : QIMAOracleSep_Separation_Supplement_Spectral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:33:33.76237+00:00
-- url     : https://prove2.me/theorems/258fba7a-90ec-4373-b2a5-66f0781a6f02
-- title:
--   Rayleigh maxima, operator-norm bounds, Hadamard-test operators and spectral projectors
-- statement:
--   General finite-dimensional matrix notions used by the supplement. Let $\iota$ be a finite index set and $A, H, P, Q, U$ complex $\iota\times\iota$ matrices; $\|v\|^2=\sum_i|v_i|^2$.
--
--   1. $P$ is an **orthogonal projector** when $P^\dagger=P$ and $P^2=P$.
--   2. The **Rayleigh maximum** of $H$ is $\sup\{\operatorname{Re}\langle v,Hv\rangle : \|v\|=1\}$; for Hermitian $H$ it is $\lambda_{\max}(H)$.
--   3. For projectors $P, Q$, the **compressed maximum** is $\sup\{\operatorname{Re}\langle v,Qv\rangle:\|v\|=1,\ Pv=v\}=\lambda_{\max}(PQP|_{\operatorname{im}P})$.
--   4. $\|A\|_{\mathrm{op}}\le\delta$ is expressed as $\delta\ge0$ and $\|Av\|^2\le\delta^2\|v\|^2$ for every $v$.
--   5. The **Hadamard-test operator** of $U$ is
--   $$E(U)=\frac{2I+U+U^\dagger}{4},$$
--   which is Hermitian for every $U$; for unitary $U$ and a unit vector $\psi$, $\langle\psi,E(U)\psi\rangle$ is the probability that the Hadamard test of $U$ accepts $\psi$.
--   6. For Hermitian $H$ and real $\mu$, the **spectral projector** $1_{\{\mu\}}(H)$ is the orthogonal projector onto the $\mu$-eigenspace of $H$ (the zero matrix if $\mu$ is not an eigenvalue), computed from an eigendecomposition $H=U\,\mathrm{diag}(\lambda)\,U^\dagger$.
--   7. The **selective phase** of a projector is $e^{i\theta P}=I+(e^{i\theta}-1)P$.
--   8. The two scalar functions of the paper:
--   $$G_\theta(\lambda)=\frac{1+\sqrt{1-(1-\lambda)^2\sin^2\theta}}{2},\qquad f_L(a)=\frac{1+\cos\!\big(\arccos(2a-1)/L\big)}{2}.$$
--
--   These notions carry Lemmas 3.9, 4.1 and 4.4.
--
--   **Formalization Note** On an empty index set the suprema are over empty sets and evaluate to $0$; every theorem using them has a nonempty index set (a nonzero projector, or the $2^w$ basis states of $w$ wires). The phase formula is the exact exponential of an orthogonal projector.
--
--   Differences from the source: none.
-- source:
--   Itay Shalit, Mark Zhandry, The Commuting Local Hamiltonian Problem: Relativized Evidence Against BQP-Hardness, STOC 2027 submission #144 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/144.pdf, Section 3.5, p. 30 (E(U), 1_J(H), footnote 13); Lemma 4.1, p. 34, (34)–(41); Section 4.2, p. 39 (µ(U)); Lemma 4.4, (81)

import Mathlib

set_option autoImplicit false

namespace QIMAOracleSep.Separation.Supplement

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Squared Euclidean norm of a finite complex vector. -/
noncomputable def vecNormSq (v : ι → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

/-- An orthogonal projector: self-adjoint and idempotent. -/
def IsOrthProjector (P : Matrix ι ι ℂ) : Prop := Pᴴ = P ∧ P * P = P

/-- Largest value of the Rayleigh quotient `⟨v, H v⟩` over unit vectors; for a Hermitian `H`
this is `λ_max(H)`. On an empty index type the set is empty and the value is `0`. -/
noncomputable def rayleighMax (H : Matrix ι ι ℂ) : ℝ :=
  sSup {r : ℝ | ∃ v : ι → ℂ, vecNormSq v = 1 ∧ r = (star v ⬝ᵥ (H *ᵥ v)).re}

/-- `λ_max(P Q P |_{im P})` for orthogonal projectors `P, Q`: the largest value of `⟨v, Q v⟩` over
unit vectors `v` in the image of `P`. -/
noncomputable def compressedMax (P Q : Matrix ι ι ℂ) : ℝ :=
  sSup {r : ℝ | ∃ v : ι → ℂ, vecNormSq v = 1 ∧ P *ᵥ v = v ∧ r = (star v ⬝ᵥ (Q *ᵥ v)).re}

/-- `‖A‖_op ≤ δ`, stated without choosing a norm instance: `δ ≥ 0` and
`‖A v‖² ≤ δ² ‖v‖²` for every vector `v`. -/
def OpNormLE (A : Matrix ι ι ℂ) (δ : ℝ) : Prop :=
  0 ≤ δ ∧ ∀ v : ι → ℂ, vecNormSq (A *ᵥ v) ≤ δ ^ 2 * vecNormSq v

/-- The accepting POVM element of the Hadamard test of `U`: `E(U) = (2I + U + U†)/4`. -/
noncomputable def hadamardTestOperator (U : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 4 : ℂ) • ((2 : ℂ) • (1 : Matrix ι ι ℂ) + U + Uᴴ)

omit [Fintype ι] in
theorem hadamardTestOperator_isHermitian (U : Matrix ι ι ℂ) :
    (hadamardTestOperator U).IsHermitian := by
  unfold hadamardTestOperator Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose]
  have h4 : star (1 / 4 : ℂ) = 1 / 4 := by simp
  have h2 : star (2 : ℂ) = 2 := by simp
  rw [h4, h2, add_assoc, add_comm Uᴴ U, ← add_assoc]

/-- The spectral projector `1_{μ}(H)` of a Hermitian matrix onto its `μ`-eigenspace (the zero
matrix when `μ` is not an eigenvalue), written through Mathlib's eigendecomposition
`H = U diag(λ) U†`. It does not depend on the chosen eigenbasis. -/
noncomputable def spectralProjector (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (μ : ℝ) :
    Matrix ι ι ℂ :=
  (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
    Matrix.diagonal (fun i => if hH.eigenvalues i = μ then (1 : ℂ) else 0) *
    star (hH.eigenvectorUnitary : Matrix ι ι ℂ)

/-- The exact selective phase shift `e^{iθP} = I + (e^{iθ} - 1) P` of an orthogonal projector `P`. -/
noncomputable def phaseShift (θ : ℝ) (P : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  1 + (Complex.exp ((θ : ℂ) * Complex.I) - 1) • P

/-- `G_θ(λ) = (1 + √(1 - (1-λ)² sin² θ))/2`, equation (39). -/
noncomputable def smallPhaseG (θ x : ℝ) : ℝ :=
  (1 + Real.sqrt (1 - (1 - x) ^ 2 * Real.sin θ ^ 2)) / 2

/-- `f_L(a) = (1 + cos(arccos(2a-1)/L))/2`, equation (81). -/
noncomputable def cyclicClockF (L : ℕ) (a : ℝ) : ℝ :=
  (1 + Real.cos (Real.arccos (2 * a - 1) / L)) / 2

end QIMAOracleSep.Separation.Supplement


