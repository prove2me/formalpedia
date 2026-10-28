-- Prove2me | Definitions.Def_DirectFidelity_RandomState_Setting
-- name    : DirectFidelity_RandomState_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:09.777601+00:00
-- url     : https://prove2.me/theorems/27a4bc37-05ce-4d5d-ab91-1abeb84ead84
-- title:
--   pp. 1, 7 — n-qubit Pauli operators W_k, states in ℂ^d, ⟨ψ|W_k|ψ⟩, the uniform measure on the unit sphere of ℂ^d, and ε, τ, C₁ of Lemma 1
-- statement:
--   This file fixes the setting of Lemma 1 of Flammia and Liu (*Direct fidelity estimation from few Pauli measurements*).
--
--   1. **Qubits and dimension.** A system of $n$ qubits has Hilbert space $\mathbb C^d$ with $d = 2^n$. Its computational basis is indexed by bit strings $x \in \{0,1\}^n$.
--   2. **Pauli operators.** The single-qubit Pauli matrices are
--   $$I = \begin{pmatrix}1&0\\0&1\end{pmatrix},\quad \sigma_x = \begin{pmatrix}0&1\\1&0\end{pmatrix},\quad \sigma_y = \begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad \sigma_z = \begin{pmatrix}1&0\\0&-1\end{pmatrix}.$$
--   A label $k = (k_1,\dots,k_n) \in \{0,1,2,3\}^n$ gives the $n$-qubit Pauli operator $W_k = \sigma_{k_1}\otimes\cdots\otimes\sigma_{k_n}$ (with $\sigma_0 = I$), with matrix entries $(W_k)_{xy} = \prod_i (\sigma_{k_i})_{x_i y_i}$. There are $d^2 = 4^n$ labels; the all-zero label gives $W_k = I$.
--   3. **States and expectations.** A (pure) state is a unit vector $\psi \in \mathbb C^d$, $\|\psi\|_2 = 1$. The overlap $\langle \varphi|\psi\rangle = \sum_x \overline{\varphi_x}\,\psi_x$ is conjugate-linear in $\varphi$, and the Pauli expectation is $\langle\psi|W_k|\psi\rangle = \langle \psi, W_k\psi\rangle$.
--   4. **Haar-random state.** The uniform probability measure on the unit sphere $\{\psi \in \mathbb C^d : \|\psi\|_2 = 1\}$ (a real $(2d-1)$-dimensional sphere): the rotation-invariant surface measure, normalised to total mass $1$.
--   5. **Constants.** For $c \ge 0$,
--   $$\varepsilon = \sqrt{9\pi^3(\log 2)\,c},\qquad \tau = \sqrt{72\pi^3},\qquad C_1 = \frac{2}{9\pi^3},$$
--   with $\log$ the natural logarithm.
--
--   These are the objects of the "First step" of the paper's lower bound for tomography with Pauli measurements: a random state that is nearly orthogonal to given states and has small Pauli expectations.
--
--   **Formalization Note** Basis labels are `Q n = Fin n → Fin 2` and Pauli labels `P n = Fin n → Fin 4`; vectors live in `EuclideanSpace ℂ (Q n)`, and `inner ℂ φ ψ` is Mathlib's inner product, conjugate-linear in the first argument. The sphere measure `unifSphere n` is Mathlib's `Measure.toSphere` of an additive Haar measure on $\mathbb C^d$ viewed as a real vector space, divided by its (finite, positive) total mass; it does not depend on the choice of Haar measure. $d$ is the real number `dim n = 2 ^ n`. The paper writes "$2/9\pi^3$", read as $2/(9\pi^3)$: this is the reading under which (35) and (38) close exactly.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 1, §Fidelity Estimation (n qubits, d = 2ⁿ, Pauli operators W_k); p. 7, Lemma 1 (ε, τ) and (34) (C₁, Haar-random vector)

import Mathlib
import Definitions.Def_DirectFidelity_State_Setting

namespace DirectFidelity.RandomState

open MeasureTheory

/-- The state space `ℂ^d` with its Euclidean (ℓ²) norm and inner product
`⟪φ, ψ⟫_ℂ = ∑ₓ conj (φ x) * ψ x` (conjugate-linear in the first slot, like `⟨φ|ψ⟩`). -/
abbrev E (n : ℕ) : Type := EuclideanSpace ℂ (DirectFidelity.State.Q n)

/-- The Pauli expectation `⟨ψ|W_k|ψ⟩ = ⟪ψ, W_k ψ⟫_ℂ`. -/
noncomputable def pauliExp {n : ℕ} (k : DirectFidelity.State.P n) (ψ : E n) : ℂ :=
  inner ℂ ψ (Matrix.toEuclideanLin (DirectFidelity.State.W k) ψ)

/-- The uniform (normalized Haar / surface) probability measure on the unit sphere of `ℂ^d`,
regarded as the real `(2d-1)`-sphere: Mathlib's surface measure `toSphere` of an additive Haar
measure on `E n` (as a real vector space), divided by its total mass. -/
noncomputable def unifSphere (n : ℕ) : Measure (Metric.sphere (0 : E n) 1) :=
  ((Measure.addHaar : Measure (E n)).toSphere Set.univ)⁻¹ • (Measure.addHaar : Measure (E n)).toSphere

/-- `ε = √(9π³(log 2)c)` of Lemma 1. -/
noncomputable def epsC (c : ℝ) : ℝ := Real.sqrt (9 * Real.pi ^ 3 * Real.log 2 * c)

/-- `τ = √(72π³)` of Lemma 1. -/
noncomputable def tau : ℝ := Real.sqrt (72 * Real.pi ^ 3)

/-- The Levy-lemma constant `C₁ = 2/(9π³)` of (34) and (37). -/
noncomputable def C1 : ℝ := 2 / (9 * Real.pi ^ 3)

end DirectFidelity.RandomState


