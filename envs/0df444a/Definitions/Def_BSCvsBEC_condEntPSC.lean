-- Prove2me | Definitions.Def_BSCvsBEC_condEntPSC
-- name    : BSCvsBEC_condEntPSC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:51.107192+00:00
-- url     : https://prove2.me/theorems/d0596f53-794b-4ae0-a177-9c2f2501db8b
-- title:
--   Pure state channel $\mathrm{PSC}_\theta$ and $H(X\mid \mathrm{PSC}_\theta(X))$
-- statement:
--   The **pure state channel** $\mathrm{PSC}_\theta$, $0\le\theta\le\pi/2$, sends a bit $b\in\mathbb F_2$ to a fixed pure qubit state $|\omega_b\rangle\in\mathbb C^2$, where $|\omega_0\rangle,|\omega_1\rangle$ are unit vectors with $\langle\omega_0|\omega_1\rangle=\cos\theta$ ("$\mathrm{IsPSCPair}$"). In the $n$-fold setting a word $x\in\mathbb F_2^n$ is sent to the product state $|\omega_x\rangle=\bigotimes_{i=1}^n|\omega_{x_i}\rangle$. More generally, a family $(\omega_a)_{a\in\Omega}$ of vectors in $\mathbb C^d$ gives the product vectors $|\omega_x\rangle\in(\mathbb C^d)^{\otimes n}$ for $x\in\Omega^n$.
--
--   Passing a random $X$ with pmf $P$ through the channel gives the classical–quantum state and its output marginal
--   $$\sigma_{XY}=\sum_x P(x)\,|x\rangle\langle x|\otimes|\omega_x\rangle\langle\omega_x|,\qquad \sigma_Y=\sum_x P(x)\,|\omega_x\rangle\langle\omega_x|.$$
--   The **conditional entropy** is
--   $$H(X\mid \mathrm{PSC}(X)) := S(\sigma_{XY})-S(\sigma_Y),$$
--   where $S$ is the von Neumann entropy in bits.
--
--   This is the quantum side of the paper's channel comparison (Theorem 1.3).
--
--   **Formalization Note** $|x\rangle\langle x|$ is a diagonal matrix unit, the tensor product is the Kronecker product with register $X$ first, and $S$ is the published `ShadowTomography.QuantumLB.vnEntropy`. The pairing $\langle u|v\rangle$ is Lean's `inner ℂ u v` (conjugate-linear in $u$). The conditional entropy is defined from the joint state, not from the formula $H(X)-S(\sigma_Y)$; that identity is a separate milestone.
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), §2.1, p.5 (qPSC_θ, n-fold action, σ_XY); p.6 (H(X|Y) := H(XY) − H(Y)); §2.3, eq. (26), p.7

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy

namespace BSCvsBEC

/-- The pair of pure states of the pure state channel `PSC_θ`: unit vectors `|ω₀⟩, |ω₁⟩ ∈ ℂ²` with
`⟨ω₀|ω₁⟩ = cos θ`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.1, p.5: "Let `(|ω_x⟩)_{x∈Ω}`
be some fixed pure states in `𝒴` such that `⟨ω_x|ω_{x'}⟩ = cos θ = ρ` for `x ≠ x'`", with `q = 2`.

**Formalization Note.** `inner ℂ u v` is conjugate-linear in `u`, so it is the bra-ket `⟨u|v⟩`.
The range `0 ≤ θ ≤ π/2` is a hypothesis of each theorem, not part of this predicate. -/
def IsPSCPair (θ : ℝ) (ω : Fin 2 → EuclideanSpace ℂ (Fin 2)) : Prop :=
  (∀ b, ‖ω b‖ = 1) ∧ inner ℂ (ω 0) (ω 1) = (Real.cos θ : ℂ)

/-- The rank-one projector `|v⟩⟨v|`, entry `(i, j)` equal to `v i * conj (v j)`. -/
noncomputable def ketbra {κ : Type*} (v : κ → ℂ) : Matrix κ κ ℂ :=
  Matrix.vecMulVec v (star v)

/-- The `n`-fold product state `|ω_x⟩ = ⨂ᵢ |ω_{xᵢ}⟩` in `(ℂ^d)^{⊗n}`, written in the product basis
indexed by `Fin n → Fin d`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.1, p.5: "in the `n`-fold
setting it maps `x = (x₁, …, xₙ)` to `|ω_x⟩ = ⨂ⁿᵢ₌₁ |ω_{xᵢ}⟩`." -/
noncomputable def pscVec {Ω : Type*} {d n : ℕ} (ω : Ω → EuclideanSpace ℂ (Fin d)) (x : Fin n → Ω) :
    (Fin n → Fin d) → ℂ :=
  fun y => ∏ i, ω (x i) (y i)

/-- The classical–quantum state `σ_XY = ∑ₓ P(x) |x⟩⟨x| ⊗ |v_x⟩⟨v_x|` of an input with pmf `P` and
its pure channel outputs `v_x`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.3, eq. (26), p.7.

**Formalization Note.** `|x⟩⟨x|` is `diagonal (Pi.single x 1)`; the tensor product is
`Matrix.kronecker`, register `X` first. -/
noncomputable def cqState {L κ : Type*} [Fintype L] [DecidableEq L] (P : L → ℝ) (v : L → κ → ℂ) :
    Matrix (L × κ) (L × κ) ℂ :=
  ∑ x, ((P x : ℂ)) • Matrix.kronecker (Matrix.diagonal (Pi.single x 1)) (ketbra (v x))

/-- The channel output state `σ_Y = ∑ₓ P(x) |v_x⟩⟨v_x|` (the marginal of `cqState` on `Y`). -/
noncomputable def outState {L κ : Type*} [Fintype L] (P : L → ℝ) (v : L → κ → ℂ) : Matrix κ κ ℂ :=
  ∑ x, ((P x : ℂ)) • ketbra (v x)

/-- The conditional entropy `H(X | PSC(X)) := H(XY) − H(Y)` (bits) of the state
`σ_XY = ∑ₓ P(x)|x⟩⟨x| ⊗ |ω_x⟩⟨ω_x|`, for a random `X ∈ Ωⁿ` with pmf `P` and a family
`ω : Ω → ℂ^d` of channel states.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.1, p.6 (`H(X|Y) := H(XY) − H(Y)`
"defined for … a state `σ_XY`"), eq. (26), p.7; `H` of a quantum register is the von Neumann entropy
in bits (`ShadowTomography.QuantumLB.vnEntropy`).

**Formalization Note.** Defined from the joint state, not from the formula `H(X) − H(Y)` (that
identity is a milestone). For `PSC_θ`, `Ω = Fin 2`, `d = 2`, and `ω` satisfies `IsPSCPair θ ω`. -/
noncomputable def condEntPSC {Ω : Type} [Fintype Ω] [DecidableEq Ω] {d n : ℕ}
    (ω : Ω → EuclideanSpace ℂ (Fin d)) (P : (Fin n → Ω) → ℝ) : ℝ :=
  ShadowTomography.QuantumLB.vnEntropy (cqState P (pscVec ω)) -
    ShadowTomography.QuantumLB.vnEntropy (outState P (pscVec ω))

end BSCvsBEC


