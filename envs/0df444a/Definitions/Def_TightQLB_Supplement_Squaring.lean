-- Prove2me | Definitions.Def_TightQLB_Supplement_Squaring
-- name    : TightQLB_Supplement_Squaring
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:21:36.412567+00:00
-- url     : https://prove2.me/theorems/c81c6bab-34a5-4358-9e89-6d14cb926908
-- title:
--   The squaring algorithm $\mathsf{Sq}_m$, the moments $M_j$, the collision distribution $r_p$, the three ensembles
-- statement:
--   In each ensemble the oracle gives **access for state preparation and reflection**: a unit vector $|\psi_\omega\rangle\in\mathbb C^N$ whose computational-basis measurement has distribution $p_\omega$, prepared with one query, and the reflection $2|\psi_\omega\rangle\langle\psi_\omega|-I$ with two. In the Fourier ensemble $|\psi_f\rangle=\sum_z\hat f(z)|z\rangle$ ($\kappa_2=3$); with the canonical oracle $|\psi_\phi\rangle=|\phi\rangle$, and with unitary access $|\psi_U\rangle=U|0^n\rangle$ ($\kappa_2=2$). Put
--
--   $$
--   M_j=N^{j-1}\sum_zp_z^j,\qquad r_p(z)=\frac{p_z^2}{\sum_yp_y^2},\qquad \mathrm{TV}(a,b)=\frac12\sum_z|a(z)-b(z)| .
--   $$
--
--   **The squaring algorithm** $\mathsf{Sq}_m$ (Definition 6.1). Let $m\ge1$ with $P_\star=\kappa_2m/N\le1/4$, $\vartheta_0=\arcsin\sqrt{P_\star}$, $\ell$ a nonnegative integer nearest to $\pi/(4\vartheta_0)-1/2$.
--
--   1. Prepare and measure $m$ copies of $|\psi_\omega\rangle$, obtaining $Y_1,\dots,Y_m$; store $S=\{Y_1,\dots,Y_m\}$.
--   2. Prepare one more copy.
--   3. Apply $\ell$ times $(2|\psi_\omega\rangle\langle\psi_\omega|-I)(I-2\Pi_S)$, $\Pi_S=\sum_{z\in S}|z\rangle\langle z|$.
--   4. Measure in the computational basis and output $Z$.
--
--   It makes $m+1+2\ell$ queries. The module defines its output distribution $a_\omega(z)=\Pr[Z=z\mid\omega]$, $\mathbb E_\omega\mathrm{TV}(a_\omega,r_{p_\omega})$, and its expected score $\mathbb E_\omega\sum_za_\omega(z)Np_\omega(z)$.
--
--   The algorithm approximately samples the collision distribution, whose score tends to $5$ (Fourier) and $3$ (Haar), with $O(N^{1/3})$ queries (Theorems 6.6, 6.9).
--
--   **Formalization Note** The output distribution is computed from the four steps for the prepared state $\psi=|\psi_\omega\rangle$: an average over the $m$ independent outcomes with law $|\psi|^2$, then the amplification, then the Born rule. An ensemble is the law $\nu$ of $|\psi_\omega\rangle$ with its $\kappa_2$ (`IsEnsemble`), and $\mathbb E_\omega$ is $\int\cdot\,d\nu$; the Fourier law is the uniform mixture over the $2^N$ sign functions. "Nearest integer" is the predicate `IsNearestNat`.
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §6, Eq. (49), §6.1, pp. 45–46 (PDF pp. 48–49); Definition 6.1, p. 47 (PDF p. 50); Lemma 6.5(iv), p. 49 (PDF p. 52)

import Mathlib
import Definitions.Def_TightQLB_Supplement_UnitaryAccess
open QAlgorithms MeasureTheory
open scoped Matrix ENNReal

set_option autoImplicit false

namespace TightQLB.Supplement

/-!
# The squaring algorithm `Sq_m`, the moments `M_j`, the collision distribution

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…), §6, Eq. (49), p.46
(PDF p.49); §6.1, p.46 (PDF p.49); Definition 6.1, p.47 (PDF p.50); Lemma 6.5(iv), p.49
(PDF p.52).

"In each case the oracle provides access for state preparation and reflection. That is, there is a
unit vector `|ψ_ω⟩ ∈ C^N` whose computational-basis measurement has distribution `p_ω`, one query
prepares `|ψ_ω⟩`, and two queries implement the reflection `2|ψ_ω⟩⟨ψ_ω| − I`." Fourier:
`|ψ_f⟩ = U_f|0ⁿ⟩ = Σ_z f̂(z)|z⟩`; canonical oracle: `|ψ_ϕ⟩ = |ϕ⟩`; unitary access: `|ψ_U⟩ = U|0ⁿ⟩`.
"`κ_j = j!` in the two Haar cases … in the Fourier ensemble, `κ_j = (2j − 1)!!`."
`M_j = N^{j−1} Σ_z p_z^j`, `r_p(z) = p_z²/Σ_y p_y²` (49).

Definition 6.1: "Let `m ≥ 1` be such that `P⋆ = κ₂m/N ≤ 1/4`, let `ϑ₀ = arcsin √P⋆`, let `ℓ` be a
nonnegative integer nearest to `π/(4ϑ₀) − 1/2`, and put `L = 2ℓ + 1`. 1. Prepare and measure `m`
copies of `|ψ_ω⟩`, obtaining outcomes `Y₁, …, Y_m`, and store the set `S = {Y₁, …, Y_m}`.
2. Prepare one more copy of `|ψ_ω⟩`. 3. Apply `ℓ` times, to the copy prepared in step 2, the
operator `(2|ψ_ω⟩⟨ψ_ω| − I)(I − 2Π_S)`, where `Π_S = Σ_{z∈S} |z⟩⟨z|`. 4. Measure this copy in the
computational basis and output the outcome `Z`." "The number of queries is `m + 1 + 2ℓ`."

**Formalization Note.**
* The algorithm is stated through its access for state preparation and reflection, as §6.1 does:
  the output distribution `a_ω` of `Sq_m` depends on the oracle only through `|ψ_ω⟩`, and
  `sqOut m ℓ ψ z` is `Pr[Z = z]` computed from the four steps (an average over the `m` measured
  outcomes, then the `ℓ` amplification steps, then the Born rule). The three identities of §6.1
  show that the queries implement exactly these two operations.
* An ensemble is the law `ν` of `|ψ_ω⟩` with its constant `κ₂` (`IsEnsemble`): the Fourier law
  (uniform over the `2^N` sign functions `f = (−1)^{fb}`, `κ₂ = 3`), the Haar law on unit vectors
  (canonical oracle, `κ₂ = 2`), or the law of `U|0ⁿ⟩` under a Haar-random `U` (unitary access,
  `κ₂ = 2`). `E_ω g(p_ω)` is `∫ g ∂ν`.
* "A nonnegative integer nearest to `x`" is `IsNearestNat x ℓ`; every theorem holds for each such
  choice.
-/

variable {n : ℕ}

/-- §6.1, p.46 (PDF p.49): `|ψ_f⟩ = U_f|0ⁿ⟩ = Σ_z f̂(z)|z⟩`, with `f = (−1)^{fb}`. -/
noncomputable def fourierState (fb : Qubits n → Bool) : EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 (fun z => ((fhat fb z : ℝ) : ℂ))

/-- The law of `|ψ_f⟩` for a uniformly random sign function. -/
noncomputable def fourierLaw (n : ℕ) : Measure (EuclideanSpace ℂ (Qubits n)) :=
  ((Fintype.card (Qubits n → Bool) : ℝ≥0∞)⁻¹) • ∑ fb : Qubits n → Bool, Measure.dirac (fourierState fb)

/-- The law of the oracle `f = (−1)^{fb}` of the Fourier ensemble: uniform over the `2^N` bit
functions `fb` (§3.1, p.13, PDF p.16). -/
noncomputable def fourierOracleLaw (n : ℕ) : Measure (Qubits n → Bool) :=
  (PMF.uniformOfFintype (Qubits n → Bool)).toMeasure

/-- The law of `|ψ_U⟩ = U|0ⁿ⟩` under `μ`. -/
noncomputable def unitaryLaw (μ : Measure (Qubits n → Qubits n → ℂ)) :
    Measure (EuclideanSpace ℂ (Qubits n)) :=
  μ.map unitaryState

/-- The three forms of access of §6.1 with their constant `κ₂` (`3` in the Fourier ensemble, `2`
for the canonical oracle and for unitary access). -/
def IsEnsemble (n : ℕ) (ν : Measure (EuclideanSpace ℂ (Qubits n))) (κ₂ : ℝ) : Prop :=
  (ν = fourierLaw n ∧ κ₂ = 3) ∨ (ν = haar n ∧ κ₂ = 2) ∨
    (∃ μ, IsHaarUnitaryLaw μ ∧ ν = unitaryLaw μ ∧ κ₂ = 2)

/-- Eq. (49): the normalized moment `M_j = N^{j−1} Σ_z p_z^j`. -/
noncomputable def moment (j : ℕ) (p : Qubits n → ℝ) : ℝ :=
  ((2 : ℝ) ^ n) ^ (j - 1) * ∑ z, p z ^ j

/-- Eq. (49): the collision distribution `r_p(z) = p_z²/Σ_y p_y²`. -/
noncomputable def collision (p : Qubits n → ℝ) (z : Qubits n) : ℝ :=
  p z ^ 2 / ∑ y, p y ^ 2

/-- Lemma 6.5(iv), p.49 (PDF p.52): `TV(a, b) = (1/2) Σ_z |a(z) − b(z)|`. -/
noncomputable def tv (a b : Qubits n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ z, |a z - b z|

/-- `Π_S = Σ_{z∈S} |z⟩⟨z|`. -/
noncomputable def projS (S : Finset (Qubits n)) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.diagonal fun z => if z ∈ S then 1 else 0

/-- The reflection `2|ψ⟩⟨ψ| − I`. -/
noncomputable def reflect (ψ : EuclideanSpace ℂ (Qubits n)) : Matrix (Qubits n) (Qubits n) ℂ :=
  (2 : ℂ) • Matrix.vecMulVec (fun z => ψ z) (fun z => star (ψ z)) - 1

/-- Step 3 of Definition 6.1: `((2|ψ⟩⟨ψ| − I)(I − 2Π_S))^ℓ ψ`. -/
noncomputable def ampState (ψ : EuclideanSpace ℂ (Qubits n)) (S : Finset (Qubits n)) (ℓ : ℕ) :
    Qubits n → ℂ :=
  (reflect ψ * (1 - (2 : ℂ) • projS S)) ^ ℓ *ᵥ (fun z => ψ z)

/-- The output distribution `a_ω(z) = Pr[Z = z | ω]` of `Sq_m` with `ℓ` amplification steps, for
the prepared state `ψ = |ψ_ω⟩`: the stored outcomes `Y₁, …, Y_m` are independent with law
`p = |ψ|²`, `S = {Y₁, …, Y_m}`. -/
noncomputable def sqOut (m ℓ : ℕ) (ψ : EuclideanSpace ℂ (Qubits n)) (z : Qubits n) : ℝ :=
  ∑ y : Fin m → Qubits n, (∏ i, pOf ψ (y i)) *
    ‖ampState ψ (Finset.univ.image y) ℓ z‖ ^ 2

/-- Definition 6.1: the number of queries `m + 1 + 2ℓ` of `Sq_m`. -/
def sqQueries (m ℓ : ℕ) : ℕ := m + 1 + 2 * ℓ

/-- `ℓ` is a nonnegative integer nearest to `x`. -/
def IsNearestNat (x : ℝ) (ℓ : ℕ) : Prop :=
  ∀ k : ℕ, |(ℓ : ℝ) - x| ≤ |(k : ℝ) - x|

/-- Definition 6.1: `ϑ₀ = arcsin √P⋆` with `P⋆ = κ₂m/N`. -/
noncomputable def theta0 (n : ℕ) (κ₂ : ℝ) (m : ℕ) : ℝ :=
  Real.arcsin (Real.sqrt (κ₂ * m / (2 : ℝ) ^ n))

/-- Definition 6.1: `ℓ` is a nonnegative integer nearest to `π/(4ϑ₀) − 1/2`. -/
def IsSqSteps (n : ℕ) (κ₂ : ℝ) (m ℓ : ℕ) : Prop :=
  IsNearestNat (Real.pi / (4 * theta0 n κ₂ m) - 1 / 2) ℓ

/-- `E_ω TV(a_ω, r_{p_ω})` for `Sq_m` in the ensemble `ν`. -/
noncomputable def sqTV (ν : Measure (EuclideanSpace ℂ (Qubits n))) (m ℓ : ℕ) : ℝ :=
  ∫ ψ, tv (sqOut m ℓ ψ) (collision (pOf ψ)) ∂ν

/-- The expected score `E_ω Σ_z a_ω(z) N p_ω(z)` of `Sq_m` in the ensemble `ν`. -/
noncomputable def sqScore (ν : Measure (EuclideanSpace ℂ (Qubits n))) (m ℓ : ℕ) : ℝ :=
  ∫ ψ, ∑ z, sqOut m ℓ ψ z * ((2 : ℝ) ^ n * pOf ψ z) ∂ν

end TightQLB.Supplement


