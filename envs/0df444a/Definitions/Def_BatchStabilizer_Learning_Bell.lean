-- Prove2me | Definitions.Def_BatchStabilizer_Learning_Bell
-- name    : BatchStabilizer_Learning_Bell
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:37.025665+00:00
-- url     : https://prove2.me/theorems/61fac1a1-7286-43e8-8e05-490953335116
-- title:
--   §4.1, (50)–(51), Def. 7.2, §8.2 — Bell distribution $\beta_\rho$, energy $E(L)$, conditional score $\gamma_L$, Pauli power $\mu$
-- statement:
--   Let $|\Phi\rangle=2^{-n/2}\sum_x|x,x\rangle$ and $|\Phi_m\rangle=(W_m\otimes I)|\Phi\rangle$ for $m\in\mathbb F_2^{2n}$. The Bell distribution of $\rho$ is the Born law of the two-copy Bell measurement,
--   $$\beta_\rho(m)=\langle\Phi_m|(\rho\otimes\rho)|\Phi_m\rangle,$$
--   with symplectic Fourier coefficients $\hat\beta_\rho(u)=\sum_m\beta_\rho(m)(-1)^{\langle m,u\rangle}$. Its normalization is not assumed; it is a consequence of the definitions. For a set $S$ of outcomes $\Pr_{M\sim\beta_\rho}(M\in S)=\sum_{m\in S}\beta_\rho(m)$, and the affine-filter energy of a subspace $L$ is $E(L)=\Pr(M\in A_L)$.
--
--   For a subspace $L$ and a label $u$, the conditional Bell score is
--   $$\gamma_L(u)=\mathbb E_{\beta_\rho}\big[(-1)^{Q(u)+\langle M,u\rangle}\,\big|\,M\in A_L\big]=\frac{\sum_{m\in A_L}\beta_\rho(m)(-1)^{Q(u)+\langle m,u\rangle}}{E(L)}.$$
--   The Pauli-power subprobability is $\mu(u)=2^{-n}(\operatorname{tr}\rho W_u)^2$, with $\mu(J)=\sum_{u\in J}\mu(u)$; its total mass is $\operatorname{tr}(\rho^2)$ and it is not renormalized. A batch $B=(B_1,\dots,B_m)$ of independent Bell records has law $\prod_i\beta_\rho(B_i)$, and $\Pr_B(E)$ denotes the probability of an event about the batch; repeated outcomes are distinct records.
--
--   These are the measurement statistics used by Algorithms 1–3.
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 11–14, 28, 34 (PDF p. 12–15, 29, 35), equations (39), (41), (50)–(51), Definition 7.2 (90), §8.2

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Paulis

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
noncomputable section

namespace BatchStabilizer.Learning

open LindbladTolerant.Testing

/-! Two-copy Bell sampling and the statistics computed from Bell records
(Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), §4.1, printed pp. 11–12
(PDF pp. 12–13); (50)–(51), printed p. 14; Definition 7.2, printed p. 28; §8.2,
printed p. 34). -/

/-- The Bell vector `|Φ_m⟩ = (W_m ⊗ I)|Φ⟩`, `|Φ⟩ = 2^{-n/2} Σ_x |x,x⟩`; its `(x,y)` entry is
`2^{-n/2} (W_m)_{x,y}`. -/
def bellVec {n : ℕ} (m : Label n) : Qubits n × Qubits n → ℂ := fun xy =>
  ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * W m xy.1 xy.2

/-- The Bell distribution `β_ρ(m) = ⟨Φ_m|(ρ ⊗ ρ)|Φ_m⟩` (equation (39)): the Born probability of
outcome `m` of the two-copy Bell measurement on `ρ ⊗ ρ`. -/
def bellProb {n : ℕ} (ρ : Op (Qubits n)) (m : Label n) : ℝ :=
  (star (bellVec m) ⬝ᵥ ((ρ ⊗ₖ ρ) *ᵥ bellVec m)).re

/-- The symplectic Fourier coefficient `β̂_ρ(u) = Σ_m β_ρ(m)(-1)^{⟨m,u⟩}` (equation (41)). -/
def bellFourier {n : ℕ} (ρ : Op (Qubits n)) (u : Label n) : ℝ :=
  ∑ m : Label n, bellProb ρ m * signZ (symp m u)

open Classical in
/-- The Bell probability `Pr_{M∼β_ρ}(M ∈ S)` of a set of outcomes. -/
def bellEventProb {n : ℕ} (ρ : Op (Qubits n)) (S : Set (Label n)) : ℝ :=
  ∑ m : Label n, if m ∈ S then bellProb ρ m else 0

/-- The affine-filter energy `E(L) = Pr_{M∼β_ρ}(M ∈ A_L)` (equations (50)–(51)). -/
def energy {n : ℕ} (ρ : Op (Qubits n)) (L : Submodule (ZMod 2) (Label n)) : ℝ :=
  bellEventProb ρ (affineFilter L)

open Classical in
/-- The conditional Bell score `γ_L(u) = E_{β_ρ}[(-1)^{Q(u)+⟨M,u⟩} | M ∈ A_L]`
(Definition 7.2, equation (90)), as the ratio of the restricted expectation to `E(L)`. -/
def condScore {n : ℕ} (ρ : Op (Qubits n)) (L : Submodule (ZMod 2) (Label n)) (u : Label n) : ℝ :=
  (∑ m : Label n, if m ∈ affineFilter L then bellProb ρ m * signZ (Q u + symp m u) else 0) /
    energy ρ L

/-- The Pauli-power subprobability `μ(u) = 2^{-n} (tr(ρ W_u))²` (§8.2, printed p. 34);
it is not normalized (its total mass is `tr(ρ²)`). -/
def pauliPower {n : ℕ} (ρ : Op (Qubits n)) (u : Label n) : ℝ := (pauliExp ρ u) ^ 2 / 2 ^ n

open Classical in
/-- `μ(J) = Σ_{u ∈ J} μ(u)`. -/
def pauliPowerSet {n : ℕ} (ρ : Op (Qubits n)) (J : Set (Label n)) : ℝ :=
  ∑ u : Label n, if u ∈ J then pauliPower ρ u else 0

open Classical in
/-- `Σ_{t ∈ T} (tr(ρ W_t))²`, the total Pauli power of a label subspace. -/
def pauliPowerSum {n : ℕ} (ρ : Op (Qubits n)) (T : Submodule (ZMod 2) (Label n)) : ℝ :=
  ∑ u : Label n, if u ∈ T then (pauliExp ρ u) ^ 2 else 0

/-- The joint law of a batch `B = (B_1,…,B_m)` of `m` independent Bell records:
`Pr(B) = ∏_i β_ρ(B_i)`. -/
def bellBatchWeight {n m : ℕ} (ρ : Op (Qubits n)) (B : Fin m → Label n) : ℝ :=
  ∏ i, bellProb ρ (B i)

open Classical in
/-- The probability `Pr_B(E)` of an event about a batch of `m` independent Bell records. -/
def bellBatchProb {n : ℕ} (ρ : Op (Qubits n)) (m : ℕ) (E : (Fin m → Label n) → Prop) : ℝ :=
  ∑ B : Fin m → Label n, if E B then bellBatchWeight ρ B else 0

end BatchStabilizer.Learning


