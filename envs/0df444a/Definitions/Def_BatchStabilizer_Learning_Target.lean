-- Prove2me | Definitions.Def_BatchStabilizer_Learning_Target
-- name    : BatchStabilizer_Learning_Target
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:58.624195+00:00
-- url     : https://prove2.me/theorems/9e4ba270-2b7c-4ab0-929a-7aff810ffad1
-- title:
--   (32), (53), §§3.4, 5.1–5.3 — $F(\rho)$, the analysis target, $\alpha$, $\tilde\beta_\sigma$, $V_{\rm bias}$, $H_2$, $\eta$, $\kappa$, $\Delta(L)$
-- statement:
--   The optimal stabilizer fidelity is $F(\rho)=\max_{P\in\mathrm{Stab}_n}\operatorname{tr}(\rho P)$, where $\mathrm{Stab}_n$ is the published set of pure stabilizer projectors (the Clifford orbit of $|0^n\rangle\langle0^n|$); it is written as the supremum over this finite nonempty set. The label space of a projector $P$ is the span of the labels $u$ with $W_uP=\pm P$. A linear equivalence $C$ of $\mathbb F_2^{2n}$ is the symplectic action of a unitary $U$ if $UW_uU^\dagger=\pm W_{Cu}$ for all $u$ (equation (53)).
--
--   The analysis setup of §5.1 consists of a density matrix $\rho$, an optimal stabilizer projector $P=|\phi^*\rangle\langle\phi^*|$ (so $\operatorname{tr}(\rho P)=F(\rho)$), a unitary $U$ with $UPU^\dagger=|0^n\rangle\langle 0^n|$, and its symplectic action $C$; these data are used only in the analysis and are never inputs of an algorithm. With $\sigma=U\rho U^\dagger$ put $p_x=\sigma_{x,x}$ for $x\in\mathbb F_2^n$ and
--   $$\alpha=\sum_xp_x^2,\qquad\tilde\beta_\sigma(x)=\sum_{z}\beta_\sigma((0,z))(-1)^{z\cdot x},\qquad V_{\rm bias}=\operatorname{span}\{x\neq0:|\tilde\beta_\sigma(x)|>\alpha/2\}.$$
--   Binary entropy is in bits, $H_2(p)=-p\log_2p-(1-p)\log_2(1-p)$ with $0\log_20=0$; $\eta=1-H_2(1/4)$ and $\kappa=6-4\sqrt2$. The Fourier transform of $\nu:\mathbb F_2^n\to\mathbb R$ is $\hat\nu(x)=\sum_u\nu(u)(-1)^{x\cdot u}$.
--
--   For a subspace $L$ with $L_0=CL$, the partial syndrome of $x\in\mathbb F_2^n$ records $z\cdot x$ for the Z-components $z$ of the labels of $L_0$, and the collision excess is
--   $$\Delta(L)=\sum_s\Big(\sum_{x:\,H_{L_0}x=s}p_x\Big)^2-\alpha .$$
--
--   **Formalization Note** The partial syndrome records the values of all Z-functionals of $L_0$ instead of those of a basis $H_{L_0}$; both induce the same partition of $\mathbb F_2^n$, hence the same $\Delta(L)$.
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 9–21 (PDF p. 10–22), equations (1), (32), (53), (57)–(61), Definitions 5.1, 5.5, 5.7, §3.4

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Bell

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
noncomputable section

namespace BatchStabilizer.Learning

open LindbladTolerant.Testing

/-! Stabilizer fidelity, the analysis-only optimal target, and the quantities of §5
(Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), equations (1), (32), (53),
§3.4, §5.1–§5.3, printed pp. 9–21 (PDF pp. 10–22)).  The target data `P, U, C` are
analysis objects only; no algorithm takes them as input. -/

/-- The optimal stabilizer fidelity `F(ρ) = max_{P ∈ Stab_n} tr(ρ P)` (equation (32)),
written as a supremum over the finite nonempty set `Stab_n` of pure stabilizer projectors
(the published `ArbLindbladLearn.Stab`). -/
def stabFidelity {n : ℕ} (ρ : Op (Qubits n)) : ℝ :=
  sSup ((fun P : Op (Qubits n) => (ρ * P).trace.re) '' ArbLindbladLearn.Stab n)

/-- `P = |ϕ*⟩⟨ϕ*|` is a stabilizer projector attaining the optimal fidelity `F(ρ)`. -/
def IsOptimalStab {n : ℕ} (ρ P : Op (Qubits n)) : Prop :=
  P ∈ ArbLindbladLearn.Stab n ∧ (ρ * P).trace.re = stabFidelity ρ

/-- The stabilizer label space of a projector `P`: the span of the labels `u` with
`W_u P = ± P`.  For a stabilizer projector these labels already form a full isotropic
subspace. -/
def labelSpace {n : ℕ} (P : Op (Qubits n)) : Submodule (ZMod 2) (Label n) :=
  Submodule.span (ZMod 2) {u | W u * P = P ∨ W u * P = -P}

/-- `C` is the symplectic action of `U` on Pauli labels: `U W_u U† = ± W_{Cu}` (equation (53)). -/
def IsSymplecticAction {n : ℕ} (U : Op (Qubits n)) (C : Label n ≃ₗ[ZMod 2] Label n) : Prop :=
  ∀ u : Label n, U * W u * Uᴴ = W (C u) ∨ U * W u * Uᴴ = -W (C u)

/-- The analysis setup of §5.1 (printed p. 16): `ρ` is a density matrix, `P = |ϕ*⟩⟨ϕ*|` is a
stabilizer projector attaining `F(ρ)`, `U` is a unitary with `U|ϕ*⟩⟨ϕ*|U† = |0ⁿ⟩⟨0ⁿ|`, and
`C` is the symplectic action of `U`. -/
def TargetSetup {n : ℕ} (ρ P U : Op (Qubits n)) (C : Label n ≃ₗ[ZMod 2] Label n) : Prop :=
  IsDensity ρ ∧ P ∈ ArbLindbladLearn.Stab n ∧ (ρ * P).trace.re = stabFidelity ρ ∧
    U ∈ Matrix.unitaryGroup (Qubits n) ℂ ∧ U * P * Uᴴ = ArbLindbladLearn.zeroProj n ∧
    IsSymplecticAction U C

/-- The computational-basis probability `p_x = σ_{x,x}` of `x ∈ F₂ⁿ`. -/
def compProb {n : ℕ} (σ : Op (Qubits n)) (x : Fin n → ZMod 2) : ℝ :=
  (σ (toQubits x) (toQubits x)).re

/-- The target Bell-coset probability `α = Σ_x p_x²` (Definition 5.1, equation (59)). -/
def alpha {n : ℕ} (σ : Op (Qubits n)) : ℝ := ∑ x : Fin n → ZMod 2, compProb σ x ^ 2

/-- The Z-type label `(0, z)`. -/
def zLabel {n : ℕ} (z : Fin n → ZMod 2) : Label n := (0, z)

/-- The restricted Bell Fourier transform `β̃_σ(x) = Σ_z β_σ((0,z))(-1)^{z·x}` (equation (61)). -/
def tildeBeta {n : ℕ} (σ : Op (Qubits n)) (x : Fin n → ZMod 2) : ℝ :=
  ∑ z : Fin n → ZMod 2, bellProb σ (zLabel z) * signZ (z ⬝ᵥ x)

/-- The strongly biased subspace `V_bias = span{x ≠ 0 : |β̃_σ(x)| > α/2}` (Definition 5.5). -/
def Vbias {n : ℕ} (σ : Op (Qubits n)) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) {x | x ≠ 0 ∧ alpha σ / 2 < |tildeBeta σ x|}

/-- The binary entropy in bits, `H₂(p) = -p log₂ p - (1-p) log₂(1-p)`, with `0 log₂ 0 = 0`. -/
def H2 (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- `η = 1 - H₂(1/4)` (Corollary 5.6). -/
def eta : ℝ := 1 - H2 (1 / 4)

/-- `κ = 6 - 4√2` (Lemma 5.2). -/
def kappa : ℝ := 6 - 4 * Real.sqrt 2

/-- The Fourier transform `ν̂(x) = Σ_u ν(u)(-1)^{x·u}` of a function on `F₂ⁿ` (equation (33)). -/
def binFourier {n : ℕ} (ν : (Fin n → ZMod 2) → ℝ) (x : Fin n → ZMod 2) : ℝ :=
  ∑ u : Fin n → ZMod 2, ν u * signZ (x ⬝ᵥ u)

/-- The partial syndrome of `x ∈ F₂ⁿ` under the Z-checks of `L₀ = C L`: the values `z·x` for
the Z-components `z` of all labels of `L₀` (equivalently, `H_{L₀} x` for a check matrix whose
rows are the Z-components of a basis of `L₀`). -/
def partialSyndrome {n : ℕ} (C : Label n ≃ₗ[ZMod 2] Label n) (L : Submodule (ZMod 2) (Label n))
    (x : Fin n → ZMod 2) : L.map C.toLinearMap → ZMod 2 :=
  fun w => (w : Label n).2 ⬝ᵥ x

open Classical in
/-- The collision excess `Δ(L) = Σ_s (Σ_{x : H_{L₀} x = s} p_x)² - α` (Definition 5.7,
equation (73)), with `σ = UρU†` and `L₀ = C L`. -/
def collisionExcess {n : ℕ} (σ : Op (Qubits n)) (C : Label n ≃ₗ[ZMod 2] Label n)
    (L : Submodule (ZMod 2) (Label n)) : ℝ :=
  (∑ s : L.map C.toLinearMap → ZMod 2,
      (∑ x : Fin n → ZMod 2, if partialSyndrome C L x = s then compProb σ x else 0) ^ 2) -
    alpha σ

end BatchStabilizer.Learning


