-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Supplement_extDynamics
-- name    : AutoQMem_Lindblad_Supplement_extDynamics
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:45:42.544571+00:00
-- url     : https://prove2.me/theorems/e8523b07-b185-4acb-9099-e16f7a7c6023
-- title:
--   Register and data Pauli noise, propagators, and the register-reduced data channel
-- statement:
--   **Pauli noise on data and registers** is the generator
--   $$\mathcal L^{\mathrm{ext}}_{\mathrm{noise}}(t)=\sum_i\sum_{P\in\{X,Y,Z\}}\gamma_{P,i}(t)\,\mathcal D[P_i]+\sum_{j\in\mathrm{Reg}}\sum_{P\in\{X,Y,Z\}}\gamma^{\mathrm{reg}}_{P,j}(t)\,\mathcal D[P_j];$$
--   it is **of rate $\eta$** if $0\le\gamma_{P,i}(t),\gamma^{\mathrm{reg}}_{P,j}(t)\le\eta$ for all $t\ge0$, with measurable time dependence. The **propagator** $W_*(t,0)$ of a time-dependent generator $\mathcal G(t)$ solves
--   $$W_*(t,0)\rho=\rho+\int_0^t\mathcal G(s)\big(W_*(s,0)\rho\big)\,ds\qquad(t\ge0).$$
--   The **register-reduced data channel** of an evolution $W$ prepares the registers in $|0\rangle$ and traces them out:
--   $$\rho\ \mapsto\ \operatorname{Tr}_{\mathrm{reg}}\,W\big(\rho\otimes|0\rangle\langle0|_{\mathrm{reg}}\big).$$
--
--   These define the evolution and the effective logical channel in Theorem 4.
--
--   **Formalization Note** Time-dependent noise rates are allowed (Remark 2.26: "covered verbatim"); constant rates are a special case. The propagator is the base mission's integrated form of the master equation (Reading R1), entrywise, with the integrand required to be integrable.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), eq. (180), p. 53 (PDF p. 55); Definition 7.7, eq. (194), p. 56 (PDF p. 58); Remark 2.26, p. 21 (PDF p. 23); eq. (40), p. 21 (PDF p. 23); eq. (183) and Corollary 7.3, p. 53 (PDF p. 55)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_Supplement_Registers
import Definitions.Def_WildeQIT_partialTrace
open Matrix

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

variable {n : ℕ} (R : Registers n)

/-- **Pauli noise on the data qubits and the registers.** Drechsler, Oreg, Aharonov, *Autonomous
Quantum Memories from Classical Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03),
eq. (180), p. 53 (PDF 55), with eq. (36) of Definition 2.25, p. 21:
`L^ext_noise = Σ_i Σ_{P∈{X,Y,Z}} γ_{P,i} D[P_i] + Σ_{j∈Reg_X⊔Reg_Z} Σ_{P∈{X,Y,Z}} γ^reg_{P,j} D[P_j]`.

**Formalization Note.** Time-dependent rates `γ(t)` are allowed (Remark 2.26, p. 21: "Rates
γ_{P,i}(t) that are measurable and locally bounded in t are covered verbatim … Section 7 uses the
rates only through the bound η := sup_{t≥0} max_{i,P} γ_{P,i}(t)"); constant rates are a special
case. The values `γ t .I i` are not used. -/
noncomputable def extNoiseGen (γ : ℝ → Pauli1 → Fin n → ℝ) (γreg : ℝ → Pauli1 → R.Reg → ℝ)
    (t : ℝ) (ρ : R.Op) : R.Op :=
  (∑ i, ∑ P ∈ ({.X, .Y, .Z} : Finset Pauli1),
      ((γ t P i : ℝ) : ℂ) • dissG (R.extData (pauliAt P i)) ρ) +
    ∑ j, ∑ P ∈ ({.X, .Y, .Z} : Finset Pauli1), ((γreg t P j : ℝ) : ℂ) • dissG (R.regPauli P j) ρ

/-- **Local Pauli noise of rate η on the code qubits and the registers** (Definition 7.7, eq. (194),
p. 56, PDF 58: "0 ≤ γ_{P,i} ≤ η and 0 ≤ γ^reg_{P,j} ≤ η for every P ∈ {X, Y, Z}, every data qubit i,
and every register qubit j"), with measurable time dependence (Remark 2.26). -/
def IsNoiseOfRate (η : ℝ) (γ : ℝ → Pauli1 → Fin n → ℝ) (γreg : ℝ → Pauli1 → R.Reg → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ P, P ≠ .I → ∀ i, 0 ≤ γ t P i ∧ γ t P i ≤ η) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ P, P ≠ .I → ∀ j, 0 ≤ γreg t P j ∧ γreg t P j ≤ η) ∧
  (∀ P i, Measurable fun t : Set.Ici (0 : ℝ) => γ t P i) ∧
  (∀ P j, Measurable fun t : Set.Ici (0 : ℝ) => γreg t P j)

/-- **Schrödinger propagator `W_*(t, 0)` of a time-dependent generator** `G(t)` on a
finite-dimensional space (§2.2.1, eq. (40), p. 21, PDF 23: "d/dt W_*(t, t′) = L(t) W_*(t, t′),
W_*(t′, t′) = id"), as in the base mission's `IsPropagator` (Reading R1): for every `t ≥ 0` and
every `ρ`, entrywise, `s ↦ G(s)(W s ρ)` is interval integrable on `[0, t]` and
`W t ρ = ρ + ∫₀ᵗ G(s)(W s ρ) ds`. -/
def IsPropagatorOf {κ : Type} [Fintype κ] (G W : ℝ → Matrix κ κ ℂ → Matrix κ κ ℂ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ (ρ : Matrix κ κ ℂ) (x y : κ),
    IntervalIntegrable (fun s => G s (W s ρ) x y) MeasureTheory.volume 0 t ∧
      W t ρ x y = ρ x y + ∫ s in (0 : ℝ)..t, G s (W s ρ) x y

/-- **The data channel with registers prepared in `|0⟩` and traced out**: `ρ ↦ Tr_reg W(ρ ⊗ |0⟩⟨0|_reg)`
(§7.1, eq. (183), p. 53: "The registers are initialized in the state |0⟩, independently of the
encoded data"; Corollary 7.3: "the effective logical channel obtained by preparing the registers in
|0⟩ at encoding and tracing them out at readout").

**Formalization Note.** `Tr_reg` is the platform's `WildeQIT.partialTraceRight` on
`H^ext = H ⊗ (ℂ²)^{⊗Reg}`; the effective logical channel is then the base `LogicalQubit.effective`
of this data map. -/
noncomputable def reducedMap (W : R.Op → R.Op) (ρ : AutoQMem.Lindblad.Op n) :
    AutoQMem.Lindblad.Op n :=
  WildeQIT.partialTraceRight (W (Matrix.kronecker ρ (Matrix.single 0 0 1)))

end AutoQMem.Lindblad.Supplement


