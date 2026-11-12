-- Prove2me | Definitions.Def_QPVEntanglement_afterVerifier
-- name    : QPVEntanglement_afterVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:32:20.707323+00:00
-- url     : https://prove2.me/theorems/ba6babe1-d734-472c-9acf-325c13f40aa3
-- title:
--   The adversarial state after the verifier acts (Lemma 8)
-- statement:
--   Given an earlier record $c$ with probability $p_c$, pure conditional states $|\psi_c\rangle$ on $O\otimes A_0\otimes A_1$ ($O$ the verifier's reference qubits) with the response register $W$ a tensor factor of the sender's side, and a measurement (POVM $\{E_z\}$) of the verifier on $O\otimes W$ whose outcome $z$ is kept as a classical record, after which $O$ and $W$ are removed, the state after the verifier acts is
--
--   $$\rho_+=\sum_{c,z}p_c\,|c,z\rangle\langle c,z|\otimes\mathrm{Tr}_{OW}\big[(E_z\otimes I)|\psi_c\rangle\langle\psi_c|\big],$$
--
--   with the record $(c,z)$ on side $A_0$ (two versions: $W$ on side $A_0$ or on side $A_1$).
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Lemma 8, p.44; proof, App. C.2, pp.74

import Mathlib
import Definitions.Def_QPVEntanglement_flaggedState

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace QPVEntanglement

/-- **The adversarial state after the verifier acts** (Lemma 8, p.44; proof App. C.2, p.74), the
response register `W` on side `A₀`. Behera–Goyal, arXiv:2609.39234 (sha256 bdf2928d…),
Lemma 8, p.44.

Given the earlier record `c` (probability `p c`), the pure conditional state `ψ_c` on
`O × ((W × A₀) × A₁)` (`O` the verifier's reference qubits, `W` the response register on side
`A₀`), and the verifier's measurement, a POVM `{E_z}` on `O × W` whose outcome `z` is kept as a
classical record after which `O` and `W` are removed, the post-measurement state is

`ρ₊ = Σ_{c,z} p_c |c,z⟩⟨c,z| ⊗ Tr_{OW}[(E_z ⊗ I) |ψ_c⟩⟨ψ_c|]`

on `((C × Z) × A₀) × A₁` (unnormalized conditional blocks: their traces are `p(z|c)`); the
record `(c, z)` is placed on side `A₀`. -/
noncomputable def afterVerifier {C Z O W A0 A1 : Type*} [Fintype O] [Fintype W] [DecidableEq C]
    [DecidableEq Z] (p : C → ℝ) (ψ : C → O × ((W × A0) × A1) → ℂ)
    (E : Z → Matrix (O × W) (O × W) ℂ) :
    Matrix (((C × Z) × A0) × A1) (((C × Z) × A0) × A1) ℂ :=
  fun x y => if x.1.1 = y.1.1 then
    (p x.1.1.1 : ℂ) * ∑ u : O × W, ∑ v : O × W,
      E x.1.1.2 u v * ψ x.1.1.1 (v.1, ((v.2, x.1.2), x.2)) * star (ψ x.1.1.1 (u.1, ((u.2, y.1.2), y.2)))
    else 0

/-- As `afterVerifier`, with the response register `W` on side `A₁`: `ψ_c` on
`O × (A₀ × (W × A₁))`, result on `((C × Z) × A₀) × A₁`. -/
noncomputable def afterVerifierRight {C Z O W A0 A1 : Type*} [Fintype O] [Fintype W]
    [DecidableEq C] [DecidableEq Z] (p : C → ℝ) (ψ : C → O × (A0 × (W × A1)) → ℂ)
    (E : Z → Matrix (O × W) (O × W) ℂ) :
    Matrix (((C × Z) × A0) × A1) (((C × Z) × A0) × A1) ℂ :=
  fun x y => if x.1.1 = y.1.1 then
    (p x.1.1.1 : ℂ) * ∑ u : O × W, ∑ v : O × W,
      E x.1.1.2 u v * ψ x.1.1.1 (v.1, (x.1.2, (v.2, x.2))) * star (ψ x.1.1.1 (u.1, (y.1.2, (u.2, y.2))))
    else 0

end QPVEntanglement


