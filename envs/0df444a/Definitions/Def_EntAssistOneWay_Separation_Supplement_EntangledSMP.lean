-- Prove2me | Definitions.Def_EntAssistOneWay_Separation_Supplement_EntangledSMP
-- name    : EntAssistOneWay_Separation_Supplement_EntangledSMP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:50:29.370356+00:00
-- url     : https://prove2.me/theorems/c19684d3-2709-4f60-9831-a5fb96df52e3
-- title:
--   Entanglement-assisted SMP protocols on qubit registers
-- statement:
--   An **entanglement-assisted SMP protocol** with $q$ qubits per player consists of a shared density matrix $\rho$ on $\mathbb C^{2^q}\otimes\mathbb C^{2^q}$, fixed before the inputs; for each input $x$ of Alice a POVM $\{A^x_\alpha\}_{\alpha\in\{0,1\}^{c_A}}$ on her register, and for each input $y$ of Bob a POVM $\{B^y_\beta\}_{\beta\in\{0,1\}^{c_B}}$ on his; and a deterministic referee $R(\alpha,\beta)\in\{0,1\}$ that sees only the two messages. The acceptance probability is
--
--   $$\Pr[\text{accept}\mid x,y]=\sum_{\alpha,\beta:\,R(\alpha,\beta)=1}\operatorname{Re}\operatorname{tr}\big((A^x_\alpha\otimes B^y_\beta)\,\rho\big).$$
--
--   Each player's measurement depends only on its own input, so the messages are simultaneous. The cost is $c_A+c_B$ bits.
--
--   **Formalization Note** The referee is deterministic, as in the protocol of Appendix A; only Alice and Bob share entanglement.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 17, §3.3 (entangled SMP model); pp. 42–44, Appendix A

import Definitions.Def_EntAssistOneWay_Separation_POVM
import Definitions.Def_WildeQIT_IsDensityOperator

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation.Supplement

noncomputable section

/-- §3.3, p. 17, and Appendix A, pp. 42–44: an entanglement-assisted SMP protocol.
Alice and Bob share a density matrix on `q` qubits each, fixed before the inputs; each
measures a POVM on its own register depending only on its own input, and sends the outcome
(`cA`, resp. `cB` bits) to a deterministic referee, which sees only the two messages. -/
structure EntangledSMPProtocol (X Y : Type) (q cA cB : ℕ) where
  state : Matrix (Fin (2 ^ q) × Fin (2 ^ q)) (Fin (2 ^ q) × Fin (2 ^ q)) ℂ
  density : WildeQIT.IsDensityOperator state
  alice : X → POVM (Fin (2 ^ q)) (Fin (2 ^ cA))
  bob : Y → POVM (Fin (2 ^ q)) (Fin (2 ^ cB))
  referee : Fin (2 ^ cA) → Fin (2 ^ cB) → Bool

/-- Acceptance probability `∑_{α,β : R(α,β)} Re tr((A^x_α ⊗ B^y_β) ρ)`. -/
def entangledSMPAccept {X Y : Type} {q cA cB : ℕ} (P : EntangledSMPProtocol X Y q cA cB)
    (x : X) (y : Y) : ℝ :=
  ∑ α, ∑ β, if P.referee α β then
    ((Matrix.kronecker ((P.alice x).op α) ((P.bob y).op β) * P.state).trace).re else 0

end

end EntAssistOneWay.Separation.Supplement


