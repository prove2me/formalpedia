-- Prove2me | Definitions.Def_EntAssistOneWay_Separation_Supplement_OneWayEA
-- name    : EntAssistOneWay_Separation_Supplement_OneWayEA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:49:38.844536+00:00
-- url     : https://prove2.me/theorems/07a4cdd9-1cbd-4ea4-b670-e497688ee4ef
-- title:
--   One-way entanglement-assisted protocols with an arbitrary shared state
-- statement:
--   A **one-way entanglement-assisted protocol** with $C$ bits from Alice to Bob consists of a shared density matrix $\rho$ on $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$ fixed before the inputs; for each input $x$ of Alice, a POVM $\{M^x_z\}_{z\in\{0,1\}^C}$ on her register, whose outcome $z$ she sends; and for each input $y$ of Bob and message $z$, a binary effect $0\preceq N^{y,z}\preceq I$ on his register. The acceptance probability is
--
--   $$\Pr[\text{output }1\mid x,y]=\sum_{z\in\{0,1\}^C}\operatorname{Re}\operatorname{tr}\big((M^x_z\otimes N^{y,z})\,\rho\big).$$
--
--   This generalizes the published one-way model with a fixed number of EPR pairs to an arbitrary, possibly mixed, shared state, as in the one-way part of Theorem 3.4.
--
--   **Formalization Note** Messages are indexed by `Fin (2^C)`; POVMs and binary effects are the published `POVM` and `BinaryEffect`.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), pp. 17–18, §3.3 and the one-way part of the proof of Theorem 3.4

import Definitions.Def_EntAssistOneWay_Separation_POVM
import Definitions.Def_WildeQIT_IsDensityOperator

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation.Supplement

noncomputable section

/-- §3.3, pp. 17–18: a one-way entanglement-assisted protocol with `C` bits from Alice to
Bob and an arbitrary shared density matrix on `ℂ^{dA} ⊗ ℂ^{dB}` (not only EPR pairs).
Alice measures a POVM with `2^C` outcomes depending on `x` and sends the outcome `z`;
Bob measures a binary effect depending on `(y, z)`; outcome `1` means accept. -/
structure OneWayEAProtocol (X Y : Type) (dA dB C : ℕ) where
  state : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ
  density : WildeQIT.IsDensityOperator state
  alice : X → POVM (Fin dA) (Fin (2 ^ C))
  bob : Y → Fin (2 ^ C) → BinaryEffect (Fin dB)

/-- Born rule: `∑_z Re tr((M^x_z ⊗ N^{y,z}) ρ)`. -/
def oneWayAccept {X Y : Type} {dA dB C : ℕ} (P : OneWayEAProtocol X Y dA dB C)
    (x : X) (y : Y) : ℝ :=
  ∑ z, ((Matrix.kronecker ((P.alice x).op z) (P.bob y z).op * P.state).trace).re

end

end EntAssistOneWay.Separation.Supplement


