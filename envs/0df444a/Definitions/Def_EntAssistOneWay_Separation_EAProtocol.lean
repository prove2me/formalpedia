-- Prove2me | Definitions.Def_EntAssistOneWay_Separation_EAProtocol
-- name    : EntAssistOneWay_Separation_EAProtocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:20.121862+00:00
-- url     : https://prove2.me/theorems/582e0d99-9356-4c5c-b830-8f2ea93e3082
-- title:
--   One-way classical protocols using a fixed number of EPR pairs
-- statement:
--   With $E$ shared EPR pairs, the input-independent shared state on two $2^E$-dimensional registers is
--   $$|\Phi_E\rangle=2^{-E/2}\sum_{i=0}^{2^E-1}|i\rangle_A|i\rangle_B.$$
--   A $C$-bit one-way protocol assigns a POVM $\{A_z^x\}_{z<2^C}$ to each Alice input $x$ and a binary effect $B^{y,z}$ to each Bob input and message. Its acceptance probability is
--   $$a(x,y)=\sum_{z<2^C}\langle\Phi_E|A_z^x\otimes B^{y,z}|\Phi_E\rangle.$$
--
--   The matrix formula uses the Kronecker product and the rank-one density matrix of $\Phi_E$. There is no further public coin or shared state. Local private randomness and ancillas are absorbed into the measurements. This is the resource-sensitive model needed for the exact EPR counts.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), pp. 17–18, §3.3 and one-way acceptance formula; pp. 19–22, EPR-resource protocols

import Definitions.Def_EntAssistOneWay_Separation_POVM

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- E EPR pairs, with Alice's and Bob's qubits grouped together. -/
def eprVector (E : ℕ) : (Fin (2 ^ E) × Fin (2 ^ E)) → ℂ :=
  fun i => if i.1 = i.2 then ((Real.sqrt (2 ^ E : ℝ))⁻¹ : ℂ) else 0

/-- The rank-one shared density matrix |Φ_E⟩⟨Φ_E|. -/
def eprDensity (E : ℕ) :
    Matrix (Fin (2 ^ E) × Fin (2 ^ E)) (Fin (2 ^ E) × Fin (2 ^ E)) ℂ :=
  fun i j => eprVector E i * star (eprVector E j)

/-- One-way classical communication using precisely E EPR pairs and C bits.
There is no additional public random seed. -/
structure EAProtocol (X Y : Type) (E C : ℕ) where
  alice : X → POVM (Fin (2 ^ E)) (Fin (2 ^ C))
  bob : Y → Fin (2 ^ C) → BinaryEffect (Fin (2 ^ E))

/-- Born rule on the fixed input-independent EPR state. -/
def eaAccept {X Y : Type} {E C : ℕ} (P : EAProtocol X Y E C)
    (x : X) (y : Y) : ℝ :=
  ∑ z, ((Matrix.kronecker ((P.alice x).op z) (P.bob y z).op * eprDensity E).trace).re

end

end EntAssistOneWay.Separation


