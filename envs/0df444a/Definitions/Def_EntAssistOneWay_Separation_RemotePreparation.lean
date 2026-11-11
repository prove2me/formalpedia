-- Prove2me | Definitions.Def_EntAssistOneWay_Separation_RemotePreparation
-- name    : EntAssistOneWay_Separation_RemotePreparation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:30.727195+00:00
-- url     : https://prove2.me/theorems/2c513aa2-d1de-413b-8042-bd0952a3a63a
-- title:
--   Remote preparation of flat states with EPR resources
-- statement:
--   Let $P$ be an orthogonal projector of rank $r$ on $\mathbb C^d$. A protocol with $E$ EPR pairs and $C$ bits gives Alice a POVM $A_z^P$ and Bob a quantum channel $\Lambda_z$ depending only on the message $z$. Define the unnormalised states and branch probabilities by
--   $$\sigma_z=\operatorname{tr}_A[(A_z^P\otimes I)|\Phi_E\rangle\langle\Phi_E|],\quad p_z=\operatorname{tr}\sigma_z,\quad\tau_z=\Lambda_z(\sigma_z).$$
--   The preparation succeeds with tolerance $\varepsilon$ when, for every legal projector,
--   $$\sum_{z:\|\tau_z-p_zP/r\|_1\ge\varepsilon p_z}p_z\le\varepsilon.$$
--
--   This expresses the strict conditional-state error $\|\rho_B-P/r\|_1<\varepsilon$ except with probability at most $\varepsilon$. The norm is full Schatten-1. A zero-probability outcome contributes zero, with no division by $p_z$. Channels and partial traces use the published Wilde definitions, and there is no additional shared random seed.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 19, Definition 3.1 and Theorem 3.5; p. 22, full trace-norm convention

import Definitions.Def_EntAssistOneWay_Separation_Analysis
import Definitions.Def_EntAssistOneWay_Separation_EAProtocol
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_partialTrace

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- An orthogonal projector of the specified rank. -/
def FlatProjector (d r : ℕ) :=
  {P : Matrix (Fin d) (Fin d) ℂ // P.IsHermitian ∧ P * P = P ∧ P.rank = r}

/-- Alice's input is a projector; Bob's channels depend only on her message. -/
structure RemotePreparation (d r E C : ℕ) where
  alice : FlatProjector d r → POVM (Fin (2 ^ E)) (Fin (2 ^ C))
  bob : Fin (2 ^ C) → WildeQIT.QChannel (Fin (2 ^ E)) (Fin d)

/-- Unnormalised conditional state on Bob's EPR register. -/
def remoteSigma {d r E C : ℕ} (P : RemotePreparation d r E C)
    (Q : FlatProjector d r) (z : Fin (2 ^ C)) :
    Matrix (Fin (2 ^ E)) (Fin (2 ^ E)) ℂ :=
  WildeQIT.partialTraceLeft
    (Matrix.kronecker ((P.alice Q).op z) (1 : Matrix (Fin (2 ^ E)) (Fin (2 ^ E)) ℂ) *
      eprDensity E)

/-- The unnormalised final branch state, after Bob's channel. -/
def remoteTau {d r E C : ℕ} (P : RemotePreparation d r E C)
    (Q : FlatProjector d r) (z : Fin (2 ^ C)) : Matrix (Fin d) (Fin d) ℂ :=
  (P.bob z).apply (remoteSigma P Q z)

def remoteProbability {d r E C : ℕ} (P : RemotePreparation d r E C)
    (Q : FlatProjector d r) (z : Fin (2 ^ C)) : ℝ :=
  (remoteSigma P Q z).trace.re

/-- Failure includes equality at the strict trace-error threshold.
Zero-probability branches contribute zero without dividing by their weight. -/
def PreparesFlat {d r E C : ℕ} (P : RemotePreparation d r E C) (ε : ℝ) : Prop :=
  ∀ Q, (∑ z, if ε * remoteProbability P Q z ≤
      traceNorm (remoteTau P Q z - (remoteProbability P Q z / r : ℂ) • Q.val)
    then remoteProbability P Q z else 0) ≤ ε

end

end EntAssistOneWay.Separation


