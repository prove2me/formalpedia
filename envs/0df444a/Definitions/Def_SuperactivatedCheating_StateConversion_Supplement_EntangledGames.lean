-- Prove2me | Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_EntangledGames
-- name    : SuperactivatedCheating_StateConversion_Supplement_EntangledGames
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:19:52.134655+00:00
-- url     : https://prove2.me/theorems/f85a7e58-d10d-462f-8285-4dc704ed031b
-- title:
--   Entangled single-round strategies, distinct-game products and the Choi/Bell game
-- statement:
--   This extension imports the published single-round game model without changing it. An assisted strategy chooses arbitrary finite prior private registers, a unit shared pure state, and two local CPTP maps. Its winning probability is the accepting trace after the maps act on the question and shared state. The entangled value is the supremum of these actual probabilities; no attainment is assumed. The binary product tensors two potentially different question vectors and accepting projections and regroups the registers by prover, following the same convention as the published power operation.
--
--   The game $G_{\rm par}(N,M)$ uses a normalized Kraus representation only to purify the channel’s normalized Choi state. Alice receives a coherent classical sample, Bob receives the Choi output register, and the referee retains the copied message, Choi input and purifying environment. Alice returns the input-sized register and Bob returns a message. The projection rejects precisely the canonical Bell outcome together with an incorrect message; it accepts on the whole complementary Bell subspace. The input dimension is the Bell dimension. Validity of the constructed question vector and projection is a conclusion of Lemma 16, not an assumption. The choice of a Kraus purification changes no observable game statistics.
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), §2.1 pp. 11–12; Proposition 8 pp. 14–15; Definition 15 pp. 17–18.

import Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_Protocols

noncomputable section

namespace SuperactivatedCheating.StateConversion.Supplement
open scoped Matrix ComplexConjugate

/-- §2.1 pp.11–12: all finite prior entanglement, with no dimension bound. -/
structure GameStrategy (A B a b : Type) [Fintype A] [Fintype B] [Fintype a] [Fintype b] [DecidableEq A] [DecidableEq B] where
  shared : Shared
  E : Map (A × Fin shared.eA) a
  F : Map (B × Fin shared.eB) b
  hE : QAlgorithms.IsChannel E
  hF : QAlgorithms.IsChannel F

variable {A B R a b : Type} [Fintype A] [Fintype B] [Fintype R] [Fintype a] [Fintype b]
  [DecidableEq A] [DecidableEq B] [DecidableEq R] [DecidableEq a] [DecidableEq b]

def gameWin (G : QuantumGame A B R a b) (S : GameStrategy A B a b) : ℝ :=
  (G.acc * localStep S.E S.F (pureState
    (fun x : (A × Fin S.shared.eA) × (B × Fin S.shared.eB) × R =>
      G.ψ (x.1.1,x.2.1.1,x.2.2) * S.shared.ψ (x.1.2,x.2.1.2)))).trace.re

def entangledValue (G : QuantumGame A B R a b) : ℝ := sSup (Set.range (gameWin G))

/-- §2.1 p.12: product of distinct games, with regrouping by prover. -/
def gameProd {A' B' R' a' b' : Type}
    (G : QuantumGame A B R a b) (H : QuantumGame A' B' R' a' b') :
    QuantumGame (A × A') (B × B') (R × R') (a × a') (b × b') where
  ψ x := G.ψ (x.1.1,x.2.1.1,x.2.2.1) * H.ψ (x.1.2,x.2.1.2,x.2.2.2)
  acc x y := G.acc (x.1.1,x.2.1.1,x.2.2.1) (y.1.1,y.2.1.1,y.2.2.1) *
    H.acc (x.1.2,x.2.1.2,x.2.2.2) (y.1.2,y.2.1.2,y.2.2.2)

/-- Use a channel's finite Kraus representation solely to purify its Choi state. -/
def krausRank (N : Map A B) (hN : QAlgorithms.IsChannel N) : ℕ := hN.choose
def kraus (N : Map A B) (hN : QAlgorithms.IsChannel N) : Fin (krausRank N hN) → Matrix B A ℂ :=
  hN.choose_spec.choose

/-- Definition 15 pp.17–18: coherent classical sampling and a referee-held Choi purification.
The acceptor rejects precisely a Bell success with an incorrect classical answer. -/
def gpar (N : Map A B) (hN : QAlgorithms.IsChannel N) (m : ℕ) :
    QuantumGame (Fin m) B (Fin m × A × Fin (krausRank N hN)) A (Fin m) where
  ψ x := if x.1 = x.2.2.1 then
    kraus N hN x.2.2.2.2 x.2.1 x.2.2.2.1 /
      (Real.sqrt ((m : ℝ) * Fintype.card A) : ℂ) else 0
  acc x y := (if x = y then 1 else 0) -
    (if x.1 = x.2.2.2.1 ∧ y.1 = y.2.2.2.1 ∧
        x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧
        x.2.2.2.2 = y.2.2.2.2 ∧ x.2.1 ≠ x.2.2.1 then
      1 / (Fintype.card A : ℂ) else 0)

end SuperactivatedCheating.StateConversion.Supplement


