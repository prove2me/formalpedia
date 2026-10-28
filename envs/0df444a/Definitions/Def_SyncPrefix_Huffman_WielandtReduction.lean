-- Prove2me | Definitions.Def_SyncPrefix_Huffman_WielandtReduction
-- name    : SyncPrefix_Huffman_WielandtReduction
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-27T07:24:17.911999+00:00
-- url     : https://prove2.me/theorems/bfa89391-7a5e-49dd-8950-c23f1c6695e8
-- title:
--   Corollary 8 (p. 8) — Wielandt code parameter $L$, duplicated-letter transition, and binary decoder automaton $A_B$
-- statement:
--   This definition formalizes the explicit alphabet-reduction construction from the proof of Corollary 8 (Ryzhikov and Szykuła, 2018, p. 8).
--
--   Given a complete deterministic automaton $A_H$ with $n$ states and alphabet size $k \ge 2$, we set the Wielandt code parameter
--
--   $$
--   L(k) = \lfloor \log_2(k - 1) \rfloor + 1,
--   $$
--
--   so that $k \le 2^L < 3 \cdot 2^{L-1} = |Z_L|$. We then extend the transition function of $A_H$ to an alphabet of size $K = |Z_L|$ by duplicating letter $0$ on all indices $b \ge k$, and reindex the tree-substitution decoder $\mathrm{composeDecoder}(\delta_Y, Z_L, e)$ along canonical lexicographical bijections to obtain a concrete binary automaton $A_B = \mathrm{wielandtAB}(A_H)$ with $n \cdot |\mathrm{properPrefixes}(Z_L)|$ states and $2$ input letters.
--
--   This construction provides the explicit target automaton used to reduce Short Sync Word on general Huffman decoders to Short Sync Word on binary Huffman decoders.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 8, proof of Corollary 8

import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Sort
import Definitions.Def_SyncPrefix_Huffman_Constructions

namespace SyncPrefix.Huffman

/-- The codeword length parameter `L = ⌊log₂(k - 1)⌋ + 1` for the Wielandt code in Corollary 8
(Ryzhikov–Szykuła, arXiv:1806.06299v1, p. 8). -/
def wielandtL (k : ℕ) : ℕ :=
  Nat.log 2 (k - 1) + 1

/-- Transition function on `Fin AH.n` over `Fin K` obtained from `AH` by duplicating letter `0`
(for `K ≥ AH.k ≥ 1`; defaults to the identity when `AH.k = 0`). -/
def dupTransition (AH : Automaton) (K : ℕ) (q : Fin AH.n) (b : Fin K) : Fin AH.n :=
  if h : b.val < AH.k then
    AH.δ q ⟨b.val, h⟩
  else if h0 : 0 < AH.k then
    AH.δ q ⟨0, h0⟩
  else
    q

/-- Canonical lexicographical bijection between `Fin (wielandtCode L).card` and `wielandtCode L`. -/
noncomputable def wielandtCodeEquiv (L : ℕ) :
    Fin (wielandtCode L).card ≃ {z // z ∈ wielandtCode L} :=
  ((wielandtCode L).orderIsoOfFin rfl).toEquiv

/-- Canonical bijection between `DecoderState (Fin n) (wielandtCode L)` and
`Fin (n * (properPrefixes (wielandtCode L)).card)`. -/
noncomputable def wielandtStateEquiv (n L : ℕ) :
    DecoderState (Fin n) (wielandtCode L) ≃ Fin (n * (properPrefixes (wielandtCode L)).card) :=
  (Equiv.prodCongr (Equiv.refl (Fin n))
    (((properPrefixes (wielandtCode L)).orderIsoOfFin rfl).toEquiv.symm)).trans finProdFinEquiv

/-- Canonical bijection `Fin 2 ≃ Bool` mapping `0 ↦ false` and `1 ↦ true`. -/
def fin2EquivBool : Fin 2 ≃ Bool where
  toFun a := decide (a.val = 1)
  invFun b := if b then ⟨1, by decide⟩ else ⟨0, by decide⟩
  left_inv a := by fin_cases a <;> rfl
  right_inv b := by cases b <;> rfl

/-- The binary Huffman decoder automaton `AB` constructed from `AH` via `composeDecoder` and the
Wielandt code `wielandtCode (wielandtL AH.k)` (Corollary 8, p. 8). -/
noncomputable def wielandtAB (AH : Automaton) : Automaton :=
  let L := wielandtL AH.k
  let Z := wielandtCode L
  let δY := dupTransition AH Z.card
  let e := wielandtCodeEquiv L
  let es := wielandtStateEquiv AH.n L
  { n := AH.n * (properPrefixes Z).card
    k := 2
    δ := fun s a => es (composeDecoder δY Z e (es.symm s) (fin2EquivBool a)) }

end SyncPrefix.Huffman


