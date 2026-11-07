-- Prove2me | Definitions.Def_ContractionLemma_Splitting_packetInput
-- name    : ContractionLemma_Splitting_packetInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:04:09.925548+00:00
-- url     : https://prove2.me/theorems/6df34fa1-beb3-4988-bff0-88c7e4841a9e
-- title:
--   Packet data and the output word of an entry of a packet tensor
-- statement:
--   These words state the cost clause of Lemma A.12.2. The **packet data** is the word holding $s,a,i$, the point $t$, the bits of the node, the coefficients of $f$, $p'$, the group $g$, for each slot of the packet the level-$i$ symbols of its vertices with the row and column bits read, and the exponents of the packet's modes. The **output word** of an element of $\mathcal O$ at precision $p$ lists its coordinates on $1,U,\dots,U^{\deg f-1}$, each reduced modulo $2^p$ to an integer in $[0,2^p)$, which is the canonical lift of p.96.
--
--   **Formalization Note** The packet data contains no table of the network, which is how the clause "without querying the old tables" is stated. Numbers are in unary, except the output coordinates, which are in binary.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.12.2, p.68; proof pp.90–91; App. A.9.3, p.96 ("Canonical lifts")

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_BipNet
import Definitions.Def_ContractionLemma_Packing
import Definitions.Def_ContractionLemma_NodeField
import Definitions.Def_ContractionLemma_Splitting_modeSet
import Definitions.Def_ContractionLemma_Splitting_childNet

set_option autoImplicit false

namespace ContractionLemma

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Polynomial

namespace Splitting

variable {U W E : Type*} {a : ℕ}

/-- The residue of a rational with odd denominator modulo `2^p`, as an integer in `[0, 2^p)`. -/
def ratResidue (p : ℕ) (q : ℚ) : ℕ :=
  ((q.num : ZMod (2 ^ p)) * ((q.den : ℕ) : ZMod (2 ^ p))⁻¹).val

/-- The word of an element of the node ring at precision `p`: its coordinates on
`1, U, …, U^{deg f − 1}`, each reduced modulo `2^p` to an integer in `[0, 2^p)` (the canonical lift
of p.96), in binary. -/
noncomputable def oWord (f : ℤ[X]) (p : ℕ) (x : NodeField f) : List Bool :=
  Encoding.encodeList countWord
    (List.ofFn fun k : Fin f.natDegree => ratResidue p ((coords f x).coeff k))

/-- The word of one slot of the packet `P`: empty slot, or the level-`i` symbols of the row and
column vertex of the edge there, with the row bit (if the row vertex is in `g`) and the column
bit (if the column vertex is in `g`). -/
noncomputable def slotWord {R : Type*} (G : BipNet U W E R) (pk : Packing U W E a) (i : ℕ)
    (g : Fin 64) (P : Fin pk.np) (Y X : E → Bool) (y : Fin (2 ^ a)) : List Bool := by
  classical
  exact if h : ∃ e, pk.packet e = P ∧ pk.slot e = y then
    Encoding.encodeList id
      [Encoding.encodeNat (pk.rowSym (G.rowOf h.choose) i),
        Encoding.encodeNat (pk.colSym (G.colOf h.choose) i),
        if pk.rowSym (G.rowOf h.choose) i = g then [Y h.choose] else [],
        if pk.colSym (G.colOf h.choose) i = g then [X h.choose] else []]
  else []

/-- The exponent `β_ξ` of the mode `ξ_{P,y₀,b}` (`0` if `(P, y₀, b)` is not a mode). -/
noncomputable def betaAt [Fintype E] {R : Type*} {G : BipNet U W E R} {pk : Packing U W E a}
    {i p' : ℕ} (β : Mode G pk i p' → ℕ) (P : Fin pk.np) (y₀ : Fin (2 ^ (i + 1))) (b : Fin p') : ℕ := by
  classical
  exact if h : (P, y₀, b) ∈ modeSet G pk i p' then β ⟨(P, y₀, b), h⟩ else 0

/-- **The packet data** handed to the algorithm that computes an entry of a packet tensor (cost
clause of Lemma A.12.2, p.68): `s`, `a`, `i`, the point `t` (as `t + 2^a`), the bits of the node, the
coefficients of `f` (in `{0, 1}`), `p′`, the group `g`, the slots of the packet `P` (`slotWord`:
symbols and the bits read), and the exponents of the modes of `P`. Numbers are in unary.

**Formalization Note.** The word contains no table of the network, which is the clause "without
querying the old tables". -/
noncomputable def packetInput [Fintype E] (s : ℕ) (f : ℤ[X]) (G : BipNet U W E (NodeField f))
    (pk : Packing U W E a) (t : ℤ) (i : ℕ) (b : Fin f.natDegree → Bool) (p' : ℕ) (g : Fin 64)
    (β : Mode G pk i p' → ℕ) (P : Fin pk.np) (Y X : E → Bool) : List Bool :=
  Encoding.encodeList id
    [Encoding.encodeNat s, Encoding.encodeNat a, Encoding.encodeNat i,
      Encoding.encodeNat (t + 2 ^ a).toNat, List.ofFn b,
      List.ofFn (fun k : Fin (f.natDegree + 1) => decide (f.coeff k = 1)),
      Encoding.encodeNat p', Encoding.encodeNat g,
      Encoding.encodeList (slotWord G pk i g P Y X) (List.finRange (2 ^ a)),
      Encoding.encodeList
        (fun y₀ : Fin (2 ^ (i + 1)) =>
          Encoding.encodeList (fun b' : Fin p' => Encoding.encodeNat (betaAt β P y₀ b'))
            (List.finRange p'))
        (List.finRange (2 ^ (i + 1)))]

end Splitting

end ContractionLemma


