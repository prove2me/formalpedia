-- Prove2me | Definitions.Def_SignFreeOracle_Separation_Encoding
-- name    : SignFreeOracle_Separation_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:23.816189+00:00
-- url     : https://prove2.me/theorems/710e1b65-9656-47d0-8f79-80bc92e0ea34
-- title:
--   Boolean block encodings and exact power-of-two normalization
-- statement:
--   A multibit graph query is encoded by the vertex bit length, the vertex's fixed-length binary label, a neighbour position and an output-bit position. Natural fields are self-delimiting unary strings; malformed addresses return false. Block queries prepend a unary block index, producing one total Boolean oracle on all finite bit strings. Thus writing a query to block $n$ costs at least $n$ machine steps, and a multibit answer uses one query per output bit.
--
--   For a degree bound $d$, set
--   $$D=2^{\lceil\log_2\max(1,d)\rceil}.$$
--   The implementation computes the same integer using a branch for $d\le1$ and the integer binary logarithm otherwise. This corrects Lemma 3.3's normalization without excluding any graph. The adjacency expectation is the real part of the actual finite Hermitian quadratic form, with binary basis labels transported through the given labelling. It accepts arbitrary complex amplitudes as arguments and adds no spectral assumption.
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Definitions 2.1–2.2, 3.1 and proof of Lemma 3.3, pp. 7, 9–10, 17–18 (PDF same)

import Definitions.Def_SignFreeOracle_Separation_Circuit
import Definitions.Def_SignFreeOracle_Separation_Graph

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity QAdvFew.PoQOracle

def parseNat : Str → Option (ℕ × Str)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (parseNat rest).map fun p => (p.1 + 1, p.2)

def labelBits {m : ℕ} (x : Fin (2 ^ m)) : Str := List.ofFn fun i : Fin m => x.val.testBit i

def labelValue (s : Str) : ℕ :=
  ((List.range s.length).map fun i => if s.getD i false then 2 ^ i else 0).sum

def labelOfBits (m : ℕ) (s : Str) : Fin (2 ^ m) :=
  ⟨labelValue s % (2 ^ m), Nat.mod_lt _ (by positivity)⟩

/-- One Boolean output bit of a graph query, with all invalid encodings fixed to false. -/
noncomputable def graphBits {m : ℕ} (d : ℕ) (G : SimpleGraph (Fin (2 ^ m)))
    (π : Equiv.Perm (Fin (2 ^ m))) : Oracle := fun s =>
  match parseNat s with
  | none => false
  | some (mm, rest) =>
    if mm = m ∧ m ≤ rest.length then
      let x := labelOfBits m (rest.take m)
      match parseNat (rest.drop m) with
      | none => false
      | some (i, rest') =>
        match parseNat rest' with
        | none => false
        | some (j, tail) =>
          if i < d ∧ j < m ∧ tail = [] then (graphQuery G π x i).val.testBit j else false
    else false

/-- Self-delimiting query: bit length, label, neighbour position, output-bit position.
All fields have polynomial length for polynomial degree. -/
def graphBitAddress {m : ℕ} (x : Fin (2 ^ m)) (i j : ℕ) : Str :=
  codeNat m ++ labelBits x ++ codeNat i ++ codeNat j

/-- A single total Boolean oracle containing all graph blocks. A query to block n has
an initial 1^n0 tag, so writing the tag alone costs at least n transitions. -/
def joinBlocks (blocks : ℕ → Oracle) : Oracle := fun s =>
  match parseNat s with
  | none => false
  | some (n, address) => blocks n address

/-- Least power of two at least max(1,d). -/
def degreeNormalization (d : ℕ) : ℕ :=
  if d ≤ 1 then 1 else 2 ^ (Nat.log2 (d - 1) + 1)

noncomputable def adjExpectation {m : ℕ} (G : SimpleGraph (Fin (2 ^ m)))
    (π : Equiv.Perm (Fin (2 ^ m))) (ψ : QState m) : ℝ := by
  classical
  exact (∑ z : Bits m, ∑ w : Bits m,
    if G.Adj (π.symm (labelOfBits m (List.ofFn z))) (π.symm (labelOfBits m (List.ofFn w)))
      then star (ψ z) * ψ w else 0).re

end SignFreeOracle.Separation


