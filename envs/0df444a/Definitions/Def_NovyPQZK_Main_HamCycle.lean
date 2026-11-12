-- Prove2me | Definitions.Def_NovyPQZK_Main_HamCycle
-- name    : NovyPQZK_Main_HamCycle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:37:13.510812+00:00
-- url     : https://prove2.me/theorems/559eb494-2948-4586-840d-9482931060da
-- title:
--   hamcycle and Blum's argument Hamiltonian-cycle_Π (Protocol 18)
-- statement:
--   **Graphs.** A simple undirected graph on vertices $0,\dots,\eta-1$ is given by its strictly upper-triangular adjacency bits $A(i,j)$, $i<j$, listed in the lexicographic order of $I_\eta = \{(i,j): i<j\}$; it is encoded as $\mathrm{pack}[1^\eta, (A(i,j))_{(i,j)\in I_\eta}]$. A **Hamiltonian cycle** (p. 44) is a list $(s_0,\dots,s_{\eta-1})$ of distinct vertices with $s_is_{i+1\bmod\eta}\in E(G)$. $\mathrm{hamRel}(x,w)$ holds iff $x$ encodes a graph and $w$ encodes a Hamiltonian cycle of it; $\mathrm{hamcycle}$ is its language.
--
--   **Protocol 18** ($\mathrm{Hamiltonian\text{-}cycle}_\Pi$) for a bit commitment $\Pi$, common input $(1^n, G)$, prover input a Hamiltonian cycle $H = (s_0,\dots,s_{\eta-1})$:
--   1. $P$ samples $\sigma\in_R S_\eta$, lets $A$ be the adjacency matrix of $\sigma(G)$, and commits to $A$ with the $|I_\eta|$-fold parallel composition of $\Pi$.
--   2. $V$ sends $ch\in_R\{0,1\}$.
--   3. If $ch = 0$, $P$ sends $\sigma$ and opens all of $A$; $V$ checks the openings and that $A$ is the adjacency matrix of $\sigma(G)$. If $ch = 1$, $P$ sends $\sigma(H)$ and opens $A(\sigma(s_i),\sigma(s_{i+1\bmod\eta}))$ for every $i$; $V$ checks the openings, that the opened entries are exactly the cycle's edges, and that each equals $1$.
--   4. $V$ outputs $1$ iff every check succeeds.
--
--   **Formalization Note** $\sigma$ is drawn with one coin of range $\eta!$ (Lehmer decoding, a bijection onto $S_\eta$); the prover draws one block of $S_{com}$ coins per position for each value of the committed bit and uses the block of the bit it commits. Responses are $\mathrm{pack}[\sigma,m,u]$ and $\mathrm{pack}[\sigma(H),\text{openings}]$. An input that is not a graph is rejected. The cycle definition is the paper's (it differs from Mathlib's `SimpleGraph.IsHamiltonian` for $\eta\le2$).
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §7 pp. 44–45, notation for graphs and Protocol 18

import Mathlib
import Definitions.Def_NovyPQZK_Main_Commitment
import Definitions.Def_NovyPQZK_Main_Argument

namespace NovyPQZK.Main

/-!
Dupuis, Ligez, Medhioub, Salvail, Thibodeau, arXiv:2610.33185 (sha256 857d8563…3257f), §7,
pp. 44–45: simple graphs, the language `hamcycle` with the paper's cycle definition, and Blum's
argument `Hamiltonian-cycle_Π` (Protocol 18) built on a bit commitment scheme `Π`.

Encodings. Vertices are `0, …, η − 1` (the paper's `1, …, η`). A simple undirected graph on `η`
vertices is the list `e` of its strictly upper-triangular adjacency bits `A(i, j)`, `i < j`, in the
lexicographic order of `I_η` (`pairsI η`), and is written `pack [1^η, e]`. A list of vertices (a
cycle, a permutation `σ` given by its list of images) is `pack` of the binary numbers. A
Hamiltonian cycle (p. 44) is a list `(s₀, …, s_{η−1})` of distinct vertices with
`s_i s_{i+1 mod η} ∈ E(G)`; in particular the graph with no vertex has one and a graph with one
vertex has none.
-/

/-- `I_η` (p. 44): the pairs `(i, j)` with `i < j` among `0, …, η − 1`, lexicographically. -/
def pairsI (η : ℕ) : List (ℕ × ℕ) :=
  (List.range η).flatMap fun i => ((List.range η).filter fun j => i < j).map fun j => (i, j)

/-- The position of the pair `{a, b}` in `I_η`. -/
def pairPos (η a b : ℕ) : ℕ := (pairsI η).idxOf (min a b, max a b)

/-- Adjacency in the graph with adjacency bits `e`: `A(a, b)` for distinct vertices `a, b < η`. -/
def adjBit (η : ℕ) (e : Bits) (a b : ℕ) : Bool :=
  decide (a < η ∧ b < η ∧ a ≠ b) && e.getD (pairPos η a b) false

/-- The encoding of the graph `(η, e)`. -/
def encGraph (η : ℕ) (e : Bits) : Bits := pack [unary η, e]

/-- Decoding of a graph: `some (η, e)` iff `x` is exactly `encGraph η e` with `|e| = |I_η|`. -/
def decodeGraph (x : Bits) : Option (ℕ × Bits) :=
  match unpack x with
  | [a, e] =>
      if a = unary a.length ∧ e.length = (pairsI a.length).length ∧ x = pack [a, e] then
        some (a.length, e)
      else none
  | _ => none

/-- The encoding of a list of vertices. -/
def encNatList (l : List ℕ) : Bits := pack (l.map natToBits)

/-- Decoding of a list of vertices (canonical encodings only). -/
def decNatList (s : Bits) : Option (List ℕ) :=
  let l := (unpack s).map bitsToNat
  if s = encNatList l then some l else none

/-- `s` lists `η` distinct vertices, all `< η`. -/
def isVertexPerm (η : ℕ) (s : List ℕ) : Bool :=
  decide (s.length = η) && decide s.Nodup && s.all (· < η)

/-- p. 44: `s` is a Hamiltonian cycle of the graph `(η, e)`. -/
def isHamCycle (η : ℕ) (e : Bits) (s : List ℕ) : Bool :=
  isVertexPerm η s && (List.range η).all fun i => adjBit η e (s.getD i 0) (s.getD ((i + 1) % η) 0)

/-- The NP relation of `hamcycle`: `x` encodes a graph and `w` encodes a Hamiltonian cycle of it. -/
def hamRel (x w : Bits) : Bool :=
  match decodeGraph x with
  | some (η, e) => match decNatList w with
    | some s => isHamCycle η e s
    | none => false
  | none => false

/-- The permutation of `{0, …, η − 1}` (list of images) with index `c ∈ {0, …, η! − 1}` (mixed-radix
Lehmer decoding, a bijection onto the permutations). -/
def permOfIndexAux : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, _ => []
  | k + 1, c, L => L.getD (c % L.length) 0 :: permOfIndexAux k (c / L.length) (L.eraseIdx (c % L.length))

/-- The permutation with index `c`. -/
def permOfIndex (η c : ℕ) : List ℕ := permOfIndexAux η c (List.range η)

/-- The adjacency bits of `σ(G)`: `A(a, b) = 1` iff `σ⁻¹(a) σ⁻¹(b) ∈ E(G)`. -/
def permGraphBits (η : ℕ) (e : Bits) (σ : List ℕ) : Bits :=
  (pairsI η).map fun p => adjBit η e (σ.idxOf p.1) (σ.idxOf p.2)

/-- The public parameters of the `|I_η|`-fold parallel composition at security parameter `n`. -/
def p18Pub (Cm : CommitmentScheme) (n η : ℕ) : Bits := pack [unary (pairsI η).length, Cm.setup n]

/-- The verifier's check (steps 9 and 12 of Protocol 18) of the response `resp` to challenge `ch`,
for the graph `(η, e)`, the verifier's receiver coins `cR` (the coins of `R^{|I_η|}_com`) and the
prover's messages `ps` of the committing phase. -/
def p18Check (Cm : CommitmentScheme) (n η : ℕ) (e : Bits) (cR : List ℕ) (ps : List Bits)
    (ch : Bool) (resp : Bits) : Bool :=
  let pub' := p18Pub Cm n η
  let pub := Cm.setup n
  let k := (pairsI η).length
  let privR := pack (cR.map natToBits)
  let vs := (List.range (Cm.rounds n)).map fun i =>
    (parRecv Cm.receiver).next (pack (pub' :: privR :: ps.take i))
  let comm := interleave vs (ps.take (Cm.rounds n))
  let chunks := splitLens (List.replicate k (Cm.receiver.coins pub).length) cR
  if ch = false then
    match unpack resp with
    | [sEnc, mAll, uAll] =>
        decide (resp = pack [sEnc, mAll, uAll]) &&
          match decNatList sEnc with
          | some σ => isVertexPerm η σ && parRopen Cm mAll uAll comm privR pub' &&
              decide (mAll = pack ((permGraphBits η e σ).map fun b => [b]))
          | none => false
    | _ => false
  else
    match unpack resp with
    | [hEnc, opens] =>
        decide (resp = pack [hEnc, opens]) &&
          match decNatList hEnc with
          | some H =>
              let ops := unpack opens
              isVertexPerm η H && decide (opens = pack ops) && decide (ops.length = η) &&
                (List.range η).all fun i =>
                  let a := H.getD i 0
                  let b := H.getD ((i + 1) % η) 0
                  let pos := pairPos η a b
                  match unpack (ops.getD i []) with
                  | [me, ue] =>
                      decide (ops.getD i [] = pack [me, ue]) && decide (a ≠ b) && decide (me = [true]) &&
                        Cm.ropen me ue (comm.map (component pos))
                          (pack ((chunks.getD pos []).map natToBits)) pub
                  | _ => false
          | none => false
    | _ => false

/-- The honest verifier of Protocol 18 (input `(1^n, x)`): coins of `R^{|I_η|}_com` and one bit
`ch`; it plays `R^{|I_η|}_com` for `rounds n` rounds, then sends `ch`, then outputs the check.
On an `x` that is not a graph it rejects. -/
def p18Verifier (Cm : CommitmentScheme) : Party where
  coins inp := match unpack inp with
    | [a, x] => match decodeGraph x with
      | some (η, _) => (parRecv Cm.receiver).coins (p18Pub Cm a.length η) ++ [2]
      | none => []
    | _ => []
  next view := match unpack view with
    | inp :: cenc :: msgs => match unpack inp with
      | [a, x] => match decodeGraph x with
        | some (η, e) =>
            let n := a.length
            let pub' := p18Pub Cm n η
            let cs := (unpack cenc).map bitsToNat
            let mR := ((parRecv Cm.receiver).coins pub').length
            let cR := cs.take mR
            let ch : Bool := cs.getD mR 0 == 1
            if msgs.length < Cm.rounds n then
              (parRecv Cm.receiver).next (pack (pub' :: pack (cR.map natToBits) :: msgs))
            else if msgs.length = Cm.rounds n then [ch]
            else if msgs.length = Cm.rounds n + 1 then
              [p18Check Cm n η e cR (msgs.take (Cm.rounds n)) ch (msgs.getD (Cm.rounds n) [])]
            else []
        | none => [false]
      | _ => [false]
    | _ => [false]

/-- The honest prover of Protocol 18 (input `(1^n, x, w)`, `w` a Hamiltonian cycle `H`): a uniform
`σ ∈ S_η` (coin of range `η!`), then for every position of `I_η` one block of coins of `S_com` for
each value of the committed bit (the block of the bit `A(i, j)` actually committed is used). It
commits to the adjacency matrix `A` of `σ(G)` with the `|I_η|`-fold parallel composition of `Π`;
on `ch = 0` it sends `σ` and opens all of `A`; on `ch = 1` it sends `σ(H)` and opens
`A(σ(s_i), σ(s_{i+1 mod η}))` for every `i`. -/
def p18Prover (Cm : CommitmentScheme) : Party where
  coins inp := match unpack inp with
    | [a, x, _] => match decodeGraph x with
      | some (η, _) =>
          let pub := Cm.setup a.length
          η.factorial :: ((List.range (pairsI η).length).map fun _ =>
            Cm.sender.coins (senderInput [false] pub) ++ Cm.sender.coins (senderInput [true] pub)).flatten
      | none => []
    | _ => []
  next view := match unpack view with
    | inp :: cenc :: msgs => match unpack inp with
      | [a, x, w] => match decodeGraph x with
        | some (η, e) =>
            let n := a.length
            let pub := Cm.setup n
            let k := (pairsI η).length
            let H := (decNatList w).getD []
            let cs := (unpack cenc).map bitsToNat
            let σ := permOfIndex η (cs.getD 0 0)
            let A := permGraphBits η e σ
            let b0 := (Cm.sender.coins (senderInput [false] pub)).length
            let b1 := (Cm.sender.coins (senderInput [true] pub)).length
            let blocks := splitLens (List.replicate k (b0 + b1)) (cs.drop 1)
            let chosen : ℕ → List ℕ := fun i =>
              if A.getD i false then (blocks.getD i []).drop b0 else (blocks.getD i []).take b0
            let instView : ℕ → List Bits → Bits := fun i ms =>
              pack (senderInput [A.getD i false] pub :: pack ((chosen i).map natToBits) ::
                ms.map (component i))
            let K := Cm.rounds n
            if msgs.length = 0 then []
            else if msgs.length ≤ K then pack ((List.range k).map fun i => Cm.sender.next (instView i msgs))
            else if msgs.length = K + 1 then
              let ch := msgs.getD K []
              let cm := msgs.take K
              if ch = [false] then
                pack [encNatList σ, pack ((List.range k).map fun i => (Cm.sopen (instView i cm)).1),
                  pack ((List.range k).map fun i => (Cm.sopen (instView i cm)).2)]
              else if ch = [true] then
                let σH := H.map fun v => σ.getD v 0
                pack [encNatList σH, pack ((List.range η).map fun i =>
                  let op := Cm.sopen (instView (pairPos η (σH.getD i 0) (σH.getD ((i + 1) % η) 0)) cm)
                  pack [op.1, op.2])]
              else []
            else []
        | none => []
      | _ => []
    | _ => []

/-- Protocol 18 (p. 45), `Hamiltonian-cycle_Π`: `rounds n + 1` rounds (the committing phase of
`Π^{|I_η|}`, then the challenge and the response). -/
def protocol18 (Cm : CommitmentScheme) : ArgSystem where
  prover := p18Prover Cm
  verifier := p18Verifier Cm
  rounds n _ := Cm.rounds n + 1

end NovyPQZK.Main


