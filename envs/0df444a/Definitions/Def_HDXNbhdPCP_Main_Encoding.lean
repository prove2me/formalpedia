-- Prove2me | Definitions.Def_HDXNbhdPCP_Main_Encoding
-- name    : HDXNbhdPCP_Main_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:58:53.582202+00:00
-- url     : https://prove2.me/theorems/9fdee220-40d7-4e83-9149-6cf17628013c
-- title:
--   3-colouring instances, their size, the input encoding of the reduction, and encodings for strong explicitness (Theorem 1.1, Theorem 6.1)
-- statement:
--   1. A **3-colouring instance** is a finite simple graph $G$ on the vertex set $\{0,\dots,k-1\}$; its **size** is $n=|V(G)|+|E(G)|$. It is 3-colourable when it admits a proper colouring with 3 colours.
--   2. The input of the reduction of Theorem 1.1 is a pair $(G,\varepsilon)$ of a graph and a rational number. It is written in binary as $k$ in unary, then the $k\times k$ adjacency matrix row by row, then the sign of $\varepsilon$ and the binary expansions of its numerator and denominator (self-delimiting).
--   3. For Theorem 6.1, vertices of a 4-partite complex are **names** (bit strings). A face is a partial assignment of names to the four colours; the **faces incident to a vertex** $v$ of colour $i$ are the nonempty faces $x_J$ ($i\in J$) of facets $x$ with $x_i=v$. The face-listing algorithm reads $N$ in binary, $q$ in unary, the colour and the name; the construction algorithm reads $N$ and $q$ in unary; lists of faces and facets are written with self-delimiting codes.
--
--   The Label Cover side uses the published definition `FourToOneGames_LabelCover` (instances with vertex sets $[n_L]$, $[n_R]$, alphabets $[|\Sigma_L|]$, $[|\Sigma_R|]$, an edge set and a projection per pair; its value, its alphabet bound and its binary encoding).
--
--   These encodings fix the machine model of "polynomial-time reduction" (Theorem 1.1) and of "strongly explicit" (Theorem 6.1, item 4): Mathlib's `Turing.TM2ComputableInPolyTime` relative to them.
--
--   **Formalization Note** The encodings are plain and polynomially related to the natural sizes: the graph encoding has length $\Theta(k^2)$, polynomial in $n$, and the rational $\varepsilon$ is in binary. Unary $q$ and binary $N$ make "time $q^{O(1)}\mathrm{poly}(\log|X[2]\sqcup X[3]|)$" equivalent to time polynomial in the input length.
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 4, Theorem 1.1 (3-coloring instance, polynomial-time reduction); p. 38, Theorem 6.1 item 4 (names, listing, construction)

import Mathlib
import Definitions.Def_FourToOneGames_LabelCover
import Definitions.Def_HDXNbhdPCP_Main_Complex

/-!
# Inputs of the reduction and binary encodings (Dikstein–Dinur–Hopkins–Singer, Theorem 1.1, §6.5)

* A 3-colouring instance is a finite simple graph on `Fin k`; its size is `n = |V| + |E|`.
* The reduction of Theorem 1.1 is one function of the pair `(G, ε)`; `encodeGraphEps` is the binary
  encoding of its input (vertex count in unary, adjacency matrix, `ε` as a signed binary fraction).
* Encodings used to state strong explicitness (Theorem 6.1, item 4): vertex names are bit strings,
  a face is a partial assignment `Fin 4 → Option (List Bool)`.
-/

namespace HDXNbhdPCP.Main

open Classical FourToOneGames

noncomputable section

/-- The input of the reduction: a graph on `Fin k` (any `k`) and a rational `ε`. -/
abbrev GraphEpsInput := (Σ k : ℕ, SimpleGraph (Fin k)) × ℚ

/-- The size `n = |V(G)| + |E(G)|` of a 3-colouring instance. -/
def graphSize {k : ℕ} (G : SimpleGraph (Fin k)) : ℕ := k + G.edgeFinset.card

/-- A self-delimiting code of a bit string: each bit `b` becomes `[true, b]`, then a `false`. -/
def selfDelim (l : List Bool) : List Bool := l.flatMap (fun b => [true, b]) ++ [false]

/-- A natural number in binary (little-endian `Nat.bits`), self-delimited. -/
def natBin (n : ℕ) : List Bool := selfDelim (Nat.bits n)

/-- A finite list of bit strings, each prefixed by `true`, terminated by `false`. -/
def encList (l : List (List Bool)) : List Bool := l.flatMap (fun s => true :: selfDelim s) ++ [false]

/-- The graph: `k` in unary, then the `k × k` adjacency matrix row by row. -/
def encodeGraph (G : Σ k : ℕ, SimpleGraph (Fin k)) : List Bool :=
  unaryCode G.1 ++ (List.finRange G.1).flatMap
    (fun i => (List.finRange G.1).map (fun j => decide (G.2.Adj i j)))

/-- A rational number: sign bit, then numerator magnitude and denominator in binary. -/
def encodeRat (ε : ℚ) : List Bool := decide (ε.num < 0) :: (natBin ε.num.natAbs ++ natBin ε.den)

/-- The binary encoding of the reduction's input `(G, ε)`. -/
def encodeGraphEps (x : GraphEpsInput) : List Bool := encodeGraph x.1 ++ encodeRat x.2

/-- A face of a 4-partite complex with named vertices: the partial assignment of names to colours. -/
abbrev Face4 := Fin 4 → Option (List Bool)

/-- Encoding of a face: for each colour `0, 1, 2, 3`, `false` if absent, else `true` and the name. -/
def encFace (f : Face4) : List Bool :=
  (List.finRange 4).flatMap (fun c => match f c with
    | none => [false]
    | some s => true :: selfDelim s)

/-- Encoding of a list of faces. -/
def encFaceList (l : List Face4) : List Bool := encList (l.map encFace)

/-- Encoding of a list of facets (total assignments of names). -/
def encFacetList (l : List (Fin 4 → List Bool)) : List Bool :=
  encList (l.map (fun x => encFace (fun c => some (x c))))

/-- Input of the face-listing algorithm: `N` in binary, `q` in unary, the colour in unary, and the
vertex name. -/
def encListInput (x : ℕ × ℕ × Fin 4 × List Bool) : List Bool :=
  natBin x.1 ++ unaryCode x.2.1 ++ unaryCode (x.2.2.1 : ℕ) ++ selfDelim x.2.2.2

/-- Input of the construction algorithm: `N` and `q` in unary. -/
def encBuildInput (x : ℕ × ℕ) : List Bool := unaryCode x.1 ++ unaryCode x.2

/-- The nonempty faces of a 4-partite complex with named vertices that contain the vertex `v` of
colour `i`, each as a partial assignment of names to colours. -/
def incidentFaces (Y : ColoredComplex (Fin 4) (fun _ => List Bool)) (i : Fin 4) (v : List Bool) :
    Finset Face4 :=
  ((Y.supp.filter (fun x => x i = v)) ×ˢ (Finset.univ.filter (fun J : Finset (Fin 4) => i ∈ J))).image
    (fun p => fun c => if c ∈ p.2 then some (p.1 c) else none)

end

end HDXNbhdPCP.Main


