-- Prove2me | Definitions.Def_CatalyticMatching_General_Encoding
-- name    : CatalyticMatching_General_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:52.122369+00:00
-- url     : https://prove2.me/theorems/24829485-8ae5-4c98-9058-3cc023e7bb96
-- title:
--   Explicit binary graph, matching, and rational matrix encodings
-- statement:
--   Vertices are $\{0,\ldots,n-1\}$. Encode a graph by $1^n0$ followed by its $n^2$ row-major adjacency bits. Encode a selected edge set by its symmetric $n^2$ row-major incidence bits. Encode an integer magnitude by its low-bit-first binary digits, framing a word $b$ by $1^{|b|}0b$. A rational uses a sign bit, framed numerator magnitude and framed positive denominator, in reduced form. A matrix concatenates its row-major rational entries, with dimension obtained from the graph header.
--
--   $$\operatorname{enc}(G)=1^n0\,\operatorname{adj}(G).$$
--
--   These encodings are explicit specifications of input and output strings; they do not provide decoding or arithmetic as free machine instructions. All rational bits contribute to input length. Malformed graph strings are outside the graph domain.
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, §2 p.10 (explicit binary encoding convention)

import Definitions.Def_CatalyticMatching_General_Matching

namespace CatalyticMatching.General

abbrev Bits := List Bool

/-- Low-bit-first binary natural number, length-prefixed when used in a record. -/
def natBits (a : ℕ) : Bits := (Nat.digits 2 a).map (fun d => d == 1)

def frame (x : Bits) : Bits := List.replicate x.length true ++ [false] ++ x

/-- Reduced numerator (sign and magnitude) and positive denominator. -/
def ratBits (a : ℚ) : Bits :=
  [decide (a.num < 0)] ++ frame (natBits a.num.natAbs) ++ frame (natBits a.den)

/-- Row-major order; n=0 gives the empty list. -/
def vertexPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i,j)))

/-- Unary vertex count and all n² adjacency bits; §2 p.10 binary bit model. -/
noncomputable def graphBits {n : ℕ} (G : SimpleGraph (Fin n)) : Bits := by
  classical
  exact List.replicate n true ++ [false] ++
    (vertexPairs n).map (fun ij => decide (G.Adj ij.1 ij.2))

/-- The symmetric n² edge-incidence output has no header (n is in the input). -/
noncomputable def matchingBits {n : ℕ} {G : SimpleGraph (Fin n)}
    (M : Finset G.edgeSet) : Bits := by
  classical
  exact (vertexPairs n).map (fun ij => decide (∃ e ∈ M,
    (e : Sym2 (Fin n)) = s(ij.1, ij.2)))

/-- Assignment is serialized as a rational n² evaluated Tutte matrix. -/
def matrixBits {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Bits :=
  ((vertexPairs n).map (fun ij => ratBits (A ij.1 ij.2))).flatten

end CatalyticMatching.General


