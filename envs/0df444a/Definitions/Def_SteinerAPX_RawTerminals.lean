-- Prove2me | Definitions.Def_SteinerAPX_RawTerminals
-- name    : SteinerAPX_RawTerminals
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:53.978743+00:00
-- url     : https://prove2.me/theorems/4233771f-2d91-45a7-8e27-4472872cb74a
-- title:
--   Rational terminal sets in $\mathbb R^k$, thresholds, raw networks, and their binary encodings
-- statement:
--   A **raw terminal set** is a pair $(k,\ (p_1,\dots,p_n))$ of a dimension $k\in\mathbb N$ and a list of rational coordinate vectors. It is **valid** if every $p_j$ has exactly $k$ coordinates and the $p_j$ are pairwise distinct; it then describes the terminal set
--   $$
--   P=\{p_1,\dots,p_n\}\subseteq\mathbb Q^k\subseteq\mathbb R^k
--   $$
--   with $n$ terminals. A **raw instance** adds a rational threshold $\tau$; a **raw network** is a list of segments with rational endpoints, read as a network in $\mathbb R^k$.
--
--   The **instance class** of the main theorem for a constant $C$ consists of the valid raw terminal sets with
--   $$
--   n\ge 2\qquad\text{and}\qquad k\le C\log n
--   $$
--   (natural logarithm): at least two distinct terminals in logarithmic dimension.
--
--   These are the inputs and outputs of the polynomial-time machines in the mission's hardness statements.
--
--   **Formalization Note** Rationals are encoded as a sign bit followed by the self-delimiting binary codes of $|\text{numerator}|$ and of the denominator; naturals, lists and pairs use the published `BinaryEncoding.natBits`, `listBits`, `pairBits` (as in the published bin packing gap reductions). Coordinates are read with default $0$, which is exact on valid points.
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), §1, p.1 (PDF p.3); Lemma 16, p.21 (PDF p.23); Theorem 1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_SteinerAPX_Network

namespace SteinerAPX

open OAI.BinPackingGap

/-- **Rational point sets in `ℝᵏ`, their binary encoding, and instances with a threshold.**
S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*, STOC 2027 submission (manuscript
sha256 6f78a9ea…), §1, p.1 (PDF p.3), the input of Euclidean Steiner Tree ("n given points in
Rd"), and Lemma 16, p.21 (PDF p.23), its output "n = Θ(m) terminals Pρ ⊆ RO(n) and a threshold τ".

A raw terminal set is a pair `(k, ps)` of a dimension `k` and a list `ps` of rational coordinate
lists. It is valid when every point has exactly `k` coordinates and no point is repeated; then
`n = |ps|` and the terminal set is `{toPoint k p : p ∈ ps} ⊆ ℝᵏ`. A raw instance adds a rational
threshold `τ`. A raw network is a list of rational segments.

**Formalization Note** Rationals are encoded as a sign bit, the self-delimiting binary code of
`|numerator|` and that of the denominator (the published `BinaryEncoding.natBits`); lists and pairs
use the published `listBits` and `pairBits`, as for the published bin packing gap reductions.
`toPoint` reads coordinate `i` with default `0`, which is exact for valid points. -/
abbrev RawTerminals := ℕ × List (List ℚ)

/-- A raw instance: terminals and a rational threshold `τ`. -/
abbrev RawInstance := RawTerminals × ℚ

/-- A raw network: a list of segments with rational endpoint coordinates. -/
abbrev RawNetwork := List (List ℚ × List ℚ)

/-- Binary code of an integer: sign bit, then the binary code of its absolute value. -/
def intBits (z : ℤ) : List Bool := decide (z < 0) :: BinaryEncoding.natBits z.natAbs

/-- Binary code of a rational: numerator, then denominator. -/
def ratBits (q : ℚ) : List Bool := intBits q.num ++ BinaryEncoding.natBits q.den

/-- Binary code of a rational point. -/
def pointBits : List ℚ → List Bool := BinaryEncoding.listBits ratBits

/-- Binary code of a raw terminal set. -/
def rawTerminalsBits : RawTerminals → List Bool :=
  BinaryEncoding.pairBits BinaryEncoding.natBits (BinaryEncoding.listBits pointBits)

/-- Binary code of a raw instance. -/
def rawInstanceBits : RawInstance → List Bool := BinaryEncoding.pairBits rawTerminalsBits ratBits

/-- Binary code of a raw network. -/
def rawNetworkBits : RawNetwork → List Bool :=
  BinaryEncoding.listBits (BinaryEncoding.pairBits pointBits pointBits)

/-- The point of `ℝᵏ` with the given rational coordinates. -/
noncomputable def toPoint (k : ℕ) (p : List ℚ) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i : Fin k => ((p.getD i.val 0 : ℚ) : ℝ))

namespace RawTerminals

/-- The dimension `k`. -/
def k (t : RawTerminals) : ℕ := t.1

/-- The number of terminals `n`. -/
def n (t : RawTerminals) : ℕ := t.2.length

/-- Validity: every point has `k` coordinates and the points are pairwise distinct. -/
def Valid (t : RawTerminals) : Prop := (∀ p ∈ t.2, p.length = t.1) ∧ t.2.Nodup

/-- The terminal set in `ℝᵏ`. -/
def terminals (t : RawTerminals) : Set (EuclideanSpace ℝ (Fin t.1)) :=
  {x | ∃ p ∈ t.2, x = toPoint t.1 p}

/-- The `j`-th terminal (0-based), for `j < n`. -/
noncomputable def point (t : RawTerminals) (j : Fin t.2.length) : EuclideanSpace ℝ (Fin t.1) :=
  toPoint t.1 (t.2.get j)

/-- The instance class of Theorem 1 for a constant `C`: valid, at least two terminals, and
dimension at most `C · log n` (natural logarithm). -/
def InClass (C : ℝ) (t : RawTerminals) : Prop :=
  t.Valid ∧ 2 ≤ t.n ∧ (t.k : ℝ) ≤ C * Real.log t.n

end RawTerminals

namespace RawNetwork

/-- Every endpoint of the raw network has `k` coordinates. -/
def ValidIn (k : ℕ) (N : RawNetwork) : Prop := ∀ e ∈ N, e.1.length = k ∧ e.2.length = k

/-- The network in `ℝᵏ` described by a raw network. -/
noncomputable def toNetwork (k : ℕ) (N : RawNetwork) : Network (EuclideanSpace ℝ (Fin k)) := by
  classical
  exact (N.map fun e => (toPoint k e.1, toPoint k e.2)).toFinset

end RawNetwork

end SteinerAPX


