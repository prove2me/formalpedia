-- Prove2me | Definitions.Def_HypercliqueCircuits_Circuits_Transpose
-- name    : HypercliqueCircuits_Circuits_Transpose
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T00:34:37.260205+00:00
-- url     : https://prove2.me/theorems/4e56d431-3e5a-4582-9187-8f64a40b7c7e
-- title:
--   Partial transposes, labelled basis and the actual support graph
-- statement:
--   Rows and columns are digit vectors in $[q]^d$. Partial transpose $\tau_A$ swaps the row and column digit at each position in $A$. Its matrix kernel, all products and both operators are computed:
--
--   $$L=\sum_{|A|\le t}\prod_{p\in A}\tau_p\prod_{p\notin A}(I-\tau_p),\qquad
--   H=\sum_{|A|>t}\prod_{p\in A}\tau_p\prod_{p\notin A}(I-\tau_p).$$
--
--   The labelled basis consists of $e_{ii}$ and $e_{ij}\pm e_{ji}$ for $i<j$; $E_\sigma$ is the product of its digit factors. Integer entries preserve the characteristic-zero signs and norms. The counts $u(\sigma)$ and $a(\sigma)$ count off-diagonal and skew factors.
--
--   For $q=2^B$ and $t=\lfloor d/B\rfloor$, the graph has left labels with $a(\sigma)\ge d-t$ and right digit rows. Its edges are exactly the nonzero rows of $E_\sigma$. A biclique partition contains every edge exactly once and has both shores at least
--
--   $$\ell=2^{(B-1)\lfloor(d-t)/B\rfloor}.$$
--
--   Admissibility means $0<\epsilon\le1/8$, $B\ge16$, and $(eB)^2\le2^{\epsilon B}$. It contains no circuit-size or partition certificate.
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, §§1.4 and 3.1–3.3, pp.12–14,17–21 (PDF 13–15,18–22), equations (6)–(7) and (10).

import Definitions.Def_HypercliqueCircuits_Circuits_Polynomials

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

abbrev Digits (q d : ℕ) := Fin d → Fin q
abbrev OffPair (q : ℕ) := {ij : Fin q × Fin q // ij.1 < ij.2}
/-- false = symmetric; true = skew; strict order prevents duplicate labels. -/
abbrev BasisLabel (q : ℕ) := Fin q ⊕ (Bool × OffPair q)
abbrev Label (q d : ℕ) := Fin d → BasisLabel q

def skew {q : ℕ} : BasisLabel q → Bool
  | .inl _ => false
  | .inr p => p.1

def offDiagonal {q : ℕ} : BasisLabel q → Bool
  | .inl _ => false
  | .inr _ => true

noncomputable def factor {q : ℕ} (b : BasisLabel q) (i j : Fin q) : ℤ :=
  match b with
  | .inl h => if i = h ∧ j = h then 1 else 0
  | .inr (s,p) =>
    (if i = p.val.1 ∧ j = p.val.2 then 1 else 0) +
    (if i = p.val.2 ∧ j = p.val.1 then (if s then -1 else 1) else 0)

noncomputable def basisMatrix {q d : ℕ} (σ : Label q d) :
    Matrix (Digits q d) (Digits q d) ℤ :=
  fun i j => ∏ p : Fin d, factor (σ p) (i p) (j p)

noncomputable def uCount {q d : ℕ} (σ : Label q d) : ℕ :=
  (Finset.univ.filter (fun p => offDiagonal (σ p) = true)).card
noncomputable def aCount {q d : ℕ} (σ : Label q d) : ℕ :=
  (Finset.univ.filter (fun p => skew (σ p) = true)).card

noncomputable def frobenius {ι : Type} [Fintype ι] (M N : Matrix ι ι ℤ) : ℤ :=
  ∑ i : ι, ∑ j : ι, M i j * N i j

noncomputable def swapDigits {q d : ℕ} (A : Finset (Fin d)) (i j : Digits q d) : Digits q d :=
  fun p => if p ∈ A then j p else i p

noncomputable def tau {q d : ℕ} (A : Finset (Fin d)) : Operator (Digits q d) := by
  classical
  exact fun ij ab =>
    if ab = (swapDigits A ij.1 ij.2, swapDigits A ij.2 ij.1) then 1 else 0

/-- Ordered composition; the partial transposes commute, so this also denotes the paper's product. -/
noncomputable def operatorTerm (q d : ℕ) (A : Finset (Fin d)) : Operator (Digits q d) := by
  classical
  exact ((List.finRange d).map (fun p =>
    if p ∈ A then tau {p} else (1 : Operator (Digits q d)) - tau {p})).prod

noncomputable def lowOperator (q d t : ℕ) : Operator (Digits q d) :=
  ∑ A ∈ Finset.univ.powerset.filter (fun A : Finset (Fin d) => A.card ≤ t), operatorTerm q d A

noncomputable def highOperator (q d t : ℕ) : Operator (Digits q d) :=
  ∑ A ∈ Finset.univ.powerset.filter (fun A : Finset (Fin d) => t < A.card), operatorTerm q d A

/-- Edges are supported rows, never an invented column for a zero row. -/
noncomputable def supportEdges (B d : ℕ) : Finset (Label (2^B) d × Digits (2^B) d) := by
  classical
  exact Finset.univ.filter (fun e => d - d / B ≤ aCount e.1 ∧
    ∃ j : Digits (2^B) d, basisMatrix e.1 e.2 j ≠ 0)

noncomputable def bicliqueThreshold (B d : ℕ) : ℕ :=
  2 ^ ((B-1) * ((d - d/B) / B))

/-- A list of bicliques with exactly one occurrence of each edge; shores may overlap. -/
def BicliquePartition (B d : ℕ)
    (bs : List (Finset (Label (2^B) d) × Finset (Digits (2^B) d))) : Prop :=
  (∀ b ∈ bs, bicliqueThreshold B d ≤ b.1.card ∧ bicliqueThreshold B d ≤ b.2.card ∧
    b.1.product b.2 ⊆ supportEdges B d) ∧
  (∀ e ∈ supportEdges B d, ∃! h : Fin bs.length,
    e ∈ (bs.get h).1.product (bs.get h).2)

/-- All section-3 numerical conditions. There is no circuit or decomposition certificate here. -/
def Admissible (ε : ℝ) (B : ℕ) : Prop :=
  0 < ε ∧ ε ≤ 1/8 ∧ 16 ≤ B ∧ (Real.exp 1 * B)^2 ≤ (2 : ℝ) ^ (ε * B)

end HypercliqueCircuits.Circuits


