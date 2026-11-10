-- Prove2me | Definitions.Def_EditGV897_Main_Construction
-- name    : EditGV897_Main_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:26:03.259542+00:00
-- url     : https://prove2.me/theorems/8e065d18-c69f-47c6-95cd-a031a7c37a8a
-- title:
--   Shared matrix, syndrome and compact setup algorithms
-- statement:
--   Given the explicit family $F$ of $M$ affine maps, set
--
--   $$b=\lceil\log_2(2M)\rceil,\qquad K=n-b-1.$$
--
--   A new parity row starts at the empty prefix and appends a bit minimizing the computed exact conditional expectation, with ties choosing zero. Repeat for $b$ rows. If all witnesses disappear early, use the first standard coordinate row that increases rank. Choose a syndrome by evaluating all $2^b$ syndromes and retaining the first minimizer of the witness count.
--
--   The setup output is the row list and its chosen syndrome, a compact description rather than an explicit set of exponentially many codewords. The associated message length is computed from the output row count. A separate finite-set average specifies the uniform-completion expectation, independently of the elimination algorithm.
--
--   These algorithms name the actual objects in Lemmas 1–3 and Theorem 1. Their rank, separation, counting, size and runtime guarantees are not assumed in the setup data.
--
--   **Formalization Note** Ceiling logarithm uses the natural-number ceiling-log operation. Both rank completion and lexicographic syndrome tie breaking are deterministic. The theorem domains impose $M\ge1$ and $b<n$; definitions have irrelevant total extensions elsewhere.
-- source:
--   Ryan Gabrys, Shubhransh Singhvi, Eitan Yaakobi, Making Every Edit Count: Efficient Binary Edit Correction at the Gilbert–Varshamov Bound, STOC 2027 submission #897 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §§4.1–4.2 and proof of Theorem 1, printed pp. 9–11, 13–14 / PDF pp. 10–12, 14–15

import Definitions.Def_EditGV897_Main_Witnesses
import Definitions.Def_EditGV897_Main_Patterns

namespace EditGV897.Main

def allBitLists : ℕ → List (List Bit)
  | 0 => [[]]
  | k + 1 => (allBitLists k).flatMap (fun p => [p ++ [0], p ++ [1]])

def chooseRowPrefix {n : ℕ} (F : Family n) (G : Rows n) : ℕ → List Bit → List Bit
  | 0, p => p
  | k + 1, p =>
    let a : Bit := if twiceExpectation F G (p ++ [0]) ≤ twiceExpectation F G (p ++ [1]) then 0 else 1
    chooseRowPrefix F G k (p ++ [a])

def chooseRow {n : ℕ} (F : Family n) (G : Rows n) : Word n :=
  listWord n (chooseRowPrefix F G n [])

def completionRow {n : ℕ} (G : Rows n) : Word n :=
  match (List.range n).find? (fun k => rowRank (G ++ [unitWord n k]) == G.length + 1) with
  | some k => unitWord n k
  | none => 0

def checkRows (M : ℕ) : ℕ := Nat.clog 2 (2 * M)

def buildRows {n : ℕ} (F : Family n) : ℕ → Rows n → Rows n
  | 0, G => G
  | k + 1, G =>
    let h := if witnessCount F G [] = 0 then completionRow G else chooseRow F G
    buildRows F k (G ++ [h])

def chooseMatrix {n : ℕ} (F : Family n) : Rows n := buildRows F (checkRows F.length) []

/-- Stable lexicographic tie breaking. The list is never empty, including b=0. -/
def chooseSyndrome {n : ℕ} (F : Family n) (G : Rows n) : List Bit :=
  (allBitLists G.length).foldl (fun best β =>
    if witnessCount F G (cosetEquations G β) < witnessCount F G (cosetEquations G best)
    then β else best) (List.replicate G.length 0)

structure Parameters (n : ℕ) where
  rows : Rows n
  beta : List Bit

def setup (t n : ℕ) : Parameters n :=
  let F := canonicalFamily t n
  let G := chooseMatrix F
  ⟨G, chooseSyndrome F G⟩

def messageLength {n : ℕ} (P : Parameters n) : ℕ := n - P.rows.length - 1

def parametersCode {n : ℕ} (P : Parameters n) : List Bool :=
  rowCode P.rows ++ frame (bitCode P.beta)

def familyRowsInput {n : ℕ} (F : Family n) (G : Rows n) : List Bool :=
  unary n ++ familyCode F ++ rowCode G

def expectationInput {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit) : List Bool :=
  familyRowsInput F G ++ frame (bitCode p)

def syndromeInput {n : ℕ} (F : Family n) (G : Rows n) : List Bool := familyRowsInput F G

noncomputable def rowCompletions (n : ℕ) (p : List Bit) : Finset (Word n) := by
  classical
  exact Finset.univ.filter (fun h => (wordList h).take p.length = p)

/-- The uniform-completion expectation itself, for auditing Eq. (10). -/
noncomputable def expectation {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit) : ℚ :=
  ((∑ h ∈ rowCompletions n p, (witnessSum F (G ++ [h]) Finset.univ : ℚ)) /
    ((rowCompletions n p).card : ℚ))

end EditGV897.Main


