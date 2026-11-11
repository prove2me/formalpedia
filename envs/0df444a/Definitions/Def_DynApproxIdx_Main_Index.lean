-- Prove2me | Definitions.Def_DynApproxIdx_Main_Index
-- name    : DynApproxIdx_Main_Index
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:52:23.687926+00:00
-- url     : https://prove2.me/theorems/8c468e18-df72-44d4-b6c8-d2a61956f5f4
-- title:
--   The dynamic k-mismatch / k-edit text index of Theorem 1.1: operations, answers, n, and the time and space bounds
-- statement:
--   A text $T$ over the alphabet $\mathbb N$ starts **empty** and undergoes a sequence $\sigma$ of operations, fixed in advance:
--   - $\mathrm{ins}(i,x)$ inserts the character $x$ before position $i$ (valid when $i\le|T|$);
--   - $\mathrm{del}(i)$ deletes $T[i]$ (valid when $i<|T|$);
--   - $\mathrm{qry}(\kappa,P)$ asks, for a nonempty pattern $P$ of length $m$ and a nonempty text, for one $k$-mismatch occurrence, all $k$-mismatch occurrences, one $k$-edit occurrence, or all $k$-edit occurrences of $P$ in $T$; it leaves $T$ unchanged.
--
--   $T_j$ is the text after the first $j$ operations. Occurrences are starting positions: $\mathrm{Occ}^H_k(P,T)$ for Hamming distance and $\mathrm{Occ}_k(P,T)=\{s\le|T| : \exists e\in[s..|T|],\ \delta_E(P,T[s..e))\le k\}$ for edit distance.
--
--   **Protocol.** The run starts with the single word $k$ pending (operation $0$). Operation $j\ge1$ is the $j$-th entry of $\sigma$, delivered as the words $0,i,x$ (insertion), $1,i$ (deletion) or $2+\mathrm{code}(\kappa),m,P[0],\dots,P[m-1]$ (query; codes $0,1,2,3$ for one-mismatch, all-mismatch, one-edit, all-edit).
--
--   **Answers.** A one-occurrence query is answered correctly when it writes nothing and there is no occurrence, or writes exactly one word that is an occurrence. A reporting query is answered correctly when it writes every occurrence exactly once, in any order.
--
--   **Bounds.** For operation $j$ let $n_j=\max(|T|,2^k)$ for the text $T$ it meets ($n_0=2^k$), $L_j=\log_2 n_j$ and
--   $$F_j=\frac{c^k L_j^k}{k!}.$$
--   The time bound is $C\,F_j L_j^e$ for the initialization and every update, $C\,(m+F_j)L_j^e$ for a one-occurrence query, $C\,(m+F_j+\mathrm{occ})L_j^e$ for reporting all $k$-mismatch occurrences and $C\,(m+F_j+3^k\,\mathrm{occ})L_j^e$ for reporting all $k$-edit occurrences, where $\mathrm{occ}$ is the number of occurrences. The space bound is $C\,n_jF_jL_j^e$ nonzero cells. The word size is measured against $\lceil\log_2(N+\sigma_{\max}+3)\rceil$, where $N$ is the largest of $2^k$ and all text lengths, and $\sigma_{\max}$ the largest word of the operation sequence.
--
--   These are the objects of the goal, Theorem 1.1.
--
--   **Formalization Note.** Each $\tilde O(g)$ of the paper becomes $C\cdot g\cdot L_j^e$. Updates may write anything. Trivial queries (empty $P$ or $T$, omitted in §3) are not valid operations.
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), Theorem 1.1, pp. 1–2 (PDF 3–4); §2, p. 5 (PDF 7); §3, p. 13 (PDF 15); Appendices A–B, pp. 56–58 (PDF 58–60)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_PMEdits_Main_Strings
import Definitions.Def_HammingSumset729_Approximation_Strings
import Definitions.Def_DynApproxIdx_Main_Strings
import Definitions.Def_DynApproxIdx_Main_Run

namespace DynApproxIdx.Main

open PMEdits.Main

/-! # The dynamic approximate text index: operations, answers and bounds of Theorem 1.1

Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*, STOC 2027 submission
(manuscript sha256 7f902057…): Theorem 1.1 and footnote 2, pp. 1–2 (PDF 3–4); the Õ convention, p. 5
(PDF 7) and the abstract's footnote 1; §3, p. 13 (PDF 15); Appendices A–B, pp. 56–58 (PDF 58–60).

**Formalization Note.**
* The text `T` starts empty. An operation is `ins i x` (insert the character `x ∈ ℕ` before position
  `i`, valid when `i ≤ |T|`), `del i` (delete `T[i]`, valid when `i < |T|`) or a query `qry κ P` of
  one of four kinds: one / all `k`-mismatch occurrences, one / all `k`-edit occurrences of `P` in
  `T`. A query is valid when `P` and `T` are nonempty (§3 omits trivial queries) and leaves `T`
  unchanged. The sequence of operations is fixed before the coin tape (Appendix B).
* Words: `ins i x` is `0, i, x`; `del i` is `1, i`; `qry κ P` is `2 + code κ, |P|, P[0], …,
  P[|P|−1]` with codes `0, 1, 2, 3` for one-mismatch, all-mismatch, one-edit, all-edit. The run
  starts with the single word `k` pending (operation `0`, the initialization on the empty text);
  operation `j ≥ 1` is the `j`-th entry of the sequence.
* `n_j = max(|T|, 2^k)` for the text `T` operation `j` meets (`n_0 = 2^k`), `L_j = log₂ n_j` and
  `F_j = c^k L_j^k / k!`. Every `Õ(g)` is `C · g · L_j^e`.
* Answers: a one-occurrence query writes either nothing (exactly when there is no occurrence) or
  one word, an occurrence position. A reporting query writes every occurrence position exactly once,
  in any order. Positions are `0`-based starting positions (`OccH`, `Occ`). Updates may write
  anything.
* The word size `w` is fixed for the run and must be at least a constant times
  `⌈log₂(N + σ_max + 3)⌉`, where `N` is the largest of `2^k` and every text length, and `σ_max` the
  largest word of the operation sequence (characters, positions, pattern lengths). -/

/-- The four query kinds of Theorem 1.1. -/
inductive QKind where
  /-- one `k`-mismatch occurrence -/
  | oneH
  /-- all `k`-mismatch occurrences -/
  | allH
  /-- one `k`-edit occurrence -/
  | oneE
  /-- all `k`-edit occurrences -/
  | allE
  deriving DecidableEq

/-- The word coding a query kind. -/
def QKind.code : QKind → ℕ
  | .oneH => 0
  | .allH => 1
  | .oneE => 2
  | .allE => 3

/-- An operation on the dynamic text. -/
inductive Op where
  /-- insert character `x` before position `i` -/
  | ins (i x : ℕ)
  /-- delete the character at position `i` -/
  | del (i : ℕ)
  /-- a query of kind `κ` with pattern `P` -/
  | qry (κ : QKind) (P : List ℕ)

/-- The text after an operation. -/
def Op.apply : Op → List ℕ → List ℕ
  | .ins i x, T => T.take i ++ x :: T.drop i
  | .del i, T => T.eraseIdx i
  | .qry _ _, T => T

/-- An operation is valid for the text `T` it meets. -/
def Op.Valid : Op → List ℕ → Prop
  | .ins i _, T => i ≤ T.length
  | .del i, T => i < T.length
  | .qry _ P, T => P ≠ [] ∧ T ≠ []

/-- The words delivered to the machine for an operation. -/
def Op.words : Op → List ℕ
  | .ins i x => [0, i, x]
  | .del i => [1, i]
  | .qry κ P => [2 + κ.code, P.length] ++ P

/-- Every operation of the list is valid for the text it meets, starting from `T`. -/
def ValidFrom : List ℕ → List Op → Prop
  | _, [] => True
  | T, o :: σ => o.Valid T ∧ ValidFrom (o.apply T) σ

/-- A valid sequence: valid from the empty text. -/
def ValidSeq (σ : List Op) : Prop := ValidFrom [] σ

/-- `T_j`: the text after the first `j` operations of `σ`, starting from the empty text. -/
def textAt (σ : List Op) (j : ℕ) : List ℕ :=
  (σ.take j).foldl (fun T o => o.apply T) []

/-- `N = max(2^k, |T_0|, …, |T_{|σ|}|)`. -/
def maxLen (k : ℕ) (σ : List Op) : ℕ :=
  ((List.range (σ.length + 1)).map fun j => (textAt σ j).length).foldl max (2 ^ k)

/-- `σ_max`: the largest word of the operation sequence. -/
def maxWord (σ : List Op) : ℕ := (σ.flatMap Op.words).foldl max 0

/-- The word-size unit `⌈log₂(N + σ_max + 3)⌉`. -/
def widthReq (k : ℕ) (σ : List Op) : ℕ := Nat.clog 2 (maxLen k σ + maxWord σ + 3)

/-- `n_j = max(|T|, 2^k)` for the text `T` that operation `j` meets (`n_0 = 2^k`). -/
def nAt (k : ℕ) (σ : List Op) : ℕ → ℕ
  | 0 => 2 ^ k
  | j + 1 => max (textAt σ j).length (2 ^ k)

/-- `L_j = log₂ n_j`. -/
noncomputable def logN (k : ℕ) (σ : List Op) (j : ℕ) : ℝ := Real.logb 2 (nAt k σ j)

/-- `F_j = c^k · L_j^k / k!`. -/
noncomputable def termF (c : ℝ) (k : ℕ) (σ : List Op) (j : ℕ) : ℝ :=
  c ^ k * logN k σ j ^ k / (Nat.factorial k : ℝ)

/-- The time bound of operation `j`: `C·F·L^e` for the initialization and every update;
`C·(m + F)·L^e` for a one-occurrence query; `C·(m + F + occ)·L^e` for reporting all `k`-mismatch
occurrences; `C·(m + F + 3^k·occ)·L^e` for reporting all `k`-edit occurrences. -/
noncomputable def timeBound (c : ℝ) (e : ℕ) (C : ℝ) (k : ℕ) (σ : List Op) (j : ℕ) : ℝ :=
  match j with
  | 0 => C * termF c k σ 0 * logN k σ 0 ^ e
  | j + 1 =>
      match σ[j]? with
      | some (.qry .oneH P) => C * ((P.length : ℝ) + termF c k σ (j + 1)) * logN k σ (j + 1) ^ e
      | some (.qry .oneE P) => C * ((P.length : ℝ) + termF c k σ (j + 1)) * logN k σ (j + 1) ^ e
      | some (.qry .allH P) =>
          C * ((P.length : ℝ) + termF c k σ (j + 1) + ((OccH k P (textAt σ j)).ncard : ℝ)) *
            logN k σ (j + 1) ^ e
      | some (.qry .allE P) =>
          C * ((P.length : ℝ) + termF c k σ (j + 1) +
              (3 : ℝ) ^ k * ((Occ k P (textAt σ j)).ncard : ℝ)) * logN k σ (j + 1) ^ e
      | _ => C * termF c k σ (j + 1) * logN k σ (j + 1) ^ e

/-- The space bound of operation `j`: `C · n_j · F_j · L_j^e` nonzero cells. -/
noncomputable def spaceBound (c : ℝ) (e : ℕ) (C : ℝ) (k : ℕ) (σ : List Op) (j : ℕ) : ℝ :=
  C * (nAt k σ j : ℝ) * termF c k σ j * logN k σ j ^ e

/-- The answer `out` to a query of kind `κ` with pattern `P` on text `T` is correct. -/
def AnswerOK (k : ℕ) (P T : List ℕ) (out : List ℕ) : QKind → Prop
  | .oneH => (out = [] ∧ OccH k P T = ∅) ∨ ∃ i ∈ OccH k P T, out = [i]
  | .allH => out.Nodup ∧ ∀ i, i ∈ out ↔ i ∈ OccH k P T
  | .oneE => (out = [] ∧ Occ k P T = ∅) ∨ ∃ i ∈ Occ k P T, out = [i]
  | .allE => out.Nodup ∧ ∀ i, i ∈ out ↔ i ∈ Occ k P T

/-- Operation `j` of the run of `P` on parameter `k` and sequence `σ` meets its time bound and,
at every step, its space bound. -/
def OpWithin (c : ℝ) (e : ℕ) (C : ℝ) (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w)
    (k : ℕ) (σ : List Op) (j : ℕ) : Prop :=
  WithinBounds P ω [k] (σ.map Op.words) j (timeBound c e C k σ j) (spaceBound c e C k σ j)

/-- Every query of `σ` that completes writes a correct answer. -/
def QueriesCorrect (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (k : ℕ)
    (σ : List Op) : Prop :=
  ∀ (j : ℕ) (κ : QKind) (Pat out : List ℕ), σ[j]? = some (.qry κ Pat) →
    opOutput P ω [k] (σ.map Op.words) (j + 1) = some out →
    AnswerOK k Pat (textAt σ j) out κ

end DynApproxIdx.Main


