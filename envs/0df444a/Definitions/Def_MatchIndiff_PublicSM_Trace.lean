-- Prove2me | Definitions.Def_MatchIndiff_PublicSM_Trace
-- name    : MatchIndiff_PublicSM_Trace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:25:34.892393+00:00
-- url     : https://prove2.me/theorems/fccecaad-2d05-4d8c-ae23-213cc3ef413e
-- title:
--   Traces, chronological rows, reverse-chronological priorities, Algorithm 1 and the marked profiles P^{X,Y} (§6, pp. 10–12)
-- statement:
--   **Traces (p. 10–11).** A trace is a finite sequence $M_0,\dots,M_L$ of perfect matchings; a student *visits* a school when that pair occurs in the trace (consecutive repetitions count once). The *chronological row* of a student lists exactly its visited schools, earlier visits strictly better. A strict complete school priority profile $Q$ is *reverse chronological* when every school ranks its visited holders in reverse chronological order and all other students below them. `NoRevisit`: no student visits a school again after leaving it; `ConsecShare`: every two consecutive steps share a student.
--
--   **Algorithm 1 (p. 11).** For even $k\ge2$ there are students $A_1..A_k$, $B_1..B_k$, $C_1..C_k$ and schools $a_i,b_i,c_j$, starting from $M_0$ ($A_i$–$a_i$, $B_i$–$b_i$, $C_j$–$c_j$). For $i=1,\dots,k$: core steps $(i,1),\dots,(i,k)$, where core $(i,j)$ sends $A_i$ to $B_i$'s old school, $B_i$ to $C_j$'s and $C_j$ to $A_i$'s; then, if $i<k$, one link sending $A_i$ to $A_{i+1}$'s old school, $A_{i+1}$ to $B_i$'s, $B_i$ to $B_{i+1}$'s and $B_{i+1}$ to $A_i$'s. There are $L=k^2+k-1$ steps.
--
--   **Marked profiles (pp. 11–12).** For $X,Y\in\{0,1\}^I$, $I=\{(i,j):1\le i\le k,\ 1\le j<k\}$, a marked boundary turns the strict comparison between two consecutive schools of a chronological list into a tie (adjacent marks merge). Fixed marks: $A_i$'s boundary at core $(i,1)$ and at its outgoing link ($i<k$). Controlled marks: at core $(i,j+1)$, $A_i$'s boundary iff $X_{ij}=1$ and $B_i$'s iff $Y_{ij}=1$. The result is $P^{X,Y}$; acceptable sets never change. The trace position right after core $(i,j)$ is $t(i,j)=(i-1)(k+1)+j$.
--
--   **Formalization Note.** Indices are 0-based: student and school $A_i=i$, $B_i=k+i$, $C_j=2k+j$ in `Fin (3k)`, block $i\in\{0..k-1\}$, core $j\in\{0..k-1\}$. A step is a student permutation $\sigma$ with $M_{\text{new}}=M_{\text{old}}\circ\sigma$; `algTrace k t s` is the school of $s$ in $M_t$ (`traceNat` composes the step permutations; the reduction mod $3k$ never changes a value). Step numbers: core $(i,j)$ is step `coreStep k i j` $=i(k+1)+j+1$, so the paper's $t(i+1,j+1)$; the link after block $i$ is step $i(k+1)+k+1$. `X i j`, `Y i j` with `i : Fin k`, `j : Fin (k-1)` are the paper's $X_{i+1,j+1}$, $Y_{i+1,j+1}$. `markedRank` gives a visited school $1+{}$(number of unmarked boundaries crossed up to its first visit) and an unvisited school $0$; with no marks it is the chronological row. The definitions were evaluated at $k=2$ and reproduce Table 6 (p. 80) and the marks of §D.2.
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), pp. 10–12 (§6: trace, Algorithm 1, Q_k, P^{X,Y}, t(i, j)); p. 80 (Table 6)

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model

namespace MatchIndiff.PublicSM

/-- The first position `t ≤ L` at which student `s` holds school `h` in the trace `M`. -/
def firstVisit {S H : Type*} [DecidableEq H] (M : ℕ → S → H) (L : ℕ) (s : S) (h : H) :
    Option ℕ :=
  (List.range (L + 1)).find? (fun t => M t s = h)

/-- The row of student `s` built from its chronological visit list in the trace `M_0, …, M_L`,
with marked boundaries turned into ties (§6, p. 11). The boundary crossed by `s` at step `u`
(between `M_{u-1}` and `M_u`) is marked when `mark s u = true`. A visited school `h` gets
`1 +` the number of unmarked boundaries crossed by `s` up to its first visit of `h`; an unvisited
school gets `0` (unacceptable). With no marks this is the chronological list itself. -/
def markedRank {S H : Type*} [DecidableEq H] (M : ℕ → S → H) (L : ℕ) (mark : S → ℕ → Bool)
    (s : S) (h : H) : ℕ :=
  match firstVisit M L s h with
  | none => 0
  | some t => 1 + ((List.range' 1 t).filter (fun u => (M (u - 1) s != M u s) && !(mark s u))).length

/-- The chronological student rows of a trace (Lemma 6.1): each student lists exactly its
visited schools, earlier visits strictly better. -/
def chronRow {S H : Type*} [DecidableEq H] (M : ℕ → S → H) (L : ℕ) : S → H → ℕ :=
  fun s h => markedRank M L (fun _ _ => false) s h

/-- No student visits a school again after leaving it. -/
def NoRevisit {S H : Type*} (M : ℕ → S → H) (L : ℕ) : Prop :=
  ∀ (s : S) (t₁ t₂ t₃ : ℕ), t₁ < t₂ → t₂ < t₃ → t₃ ≤ L → M t₂ s ≠ M t₁ s → M t₃ s ≠ M t₁ s

/-- Every two consecutive steps share a student (a student that moves in both). -/
def ConsecShare {S H : Type*} (M : ℕ → S → H) (L : ℕ) : Prop :=
  ∀ t, t + 2 ≤ L → ∃ s : S, M (t + 1) s ≠ M t s ∧ M (t + 2) s ≠ M (t + 1) s

/-- `Q` is a strict, complete public priority profile that ranks each school's visited holders in
reverse chronological order and all other students below them (§6, p. 11). -/
def IsRevChronPriority {n : ℕ} (M : ℕ → Fin n → Fin n) (L : ℕ) (Q : Fin n → Fin n → ℕ) :
    Prop :=
  (∀ h, IsRow (Q h)) ∧ (∀ h d, Q h d ≠ 0) ∧ (∀ h d e, Q h d = Q h e → d = e) ∧
    (∀ (h d e : Fin n) (t₁ t₂ : ℕ), t₁ < t₂ → t₂ ≤ L → M t₁ d = h → M t₂ e = h → d ≠ e →
      Q h e < Q h d) ∧
    (∀ (h d e : Fin n), (∃ t ≤ L, M t d = h) → (¬ ∃ t ≤ L, M t e = h) → Q h d < Q h e)

/-- A step of Algorithm 1 (0-based indices): core step `(i, j)` or the link after block `i`. -/
inductive Step
  | core (i j : ℕ)
  | link (i : ℕ)

/-- The student permutation `σ` of a step, with `M_new = M_old ∘ σ` on student indices
`A_i = i`, `B_i = k + i`, `C_j = 2k + j`. Core `(i, j)`: `A_i` takes `B_i`'s old school, `B_i`
takes `C_j`'s, `C_j` takes `A_i`'s. Link `i`: `A_i` takes `A_{i+1}`'s old school, `A_{i+1}` takes
`B_i`'s, `B_i` takes `B_{i+1}`'s, `B_{i+1}` takes `A_i`'s. -/
def Step.perm (k : ℕ) : Step → ℕ → ℕ
  | .core i j => fun s =>
      if s = i then k + i else if s = k + i then 2 * k + j else if s = 2 * k + j then i else s
  | .link i => fun s =>
      if s = i then i + 1 else if s = i + 1 then k + i else if s = k + i then k + i + 1
      else if s = k + i + 1 then i else s

/-- The steps of Algorithm 1 in order: for each block `i = 0, …, k-1`, core steps
`(i, 0), …, (i, k-1)`, then the link `i` when `i + 1 < k`. -/
def algSteps (k : ℕ) : List Step :=
  (List.range k).flatMap (fun i =>
    (List.range k).map (Step.core i) ++ (if i + 1 < k then [Step.link i] else []))

/-- The trace of Algorithm 1 on natural-number indices: `M_t = σ_1 ∘ ⋯ ∘ σ_t`, starting from
`M_0 = id` (student `A_i = i` at school `a_i = i`, `B_i = k + i` at `b_i = k + i`, `C_j = 2k + j`
at `c_j = 2k + j`). -/
def traceNat (k t : ℕ) : ℕ → ℕ :=
  ((algSteps k).take t).foldl (fun f st => f ∘ st.perm k) id

/-- The trace of Algorithm 1 on `3k` students and `3k` schools: `algTrace k t s` is the school of
student `s` in `M_t`. (The reduction mod `3k` never changes a value: every step permutes
`{0, …, 3k - 1}`.) -/
def algTrace (k : ℕ) (t : ℕ) (s : Fin (3 * k)) : Fin (3 * k) :=
  ⟨traceNat k t s.val % (3 * k), Nat.mod_lt _ s.pos⟩

/-- The number of steps `L = k² + k - 1`. -/
def algL (k : ℕ) : ℕ := k ^ 2 + k - 1

/-- The step number of core `(i, j)` (0-based `i, j`); the trace position right after it is the
paper's `t(i + 1, j + 1) = i (k + 1) + j + 1`. -/
def coreStep (k i j : ℕ) : ℕ := i * (k + 1) + j + 1

/-- The step number of the link after block `i` (0-based). -/
def linkStep (k i : ℕ) : ℕ := i * (k + 1) + k + 1

/-- The boundary marks of `P^{X,Y}` (§6, p. 11–12), 0-based: `X i j`, `Y i j` with `i < k`,
`j < k - 1` are the paper's `X_{i+1, j+1}`, `Y_{i+1, j+1}`. Fixed marks: `A_i`'s boundary at core
`(i, 0)` and at link `i` (when `i + 1 < k`). Controlled marks: `A_i`'s boundary at core
`(i, j + 1)` iff `X i j`, `B_i`'s iff `Y i j`. No other marks. -/
def markXY (k : ℕ) (X Y : Fin k → Fin (k - 1) → Bool) (s u : ℕ) : Bool :=
  (List.finRange k).any fun i =>
    (s == i.val &&
      (u == coreStep k i.val 0 || (decide (i.val + 1 < k) && u == linkStep k i.val) ||
        (List.finRange (k - 1)).any fun j => u == coreStep k i.val (j.val + 1) && X i j)) ||
    (s == k + i.val &&
      (List.finRange (k - 1)).any fun j => u == coreStep k i.val (j.val + 1) && Y i j)

/-- The marked student profile `P^{X,Y}`: the chronological lists of Algorithm 1 with the marked
boundaries turned into ties (adjacent marks merge). Acceptable sets never change. -/
def markedProfile (k : ℕ) (X Y : Fin k → Fin (k - 1) → Bool) :
    Fin (3 * k) → Fin (3 * k) → ℕ :=
  fun s h => markedRank (algTrace k) (algL k) (fun s' u => markXY k X Y s'.val u) s h

end MatchIndiff.PublicSM


