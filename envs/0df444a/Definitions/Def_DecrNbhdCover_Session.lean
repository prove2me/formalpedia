-- Prove2me | Definitions.Def_DecrNbhdCover_Session
-- name    : DecrNbhdCover_Session
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:53.304988+00:00
-- url     : https://prove2.me/theorems/d75017c6-5d20-4a3b-87b6-265b0d4a1f36
-- title:
--   Online sessions on the word RAM: windows, reports, total update time
-- statement:
--   A session feeds a program of the published word RAM `DynConnWC.Program` blocks of words: block $0$ is the initialization input and block $t+1$ is the $t$-th operation. The machine is online, so what a program writes before it reads a block does not depend on that block. Hence the validity of an operation may depend on what the run has already reported, and no adversary object is needed. Programs are **deterministic**: they contain no `rand` instruction.
--
--   Window $k$ runs from the read of the first word of block $k$ to the read of the first word of block $k+1$, or of the end marker returned after the input is exhausted. Window $0$ starts at step $0$. A window's output is what is written in it, and its time is its number of steps. The output is parsed into reports by inverting an encoding, and reports are folded into a state by a step function that refuses illegal reports. Query windows change no state. The **total update time** is the time outside query windows, initialization included.
--
--   These conventions give precise meaning to "online sequence", "reports", "maintains", "total update time" and "query time".
--
--   **Formalization Note** The paper names no machine. $2^{C/\epsilon^C}$ stands for $2^{1/\mathrm{poly}(\epsilon)}$, $2^{\mathrm{poly}(1/\epsilon)}$ and $2^{O(1/\mathrm{poly}(\epsilon))}$, following the explicit form on p.81, and $C(\log_2(2+n+m))^C$ stands for the factor hidden by $\tilde O$ on p.13.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), §1, p.1 (PDF 5); §2.1, p.13 (PDF 17); p.81 (PDF 85)

import Mathlib
import Definitions.Def_DynConnWC_Program

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC

/-! # Online sessions on the word RAM

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), §1, p.1: "all algorithms in this paper are deterministic"; p.13: "we
use the ˜O(·) notation to hide multiplicative factors that are polylogarithmic in m and n, where m and n are the number of
edges and vertices, respectively, in the initial input graph."

**Formalization Note.** The paper names no machine. Programs are those of the published word RAM `DynConnWC.Program` (`read`,
`write`, unit cost per instruction), containing no `rand` instruction. A session feeds the program **blocks** of words: block `0`
is the initialization input and block `t + 1` the `t`-th operation. Since the machine is online, nothing a program writes before it
reads a block depends on that block, so the validity of an operation may depend on what the run has already reported, with no
adversary object: this is what "deterministic algorithms can withstand an adaptive adversary by definition" gives (p.1). Reading past
the last word returns the all-ones word, which is the end marker.

Window `k` runs from the read of the first word of block `k` (from step `0` for `k = 0`) to the read of the first word of block `k + 1` (the
end marker for the last block). A window's **output** is what is written in it. Its **time** is its number of steps. Reports are parsed by
inverting a word encoding: `parseWith enc out` is a list of reports whose concatenated encodings are exactly `out`, and is `none` if there is
no such list. Each encoding used in the mission is prefix-free, so the list is unique. A window's reports are folded into a state by a step
function that returns `none` on an illegal report, so an illegal report makes the run fail its specification.

`Protocol` collects the conventions of one problem. Query windows change no state: their output is the answer. -/

/-- The program contains no `rand` instruction: it is deterministic. -/
def NoRand (P : Program) : Prop :=
  ∀ i, Instr.rand i ∉ P

/-- A constant random tape, never read by a program with `NoRand`. -/
def zeroTape (W : ℕ) : ℕ → Fin (2 ^ W) :=
  fun _ => ⟨0, by positivity⟩

/-- The read number (from `1`) of the first word of block `k`; for `k` the number of blocks it is the read of the end marker. -/
def startRead (blocks : List (List ℕ)) (k : ℕ) : ℕ :=
  1 + ((blocks.take k).map List.length).sum

/-- The run executes every read up to the end marker. -/
def RunsThrough (W : ℕ) (P : Program) (blocks : List (List ℕ)) : Prop :=
  ∀ k ≤ blocks.length,
    (readStep W P blocks.flatten (zeroTape W) (startRead blocks k)).isSome

/-- The step at which window `k` starts. -/
noncomputable def wStart (W : ℕ) (P : Program) (blocks : List (List ℕ)) (k : ℕ) : ℕ :=
  if k = 0 then 0 else (readStep W P blocks.flatten (zeroTape W) (startRead blocks k)).getD 0

/-- The step at which window `k` ends. -/
noncomputable def wEnd (W : ℕ) (P : Program) (blocks : List (List ℕ)) (k : ℕ) : ℕ :=
  (readStep W P blocks.flatten (zeroTape W) (startRead blocks (k + 1))).getD 0

/-- The number of steps of window `k`. -/
noncomputable def wTime (W : ℕ) (P : Program) (blocks : List (List ℕ)) (k : ℕ) : ℕ :=
  wEnd W P blocks k - wStart W P blocks k

/-- The words written in window `k`. -/
noncomputable def wOutput (W : ℕ) (P : Program) (blocks : List (List ℕ)) (k : ℕ) : List ℕ :=
  outputBetween W P blocks.flatten (zeroTape W) (wStart W P blocks k) (wEnd W P blocks k)

open Classical in
/-- The list of reports whose encodings concatenate to `out`. -/
noncomputable def parseWith {R : Type} (enc : R → List ℕ) (out : List ℕ) : Option (List R) :=
  if h : ∃ rs : List R, rs.flatMap enc = out then some h.choose else none

/-- The largest word of a list. -/
def maxWord (l : List ℕ) : ℕ :=
  l.foldr max 0

/-- The answer format `k, e₁, …, e_k` of a path query: the edges of the returned path. -/
def answerEdges : List ℕ → Option (List ℕ)
  | [] => none
  | k :: es => if es.length = k then some es else none

/-- The bound `C·(log₂(2 + n + m))^C` hidden by `Õ`. -/
noncomputable def polylog (C n m : ℕ) : ℝ :=
  (C : ℝ) * (Real.logb 2 (2 + (n : ℝ) + (m : ℝ))) ^ C

/-- The factor `2^{C/ε^C}`, standing for `2^{1/poly(ϵ)}`, `2^{poly(1/ϵ)}` and `2^{O(1/poly(ϵ))}` (the explicit form on p.81). -/
noncomputable def expEps (C : ℕ) (eps : ℝ) : ℝ :=
  (2 : ℝ) ^ ((C : ℝ) / eps ^ C)

/-- The conventions of one online problem. -/
structure Protocol (Op Rep St : Type) where
  /-- The words of an operation. -/
  opWords : Op → List ℕ
  /-- Whether the operation is a query. -/
  isQuery : Op → Bool
  /-- The words of a report. -/
  enc : Rep → List ℕ
  /-- The effect of a report on the state; `none` if the report is illegal. -/
  step : St → Rep → Option St
  /-- The state before the run. -/
  st₀ : St

namespace Protocol

variable {Op Rep St : Type} (π : Protocol Op Rep St)

/-- The blocks of a session: the initialization input, then the operations. -/
def blocks (init : List ℕ) (σ : List Op) : List (List ℕ) :=
  init :: σ.map π.opWords

/-- The words written in window `k` of the session. -/
noncomputable def out (W : ℕ) (P : Program) (init : List ℕ) (σ : List Op) (k : ℕ) : List ℕ :=
  wOutput W P (π.blocks init σ) k

/-- The effect of a window's output on a state. -/
noncomputable def applyWindow (s : St) (out : List ℕ) : Option St :=
  (parseWith π.enc out).bind (fun rs => rs.foldlM π.step s)

/-- The state after initialization and the first `t` operations (`none` if a report so far is illegal or does not parse). -/
noncomputable def state (W : ℕ) (P : Program) (init : List ℕ) (σ : List Op) : ℕ → Option St
  | 0 => π.applyWindow π.st₀ (π.out W P init σ 0)
  | t + 1 =>
    match σ[t]? with
    | some o =>
      if π.isQuery o then state W P init σ t
      else (state W P init σ t).bind (fun s => π.applyWindow s (π.out W P init σ (t + 1)))
    | none => state W P init σ t

/-- The time spent outside query windows, initialization included: the total update time. -/
noncomputable def updateTime (W : ℕ) (P : Program) (init : List ℕ) (σ : List Op) : ℕ :=
  wTime W P (π.blocks init σ) 0 +
    ∑ t ∈ Finset.range σ.length,
      match σ[t]? with
      | some o => if π.isQuery o then 0 else wTime W P (π.blocks init σ) (t + 1)
      | none => 0

/-- The time of the window of operation `t`. -/
noncomputable def opTime (W : ℕ) (P : Program) (init : List ℕ) (σ : List Op) (t : ℕ) : ℕ :=
  wTime W P (π.blocks init σ) (t + 1)

/-- The edges of the path answering operation `t`. -/
noncomputable def answer (W : ℕ) (P : Program) (init : List ℕ) (σ : List Op) (t : ℕ) : Option (List ℕ) :=
  answerEdges (π.out W P init σ (t + 1))

/-- The largest word of the session's input. -/
def inputMax (init : List ℕ) (σ : List Op) : ℕ :=
  maxWord (π.blocks init σ).flatten

end Protocol

end DecrNbhdCover


