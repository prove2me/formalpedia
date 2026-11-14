-- Prove2me | Definitions.Def_CatalyticTreeEval_MachineContracts
-- name    : CatalyticTreeEval_MachineContracts
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T01:28:28.913032+00:00
-- url     : https://prove2.me/theorems/8c73ad92-1b77-4d15-9fdf-f1117157132d
-- title:
--   Exact-time framed contracts for native catalytic machines
-- statement:
--   Execution contracts over the existing finite binary catalytic machine. A segment certifies a successful exact-length run and an invariant at every intermediate configuration. First-exit and first-return variants express control boundaries. Head envelopes bound addressed positions, while writable footprints preserve all other cells and the entire catalyst length. A uniform native contract combines these guarantees with an output append equality. The local seam normalizes heads and clears work beyond the retained prefix; indexed printers return a requested bit or an explicit end-of-file marker. This module supplies interfaces rather than assuming a machine implementation.
-- source:
--   Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Sections 3.1 and 4. Contract design adapted to the native partial binary semantics from tcslib TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean at commit dead9dc88967b25c7aa2db950740ba7b2d74b67e (Apache-2.0).

import Definitions.Def_CatalyticTreeEval_Main_Resources

set_option autoImplicit false

/-!
# Contracts over the existing catalytic machine

The design follows the exact-time segments, first-exit cuts, head envelopes, and frames
in tcslib's `TuringMachine/Build/Contract/Basic.lean` (Apache-2.0, copyright 2026
Seyoon Ragavan). This is a new implementation over the mission's partial binary step
function; it does not introduce another machine model or a simulation assumption.
-/

namespace CatalyticTreeEval.Contracts

universe u

/-- Iteration of a deterministic, possibly failing transition from an arbitrary start.
One iteration is one transition of the supplied semantics. -/
def runFrom {C : Type u} (step : C → Option C) (start : C) : ℕ → Option C
  | 0 => some start
  | t + 1 => (runFrom step start t).bind step

/-- A successful exact-length segment. Its invariant includes both endpoints.
The invariant may depend on elapsed time, for example to locate an oracle query. -/
structure Segment {C : Type u} (step : C → Option C) (inv : ℕ → C → Prop)
    (start finish : C) (time : ℕ) : Prop where
  result : runFrom step start time = some finish
  during : ∀ t ≤ time, ∀ c, runFrom step start t = some c → inv t c

/-- A segment ending at its first exit. A zero-length exit is permitted; callers
which iterate returning rounds must additionally prove positive time. -/
structure FirstExit {C : Type u} (step : C → Option C) (inv : ℕ → C → Prop)
    (exits : Set C) (start finish : C) (time : ℕ) : Prop
    extends Segment step inv start finish time where
  exit_mem : finish ∈ exits
  cut : ∀ t < time, ∀ c, runFrom step start t = some c → c ∉ exits

/-- A positive return to a set containing the starting configuration. Its cut
starts at time one. Loop bodies returning to their own entry must use this
interface rather than `FirstExit`, whose cut also includes time zero. -/
structure FirstReturn {C : Type u} (step : C → Option C) (inv : ℕ → C → Prop)
    (exits : Set C) (start finish : C) (time : ℕ) : Prop
    extends Segment step inv start finish time where
  positive : 0 < time
  start_mem : start ∈ exits
  exit_mem : finish ∈ exits
  cut : ∀ t, 0 < t → t < time → ∀ c, runFrom step start t = some c → c ∉ exits

abbrev Config (M : Main.Machine) := CatalyticMatching.General.Configuration M

/-- Half-open envelopes for the two charged heads. For a printer with an empty
catalyst the catalyst envelope is `[0,1)`, not an assertion that a bit exists. -/
structure Envelope where
  workLo : ℕ
  workHi : ℕ
  catalystLo : ℕ
  catalystHi : ℕ

def Envelope.Contains (E : Envelope) {M : Main.Machine} (c : Config M) : Prop :=
  E.workLo ≤ c.workHead ∧ c.workHead < E.workHi ∧
  E.catalystLo ≤ c.catalystHead ∧ c.catalystHead < E.catalystHi

def Envelope.hull (A B : Envelope) : Envelope :=
  ⟨min A.workLo B.workLo, max A.workHi B.workHi,
   min A.catalystLo B.catalystLo, max A.catalystHi B.catalystHi⟩

/-- The cells a subroutine may change, independently of the head envelope.
In particular, an empty footprint promises preservation, not zero contents. -/
structure Footprint where
  work : Set ℕ
  catalyst : Set ℕ

def Footprint.union (A B : Footprint) : Footprint :=
  ⟨A.work ∪ B.work, A.catalyst ∪ B.catalyst⟩

/-- Exact preservation outside the writable cells, including catalyst length.
Optional list reads distinguish a present `false` bit from the end of the tape. -/
def SameOutside {M : Main.Machine} (F : Footprint) (start finish : Config M) : Prop :=
  (∀ p, p ∉ F.work → finish.work p = start.work p) ∧
  finish.catalyst.length = start.catalyst.length ∧
  (∀ p, p ∉ F.catalyst → finish.catalyst[p]? = start.catalyst[p]?)

/-- Saved caller bits. Restoration of the callee's scratch is a separate claim. -/
def SavedPrefix {M : Main.Machine} (r : ℕ) (start finish : Config M) : Prop :=
  ∀ p < r, finish.work p = start.work p

/-- A caller may discard the suffix only after proving that every bit is zero. -/
def CleanSuffix {M : Main.Machine} (r : ℕ) (c : Config M) : Prop :=
  ∀ p, r ≤ p → c.work p = false

/-- Shared call convention: heads are at origin, retained data occupies the
prefix, and the rest of work is blank. This strengthens the source's suspension
condition by also normalizing the work head, avoiding an implicit saved address. -/
def LocalSeam {M : Main.Machine} (r : ℕ) (c : Config M) : Prop :=
  c.workHead = 0 ∧ c.inputHead = 0 ∧ c.catalystHead = 0 ∧ CleanSuffix r c

/-- A fixed native machine with a uniform, data-indexed subroutine contract.
`post` is the actual endpoint; `emitted` is appended to any pre-existing output.
The footprint holds throughout the run, not just at return. Resource inequalities
and input-specific validity conditions are supplied by clients through `pre`.

Sequencing within this machine has additive time. Combining different machines
requires a separately verified finite-control host and must charge its dispatch.
-/
structure Contract (M : Main.Machine) (ι : Type) where
  entry : Fin M.states
  exits : Set (Option (Fin M.states))
  input : ι → List Bool
  pre : ι → Config M → Prop
  time : ι → Config M → ℕ
  post : ι → Config M → Config M
  envelope : ι → Config M → Envelope
  writes : ι → Config M → Footprint
  emitted : ι → Config M → List Bool
  executes : ∀ i c, c.state = some entry → pre i c →
    FirstExit (M.step (input i))
      (fun _ d => (envelope i c).Contains d ∧ SameOutside (writes i c) c d)
      {d | d.state ∈ exits} c (post i c) (time i c)
  output_eq : ∀ i c, c.state = some entry → pre i c →
    (post i c).output = c.output ++ emitted i c

/-- EOF is distinct from a false data bit; this is the reply to an indexed
stream request, not a buffer containing the entire output. -/
def bitReply : Option Bool → List Bool
  | none => [false]
  | some b => [true, b]

/-- A fixed binary machine recomputes any requested output bit (or EOF) from
the original parameters. Deriving this interface from `Prints` requires a
verified streaming/replay host and its counter bounds; it is not assumed free. -/
def IndexedPrinter {ι : Type} (M : Main.Machine) (params code : ι → List Bool)
    (space time : ι → ℕ → ℝ) : Prop :=
  ∀ i j, Main.PrintsIn M (Main.listCode (params i) ++ Main.natCode j)
    (bitReply ((code i)[j]?)) (space i j) (time i j)

end CatalyticTreeEval.Contracts


