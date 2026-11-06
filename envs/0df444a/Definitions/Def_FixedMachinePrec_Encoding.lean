-- Prove2me | Definitions.Def_FixedMachinePrec_Encoding
-- name    : FixedMachinePrec_Encoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:00.425198+00:00
-- url     : https://prove2.me/theorems/e4a23395-38d0-4739-b38e-c79f59b15e80
-- title:
--   Input and output words: $\mathrm{enc}(m,G)$, the deadline input, schedules, and correct outputs
-- statement:
--   Numbers are written with the self-delimiting binary code $\mathrm{encBin}$ (each bit $\beta$ of the binary expansion as $1\beta$, then $00$).
--
--   1. The **input word** of $(m,G)$ is the concatenation of the codes of $m$, $n$, the vertex labels $1,\dots,n$, the number of arcs, and the arcs as pairs of labels in the order in which $G$ lists them. Its length is $L$, the binary input length up to a constant factor. A deadline input appends the code of the nonnegative integer $T$.
--   2. The **output word** of an integral schedule lists, for each job $x=1,\dots,n$, the code of its slot and of its machine number ($1,2,\dots$). A deadline answer is the bit $0$ for NO, or the bit $1$ followed by a schedule.
--   3. An output is a **correct optimization output** if it encodes an integral schedule whose real-time reading is optimum among all feasible schedules with real start times; it is a **correct deadline output** if it is NO exactly when the instance is not feasible by $T$, and otherwise encodes a schedule that is feasible with makespan at most $T$.
--
--   **Formalization Note** The code `encBin` is the published definition `QAlgorithms.LocalHamiltonian.encBin`. The arc count is written before the arcs so that a following deadline can be located; no bound is put on $T$.
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), §1, p.1 (binary input length L, listed vertices, distinct arcs, binary deadline)

import Mathlib
import Definitions.Def_FixedMachinePrec_Instance
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding

namespace FixedMachinePrec

open QAlgorithms.LocalHamiltonian (encBin)

/-- **The binary input word of an instance** (Jansen, *Precedence Constraint Scheduling on a Fixed
Number of Machines*, manuscript, sha256 08cdf3e1…, §1, p.1: "let L be the binary input length.
Vertices 1, . . . , n are individually listed, including isolated vertices; arcs are distinct and
use standard binary vertex labels"; Theorem 1.1: "all constants, families, and loops are specified
as functions of its input").

`encInput m G` is the concatenation of the self-delimiting binary codes of `m`, `n`, the vertex
labels `1, …, n`, the number of arcs, and the arcs `(x, y)` as label pairs in the order in which
`G` lists them.

**Formalization Note** Numbers are written with the published self-delimiting code `encBin`
(each bit `β` of the binary expansion as `1β`, then `00`), so the word is uniquely decodable and
its length `L` is the binary input length up to a constant factor; labels are 1-based as printed.
The number of arcs is written before the arcs so that a following deadline can be located. -/
def encInput (m : ℕ) (G : Instance) : List Bool :=
  encBin m ++ encBin G.n ++ (List.range G.n).flatMap (fun i => encBin (i + 1)) ++
    encBin G.arcs.length ++ G.arcs.flatMap (fun a => encBin (a.1.val + 1) ++ encBin (a.2.val + 1))

/-- The input word of a deadline test: the instance followed by the nonnegative binary integer
deadline `T` (§1, p.1: "A deadline, when supplied, is a nonnegative binary integer"). No bound is
placed on `T`. -/
def encDeadlineInput (m : ℕ) (G : Instance) (T : ℕ) : List Bool :=
  encInput m G ++ encBin T

/-- **The output word of an integral schedule**: for each job `x = 1, …, n` in turn, the code of
its slot and the code of its machine number (1-based, machine `1, 2, …` as on p.10). -/
def encSchedule {G : Instance} (σ : SlotSchedule G) : List Bool :=
  (List.finRange G.n).flatMap fun x => encBin (σ.slot x) ++ encBin (σ.machine x + 1)

/-- The output word of a deadline test: `false` for NO, or `true` followed by the schedule. -/
def encDeadlineResult {G : Instance} : Option (SlotSchedule G) → List Bool
  | none => [false]
  | some σ => true :: encSchedule σ

/-- **A correct optimization output**: the word encodes an integral schedule whose real-time
reading is an optimum schedule among all feasible schedules with real start times. -/
def IsOptimumOutput (m : ℕ) (G : Instance) (out : List Bool) : Prop :=
  ∃ σ : SlotSchedule G, out = encSchedule σ ∧ σ.IsOptimum m

/-- **A correct deadline-test output**: NO exactly when no feasible schedule meets `T`; otherwise
`true` followed by an integral schedule whose real-time reading is feasible with makespan at most
`T`. -/
def IsDeadlineOutput (m : ℕ) (G : Instance) (T : ℕ) (out : List Bool) : Prop :=
  (out = [false] ∧ ¬ DeadlineFeasible G m T) ∨
    ∃ σ : SlotSchedule G, out = true :: encSchedule σ ∧ σ.MeetsDeadline m T

end FixedMachinePrec


