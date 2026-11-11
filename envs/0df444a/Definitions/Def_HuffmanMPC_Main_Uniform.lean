-- Prove2me | Definitions.Def_HuffmanMPC_Main_Uniform
-- name    : HuffmanMPC_Main_Uniform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:24:29.333213+00:00
-- url     : https://prove2.me/theorems/10600a4a-1057-455a-b27f-3251fb0f09d9
-- title:
--   Uniform MPC solvability: one program and constants for all sizes, simultaneous resources
-- statement:
--   An MPC problem specifies, for each index (size and parameter values), its instances, their input words, a validity condition and the required output. A resource envelope gives four real functions of the index: rounds, local memory, total memory and total work.
--
--   A program $p$ solves a problem within $c$ times an envelope, with word coefficient $k$, when for every index there is a machine count such that for every valid instance and every legal input placement some execution of $p$ with words of $k(\lfloor\log_2(2+N)\rfloor+1)$ bits is correct and has at most $c$ times each of the four envelope values, all on the same execution. Here $N$ is the index's scale. A predicate `large` restricts the indices where the bounds are required; correctness is required everywhere. A problem is solvable within $O(\text{envelope})$ when one program and one pair $(c,k)$ work for all indices.
--
--   The output of a table-producing algorithm is the concatenation, in any order, of its fixed-length records.
--
--   **Formalization Note** The program, $c$ and $k$ are chosen before any index or instance, so they cannot depend on the input; the machine count and execution budgets may depend on the index.
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, §§1, 3, 7: the resource claims of Lemmas 4.5–7.3 and Theorems 3.1, 7.1

import Definitions.Def_HuffmanMPC_Main_Machine
import Definitions.Def_HuffmanMPC_Main_Coding

set_option autoImplicit false

namespace HuffmanMPC.Main

/-- A distributed problem. `Index` carries size and algorithm parameters only;
the instances of one index share a single machine count and budget. `scale`
fixes the word universe: words have `k * (⌊log₂(2 + scale)⌋ + 1)` bits. -/
structure MPCProblem (Index : Type) where
  Instance : Index → Type
  scale : Index → ℕ
  input : {i : Index} → Instance i → List ℕ
  valid : {i : Index} → Instance i → Prop
  output : {i : Index} → Instance i → List ℕ → Prop

/-- The four resource envelopes: rounds, peak words per machine, peak words over
all machines, and total word operations. -/
structure ResourceEnvelope (Index : Type) where
  rounds : Index → ℝ
  localSpace : Index → ℝ
  aggregate : Index → ℝ
  work : Index → ℝ

/-- Word width with coefficient `k` for a word universe of size `scale`. -/
def wordWidth (k scale : ℕ) : ℕ := k * (Nat.log2 (2 + scale) + 1)

/-- The single program `p` solves `q` on every index, correctly and with words of
`wordWidth k (scale i)` bits.  On the indices with `large i` its four resources
are at most `c` times the envelope, simultaneously on one execution; on the other
indices it must still be correct, within some finite budget.  `p`, `c` and `k`
are fixed before any index or instance. -/
def ProgramSolves {Index : Type} (q : MPCProblem Index) (bounds : ResourceEnvelope Index)
    (large : Index → Prop) (p : MPCProgram) (c : ℝ) (k : ℕ) : Prop :=
  ∀ i : Index, ∃ (machines : ℕ) (r s mem work : ℝ),
    (large i → r ≤ c * bounds.rounds i ∧ s ≤ c * bounds.localSpace i ∧
      mem ≤ c * bounds.aggregate i ∧ work ≤ c * bounds.work i) ∧
    ∀ x : q.Instance i, q.valid x →
      RunsMPC p (q.input x) (q.output x) (q.scale i) machines
        (wordWidth k (q.scale i)) r s mem work

/-- `q` is solvable within `O(bounds)` at every index: one program and one pair of
constants for all indices. -/
def SolvableMPC {Index : Type} (q : MPCProblem Index) (bounds : ResourceEnvelope Index) : Prop :=
  ∃ (p : MPCProgram) (c : ℝ) (k : ℕ), 0 < c ∧ 0 < k ∧
    ProgramSolves q bounds (fun _ => True) p c k

/-- The distributed output is the concatenation, in some order, of exactly the
records `rs` (each machine emits whole records). -/
def EmitsRecords (out : List ℕ) (rs : List (List ℕ)) : Prop :=
  ∃ rs' : List (List ℕ), rs'.Perm rs ∧ out = rs'.flatten

end HuffmanMPC.Main


