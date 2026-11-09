-- Prove2me | Definitions.Def_NearLinearRSP_TwoResources_RAM
-- name    : NearLinearRSP_TwoResources_RAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:54.454715+00:00
-- url     : https://prove2.me/theorems/c1e3e805-2871-4206-ba3f-2dda44eeb353
-- title:
--   Unit-cost real RAM, counted execution and sparse output encoding
-- statement:
--   The problem-specific interface builds on the separate primitive real-RAM machine definition. It supplies read-only edge-list input, a compact preprocessing snapshot, a target query state and an explicit path-output layout.
--
--   The sparse output layout stores target tags and upper distances, the two boundary-tree parent maps, and every computed inner table's values, parent types, predecessor vertices, extraction ranks and edge generating-function factors. Only active vertices require nondefault records. A query starts from this data structure with a target register and otherwise zero registers; its path presence flag, list length and vertex-memory base have fixed register locations. Every path output cell is written by an ordinary charged instruction.
--
--   The separate scales are
--   $$
--   T_{\rm pre}=\frac{\max(1,m)(1+\log\max(2,n))(1+\log(\max(2,n)W))}{\varepsilon^9},\qquad
--   T_{\rm query}=(q+1)^2(|P|+1),
--   $$
--   with $q=\lceil512/(\varepsilon/4)^2\rceil$; an absent path has length zero for this scale. The latter accounts for the finite pair scan and path-writing work separately from preprocessing.
--
--   **Formalization Note** Unit-cost exact exponential evaluation is the computational-model reading of the paper's real-RAM use of exact Poisson probabilities and generating functions. Mathematical definitions of $q$, guesses, logarithmic bounds and tables do not become machine instructions. A program must generate loop bounds by charged operations. Reading or updating fixed operand registers is included in its arithmetic instruction cost; memory access has its own unit cost. Passing a stored data structure to a query means retaining its memory, not copying every cell.
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), p.3, real-RAM computation and compact path representation; p.7 update (✣); pp.9–12 time analysis and deterministic retrieval

import Definitions.Def_NearLinearRSP_TwoResources_Outer
import Definitions.Def_NearLinearRSP_TwoResources_Machine

set_option autoImplicit false

namespace NearLinearRSP.TwoResources

/-- Fixed edge-list input ABI. Only real input cells store weights, C and epsilon. -/
noncomputable def encodeInput (I : Instance) (ε : ℝ) : RAMInput where
  naturals a := if a = 0 then I.graph.n else if a = 1 then I.graph.edges.length else
    if a = 2 then I.source else
      let e := I.graph.edges[(a - 3) / 2]?.getD (0, 0)
      if (a - 3) % 2 = 0 then e.1 else e.2
  reals a := if a = 0 then ε else if a = 1 then I.budget else
    match I.graph.edges[(a - 2) / 2]? with
    | none => 0
    | some e => if (a - 2) % 2 = 0 then I.length e.1 e.2 else I.cost e.1 e.2

/-- A query receives the preprocessing memory snapshot, its target in register 0,
and otherwise zero registers. Passing this data structure incurs no copying charge. -/
noncomputable def queryStart (S : RAMState) (t : ℕ) : RAMState :=
  ⟨0, false, Function.update (fun _ => 0) 0 t, fun _ => 0, S.nm, S.rm⟩

def targetAddress (t : ℕ) : ℕ := 16 + 4 * t
noncomputable def outerQ (ε : ℝ) : ℕ := Nat.ceil (512 / (ε / 4) ^ 2)
noncomputable def tableBase (I : Instance) (ε : ℝ) (r : ℕ) : ℕ :=
  16 + 4 * I.graph.n + 4 * I.graph.n * outerQ ε ^ 2 * r
noncomputable def tableAddress (I : Instance) (ε : ℝ) (r v i j : ℕ) : ℕ :=
  tableBase I ε r + 4 * ((i * outerQ ε + j) * I.graph.n + v)

def parentTag : Parent → ℕ
  | .none => 0
  | .lengthTick => 1
  | .costTick => 2
  | .edge _ => 3

def parentVertex : Parent → ℕ
  | .edge u => u
  | _ => 0

def branchTag : AnswerBranch → ℕ
  | .absent => 0
  | .zeroLength => 1
  | .zeroBudget => 2
  | .inner _ => 3

/-- Sparse layout of the actual output tables and parents. This predicate contains no
correctness or time bound. Unspecified cells are scratch space written by the program. -/
noncomputable def EncodesOutput (I : Instance) (ε : ℝ) (S : RAMState) : Prop :=
  S.nm 0 = outerQ ε ∧ S.nm 1 = I.source ∧ S.nm 2 = I.graph.n ∧
  S.rm 0 = (1 + ε / 8) / (1 + ε / 4) ∧
  (∀ t < I.graph.n,
    S.nm (targetAddress t) = branchTag (answerBranch I ε t) ∧
    (∀ d, answerDistance I ε t = some d → S.rm (targetAddress t) = d) ∧
    (∀ r, answerBranch I ε t = .inner r → S.nm (targetAddress t + 1) = tableBase I ε r)) ∧
  (∀ v ∈ activeVertices I,
    S.nm (targetAddress v + 2) = ((zeroLengthTree I v).parent.map (· + 1)).getD 0 ∧
    S.nm (targetAddress v + 3) = ((zeroBudgetTree I v).parent.map (· + 1)).getD 0) ∧
  (∀ r A, (outerInputs I ε)[r]? = some A →
    ∀ v ∈ activeVertices I, ∀ i < tickLimit A, ∀ j < tickLimit A,
      let addr := tableAddress I ε r v i j
      let c := buildTable A v i j
      S.rm addr = 1 - c.value ∧ S.nm addr = parentTag c.parent ∧
      S.nm (addr + 1) = parentVertex c.parent ∧ S.nm (addr + 2) = c.rank ∧
      (∀ u, c.parent = .edge u →
        S.rm (addr + 1) = lengthPGF A u v ∧ S.rm (addr + 2) = costPGF A u v))

/-- A distance read is constant time from the sparse/default target record. -/
noncomputable def readDistance (S : RAMState) (t : ℕ) : Option ℝ :=
  if S.nm (targetAddress t) = 0 then none else some (S.rm (targetAddress t))

/-- Query output ABI: register 1 is the presence flag, register 2 the list length;
register 3 is the base address of the path vertices in natural memory. Output writes are ordinary store instructions. -/
def queryPath (S : RAMState) : Option (List ℕ) :=
  if S.nr 1 = 0 then none else some ((List.range (S.nr 2)).map (fun k => S.nm (S.nr 3 + k)))

noncomputable def retrievalScale (ε : ℝ) (P : Option (List ℕ)) : ℝ :=
  ((outerQ ε + 1 : ℕ) : ℝ) ^ 2 * ((P.getD []).length + 1 : ℕ)

end NearLinearRSP.TwoResources


