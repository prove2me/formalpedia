-- Prove2me | Definitions.Def_StableMSR_SeparatorOrdinals
-- name    : StableMSR_SeparatorOrdinals
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-26T00:52:41.5248+00:00
-- url     : https://prove2.me/theorems/8d2edb20-4d85-429d-9d6a-cd3c2a89e23c
-- title:
--   One iteration of the separator assignment writer
-- statement:
--   One iteration consumes a boundary ordinal, decodes it against the regional tables and, when feasible, emits one component entry. The scratch vector can be overwritten while the preceding heap, cut pointers and enclosing loop counters are preserved.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.4 and A.6. Implementation of the regional separator dynamic program.

import Definitions.Def_StableMSR_EligibleSeparatorRows

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit SeparatorLevels TightLanguage
set_option autoImplicit false
set_option maxRecDepth 35000

/-- One iteration of the source loop over boundary ordinals, including validation and emission. -/
def ordinalBody : Program :=
  let counted := ((listOf entryProgram)[5]?).getD .skip
  match ((listOf counted)[3]? : Option Program) with
  | some (Program.loop _ _ body) => ((listOf body)[0]?).getD .skip
  | _ => .skip

/-- Read an ordinal against the immutable word and feasibility tables. -/
def ordinalAssignment (a : State) (cut : List ℕ) : ℕ → Option Assignment :=
  let M := (a.reg 70).toNat
  let word := fun i => (a.heap ((a.reg 76).toNat+i)).toNat
  let ok := fun p i => decide (1 ≤ a.heap ((a.reg 81).toNat+(p*M+i)))
  cut.reverse.foldr (fun v (k : ℕ → Option Assignment) q =>
    if ok v (q%M) then (k (q/M)).map (fun row => row++[(v,word (q%M))]) else none)
    (fun _ => some [])

/-- The scratch vector starts at the cursor on entry. Its cells can be reused
between ordinals; older heap cells and the cut and component pointers survive. -/
structure OrdinalFrame (n : ℕ) (a t : State) : Prop where
  preserved : Between a t
  bitmap : t.reg 241 = a.reg 241
  vector : t.reg 242 = a.reg 242
  lengthReg : t.reg 243 = a.reg 243
  component : t.reg 247 = a.reg 247
  scratch : t.reg 250 = a.reg 8
  reserved : a.reg 8 + (n:ℤ) ≤ t.reg 8

/-- Correctness of just one ordinal, from any state satisfying the loop invariant.
A rejected ordinal emits nothing, and a successful one emits exactly one entry. -/
def OrdinalSteps (d : Instance) (w level : ℕ) (m : ℤ → ℤ) (z : State) (V : ℕ) : Prop :=
  ∀ a cut seed, Between z a → cut ∈ cuts (vertices d) (min w d.n) → CutInput d.n level cut a →
    seed ∈ allowed d cut → a.reg 246 = (seed:ℤ) →
    let c := pieceAt d (allowed d cut) seed
    c.head? = some seed → ComponentArg d.n c a → c.length = level+1 → rimOf d c = cut →
    ∀ q < (a.reg 70).toNat ^ cut.length, ∀ t : State, OrdinalFrame d.n a t →
      t.reg 251 = (q:ℤ) →
      ∃ y k, Executes d.n m ordinalBody t y k ∧ k ≤ V ∧ OrdinalFrame d.n a y ∧
        y.reg 251 = t.reg 251 ∧ y.reg 1085 = t.reg 1085 ∧
        y.output = t.output ++ (ordinalAssignment a cut q).toList.flatMap (entry Naming.name d c)

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal


