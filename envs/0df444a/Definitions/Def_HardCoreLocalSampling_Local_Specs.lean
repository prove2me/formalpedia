-- Prove2me | Definitions.Def_HardCoreLocalSampling_Local_Specs
-- name    : HardCoreLocalSampling_Local_Specs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:40.72504+00:00
-- url     : https://prove2.me/theorems/20748a32-bfaa-43c8-88c8-17e6f6e97cfb
-- title:
--   Input and output conventions of machine-level statements
-- statement:
--   This fixes how the machine-level lemmas read their input and write their output. A graph-context routine has the query label in a register, the deletion list in label memory with its length in an address register, and an index in another; the deleted set of the context is the list together with the pin deletions. The envelope of Lemma 10 assigns mass $q_0$ to $\alpha=0$, the given linear mass to $e_i$, and $(M/\eta)t^{|\alpha|}$ in degrees at least two. Jet outputs are written to fixed cells, in order of total degree and lexicographically within a degree, as signed dyadic endpoints, and an enclosure of $x$ of width at most $2^{-L}$ means both endpoints bracket $x$. A run *fits in $w$ bits* if at every time every number register and number memory cell has at most $w$ bits, which is how working precision is read from a run.
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Lemma 14, printed p.11 (PDF p.12); Appendix A, printed pp.13–14 (PDF pp.14–15)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Params
import Definitions.Def_HardCoreLocalSampling_Local_Instance

namespace HardCoreLocalSampling.Local

/-! Input/output conventions of the machine-level statements in §10 and Appendix A
(printed pp.11–14 / PDF pp.12–15). -/

/-- The run halts within `w` intrinsic work and `q` oracle queries, in a configuration satisfying
`post`. -/
def RunsTo (P : Program) (O : Oracle) (ω : ℕ → Bool) (ξ : ℕ → ℕ → Bool) (init : Config)
    (w q : ℕ) (post : Config → Prop) : Prop :=
  ∃ c, finalConfig P O ω ξ init = some c ∧ c.word ≤ w ∧ c.query ≤ q ∧ post c

/-- The input of a graph-context routine: query label in `L[0]`, the deletion list of length
`D.length` in `Lm[0], Lm[1], ...` with the length in `A[0]`, and an index in `A[1]`. -/
def contextConfig {I : LocalInstance} (D : List I.vertices) (x : I.vertices) (i : ℕ) : Config :=
  { L := regsOf [x.val]
    A := regsOf [D.length, i]
    Lm := regsOf (D.map Subtype.val) }

/-- The deleted set of a graph context: its deletion list together with the pin deletions. -/
noncomputable def contextDeleted {I : LocalInstance} (D : List I.vertices) : Finset I.vertices := by
  classical
  exact D.toFinset ∪ I.pinDeleted

/-- The multi-index envelope of Lemma 10 and Lemma 15: mass `qConst` on `α = 0`, the given linear
mass on `e_i`, and `scale * t^{|α|}` in degrees at least two. -/
noncomputable def envelopeMass {d : ℕ} (qConst : ℚ) (lin : Fin d → ℚ) (scale t : ℚ)
    (α : Fin d → ℕ) : ℚ :=
  if mdeg α = 0 then qConst
  else if mdeg α = 1 then ∑ i, (if α i = 1 then lin i else 0)
  else scale * t ^ mdeg α

/-- The linear masses given as input to the envelope sampler: numerator in `Nm[2i]`,
denominator in `Nm[2i+1]`. -/
def linCells {d : ℕ} (lin : Fin d → ℚ) : List ℕ :=
  (List.ofFn lin).flatMap fun q => [q.num.toNat, q.den]

/-- The multi-index stored in the first `d` number memory cells. -/
def readIndex (c : Config) (d : ℕ) : Fin d → ℕ := fun i => c.Nm i.val

/-- All multi-indices of total degree at most `K`, by degree and lexicographically within a
degree. This fixes where the output of the jet computation is written. -/
def gradedIndices (d K : ℕ) : List (Fin d → ℕ) :=
  (List.range (K + 1)).flatMap fun k => List.Nat.antidiagonalTuple d k

/-- A certified enclosure of `x` stored at address `a`, with lower endpoint at `a` and upper at
`a + 3`, of width at most `2^{-L}`. -/
def EnclosesAt (c : Config) (a L : ℕ) (x : ℝ) : Prop :=
  readDyadic c a ≤ x ∧ x ≤ readDyadic c (a + 3) ∧
    readDyadic c (a + 3) - readDyadic c a ≤ (1 / 2 : ℝ) ^ L

/-- Every number register and number memory cell, at every time of the run, has at most `w`
bits. This is how working precision is read off the run. -/
def NumbersFit (P : Program) (O : Oracle) (ω : ℕ → Bool) (ξ : ℕ → ℕ → Bool) (init : Config)
    (w : ℕ) : Prop :=
  ∀ t a, Nat.size ((run P O ω ξ init t).N a) ≤ w ∧ Nat.size ((run P O ω ξ init t).Nm a) ≤ w

end HardCoreLocalSampling.Local


