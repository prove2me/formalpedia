-- Prove2me | Definitions.Def_StableMSR_CanonicalRegionalCompiler
-- name    : StableMSR_CanonicalRegionalCompiler
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-24T00:54:06.351161+00:00
-- url     : https://prove2.me/theorems/29914ac6-fe3a-477a-8fe4-029e297db8e8
-- title:
--   A deterministic ordering of owned blocks in the regional compiler
-- statement:
--   Sort the point indices within each owned block and sort the list of blocks lexicographically, retaining multiplicities. The resulting regional circuit uses an explicit order computable from the integer geometry. Local circuits and their relocated global assembly are specified with that order. Equivalence of two gate languages records that every recognized word on either side has a permutation recognized on the other side.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547

import Definitions.Def_StableMSR_IntegerWindowCandidates
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP
set_option autoImplicit false

/-- Points increase within a block. The outer list uses lexicographic order and
retains repeated block occurrences. -/
def pointList (l:List ℕ) := l.toFinset.sort (·≤·)
def blockList (ls:List (List ℕ)) := (ls.map pointList).mergeSort (fun a b=>decide (a≤b))
def arrange (d:Instance) : Instance := {d with owned:=fun a c=>blockList (d.owned a c)}
def integerData (n:ℕ) (scene:ℕ→ℤ) (m:ℤ→ℤ) (r h:ℕ) :=
  arrange (Bits.normalized m (Bits.piece n scene (r/n) (r%n)) h)
noncomputable def region (x:World) (W:Cluster x.n) (R:ℝ) (h w:ℕ) :=
  compileRegion (arrange (SingleCodes.instanceOf x W R h)) w
def Equivalent (n:ℕ) (g:Gates) (p:ℕ) (G:Gates) (q:ℕ) :=
  (∀L,Language n g p L → ∃K,Language n G q K ∧ L.Perm K) ∧
  (∀K,Language n G q K → ∃L,Language n g p L ∧ L.Perm K)
noncomputable def appendRegion (x:World) (h w r:ℕ) (a:Assembly) : Assembly :=
  let u:=r/x.n
  let i:=r%x.n
  if i∈WindowProfiles.keys x u then
    if 0<scale x u then
      let c:=region x (WindowProfiles.piece x u i) (scale x u) h w
      {gates:=a.gates++c.1.map (relocateGate a.gates.size),roots:=Function.update a.roots r (a.gates.size+c.2)}
    else {a with roots:=Function.update a.roots r 1}
  else {a with roots:=Function.update a.roots r 0}
noncomputable def rawAssembly (x:World) (h w R:ℕ) :=
  (List.range R).foldl (fun a r=>appendRegion x h w r a) emptyAssembly
noncomputable def assembly (x:World) (h w:ℕ) := padAssembly (rawAssembly x h w (x.rows*x.n)) (x.rows*x.n)
noncomputable def script (x:World) (h w r:ℕ) : Production.Script :=
  let u:=r/x.n
  let i:=r%x.n
  if i∈WindowProfiles.keys x u then
    if 0<scale x u then
      let t:=chart (arrange (SingleCodes.instanceOf x (WindowProfiles.piece x u i) (scale x u) h)) w
      ⟨t.1,(t.2:ℤ)⟩
    else ⟨[],-2⟩
  else ⟨[],-1⟩
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical


