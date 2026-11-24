-- Prove2me | Definitions.Def_StableMSR_ExecutableIntegerAssembly
-- name    : StableMSR_ExecutableIntegerAssembly
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-24T01:04:18.338812+00:00
-- url     : https://prove2.me/theorems/e34a36d7-9399-489c-889f-c44b711e76e9
-- title:
--   The full regional assembly as an executable integer function
-- statement:
--   The input consists of the point count, the scene labels and endpoints, and an integer distance table for each positive row scale. A finite fold checks representatives and valid unequal endpoints, compiles live slots, relocates predecessor pointers, writes the root directory, and pads the gate array. This specifies the complete regional circuit and root directory using integer operations and bounded finite collections.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547

import Definitions.Def_StableMSR_CanonicalRegionalCompiler
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP
set_option autoImplicit false

/-- Positive scales have two distinct valid endpoints in a metric. -/
def positive (n:ℕ) (a b:ℤ) : Bool :=
  match MinSumFPT.toPoint n a,MinSumFPT.toPoint n b with
  | some i,some j=>i != j
  | _,_=>false

def appendInteger (n h w:ℕ) (scene:ℕ→ℤ) (tables:ℕ→ℤ→ℤ) (a:Assembly) (r:ℕ) : Assembly :=
  let u:=r/n
  let base:=3+u*(n+2)
  if (Bits.piece n scene u (r%n)).Nonempty then
    if positive n (scene base) (scene (base+1)) then
      let c:=compileRegion (integerData n scene (tables u) r h) w
      {gates:=a.gates++c.1.map (relocateGate a.gates.size), roots:=Function.update a.roots r (a.gates.size+c.2)}
    else {a with roots:=Function.update a.roots r 1}
  else {a with roots:=Function.update a.roots r 0}

/-- All rows share the scene memory. Each row has an integer table for its scale. -/
def buildInteger (n rows h w:ℕ) (scene:ℕ→ℤ) (tables:ℕ→ℤ→ℤ) : Assembly :=
  let R:=rows*n
  let a:=(List.range R).foldl (appendInteger n h w scene tables) emptyAssembly
  {a with gates:=a.gates++Array.replicate ((R+2)/3-a.gates.size) .stop}

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical


