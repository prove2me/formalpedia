-- Prove2me | Definitions.Def_StableMSR_DenseGlobalAssembly
-- name    : StableMSR_DenseGlobalAssembly
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:23:07.679056+00:00
-- url     : https://prove2.me/theorems/4b34a6ad-cd53-4da7-b793-eed8de54125b
-- title:
--   Global assembly of relocated dense regional singleton circuits
-- statement:
--   This module specifies the global circuit used by the dense singleton separator construction. Gate $0$ is the empty word and gate $1$ is the empty language. For each flattened scene/point slot, a live positive-scale region appends `SingleCodes.regionalCircuit` after adding the current array size to both predecessor indices; a nonpositive-scale live slot points to gate $1$, and every other slot points to gate $0$. Empty-language padding ensures that all $S n$ root slots lie below $3|g|$.
--
--   The module also isolates the exact language contract of a live regional circuit and a uniform RAM/layout contract for materializing this fixed global array. These interfaces separate the local compiler induction and the integer-writer/resource proof from the generic global relocation argument.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Supporting implementation of the singleton dynamic-programming circuit and its global gate/root layout.

import Definitions.Def_StableMSR_DenseSingletonCompilation
import Definitions.Def_StableMSR_SingleWindowCodes

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleCodes
open StableMSR.Recovery.WindowProfiles (piece keys)
open StableMSR.Recovery.SingleWindows

namespace StableMSR.Recovery.SingleRAM

/-- Shift every predecessor index, but not literal masks or empty gates. -/
def relocateGate (off : ℕ) : Gate → Gate
  | .stop => .stop
  | .atom pts => .atom pts
  | .both l r => .both (off+l) (off+r)
  | .either l r => .either (off+l) (off+r)

structure Assembly where
  gates : Gates
  roots : ℕ → ℕ

/-- The two global default gates: the empty word and the empty language. -/
def emptyAssembly : Assembly where
  gates := #[.atom [], .stop]
  roots := fun _ => 0

/-- Append one region slot. Missing slots select the global empty word, live slots at
nonpositive scale select the global stop gate, and positive-scale live slots append
`SingleCodes.regionalCircuit` after relocating both predecessor fields. -/
noncomputable def appendRegion (x : World) (h w r : ℕ) (a : Assembly) : Assembly :=
  let u := r / x.n
  let i := r % x.n
  if i ∈ keys x u then
    if 0 < scale x u then
      let c := regionalCircuit x (piece x u i) (scale x u) h w
      { gates := a.gates ++ c.1.map (relocateGate a.gates.size)
        roots := Function.update a.roots r (a.gates.size + c.2) }
    else { a with roots := Function.update a.roots r 1 }
  else { a with roots := Function.update a.roots r 0 }

/-- Assemble the first `R` flattened row/point slots. -/
noncomputable def rawAssembly (x : World) (h w R : ℕ) : Assembly :=
  (List.range R).foldl (fun a r => appendRegion x h w r a) emptyAssembly

/-- Pad with empty-language gates until all `R` roots lie in the three-record arena. -/
noncomputable def padAssembly (a : Assembly) (R : ℕ) : Assembly :=
  { a with gates := a.gates ++ Array.replicate ((R+2)/3 - a.gates.size) .stop }

noncomputable def globalAssembly (x : World) (h w : ℕ) : Assembly :=
  padAssembly (rawAssembly x h w (x.rows*x.n)) (x.rows*x.n)

/-- Exact semantic contract for one positive-scale regional circuit. -/
def LiveCircuitCorrect (x : World) (h w u i : ℕ) : Prop :=
  let c := regionalCircuit x (piece x u i) (scale x u) h w
  let gen := generates x (piece x u i) (scale x u) h w
  c.2 < c.1.size ∧
    (∀ L, Language x.n c.1 c.2 L → L.Nodup ∧ gen L.toFinset) ∧
    ∀ Q, gen Q → ∃ L, Language x.n c.1 c.2 L ∧ L.toFinset = Q

/-- Uniform native realization of the explicitly assembled circuit. Unlike `denseSpec`,
this isolates computation and layout from regional language correctness. -/
def NativeAssemblySpec (e : ℚ) (c D b : ℕ) (cmd : Cmd) : Prop :=
  ∀ (x : World) (s : Store), 1 ≤ x.k → x.k < x.n → IsMetricArray x.dist → Ready x s →
    ∃ t z H, Executes x.dist cmd s t z ∧
      z ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      H ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      let y := worldOf x.k H x.dist t
      Ready y t ∧ y.mem 1 = (x.rows:ℤ) ∧
        let a := globalAssembly x (budget (e:ℝ)) (widthBound (e:ℝ))
        1+5*(1+3*a.gates.size*x.n*x.n) < H ∧ Input y a.gates a.roots

end StableMSR.Recovery.SingleRAM


