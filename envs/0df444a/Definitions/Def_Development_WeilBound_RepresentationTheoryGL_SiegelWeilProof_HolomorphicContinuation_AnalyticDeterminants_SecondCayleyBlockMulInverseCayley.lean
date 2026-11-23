-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:47.837378+00:00
-- url     : https://prove2.me/theorems/31ab5ecf-8b19-4b58-9fcc-504629482c9e
-- title:
--   Second Cayley Block Mul Inverse Cayley
-- statement:
--   Definitions and structural lemmas for Second Cayley Block Mul Inverse Cayley, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def Cmi (n : ℕ) : M2 n :=
  fromBlocks ((-Complex.I / 2) • 1) ((1 / 2 : ℂ) • 1) ((Complex.I / 2) • 1) ((1 / 2 : ℂ) • 1)
def incl (s : Finset (Fin n)) : Matrix (Fin n) s ℂ := Matrix.of fun c i => if c = (i : Fin n) then 1 else 0
def subOn (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix s s ℂ :=
  M.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n))
end PositivityTheory.Rg.Sw.LVs


