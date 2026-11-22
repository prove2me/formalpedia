-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:04:11.866882+00:00
-- url     : https://prove2.me/theorems/802077e1-8546-41c6-a31b-cbc7cf868e67
-- title:
--   Average One
-- statement:
--   Definitions and structural lemmas for Average One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
section Abstract
variable {Λ : Type} [AddCommGroup Λ] {ι : Type} [Fintype ι] [DecidableEq ι]
def box (ι : Type) [Fintype ι] [DecidableEq ι] (R : ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset (fun _ => range R)
def bpt (e : ι → Λ) (c : Λ) (m : ι → ℕ) : Λ := c + ∑ i, m i • e i
def avg (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) (n : ℕ) : ℂ :=
  ((1 / ((n + 1 : ℝ) ^ Fintype.card ι) : ℝ) : ℂ) * ∑ m ∈ box ι (n + 1), g (bpt e (c n) m)
def LIMf (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) : ℂ :=
  limUnder (hyperfilter ℕ : Filter ℕ) (avg e c g)
def InvAt (e : ι → Λ) (c : ℕ → Λ) (σ : Λ) : Prop :=
  ∀ g, Bdd g → LIMf e c (fun x => g (x + σ)) = LIMf e c g
end Abstract
section Lattice
end Lattice
end Formalism.FourierDecayAlt.P.BoxAverageLimits


