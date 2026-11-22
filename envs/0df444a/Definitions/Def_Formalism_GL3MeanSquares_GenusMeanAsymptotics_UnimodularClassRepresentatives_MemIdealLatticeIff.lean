-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:57.774064+00:00
-- url     : https://prove2.me/theorems/d473c861-9d1f-4cf7-9004-b6799214de13
-- title:
--   Mem Ideal Lattice Iff
-- statement:
--   Definitions and structural lemmas for Mem Ideal Lattice Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemIdealLatticeIff.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoTsumDivPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology MeasureTheory Pointwise
open scoped Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
def sBox (F : Type) [Field F] [NumberField F] : Set (mixedEmbedding.mixedSpace F) :=
  {x | ∀ w, 0 < x.1 w ∧ x.1 w ≤ 1}
def gW (F : Type) [Field F] [NumberField F] (m : ℕ) : mixedEmbedding.mixedSpace F → ℝ :=
  fun x => ∏ w, (x.1 w) ^ (m - 1)
def fracU {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ :=
  Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (FractionalIdeal.coeIdeal_ne_zero.2 hI)
end Formalism.HermitianLattices.Ext.L3.BoxSum


