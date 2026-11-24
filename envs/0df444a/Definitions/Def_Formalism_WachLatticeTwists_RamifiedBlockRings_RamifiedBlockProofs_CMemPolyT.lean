-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CMemPolyT
-- name    : Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CMemPolyT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:30.371895+00:00
-- url     : https://prove2.me/theorems/3f76e0d1-72d9-426f-993c-bd73ee423c6a
-- title:
--   CMem Poly T
-- statement:
--   Definitions and structural lemmas for CMem Poly T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/CMemPolyT.lean

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_RingDataObjects
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical Polynomial
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
section
variable {O : Type} [CommRing O] {Xs : Type} (T : Subalgebra O (Xs → O))
  {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (Xs → Matrix d d O))
def polyT : Subalgebra O[X] (Xs → O[X]) where
  carrier := {f | ∀ k, (fun x => (f x).coeff k) ∈ T}
  mul_mem' := by
    intro f g hf hg k
    have h : (fun x => ((f * g) x).coeff k) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, (fun x => (f x).coeff p.1) * (fun x => (g x).coeff p.2) := by
      funext x; simp [Polynomial.coeff_mul, Finset.sum_apply]
    rw [h]
    exact T.sum_mem fun p _ => T.mul_mem (hf _) (hg _)
  add_mem' := by
    intro f g hf hg k
    have h : (fun x => ((f + g) x).coeff k) = (fun x => (f x).coeff k) + fun x => (g x).coeff k := by
      funext x; simp
    rw [h]
    exact T.add_mem (hf k) (hg k)
  algebraMap_mem' p := by
    intro k
    have h : (fun x => ((algebraMap O[X] (Xs → O[X]) p) x).coeff k) =
        algebraMap O (Xs → O) (p.coeff k) := by
      funext x; simp
    rw [h]
    exact T.algebraMap_mem _
def rPoly : G →* (Xs → Matrix d d O[X]) where
  toFun g x := (r g x).map C
  map_one' := by funext x; simp
  map_mul' g h := by funext x; simp [Matrix.map_mul]
end
end Formalism.RepresentationBoundsCohomology.ringDataObjects


