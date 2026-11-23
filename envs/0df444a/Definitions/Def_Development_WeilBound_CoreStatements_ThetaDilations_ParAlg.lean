-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_ParAlg
-- name    : Development_WeilBound_CoreStatements_ThetaDilations_ParAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:38.486878+00:00
-- url     : https://prove2.me/theorems/cbc7f946-dc11-4e1f-8b40-6ae9a775bf11
-- title:
--   Par Alg
-- statement:
--   Definitions and structural lemmas for Par Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}
def blk (a b : K) (r : Fin M → K) (c d : K) (r' u w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    Matrix (Fin (M + 2)) (Fin (M + 2)) K :=
  Matrix.of (Fin.cons (Fin.cons a (Fin.cons b r))
    (Fin.cons (Fin.cons c (Fin.cons d r')) fun i => Fin.cons (u i) (Fin.cons (w i) (U i))))
def pm (a b : K) (r : Fin M → K) (d : K) (w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    Matrix (Fin (M + 2)) (Fin (M + 2)) K := blk a b r 0 d 0 0 w U
variable (s : K →+* K) (J : Matrix (Fin M) (Fin M) K)
def nM (w : Fin M → K) (z : K) : Matrix (Fin (M + 2)) (Fin (M + 2)) K := pm 1 z (-((s ∘ w) ᵥ* J)) 1 w 1
variable {s J}
def mkU {n : ℕ} (s : K →+* K) {J Ji : Matrix (Fin n) (Fin n) K} (hJ : Ji * J = 1) (g : Matrix (Fin n) (Fin n) K)
    (hg : cT s g * J * g = J) : UJ s J :=
  have h : Ji * cT s g * J * g = 1 := by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s g), hg, hJ]
  ⟨⟨g, Ji * cT s g * J, mul_eq_one_comm.1 h, h⟩, hg⟩
end PositivityTheory.PlacePermOperatorBicommutantSpan


