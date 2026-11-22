-- Prove2me | Definitions.Def_BornVolumeLean_Volume_BornFrequency
-- name    : BornVolumeLean_Volume_BornFrequency
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:06:25.874452+00:00
-- url     : https://prove2.me/theorems/f0080bd8-568b-4161-bab9-f3a3ab2bcf79
-- title:
--   Born Frequency
-- statement:
--   Definitions and structural lemmas for Born Frequency, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornFrequency.lean

module
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
namespace BornVolume
variable {M : ℕ}
noncomputable def bornCell (ψ : EuclideanSpace ℂ (Fin (M + 1))) :
    Fin (M + 1) → Set (CPN (M + 1)) :=
  Fin.lastCases
    ((fun (p : CPN (M + 1)) (k : Fin M) => momentMap p (Fin.castSucc k)) ⁻¹'
      ((fun x => apexLin (fun k => ‖ψ (Fin.castSucc k)‖ ^ 2) x
        + fun k => ‖ψ (Fin.castSucc k)‖ ^ 2) '' openSimplexFree))
    (fun i => (fun (p : CPN (M + 1)) (k : Fin M) => momentMap p (Fin.castSucc k)) ⁻¹'
      (replaceMap (fun k => ‖ψ (Fin.castSucc k)‖ ^ 2) i '' openSimplexFree))
end BornVolume


