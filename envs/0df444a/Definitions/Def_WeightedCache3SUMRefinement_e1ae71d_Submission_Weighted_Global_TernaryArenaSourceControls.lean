-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceControls
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceControls
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:59:13.784878+00:00
-- url     : https://prove2.me/theorems/396a7e38-add6-4a9b-af11-a889b470add5
-- title:
--   TernaryArenaSourceControls
-- statement:
--   Definitions and structural lemmas for TernaryArenaSourceControls, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceControls.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Theorems.Thm_ThreeSum_ReportingHostRelocation_lookup

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSourceControls
open Light WeightedGlobalArenaSourceSetup WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps LightTernarySourceHost
variable {p m F r : ℕ} [Fact p.Prime]
def rowBound (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) : ℕ :=
  (source (r := r) maps cap I right).NL*(localRecords maps cap right).length^r
def components (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) : List ℕ :=
  let S := source (r := r) maps cap I right
  [LightRadixKeys.word S.p0 S.U0 r,LightRadixKeys.word S.p1 S.U1 r,
    LightRadixKeys.word S.p2 S.U2 r,LightSourceResidues.word S.M S.M S.U 0,
    S.bank+2^(S.W+1)+16,S.groups*S.bank+1,S.factor,
    S.factor*(rowBound (r := r) maps cap I right*S.weightU),
    (rowBound (r := r) maps cap I right+1)*S.weightU]
def word (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) : ℕ :=
  (components (r := r) maps cap I right).sum
def depth (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) : ℕ :=
  let S := source (r := r) maps cap I right
  S.NL+S.L+S.J+8
def need (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) : Need :=
  ⟨word (r := r) maps cap I right,0,depth (r := r) maps cap I right⟩
structure Controls (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (lim : Limits) (d : ℕ) : Prop where
  hword0 : (LightRadixKeys.word (source (r := r) maps cap I right).p0
    (source (r := r) maps cap I right).U0 r : ℤ)≤lim.word
  hword1 : (LightRadixKeys.word (source (r := r) maps cap I right).p1
    (source (r := r) maps cap I right).U1 r : ℤ)≤lim.word
  hword2 : (LightRadixKeys.word (source (r := r) maps cap I right).p2
    (source (r := r) maps cap I right).U2 r : ℤ)≤lim.word
  join : (LightSourceResidues.word (p^r) (p^r) (p*(p+1)^r) 0 : ℤ)≤lim.word
  lookup : (((nb m r)+2^(2*N m r+1)+16 : ℕ) : ℤ)≤lim.word
  group : (((F^r)*(nb m r)+1 : ℕ) : ℤ)≤lim.word
  factor : (((2^(r*fixedAlpha m 2)) : ℕ) : ℤ)≤lim.word
  weighted : ((source (r := r) maps cap I right).factor : ℤ)*
    (count (source (r := r) maps cap I right).xs p r (p^r)
      (source (r := r) maps cap I right).NL (source (r := r) maps cap I right).input*I.weightCap : ℕ)≤lim.word
  hist : ((count (source (r := r) maps cap I right).xs p r (p^r)
      (source (r := r) maps cap I right).NL (source (r := r) maps cap I right).input+1 : ℕ) : ℤ)*I.weightCap≤lim.word
  callDepth : d+(source (r := r) maps cap I right).NL+2*N m r+r+8≤lim.depth
end ThreeSum.WeightedGlobalArenaSourceControls
end
end WeightedCache3SUMRefinement_e1ae71d


