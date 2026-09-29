-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B040
-- name    : CK_CKLaneC2R_EpCells_B040
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:27:57.63355+00:00
-- url     : https://prove2.me/theorems/7e7dc0f4-539b-496d-8ae3-1bc96ea5d16c
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B040` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B040` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B040` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B040 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B040.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B040 =====
section

namespace CKLaneC2R.EpCells.B040

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['164637/1024000', '263589/1638400', '3999/4000', '7999/8000']  interval_lower 112300891/549755813888
noncomputable def e2400 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260453,0,true,163927008704,163927008768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995099,0,false,-192722825280,-192722825216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211305,0,true,164025171904,164025171968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044247,0,false,-192858615232,-192858615168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276245066044,0,true,163888934976,163888935040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922778189508,0,false,-192670165376,-192670165312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276381099858,0,true,164006124672,164006124736⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922642155694,0,false,-192832264768,-192832264704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522886932,0,true,11259072,11259136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500368620,0,false,-11259264,-11259200⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534161985,0,true,22533952,22534016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489093567,0,false,-22534464,-22534400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627314,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627661,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276267158663,0,true,163907968000,163907968064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922756096889,0,false,-192696489536,-192696489472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276392164062,0,true,164015655616,164015655680⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922631091490,0,false,-192845450048,-192845449984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071056517955,0,false,-28829794368,-28829794304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071096723459,0,false,-28788521472,-28788521408⟩
    { al := (164637/1024000), au := (263589/1638400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨176777632677,176891583529⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511216,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163888934976,163888935040⟩ : DyadicInterval 40),(⟨-192670165376,-192670165312⟩ : DyadicInterval 40),(⟨747857678000,747857697329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164006124672,164006124736⟩ : DyadicInterval 40),(⟨-192832264768,-192832264704⟩ : DyadicInterval 40),(⟨747835612260,747835631589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11259156,22534209⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11259072,11259136⟩ : DyadicInterval 40),(⟨-11259264,-11259200⟩ : DyadicInterval 40),(⟨762123383532,762123402861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22533952,22534016⟩ : DyadicInterval 40),(⟨-22534464,-22534400⟩ : DyadicInterval 40),(⟨762123383346,762123402675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176755530887,176880536286⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163907968000,163907968064⟩ : DyadicInterval 40),(⟨-192696489536,-192696489472⟩ : DyadicInterval 40),(⟨747854095605,747854114935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164015655616,164015655680⟩ : DyadicInterval 40),(⟨-192845450048,-192845449984⟩ : DyadicInterval 40),(⟨747833816824,747833836153⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28829794368,-28788521408⟩ : DyadicInterval 40),(⟨776517644320,776538300064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨163927008704,164025171968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192858615232,-192722825216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2400_ok : ecellOkT e2400 = true := by decide +kernel
theorem e2400_pos {a z : ℝ} (ha1 : ((164637/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((263589/1638400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2400 e2400_ok ha1 ha2 hz1 hz2 hz

-- box ['263589/1638400', '659397/4096000', '3999/4000', '7999/8000']  interval_lower 225814985/1099511627776
noncomputable def e2401 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211304,0,true,164025171904,164025171968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044248,0,false,-192858615232,-192858615168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162157,0,true,164123326400,164123326464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093395,0,false,-192994422016,-192994421952⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276358988408,0,true,163987077056,163987077120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922664267144,0,false,-192805914880,-192805914816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276495036466,0,true,164104268544,164104268608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922528219086,0,false,-192968051264,-192968051200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522894467,0,true,11266624,11266688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500361085,0,false,-11266752,-11266688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534177059,0,true,22548992,22549056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489078493,0,false,-22549568,-22549504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627313,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627661,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276381095266,0,true,164006120704,164006120768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922642160286,0,false,-192832259264,-192832259200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276506107789,0,true,164113804864,164113804928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922517147763,0,false,-192981246656,-192981246592⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071019845457,0,false,-28867441792,-28867441728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071060079162,0,false,-28826138560,-28826138496⟩
    { al := (263589/1638400), au := (659397/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨176891583528,177005534381⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163987077056,163987077120⟩ : DyadicInterval 40),(⟨-192805914880,-192805914816⟩ : DyadicInterval 40),(⟨747839200085,747839219414⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164104268544,164104268608⟩ : DyadicInterval 40),(⟨-192968051264,-192968051200⟩ : DyadicInterval 40),(⟨747817117573,747817136902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11266691,22549283⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11266624,11266688⟩ : DyadicInterval 40),(⟨-11266752,-11266688⟩ : DyadicInterval 40),(⟨762123383500,762123402829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22548992,22549056⟩ : DyadicInterval 40),(⟨-22549568,-22549504⟩ : DyadicInterval 40),(⟨762123383377,762123402706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176869467490,176994480013⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164006120704,164006120768⟩ : DyadicInterval 40),(⟨-192832259264,-192832259200⟩ : DyadicInterval 40),(⟨747835612999,747835632328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164113804864,164113804928⟩ : DyadicInterval 40),(⟨-192981246656,-192981246592⟩ : DyadicInterval 40),(⟨747815319748,747815339078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28867441792,-28826138496⟩ : DyadicInterval 40),(⟨776536452864,776557123776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164025171904,164123326464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192994422016,-192858615168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2401_ok : ecellOkT e2401 = true := by decide +kernel
theorem e2401_pos {a z : ℝ} (ha1 : ((263589/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((659397/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2401 e2401_ok ha1 ha2 hz1 hz2 hz

-- box ['164637/1024000', '263589/1638400', '7999/8000', '1']  interval_lower 28053531/137438953472
noncomputable def e2402 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276289260453,0,true,163927008704,163927008768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922733995099,0,false,-192722825280,-192722825216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211305,0,true,164025171904,164025171968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044247,0,false,-192858615232,-192858615168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276267163248,0,true,163907971968,163907972032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922756092304,0,false,-192696494976,-192696494912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522895037,0,true,11267200,11267264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500360515,0,false,-11267328,-11267264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627660,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1276278207225,0,true,163917486400,163917486464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨922745048327,0,false,-192709654528,-192709654464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403219771,0,true,164025179200,164025179264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨922620035781,0,false,-192858625344,-192858625280⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071052960738,0,false,-28833446080,-28833446016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071093171054,0,false,-28792168128,-28792168064⟩
    { al := (164637/1024000), au := (263589/1638400), zl := (7999/8000), zu := 1,
      A := ⟨176777632677,176891583529⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163927008704,163927008768⟩ : DyadicInterval 40),(⟨-192722825280,-192722825216⟩ : DyadicInterval 40),(⟨747850511216,747850530545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163907971968,163907972032⟩ : DyadicInterval 40),(⟨-192696494976,-192696494912⟩ : DyadicInterval 40),(⟨747854094842,747854114171⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11267261⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11267200,11267264⟩ : DyadicInterval 40),(⟨-11267328,-11267264⟩ : DyadicInterval 40),(⟨762123383500,762123402829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨176766579449,176891591995⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨163917486400,163917486464⟩ : DyadicInterval 40),(⟨-192709654528,-192709654464⟩ : DyadicInterval 40),(⟨747852303827,747852323157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025179200,164025179264⟩ : DyadicInterval 40),(⟨-192858625344,-192858625280⟩ : DyadicInterval 40),(⟨747832022621,747832041950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28833446080,-28792168064⟩ : DyadicInterval 40),(⟨776519467648,776540125920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨163927008704,164025171968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192858615232,-192722825216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2402_ok : ecellOkT e2402 = true := by decide +kernel
theorem e2402_pos {a z : ℝ} (ha1 : ((164637/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((263589/1638400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2402 e2402_ok ha1 ha2 hz1 hz2 hz

-- box ['263589/1638400', '659397/4096000', '7999/8000', '1']  interval_lower 56410185/274877906944
noncomputable def e2403 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276403211304,0,true,164025171904,164025171968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922620044248,0,false,-192858615232,-192858615168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162157,0,true,164123326400,164123326464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093395,0,false,-192994422016,-192994421952⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276381099855,0,true,164006124672,164006124736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922642155697,0,false,-192832264768,-192832264704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522902573,0,true,11274688,11274752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500352979,0,false,-11274880,-11274816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627660,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1276392150950,0,true,164015644352,164015644416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨922631104602,0,false,-192845434432,-192845434368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517170621,0,true,164123333696,164123333760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨922506084931,0,false,-192994432064,-192994432000⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1071016283655,0,false,-28871098368,-28871098304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071056522175,0,false,-28829790016,-28829789952⟩
    { al := (263589/1638400), au := (659397/4096000), zl := (7999/8000), zu := 1,
      A := ⟨176891583528,177005534381⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164025171904,164025171968⟩ : DyadicInterval 40),(⟨-192858615232,-192858615168⟩ : DyadicInterval 40),(⟨747832023988,747832043317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164006124672,164006124736⟩ : DyadicInterval 40),(⟨-192832264768,-192832264704⟩ : DyadicInterval 40),(⟨747835612260,747835631590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11274797⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11274688,11274752⟩ : DyadicInterval 40),(⟨-11274880,-11274816⟩ : DyadicInterval 40),(⟨762123383532,762123402861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨176880523174,177005542845⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164015644352,164015644416⟩ : DyadicInterval 40),(⟨-192845434432,-192845434368⟩ : DyadicInterval 40),(⟨747833818938,747833838267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123333696,164123333760⟩ : DyadicInterval 40),(⟨-192994432064,-192994432000⟩ : DyadicInterval 40),(⟨747813523232,747813542561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28871098368,-28829789952⟩ : DyadicInterval 40),(⟨776538278592,776558952064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨164025171904,164123326464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-192994422016,-192858615168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2403_ok : ecellOkT e2403 = true := by decide +kernel
theorem e2403_pos {a z : ℝ} (ha1 : ((263589/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((659397/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2403 e2403_ok ha1 ha2 hz1 hz2 hz

-- box ['659397/4096000', '1319643/8192000', '3999/4000', '7999/8000']  interval_lower 56757615/274877906944
noncomputable def e2404 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162156,0,true,164123326400,164123326464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093396,0,false,-192994422016,-192994421952⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113008,0,true,164221472128,164221472192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142544,0,false,-193130245504,-193130245440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276472910772,0,true,164085210368,164085210432⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922550344780,0,false,-192941681152,-192941681088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276608973073,0,true,164202403712,164202403776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922414282479,0,false,-193103854528,-193103854464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522902004,0,true,11274112,11274176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500353548,0,false,-11274304,-11274240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534192134,0,true,22564096,22564160⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489063418,0,false,-22564608,-22564544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627312,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627661,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276495031869,0,true,164104264576,164104264640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922528223683,0,false,-192968045760,-192968045696⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276620051523,0,true,164211945280,164211945344⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922403204029,0,false,-193117060096,-193117060032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070983149340,0,false,-28905114752,-28905114688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1071023411251,0,false,-28863781120,-28863781056⟩
    { al := (659397/4096000), au := (1319643/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨177005534380,177119485232⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013115,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164085210368,164085210432⟩ : DyadicInterval 40),(⟨-192941681152,-192941681088⟩ : DyadicInterval 40),(⟨747820710060,747820729389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164202403712,164202403776⟩ : DyadicInterval 40),(⟨-193103854528,-193103854464⟩ : DyadicInterval 40),(⟨747798610732,747798630061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11274228,22564358⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11274112,11274176⟩ : DyadicInterval 40),(⟨-11274304,-11274240⟩ : DyadicInterval 40),(⟨762123383532,762123402861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22564096,22564160⟩ : DyadicInterval 40),(⟨-22564608,-22564544⟩ : DyadicInterval 40),(⟨762123383344,762123402673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨176983404093,177108423747⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164104264576,164104264640⟩ : DyadicInterval 40),(⟨-192968045760,-192968045696⟩ : DyadicInterval 40),(⟨747817118314,747817137643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164211945280,164211945344⟩ : DyadicInterval 40),(⟨-193117060096,-193117060032⟩ : DyadicInterval 40),(⟨747796810615,747796829945⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28905114752,-28863781056⟩ : DyadicInterval 40),(⟨776555274144,776575960256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164123326400,164221472192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193130245504,-192994421952⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2404_ok : ecellOkT e2404 = true := by decide +kernel
theorem e2404_pos {a z : ℝ} (ha1 : ((659397/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1319643/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2404 e2404_ok ha1 ha2 hz1 hz2 hz

-- box ['1319643/8192000', '330123/2048000', '3999/4000', '7999/8000']  interval_lower 114124639/549755813888
noncomputable def e2405 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113007,0,true,164221472128,164221472192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142545,0,false,-193130245504,-193130245440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063859,0,true,164319609088,164319609152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191693,0,false,-193266085824,-193266085760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276586833135,0,true,164183334976,164183335040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922436422417,0,false,-193077464192,-193077464128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276722909680,0,true,164300530112,164300530176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922300345872,0,false,-193239674624,-193239674560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522909541,0,true,11281664,11281728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500346011,0,false,-11281856,-11281792⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534207210,0,true,22579200,22579264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489048342,0,false,-22579712,-22579648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627312,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627661,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276608968478,0,true,164202399744,164202399808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922414287074,0,false,-193103849088,-193103849024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276733995249,0,true,164310076928,164310076992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922289260303,0,false,-193252890240,-193252890176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070946429610,0,false,-28942813248,-28942813184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070986719725,0,false,-28901449280,-28901449216⟩
    { al := (1319643/8192000), au := (330123/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨177119485231,177233436083⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013116,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164183334976,164183335040⟩ : DyadicInterval 40),(⟨-193077464192,-193077464128⟩ : DyadicInterval 40),(⟨747802207887,747802227217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164300530112,164300530176⟩ : DyadicInterval 40),(⟨-193239674624,-193239674560⟩ : DyadicInterval 40),(⟨747780091799,747780111129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11281765,22579434⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11281664,11281728⟩ : DyadicInterval 40),(⟨-11281856,-11281792⟩ : DyadicInterval 40),(⟨762123383532,762123402861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22579200,22579264⟩ : DyadicInterval 40),(⟨-22579712,-22579648⟩ : DyadicInterval 40),(⟨762123383344,762123402673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177097340702,177222367473⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164202399744,164202399808⟩ : DyadicInterval 40),(⟨-193103849088,-193103849024⟩ : DyadicInterval 40),(⟨747798611500,747798630829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164310076928,164310076992⟩ : DyadicInterval 40),(⟨-193252890240,-193252890176⟩ : DyadicInterval 40),(⟨747778289335,747778308664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28942813248,-28901449216⟩ : DyadicInterval 40),(⟨776574108224,776594809504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164221472128,164319609152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193266085824,-193130245440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2405_ok : ecellOkT e2405 = true := by decide +kernel
theorem e2405_pos {a z : ℝ} (ha1 : ((1319643/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((330123/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2405 e2405_ok ha1 ha2 hz1 hz2 hz

-- box ['659397/4096000', '1319643/8192000', '7999/8000', '1']  interval_lower 226856083/1099511627776
noncomputable def e2406 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276517162156,0,true,164123326400,164123326464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922506093396,0,false,-192994422016,-192994421952⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113008,0,true,164221472128,164221472192⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142544,0,false,-193130245504,-193130245440⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276495036464,0,true,164104268544,164104268608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922528219088,0,false,-192968051264,-192968051200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522910111,0,true,11282240,11282304⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500345441,0,false,-11282432,-11282368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627660,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1276506094676,0,true,164113793536,164113793600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨922517160876,0,false,-192981231040,-192981230976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631121477,0,true,164221479424,164221479488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨922392134075,0,false,-193130255616,-193130255552⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070979582951,0,false,-28908776192,-28908776128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1071019849680,0,false,-28867437440,-28867437376⟩
    { al := (659397/4096000), au := (1319643/8192000), zl := (7999/8000), zu := 1,
      A := ⟨177005534380,177119485232⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164123326400,164123326464⟩ : DyadicInterval 40),(⟨-192994422016,-192994421952⟩ : DyadicInterval 40),(⟨747813524627,747813543956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013115,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164104268544,164104268608⟩ : DyadicInterval 40),(⟨-192968051264,-192968051200⟩ : DyadicInterval 40),(⟨747817117573,747817136903⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013115,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11282335⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11282240,11282304⟩ : DyadicInterval 40),(⟨-11282432,-11282368⟩ : DyadicInterval 40),(⟨762123383532,762123402861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨176994466900,177119493701⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164113793536,164113793600⟩ : DyadicInterval 40),(⟨-192981231040,-192981230976⟩ : DyadicInterval 40),(⟨747815321903,747815341232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221479424,164221479488⟩ : DyadicInterval 40),(⟨-193130255616,-193130255552⟩ : DyadicInterval 40),(⟨747795011745,747795031075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28908776192,-28867437376⟩ : DyadicInterval 40),(⟨776557102304,776577790976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨164123326400,164221472192⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193130245504,-192994421952⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2406_ok : ecellOkT e2406 = true := by decide +kernel
theorem e2406_pos {a z : ℝ} (ha1 : ((659397/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1319643/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2406 e2406_ok ha1 ha2 hz1 hz2 hz

-- box ['1319643/8192000', '330123/2048000', '7999/8000', '1']  interval_lower 228074481/1099511627776
noncomputable def e2407 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276631113007,0,true,164221472128,164221472192⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922392142545,0,false,-193130245504,-193130245440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063859,0,true,164319609088,164319609152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191693,0,false,-193266085824,-193266085760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276608973071,0,true,164202403712,164202403776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922414282481,0,false,-193103854528,-193103854464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522917648,0,true,11289792,11289856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500337904,0,false,-11289984,-11289920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627660,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1276620038406,0,true,164211933952,164211934016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨922403217146,0,false,-193117044416,-193117044352⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745072326,0,true,164319616384,164319616448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨922278183226,0,false,-193266095936,-193266095872⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070942858630,0,false,-28946479488,-28946479424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070983153567,0,false,-28905110400,-28905110336⟩
    { al := (1319643/8192000), au := (330123/2048000), zl := (7999/8000), zu := 1,
      A := ⟨177119485231,177233436083⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164221472128,164221472192⟩ : DyadicInterval 40),(⟨-193130245504,-193130245440⟩ : DyadicInterval 40),(⟨747795013116,747795032445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164202403712,164202403776⟩ : DyadicInterval 40),(⟨-193103854528,-193103854464⟩ : DyadicInterval 40),(⟨747798610732,747798630061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11289872⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11289792,11289856⟩ : DyadicInterval 40),(⟨-11289984,-11289920⟩ : DyadicInterval 40),(⟨762123383532,762123402861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨177108410630,177233444550⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164211933952,164211934016⟩ : DyadicInterval 40),(⟨-193117044416,-193117044352⟩ : DyadicInterval 40),(⟨747796812746,747796832075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319616384,164319616448⟩ : DyadicInterval 40),(⟨-193266095936,-193266095872⟩ : DyadicInterval 40),(⟨747776488135,747776507464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28946479488,-28905110336⟩ : DyadicInterval 40),(⟨776575938784,776596642624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨164221472128,164319609152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193266085824,-193130245440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2407_ok : ecellOkT e2407 = true := by decide +kernel
theorem e2407_pos {a z : ℝ} (ha1 : ((1319643/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((330123/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2407 e2407_ok ha1 ha2 hz1 hz2 hz

-- box ['330123/2048000', '1321341/8192000', '1999/2000', '7997/8000']  interval_lower 114910831/549755813888
noncomputable def e2408 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063858,0,true,164319609088,164319609152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191694,0,false,-193266085824,-193266085760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014710,0,true,164417737280,164417737344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240842,0,false,-193401942912,-193401942848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276656447139,0,true,164243291200,164243291264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922366808413,0,false,-193160444800,-193160444736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276792509440,0,true,164360467648,164360467712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922230746112,0,false,-193322650432,-193322650368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545496039,0,true,33867712,33867776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477759513,0,false,-33868800,-33868736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556816323,0,true,45187584,45187648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466439229,0,false,-45189504,-45189440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625918,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626733,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276700751057,0,true,164281446976,164281447040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922322504495,0,false,-193213258752,-193213258688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276825770658,0,true,164389110272,164389110336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922197484894,0,false,-193362306176,-193362306112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070916836714,0,false,-28973195904,-28973195840⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070957145390,0,false,-28931811712,-28931811648⟩
    { al := (330123/2048000), au := (1321341/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨177233436082,177347386934⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164243291200,164243291264⟩ : DyadicInterval 40),(⟨-193160444800,-193160444736⟩ : DyadicInterval 40),(⟨747790895912,747790915242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164360467648,164360467712⟩ : DyadicInterval 40),(⟨-193322650432,-193322650368⟩ : DyadicInterval 40),(⟨747768773288,747768792618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33868263,45188547⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33867712,33867776⟩ : DyadicInterval 40),(⟨-33868800,-33868736⟩ : DyadicInterval 40),(⟨762123383052,762123402381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45187584,45187648⟩ : DyadicInterval 40),(⟨-45189504,-45189440⟩ : DyadicInterval 40),(⟨762123382654,762123401983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177189123281,177314142882⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164281446976,164281447040⟩ : DyadicInterval 40),(⟨-193213258752,-193213258688⟩ : DyadicInterval 40),(⟨747783694353,747783713682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164389110272,164389110336⟩ : DyadicInterval 40),(⟨-193362306176,-193362306112⟩ : DyadicInterval 40),(⟨747763362618,747763381948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28973195904,-28931811648⟩ : DyadicInterval 40),(⟨776589289440,776610000832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164319609088,164417737344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193401942912,-193266085760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2408_ok : ecellOkT e2408 = true := by decide +kernel
theorem e2408_pos {a z : ℝ} (ha1 : ((330123/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1321341/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2408 e2408_ok ha1 ha2 hz1 hz2 hz

-- box ['1321341/8192000', '132219/819200', '1999/2000', '7997/8000']  interval_lower 231047045/1099511627776
noncomputable def e2409 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014709,0,true,164417737280,164417737344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240843,0,false,-193401942912,-193401942848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965561,0,true,164515856704,164515856768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289991,0,false,-193537816768,-193537816704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276770341015,0,true,164341377152,164341377216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922252914537,0,false,-193296220864,-193296220800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276906417560,0,true,164458555456,164458555520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922116837992,0,false,-193458463552,-193458463488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545518654,0,true,33890304,33890368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477736898,0,false,-33891456,-33891392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556846479,0,true,45217728,45217792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466409073,0,false,-45219648,-45219584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625916,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626732,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276814673421,0,true,164379554048,164379554112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922208582131,0,false,-193349075328,-193349075264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276939700147,0,true,164487213824,164487213888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922083555405,0,false,-193498149696,-193498149632⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070880078941,0,false,-29010935808,-29010935744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070920415823,0,false,-28969521216,-28969521152⟩
    { al := (1321341/8192000), au := (132219/819200), zl := (1999/2000), zu := (7997/8000),
      A := ⟨177347386933,177461337785⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164341377152,164341377216⟩ : DyadicInterval 40),(⟨-193296220864,-193296220800⟩ : DyadicInterval 40),(⟨747772378845,747772398175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164458555456,164458555520⟩ : DyadicInterval 40),(⟨-193458463552,-193458463488⟩ : DyadicInterval 40),(⟨747750239424,747750258753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33890878,45218703⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33890304,33890368⟩ : DyadicInterval 40),(⟨-33891456,-33891392⟩ : DyadicInterval 40),(⟨762123383083,762123402412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45217728,45217792⟩ : DyadicInterval 40),(⟨-45219648,-45219584⟩ : DyadicInterval 40),(⟨762123382652,762123401981⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177303045645,177428072371⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164379554048,164379554112⟩ : DyadicInterval 40),(⟨-193349075328,-193349075264⟩ : DyadicInterval 40),(⟨747765167955,747765187284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164487213824,164487213888⟩ : DyadicInterval 40),(⟨-193498149696,-193498149632⟩ : DyadicInterval 40),(⟨747744821804,747744841134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29010935808,-28969521152⟩ : DyadicInterval 40),(⟨776608144192,776628870784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164417737280,164515856768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193537816768,-193401942848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2409_ok : ecellOkT e2409 = true := by decide +kernel
theorem e2409_pos {a z : ℝ} (ha1 : ((1321341/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((132219/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2409 e2409_ok ha1 ha2 hz1 hz2 hz

-- box ['330123/2048000', '1321341/8192000', '7997/8000', '3999/4000']  interval_lower 28705807/137438953472
noncomputable def e2410 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063858,0,true,164319609088,164319609152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191694,0,false,-193266085824,-193266085760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014710,0,true,164417737280,164417737344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240842,0,false,-193401942912,-193401942848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276678601319,0,true,164262371136,164262371200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922344654233,0,false,-193186854080,-193186854016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276814677864,0,true,164379557888,164379557952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922208577688,0,false,-193349080640,-193349080576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534206586,0,true,22578560,22578624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489048966,0,false,-22579072,-22579008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545519333,0,true,33891008,33891072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477736219,0,false,-33892096,-33892032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626731,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627313,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276711828055,0,true,164290986624,164290986688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922311427497,0,false,-193226463808,-193226463744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276836854806,0,true,164398655104,164398655168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922186400746,0,false,-193375521600,-193375521536⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070913261604,0,false,-28976866496,-28976866432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070953575105,0,false,-28935477184,-28935477120⟩
    { al := (330123/2048000), au := (1321341/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨177233436082,177347386934⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164262371136,164262371200⟩ : DyadicInterval 40),(⟨-193186854080,-193186854016⟩ : DyadicInterval 40),(⟨747787295007,747787314337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164379557888,164379557952⟩ : DyadicInterval 40),(⟨-193349080640,-193349080576⟩ : DyadicInterval 40),(⟨747765167231,747765186560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22578810,33891557⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22578560,22578624⟩ : DyadicInterval 40),(⟨-22579072,-22579008⟩ : DyadicInterval 40),(⟨762123383344,762123402673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33891008,33891072⟩ : DyadicInterval 40),(⟨-33892096,-33892032⟩ : DyadicInterval 40),(⟨762123383051,762123402380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177200200279,177325227030⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164290986624,164290986688⟩ : DyadicInterval 40),(⟨-193226463808,-193226463744⟩ : DyadicInterval 40),(⟨747781893473,747781912803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164398655104,164398655168⟩ : DyadicInterval 40),(⟨-193375521600,-193375521536⟩ : DyadicInterval 40),(⟨747761559328,747761578657⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28976866496,-28935477120⟩ : DyadicInterval 40),(⟨776591122176,776611836128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164319609088,164417737344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193401942912,-193266085760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2410_ok : ecellOkT e2410 = true := by decide +kernel
theorem e2410_pos {a z : ℝ} (ha1 : ((330123/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1321341/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2410 e2410_ok ha1 ha2 hz1 hz2 hz

-- box ['1321341/8192000', '132219/819200', '7997/8000', '3999/4000']  interval_lower 230871463/1099511627776
noncomputable def e2411 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014709,0,true,164417737280,164417737344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240843,0,false,-193401942912,-193401942848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965561,0,true,164515856704,164515856768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289991,0,false,-193537816768,-193537816704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276792509438,0,true,164360467648,164360467712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922230746114,0,false,-193322650432,-193322650368⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276928600227,0,true,164477656192,164477656256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922094655325,0,false,-193484913984,-193484913920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534221663,0,true,22593600,22593664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489033889,0,false,-22594176,-22594112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545541950,0,true,33913600,33913664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477713602,0,false,-33914752,-33914688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626729,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627312,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276825757536,0,true,164389098944,164389099008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922197498016,0,false,-193362290560,-193362290496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276950791413,0,true,164496763968,164496764032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922072464139,0,false,-193511375232,-193511375168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070876499236,0,false,-29014611200,-29014611136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070916840947,0,false,-28973191552,-28973191488⟩
    { al := (1321341/8192000), au := (132219/819200), zl := (7997/8000), zu := (3999/4000),
      A := ⟨177347386933,177461337785⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164360467648,164360467712⟩ : DyadicInterval 40),(⟨-193322650432,-193322650368⟩ : DyadicInterval 40),(⟨747768773288,747768792618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164477656192,164477656256⟩ : DyadicInterval 40),(⟨-193484913984,-193484913920⟩ : DyadicInterval 40),(⟨747746628717,747746648047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22593887,33914174⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22593600,22593664⟩ : DyadicInterval 40),(⟨-22594176,-22594112⟩ : DyadicInterval 40),(⟨762123383375,762123402704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33913600,33913664⟩ : DyadicInterval 40),(⟨-33914752,-33914688⟩ : DyadicInterval 40),(⟨762123383081,762123402410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177314129760,177439163637⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164389098944,164389099008⟩ : DyadicInterval 40),(⟨-193362290560,-193362290496⟩ : DyadicInterval 40),(⟨747763364781,747763384111⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164496763968,164496764032⟩ : DyadicInterval 40),(⟨-193511375232,-193511375168⟩ : DyadicInterval 40),(⟨747743016152,747743035481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29014611200,-28973191488⟩ : DyadicInterval 40),(⟨776609979360,776630708480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164417737280,164515856768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193537816768,-193401942848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2411_ok : ecellOkT e2411 = true := by decide +kernel
theorem e2411_pos {a z : ℝ} (ha1 : ((1321341/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((132219/819200 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2411 e2411_ok ha1 ha2 hz1 hz2 hz

-- box ['132219/819200', '1323039/8192000', '1999/2000', '7997/8000']  interval_lower 232275599/1099511627776
noncomputable def e2412 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965560,0,true,164515856704,164515856768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289992,0,false,-193537816768,-193537816704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916412,0,true,164613967424,164613967488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339140,0,false,-193673707456,-193673707392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276884234891,0,true,164439454336,164439454400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922139020661,0,false,-193432013760,-193432013696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277020325679,0,true,164556634432,164556634496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922002929873,0,false,-193594293440,-193594293376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545541270,0,true,33912960,33913024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477714282,0,false,-33914048,-33913984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556876638,0,true,45247872,45247936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466378914,0,false,-45249856,-45249792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625913,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626730,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276928595780,0,true,164477652352,164477652416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922094659772,0,false,-193484908672,-193484908608⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277053629632,0,true,164585308672,164585308736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921969625920,0,false,-193634009984,-193634009920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070843297558,0,false,-29048701248,-29048701184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070883662650,0,false,-29007256320,-29007256256⟩
    { al := (132219/819200), au := (1323039/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨177461337784,177575288636⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164439454336,164439454400⟩ : DyadicInterval 40),(⟨-193432013760,-193432013696⟩ : DyadicInterval 40),(⟨747753849704,747753869033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164556634432,164556634496⟩ : DyadicInterval 40),(⟨-193594293440,-193594293376⟩ : DyadicInterval 40),(⟨747731693488,747731712817⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33913494,45248862⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33912960,33913024⟩ : DyadicInterval 40),(⟨-33914048,-33913984⟩ : DyadicInterval 40),(⟨762123383049,762123402378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45247872,45247936⟩ : DyadicInterval 40),(⟨-45249856,-45249792⟩ : DyadicInterval 40),(⟨762123382681,762123402010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177416968004,177542001856⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164477652352,164477652416⟩ : DyadicInterval 40),(⟨-193484908672,-193484908608⟩ : DyadicInterval 40),(⟨747746629444,747746648773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164585308672,164585308736⟩ : DyadicInterval 40),(⟨-193634009984,-193634009920⟩ : DyadicInterval 40),(⟨747726268835,747726288165⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29048701248,-29007256256⟩ : DyadicInterval 40),(⟨776627011744,776647753504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164515856704,164613967488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193673707456,-193537816704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2412_ok : ecellOkT e2412 = true := by decide +kernel
theorem e2412_pos {a z : ℝ} (ha1 : ((132219/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1323039/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2412 e2412_ok ha1 ha2 hz1 hz2 hz

-- box ['1323039/8192000', '82743/512000', '1999/2000', '7997/8000']  interval_lower 58376681/274877906944
noncomputable def e2413 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916411,0,true,164613967424,164613967488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339141,0,false,-193673707456,-193673707392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867263,0,true,164712069376,164712069440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388289,0,false,-193809614912,-193809614848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276998128766,0,true,164537522816,164537522880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922025126786,0,false,-193567823424,-193567823360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277134233799,0,true,164654704704,164654704768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921889021753,0,false,-193730140160,-193730140096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545563889,0,true,33935552,33935616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477691663,0,false,-33936640,-33936576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556906798,0,true,45278080,45278144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466348754,0,false,-45280000,-45279936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625911,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626729,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277042518143,0,true,164575741952,164575742016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921980737409,0,false,-193620758848,-193620758784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277167559118,0,true,164683394816,164683394880⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921855696434,0,false,-193769887040,-193769886976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070806492565,0,false,-29086492224,-29086492160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070846885869,0,false,-29045016896,-29045016832⟩
    { al := (1323039/8192000), au := (82743/512000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨177575288635,177689239487⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164537522816,164537522880⟩ : DyadicInterval 40),(⟨-193567823424,-193567823360⟩ : DyadicInterval 40),(⟨747735308421,747735327751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164654704704,164654704768⟩ : DyadicInterval 40),(⟨-193730140160,-193730140096⟩ : DyadicInterval 40),(⟨747713135430,747713154759⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33936113,45279022⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33935552,33935616⟩ : DyadicInterval 40),(⟨-33936640,-33936576⟩ : DyadicInterval 40),(⟨762123383048,762123402377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45278080,45278144⟩ : DyadicInterval 40),(⟨-45280000,-45279936⟩ : DyadicInterval 40),(⟨762123382647,762123401976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177530890367,177655931342⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164575741952,164575742016⟩ : DyadicInterval 40),(⟨-193620758848,-193620758784⟩ : DyadicInterval 40),(⟨747728078805,747728098135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164683394816,164683394880⟩ : DyadicInterval 40),(⟨-193769887040,-193769886976⟩ : DyadicInterval 40),(⟨747707703708,747707723038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29086492224,-29045016832⟩ : DyadicInterval 40),(⟨776645892032,776666648992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164613967424,164712069440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193809614912,-193673707392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2413_ok : ecellOkT e2413 = true := by decide +kernel
theorem e2413_pos {a z : ℝ} (ha1 : ((1323039/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((82743/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2413 e2413_ok ha1 ha2 hz1 hz2 hz

-- box ['132219/819200', '1323039/8192000', '7997/8000', '3999/4000']  interval_lower 232099341/1099511627776
noncomputable def e2414 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965560,0,true,164515856704,164515856768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289992,0,false,-193537816768,-193537816704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916412,0,true,164613967424,164613967488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339140,0,false,-193673707456,-193673707392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276906417558,0,true,164458555456,164458555520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922116837994,0,false,-193458463552,-193458463488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277042522590,0,true,164575745792,164575745856⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921980732962,0,false,-193620764160,-193620764096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534236741,0,true,22608704,22608768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489018811,0,false,-22609216,-22609152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545564568,0,true,33936256,33936320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477690984,0,false,-33937344,-33937280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626728,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627312,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276939687023,0,true,164487202560,164487202624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922083568529,0,false,-193498134016,-193498133952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277064728022,0,true,164594864064,164594864128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921958527530,0,false,-193647245632,-193647245568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070839713254,0,false,-29052381504,-29052381440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070880083177,0,false,-29010931456,-29010931392⟩
    { al := (132219/819200), au := (1323039/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨177461337784,177575288636⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164458555456,164458555520⟩ : DyadicInterval 40),(⟨-193458463552,-193458463488⟩ : DyadicInterval 40),(⟨747750239424,747750258754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164575745792,164575745856⟩ : DyadicInterval 40),(⟨-193620764160,-193620764096⟩ : DyadicInterval 40),(⟨747728078078,747728097407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22608965,33936792⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22608704,22608768⟩ : DyadicInterval 40),(⟨-22609216,-22609152⟩ : DyadicInterval 40),(⟨762123383343,762123402672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33936256,33936320⟩ : DyadicInterval 40),(⟨-33937344,-33937280⟩ : DyadicInterval 40),(⟨762123383048,762123402377⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177428059247,177553100246⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164487202560,164487202624⟩ : DyadicInterval 40),(⟨-193498134016,-193498133952⟩ : DyadicInterval 40),(⟨747744823907,747744843237⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164594864064,164594864128⟩ : DyadicInterval 40),(⟨-193647245632,-193647245568⟩ : DyadicInterval 40),(⟨747724460854,747724480183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29052381504,-29010931392⟩ : DyadicInterval 40),(⟨776628849312,776649593632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164515856704,164613967488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193673707456,-193537816704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2414_ok : ecellOkT e2414 = true := by decide +kernel
theorem e2414_pos {a z : ℝ} (ha1 : ((132219/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1323039/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2414 e2414_ok ha1 ha2 hz1 hz2 hz

-- box ['1323039/8192000', '82743/512000', '7997/8000', '3999/4000']  interval_lower 233330321/1099511627776
noncomputable def e2415 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916411,0,true,164613967424,164613967488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339141,0,false,-193673707456,-193673707392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867263,0,true,164712069376,164712069440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388289,0,false,-193809614912,-193809614848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277020325677,0,true,164556634432,164556634496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922002929875,0,false,-193594293440,-193594293376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277156444954,0,true,164673826560,164673826624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921866810598,0,false,-193756631104,-193756631040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534251821,0,true,22623808,22623872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489003731,0,false,-22624320,-22624256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545587189,0,true,33958848,33958912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477668363,0,false,-33960000,-33959936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626727,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627311,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277053616505,0,true,164585297408,164585297472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921969639047,0,false,-193633994304,-193633994240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277178664629,0,true,164692955456,164692955520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921844590923,0,false,-193783132864,-193783132800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070802903660,0,false,-29090177344,-29090177280⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070843301798,0,false,-29048696896,-29048696832⟩
    { al := (1323039/8192000), au := (82743/512000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨177575288635,177689239487⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164556634432,164556634496⟩ : DyadicInterval 40),(⟨-193594293440,-193594293376⟩ : DyadicInterval 40),(⟨747731693488,747731712818⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164673826560,164673826624⟩ : DyadicInterval 40),(⟨-193756631104,-193756631040⟩ : DyadicInterval 40),(⟨747709515358,747709534688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22624045,33959413⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22623808,22623872⟩ : DyadicInterval 40),(⟨-22624320,-22624256⟩ : DyadicInterval 40),(⟨762123383342,762123402671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33958848,33958912⟩ : DyadicInterval 40),(⟨-33960000,-33959936⟩ : DyadicInterval 40),(⟨762123383079,762123402408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177541988729,177667036853⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164585297408,164585297472⟩ : DyadicInterval 40),(⟨-193633994304,-193633994240⟩ : DyadicInterval 40),(⟨747726270941,747726290271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164692955456,164692955520⟩ : DyadicInterval 40),(⟨-193783132864,-193783132800⟩ : DyadicInterval 40),(⟨747705893422,747705912752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29090177344,-29048696832⟩ : DyadicInterval 40),(⟨776647732032,776668491552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164613967424,164712069440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193809614912,-193673707392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2415_ok : ecellOkT e2415 = true := by decide +kernel
theorem e2415_pos {a z : ℝ} (ha1 : ((1323039/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((82743/512000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2415 e2415_ok ha1 ha2 hz1 hz2 hz

-- box ['330123/2048000', '1321341/8192000', '3999/4000', '7999/8000']  interval_lower 114735439/549755813888
noncomputable def e2416 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063858,0,true,164319609088,164319609152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191694,0,false,-193266085824,-193266085760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014710,0,true,164417737280,164417737344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240842,0,false,-193401942912,-193401942848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276700755498,0,true,164281450816,164281450880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922322500054,0,false,-193213264000,-193213263936⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276836846287,0,true,164398647744,164398647808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922186409265,0,false,-193375511424,-193375511360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522917079,0,true,11289216,11289280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500338473,0,false,-11289408,-11289344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534222288,0,true,22594240,22594304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489033264,0,false,-22594752,-22594688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627311,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627661,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276722905083,0,true,164300526144,164300526208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922300350469,0,false,-193239669120,-193239669056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276847938980,0,true,164408199872,164408199936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922175316572,0,false,-193388737216,-193388737152⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070909686262,0,false,-28980537344,-28980537280⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070950004587,0,false,-28939142912,-28939142848⟩
    { al := (330123/2048000), au := (1321341/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨177233436082,177347386934⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164281450816,164281450880⟩ : DyadicInterval 40),(⟨-193213264000,-193213263936⟩ : DyadicInterval 40),(⟨747783693603,747783712932⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164398647744,164398647808⟩ : DyadicInterval 40),(⟨-193375511424,-193375511360⟩ : DyadicInterval 40),(⟨747761560719,747761580049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11289303,22594512⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11289216,11289280⟩ : DyadicInterval 40),(⟨-11289408,-11289344⟩ : DyadicInterval 40),(⟨762123383532,762123402861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22594240,22594304⟩ : DyadicInterval 40),(⟨-22594752,-22594688⟩ : DyadicInterval 40),(⟨762123383343,762123402672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177211277307,177336311204⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164300526144,164300526208⟩ : DyadicInterval 40),(⟨-193239669120,-193239669056⟩ : DyadicInterval 40),(⟨747780092542,747780111871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164408199872,164408199936⟩ : DyadicInterval 40),(⟨-193388737216,-193388737152⟩ : DyadicInterval 40),(⟨747759755920,747759775250⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28980537344,-28939142848⟩ : DyadicInterval 40),(⟨776592955040,776613671552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164319609088,164417737344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193401942912,-193266085760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2416_ok : ecellOkT e2416 = true := by decide +kernel
theorem e2416_pos {a z : ℝ} (ha1 : ((330123/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1321341/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2416 e2416_ok ha1 ha2 hz1 hz2 hz

-- box ['1321341/8192000', '132219/819200', '3999/4000', '7999/8000']  interval_lower 230695479/1099511627776
noncomputable def e2417 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014709,0,true,164417737280,164417737344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240843,0,false,-193401942912,-193401942848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965561,0,true,164515856704,164515856768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289991,0,false,-193537816768,-193537816704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276814677862,0,true,164379557888,164379557952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922208577690,0,false,-193349080640,-193349080576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1276950782894,0,true,164496756608,164496756672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨922072472658,0,false,-193511365056,-193511364992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522924618,0,true,11296768,11296832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500330934,0,false,-11296960,-11296896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534237366,0,true,22609344,22609408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489018186,0,false,-22609856,-22609792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627311,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627660,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276836841684,0,true,164398643776,164398643840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922186413868,0,false,-193375505984,-193375505920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1276961882707,0,true,164506314048,164506314112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨922061372845,0,false,-193524600960,-193524600896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070872919298,0,false,-29018286912,-29018286848⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070913265837,0,false,-28976862144,-28976862080⟩
    { al := (1321341/8192000), au := (132219/819200), zl := (3999/4000), zu := (7999/8000),
      A := ⟨177347386933,177461337785⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164379557888,164379557952⟩ : DyadicInterval 40),(⟨-193349080640,-193349080576⟩ : DyadicInterval 40),(⟨747765167231,747765186560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164496756608,164496756672⟩ : DyadicInterval 40),(⟨-193511365056,-193511364992⟩ : DyadicInterval 40),(⟨747743017546,747743036875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11296842,22609590⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11296768,11296832⟩ : DyadicInterval 40),(⟨-11296960,-11296896⟩ : DyadicInterval 40),(⟨762123383531,762123402860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22609344,22609408⟩ : DyadicInterval 40),(⟨-22609856,-22609792⟩ : DyadicInterval 40),(⟨762123383343,762123402672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177325213908,177450254931⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164398643776,164398643840⟩ : DyadicInterval 40),(⟨-193375505984,-193375505920⟩ : DyadicInterval 40),(⟨747761561491,747761580821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164506314048,164506314112⟩ : DyadicInterval 40),(⟨-193524600960,-193524600896⟩ : DyadicInterval 40),(⟨747741210382,747741229712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29018286912,-28976862080⟩ : DyadicInterval 40),(⟨776611814656,776632546336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164417737280,164515856768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193537816768,-193401942848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2417_ok : ecellOkT e2417 = true := by decide +kernel
theorem e2417_pos {a z : ℝ} (ha1 : ((1321341/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((132219/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2417 e2417_ok ha1 ha2 hz1 hz2 hz

-- box ['330123/2048000', '1321341/8192000', '7999/8000', '1']  interval_lower 114647795/549755813888
noncomputable def e2418 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276745063858,0,true,164319609088,164319609152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922278191694,0,false,-193266085824,-193266085760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014710,0,true,164417737280,164417737344⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240842,0,false,-193401942912,-193401942848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276722909678,0,true,164300530112,164300530176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922300345874,0,false,-193239674624,-193239674560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522925187,0,true,11297344,11297408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500330365,0,false,-11297472,-11297408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627659,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1276733982130,0,true,164310065664,164310065728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨922289273422,0,false,-193252874624,-193252874560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859023175,0,true,164417744576,164417744640⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨922164232377,0,false,-193401953024,-193401952960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070906110689,0,false,-28984208384,-28984208320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070946433840,0,false,-28942808896,-28942808832⟩
    { al := (330123/2048000), au := (1321341/8192000), zl := (7999/8000), zu := 1,
      A := ⟨177233436082,177347386934⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164319609088,164319609152⟩ : DyadicInterval 40),(⟨-193266085824,-193266085760⟩ : DyadicInterval 40),(⟨747776489507,747776508837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164300530112,164300530176⟩ : DyadicInterval 40),(⟨-193239674624,-193239674560⟩ : DyadicInterval 40),(⟨747780091799,747780111129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11297411⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11297344,11297408⟩ : DyadicInterval 40),(⟨-11297472,-11297408⟩ : DyadicInterval 40),(⟨762123383499,762123402828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨177222354354,177347395399⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164310065664,164310065728⟩ : DyadicInterval 40),(⟨-193252874624,-193252874560⟩ : DyadicInterval 40),(⟨747778291458,747778310788⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417744576,164417744640⟩ : DyadicInterval 40),(⟨-193401953024,-193401952960⟩ : DyadicInterval 40),(⟨747757952398,747757971728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-28984208384,-28942808832⟩ : DyadicInterval 40),(⟨776594788032,776615507072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨164319609088,164417737344⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193401942912,-193266085760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2418_ok : ecellOkT e2418 = true := by decide +kernel
theorem e2418_pos {a z : ℝ} (ha1 : ((330123/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1321341/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2418 e2418_ok ha1 ha2 hz1 hz2 hz

-- box ['1321341/8192000', '132219/819200', '7999/8000', '1']  interval_lower 230520035/1099511627776
noncomputable def e2419 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276859014709,0,true,164417737280,164417737344⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922164240843,0,false,-193401942912,-193401942848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965561,0,true,164515856704,164515856768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289991,0,false,-193537816768,-193537816704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276836846285,0,true,164398647744,164398647808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922186409267,0,false,-193375511424,-193375511360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522932727,0,true,11304832,11304896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500322825,0,false,-11305024,-11304960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627659,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1276847925858,0,true,164408188544,164408188608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨922175329694,0,false,-193388721536,-193388721472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972974026,0,true,164515864000,164515864064⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨922050281526,0,false,-193537826880,-193537826816⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070869339129,0,false,-29021962816,-29021962752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070909690495,0,false,-28980532992,-28980532928⟩
    { al := (1321341/8192000), au := (132219/819200), zl := (7999/8000), zu := 1,
      A := ⟨177347386933,177461337785⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164417737280,164417737344⟩ : DyadicInterval 40),(⟨-193401942912,-193401942848⟩ : DyadicInterval 40),(⟨747757953772,747757973101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164398647744,164398647808⟩ : DyadicInterval 40),(⟨-193375511424,-193375511360⟩ : DyadicInterval 40),(⟨747761560720,747761580049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11304951⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11304832,11304896⟩ : DyadicInterval 40),(⟨-11305024,-11304960⟩ : DyadicInterval 40),(⟨762123383531,762123402860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨177336298082,177461346250⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164408188544,164408188608⟩ : DyadicInterval 40),(⟨-193388721536,-193388721472⟩ : DyadicInterval 40),(⟨747759758058,747759777387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515864000,164515864064⟩ : DyadicInterval 40),(⟨-193537826880,-193537826816⟩ : DyadicInterval 40),(⟨747739404534,747739423864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29021962816,-28980532928⟩ : DyadicInterval 40),(⟨776613650080,776634384288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨164417737280,164515856768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193537816768,-193401942848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2419_ok : ecellOkT e2419 = true := by decide +kernel
theorem e2419_pos {a z : ℝ} (ha1 : ((1321341/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((132219/819200 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2419 e2419_ok ha1 ha2 hz1 hz2 hz

-- box ['132219/819200', '1323039/8192000', '3999/4000', '7999/8000']  interval_lower 1811899/8589934592
noncomputable def e2420 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965560,0,true,164515856704,164515856768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289992,0,false,-193537816768,-193537816704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916412,0,true,164613967424,164613967488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339140,0,false,-193673707456,-193673707392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276928600225,0,true,164477656192,164477656256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922094655327,0,false,-193484913984,-193484913920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277064719501,0,true,164594856768,164594856832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921958536051,0,false,-193647235456,-193647235392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522932157,0,true,11304320,11304384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500323395,0,false,-11304448,-11304384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534252445,0,true,22624384,22624448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489003107,0,false,-22624960,-22624896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627310,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627660,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1276950778289,0,true,164496752640,164496752704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨922072477263,0,false,-193511359552,-193511359488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277075826439,0,true,164604419456,164604419520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921947429113,0,false,-193660481472,-193660481408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070836128717,0,false,-29056062016,-29056061952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070876503473,0,false,-29014606848,-29014606784⟩
    { al := (132219/819200), au := (1323039/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨177461337784,177575288636⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164477656192,164477656256⟩ : DyadicInterval 40),(⟨-193484913984,-193484913920⟩ : DyadicInterval 40),(⟨747746628718,747746648047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164594856768,164594856832⟩ : DyadicInterval 40),(⟨-193647235456,-193647235392⟩ : DyadicInterval 40),(⟨747724462213,747724481542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11304381,22624669⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11304320,11304384⟩ : DyadicInterval 40),(⟨-11304448,-11304384⟩ : DyadicInterval 40),(⟨762123383499,762123402828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22624384,22624448⟩ : DyadicInterval 40),(⟨-22624960,-22624896⟩ : DyadicInterval 40),(⟨762123383374,762123402703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177439150513,177564198663⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164496752640,164496752704⟩ : DyadicInterval 40),(⟨-193511359552,-193511359488⟩ : DyadicInterval 40),(⟨747743018292,747743037621⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164604419456,164604419520⟩ : DyadicInterval 40),(⟨-193660481472,-193660481408⟩ : DyadicInterval 40),(⟨747722652718,747722672048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29056062016,-29014606784⟩ : DyadicInterval 40),(⟨776630687008,776651433888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164515856704,164613967488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193673707456,-193537816704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2420_ok : ecellOkT e2420 = true := by decide +kernel
theorem e2420_pos {a z : ℝ} (ha1 : ((132219/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1323039/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2420 e2420_ok ha1 ha2 hz1 hz2 hz

-- box ['1323039/8192000', '82743/512000', '3999/4000', '7999/8000']  interval_lower 7286043/34359738368
noncomputable def e2421 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916411,0,true,164613967424,164613967488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339141,0,false,-193673707456,-193673707392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867263,0,true,164712069376,164712069440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388289,0,false,-193809614912,-193809614848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277042522588,0,true,164575745792,164575745856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921980732964,0,false,-193620764160,-193620764096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277178656109,0,true,164692948160,164692948224⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921844599443,0,false,-193783122688,-193783122624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522939697,0,true,11311808,11311872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500315855,0,false,-11312000,-11311936⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534267525,0,true,22639488,22639552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488988027,0,false,-22640000,-22639936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627309,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627660,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277064714896,0,true,164594852800,164594852864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921958540656,0,false,-193647230016,-193647229952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277189770170,0,true,164702516096,164702516160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921833485382,0,false,-193796378816,-193796378752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070799314520,0,false,-29093862720,-29093862656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070839717494,0,false,-29052377152,-29052377088⟩
    { al := (1323039/8192000), au := (82743/512000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨177575288635,177689239487⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164575745792,164575745856⟩ : DyadicInterval 40),(⟨-193620764160,-193620764096⟩ : DyadicInterval 40),(⟨747728078078,747728097408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164692948160,164692948224⟩ : DyadicInterval 40),(⟨-193783122688,-193783122624⟩ : DyadicInterval 40),(⟨747705894783,747705914112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11311921,22639749⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11311808,11311872⟩ : DyadicInterval 40),(⟨-11312000,-11311936⟩ : DyadicInterval 40),(⟨762123383531,762123402860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22639488,22639552⟩ : DyadicInterval 40),(⟨-22640000,-22639936⟩ : DyadicInterval 40),(⟨762123383341,762123402670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177553087120,177678142394⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164594852800,164594852864⟩ : DyadicInterval 40),(⟨-193647230016,-193647229952⟩ : DyadicInterval 40),(⟨747724462986,747724482316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164702516096,164702516160⟩ : DyadicInterval 40),(⟨-193796378816,-193796378752⟩ : DyadicInterval 40),(⟨747704082954,747704102284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29093862720,-29052377088⟩ : DyadicInterval 40),(⟨776649572160,776670334240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164613967424,164712069440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193809614912,-193673707392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2421_ok : ecellOkT e2421 = true := by decide +kernel
theorem e2421_pos {a z : ℝ} (ha1 : ((1323039/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((82743/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2421 e2421_ok ha1 ha2 hz1 hz2 hz

-- box ['132219/819200', '1323039/8192000', '7999/8000', '1']  interval_lower 231747087/1099511627776
noncomputable def e2422 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1276972965560,0,true,164515856704,164515856768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨922050289992,0,false,-193537816768,-193537816704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916412,0,true,164613967424,164613967488⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339140,0,false,-193673707456,-193673707392⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1276950782892,0,true,164496756608,164496756672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922072472660,0,false,-193511365056,-193511364992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522940267,0,true,11312384,11312448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500315285,0,false,-11312576,-11312512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627659,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1276961869582,0,true,164506302720,164506302784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨922061385970,0,false,-193524585280,-193524585216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086924879,0,true,164613974720,164613974784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨921936330673,0,false,-193673717568,-193673717504⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070832543949,0,false,-29059742784,-29059742720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070872923536,0,false,-29018282560,-29018282496⟩
    { al := (132219/819200), au := (1323039/8192000), zl := (7999/8000), zu := 1,
      A := ⟨177461337784,177575288636⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164515856704,164515856768⟩ : DyadicInterval 40),(⟨-193537816768,-193537816704⟩ : DyadicInterval 40),(⟨747739405909,747739425239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164496756608,164496756672⟩ : DyadicInterval 40),(⟨-193511365056,-193511364992⟩ : DyadicInterval 40),(⟨747743017546,747743036876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11312491⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11312384,11312448⟩ : DyadicInterval 40),(⟨-11312576,-11312512⟩ : DyadicInterval 40),(⟨762123383531,762123402860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨177450241806,177575297103⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164506302720,164506302784⟩ : DyadicInterval 40),(⟨-193524585280,-193524585216⟩ : DyadicInterval 40),(⟨747741212523,747741231853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613974720,164613974784⟩ : DyadicInterval 40),(⟨-193673717568,-193673717504⟩ : DyadicInterval 40),(⟨747720844531,747720863861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29059742784,-29018282496⟩ : DyadicInterval 40),(⟨776632524864,776653274272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨164515856704,164613967488⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193673707456,-193537816704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2422_ok : ecellOkT e2422 = true := by decide +kernel
theorem e2422_pos {a z : ℝ} (ha1 : ((132219/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1323039/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2422 e2422_ok ha1 ha2 hz1 hz2 hz

-- box ['1323039/8192000', '82743/512000', '7999/8000', '1']  interval_lower 29122119/137438953472
noncomputable def e2423 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277086916411,0,true,164613967424,164613967488⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921936339141,0,false,-193673707456,-193673707392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867263,0,true,164712069376,164712069440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388289,0,false,-193809614912,-193809614848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277064719499,0,true,164594856768,164594856832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921958536053,0,false,-193647235456,-193647235392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522947807,0,true,11319936,11320000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500307745,0,false,-11320128,-11320064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627659,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1277075813312,0,true,164604408128,164604408192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨921947442240,0,false,-193660465856,-193660465792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200875734,0,true,164712076672,164712076736⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨921822379818,0,false,-193809625024,-193809624960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1070795725149,0,false,-29097548352,-29097548288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1070836132958,0,false,-29056057664,-29056057600⟩
    { al := (1323039/8192000), au := (82743/512000), zl := (7999/8000), zu := 1,
      A := ⟨177575288635,177689239487⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164613967424,164613967488⟩ : DyadicInterval 40),(⟨-193673707456,-193673707392⟩ : DyadicInterval 40),(⟨747720845908,747720865238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164594856768,164594856832⟩ : DyadicInterval 40),(⟨-193647235456,-193647235392⟩ : DyadicInterval 40),(⟨747724462213,747724481543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11320031⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11319936,11320000⟩ : DyadicInterval 40),(⟨-11320128,-11320064⟩ : DyadicInterval 40),(⟨762123383531,762123402860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨177564185536,177689247958⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164604408128,164604408192⟩ : DyadicInterval 40),(⟨-193660465856,-193660465792⟩ : DyadicInterval 40),(⟨747722654889,747722674218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712076672,164712076736⟩ : DyadicInterval 40),(⟨-193809625024,-193809624960⟩ : DyadicInterval 40),(⟨747702272397,747702291727⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29097548352,-29056057600⟩ : DyadicInterval 40),(⟨776651412416,776672177056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨164613967424,164712069440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193809614912,-193673707392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2423_ok : ecellOkT e2423 = true := by decide +kernel
theorem e2423_pos {a z : ℝ} (ha1 : ((1323039/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((82743/512000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2423 e2423_ok ha1 ha2 hz1 hz2 hz

-- box ['82743/512000', '1324737/8192000', '999/1000', '7993/8000']  interval_lower 117723983/549755813888
noncomputable def e2424 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867262,0,true,164712069376,164712069440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388290,0,false,-193809614912,-193809614848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818114,0,true,164810162560,164810162624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437438,0,false,-193945539200,-193945539136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277023178022,0,true,164559090304,164559090368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨922000077530,0,false,-193597694976,-193597694912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277159240323,0,true,164676233152,164676233216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921864015229,0,false,-193759965120,-193759965056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590864396,0,true,79233728,79233792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432391156,0,false,-79239488,-79239424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602245010,0,true,90613440,90613504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421010542,0,false,-90620992,-90620928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620307,0,false,-7488,-7424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622066,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277112018827,0,true,164635579200,164635579264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921911236725,0,false,-193703645248,-193703645184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277237038336,0,true,164743207744,164743207808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921786217216,0,false,-193852759104,-193852759040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070784035669,0,false,-29109551360,-29109551296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070824437842,0,false,-29068066048,-29068065984⟩
    { al := (82743/512000), au := (1324737/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨177689239486,177803190338⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164559090304,164559090368⟩ : DyadicInterval 40),(⟨-193597694976,-193597694912⟩ : DyadicInterval 40),(⟨747731228937,747731248266⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164676233152,164676233216⟩ : DyadicInterval 40),(⟨-193759965120,-193759965056⟩ : DyadicInterval 40),(⟨747709059685,747709079014⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79236620,90617234⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79233728,79233792⟩ : DyadicInterval 40),(⟨-79239488,-79239424⟩ : DyadicInterval 40),(⟨762123380721,762123400050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90613440,90613504⟩ : DyadicInterval 40),(⟨-90620992,-90620928⟩ : DyadicInterval 40),(⟨762123379859,762123399189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7488,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123406624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177600391051,177725410560⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164635579200,164635579264⟩ : DyadicInterval 40),(⟨-193703645248,-193703645184⟩ : DyadicInterval 40),(⟨747716755657,747716774986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164743207744,164743207808⟩ : DyadicInterval 40),(⟨-193852759104,-193852759040⟩ : DyadicInterval 40),(⟨747696375945,747696395275⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29109551360,-29068065984⟩ : DyadicInterval 40),(⟨776657416608,776678178560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164712069376,164810162624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193945539200,-193809614848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2424_ok : ecellOkT e2424 = true := by decide +kernel
theorem e2424_pos {a z : ℝ} (ha1 : ((82743/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1324737/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2424 e2424_ok ha1 ha2 hz1 hz2 hz

-- box ['1324737/8192000', '662793/4096000', '999/1000', '7993/8000']  interval_lower 236686719/1099511627776
noncomputable def e2425 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818113,0,true,164810162560,164810162624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437439,0,false,-193945539200,-193945539136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768965,0,true,164908246976,164908247040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486587,0,false,-194081480256,-194081480192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277137014922,0,true,164657099008,164657099072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921886240630,0,false,-193733457088,-193733457024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277273091467,0,true,164774243712,164774243776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921750164085,0,false,-193895764352,-193895764288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590917178,0,true,79286528,79286592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432338374,0,false,-79292288,-79292224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602305337,0,true,90673792,90673856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420950215,0,false,-90681344,-90681280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620297,0,false,-7488,-7424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622059,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277225912701,0,true,164733630144,164733630208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921797342851,0,false,-193839488448,-193839488384⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277350939333,0,true,164841255232,164841255296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921672316219,0,false,-193988629248,-193988629184⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070747201883,0,false,-29147374016,-29147373952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070787632260,0,false,-29105858304,-29105858240⟩
    { al := (1324737/8192000), au := (662793/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨177803190337,177917141189⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164657099008,164657099072⟩ : DyadicInterval 40),(⟨-193733457088,-193733457024⟩ : DyadicInterval 40),(⟨747712682167,747712701496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164774243712,164774243776⟩ : DyadicInterval 40),(⟨-193895764352,-193895764288⟩ : DyadicInterval 40),(⟨747690496144,747690515473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79289402,90677561⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79286528,79286592⟩ : DyadicInterval 40),(⟨-79292288,-79292224⟩ : DyadicInterval 40),(⟨762123380713,762123400043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90673792,90673856⟩ : DyadicInterval 40),(⟨-90681344,-90681280⟩ : DyadicInterval 40),(⟨762123379849,762123399179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7488,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123406624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177714284925,177839311557⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164733630144,164733630208⟩ : DyadicInterval 40),(⟨-193839488448,-193839488384⟩ : DyadicInterval 40),(⟨747698190165,747698209495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164841255232,164841255296⟩ : DyadicInterval 40),(⟨-193988629248,-193988629184⟩ : DyadicInterval 40),(⟨747677795997,747677815327⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29147374016,-29105858240⟩ : DyadicInterval 40),(⟨776676312736,776697089888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164810162560,164908247040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194081480256,-193945539136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2425_ok : ecellOkT e2425 = true := by decide +kernel
theorem e2425_pos {a z : ℝ} (ha1 : ((1324737/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((662793/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2425 e2425_ok ha1 ha2 hz1 hz2 hz

-- box ['82743/512000', '1324737/8192000', '7993/8000', '3997/4000']  interval_lower 7352221/34359738368
noncomputable def e2426 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867262,0,true,164712069376,164712069440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388290,0,false,-193809614912,-193809614848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818114,0,true,164810162560,164810162624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437438,0,false,-193945539200,-193945539136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277045389177,0,true,164578213824,164578213888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921977866375,0,false,-193624182720,-193624182656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277181465722,0,true,164695366912,164695366976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921841789830,0,false,-193786473792,-193786473728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579545006,0,true,67915072,67915136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443710546,0,false,-67919360,-67919296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590918079,0,true,79287424,79287488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432337473,0,false,-79293184,-79293120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622058,0,false,-5760,-5696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623581,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277123124205,0,true,164645140160,164645140224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921900131347,0,false,-193716890112,-193716890048⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277248150862,0,true,164752773888,164752773952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921775104690,0,false,-193866014272,-193866014208⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070780443093,0,false,-29113240320,-29113240256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070820850101,0,false,-29071749888,-29071749824⟩
    { al := (82743/512000), au := (1324737/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨177689239486,177803190338⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164578213824,164578213888⟩ : DyadicInterval 40),(⟨-193624182720,-193624182656⟩ : DyadicInterval 40),(⟨747727611165,747727630494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164695366912,164695366976⟩ : DyadicInterval 40),(⟨-193786473792,-193786473728⟩ : DyadicInterval 40),(⟨747705436772,747705456101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67917230,79290303⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67915072,67915136⟩ : DyadicInterval 40),(⟨-67919360,-67919296⟩ : DyadicInterval 40),(⟨762123381500,762123400829⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79287424,79287488⟩ : DyadicInterval 40),(⟨-79293184,-79293120⟩ : DyadicInterval 40),(⟨762123380713,762123400043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177611496429,177736523086⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164645140160,164645140224⟩ : DyadicInterval 40),(⟨-193716890112,-193716890048⟩ : DyadicInterval 40),(⟨747714945956,747714965285⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164752773888,164752773952⟩ : DyadicInterval 40),(⟨-193866014272,-193866014208⟩ : DyadicInterval 40),(⟨747694563794,747694583123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29113240320,-29071749824⟩ : DyadicInterval 40),(⟨776659258528,776680023040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164712069376,164810162624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193945539200,-193809614848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2426_ok : ecellOkT e2426 = true := by decide +kernel
theorem e2426_pos {a z : ℝ} (ha1 : ((82743/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1324737/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2426 e2426_ok ha1 ha2 hz1 hz2 hz

-- box ['1324737/8192000', '662793/4096000', '7993/8000', '3997/4000']  interval_lower 236509563/1099511627776
noncomputable def e2427 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818113,0,true,164810162560,164810162624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437439,0,false,-193945539200,-193945539136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768965,0,true,164908246976,164908247040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486587,0,false,-194081480256,-194081480192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277159240321,0,true,164676233152,164676233216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921864015231,0,false,-193759965120,-193759965056⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277295331110,0,true,164793388032,164793388096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921727924442,0,false,-193922293248,-193922293184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579590249,0,true,67960320,67960384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443665303,0,false,-67964608,-67964544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590970867,0,true,79340224,79340288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432284685,0,false,-79345984,-79345920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622050,0,false,-5760,-5696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623576,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277237025205,0,true,164743196416,164743196480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921786230347,0,false,-193852743424,-193852743360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277362058984,0,true,164850826688,164850826752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921661196568,0,false,-194001894528,-194001894464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070743604699,0,false,-29151067840,-29151067776⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070784039915,0,false,-29109547008,-29109546944⟩
    { al := (1324737/8192000), au := (662793/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨177803190337,177917141189⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164676233152,164676233216⟩ : DyadicInterval 40),(⟨-193759965120,-193759965056⟩ : DyadicInterval 40),(⟨747709059685,747709079015⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164793388032,164793388096⟩ : DyadicInterval 40),(⟨-193922293248,-193922293184⟩ : DyadicInterval 40),(⟨747686868525,747686887854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨67962473,79343091⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67960320,67960384⟩ : DyadicInterval 40),(⟨-67964608,-67964544⟩ : DyadicInterval 40),(⟨762123381495,762123400824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79340224,79340288⟩ : DyadicInterval 40),(⟨-79345984,-79345920⟩ : DyadicInterval 40),(⟨762123380706,762123400035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177725397429,177850431208⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164743196416,164743196480⟩ : DyadicInterval 40),(⟨-193852743424,-193852743360⟩ : DyadicInterval 40),(⟨747696378094,747696397423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164850826688,164850826752⟩ : DyadicInterval 40),(⟨-194001894528,-194001894464⟩ : DyadicInterval 40),(⟨747675981471,747676000801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29151067840,-29109546944⟩ : DyadicInterval 40),(⟨776678157088,776698936800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164810162560,164908247040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194081480256,-193945539136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2427_ok : ecellOkT e2427 = true := by decide +kernel
theorem e2427_pos {a z : ℝ} (ha1 : ((1324737/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((662793/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2427 e2427_ok ha1 ha2 hz1 hz2 hz

-- box ['662793/4096000', '265287/1638400', '999/1000', '7993/8000']  interval_lower 118964111/549755813888
noncomputable def e2428 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768964,0,true,164908246976,164908247040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486588,0,false,-194081480256,-194081480192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719816,0,true,165006322624,165006322688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535736,0,false,-194217438144,-194217438080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277250851822,0,true,164755099008,164755099072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921772403730,0,false,-193869236032,-193869235968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277386942611,0,true,164872245504,164872245568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921636312941,0,false,-194031580288,-194031580224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099590969966,0,true,79339264,79339328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432285586,0,false,-79345088,-79345024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602365670,0,true,90734144,90734208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420889882,0,false,-90741696,-90741632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620287,0,false,-7552,-7488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622051,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277339806576,0,true,164831672384,164831672448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921683448976,0,false,-193975348480,-193975348416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277464840330,0,true,164939293952,164939294016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921558415222,0,false,-194124516160,-194124516096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070710344498,0,false,-29185222144,-29185222080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070750803083,0,false,-29143676032,-29143675968⟩
    { al := (662793/4096000), au := (265287/1638400), zl := (999/1000), zu := (7993/8000),
      A := ⟨177917141188,178031092040⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164755099008,164755099072⟩ : DyadicInterval 40),(⟨-193869236032,-193869235968⟩ : DyadicInterval 40),(⟨747694123304,747694142634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164872245504,164872245568⟩ : DyadicInterval 40),(⟨-194031580288,-194031580224⟩ : DyadicInterval 40),(⟨747671920487,747671939817⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79342190,90737894⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79339264,79339328⟩ : DyadicInterval 40),(⟨-79345088,-79345024⟩ : DyadicInterval 40),(⟨762123380738,762123400067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90734144,90734208⟩ : DyadicInterval 40),(⟨-90741696,-90741632⟩ : DyadicInterval 40),(⟨762123379839,762123399169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7552,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123406656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177828178800,177953212554⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164831672384,164831672448⟩ : DyadicInterval 40),(⟨-193975348480,-193975348416⟩ : DyadicInterval 40),(⟨747679612556,747679631885⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164939293952,164939294016⟩ : DyadicInterval 40),(⟨-194124516160,-194124516096⟩ : DyadicInterval 40),(⟨747659203937,747659223266⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29185222144,-29143675968⟩ : DyadicInterval 40),(⟨776695221600,776716013952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164908246976,165006322688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194217438144,-194081480192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2428_ok : ecellOkT e2428 = true := by decide +kernel
theorem e2428_pos {a z : ℝ} (ha1 : ((662793/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((265287/1638400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2428 e2428_ok ha1 ha2 hz1 hz2 hz

-- box ['265287/1638400', '331821/2048000', '999/1000', '7993/8000']  interval_lower 119586489/549755813888
noncomputable def e2429 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719815,0,true,165006322624,165006322688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535737,0,false,-194217438144,-194217438080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670667,0,true,165104389568,165104389632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584885,0,false,-194353412800,-194353412736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277364688722,0,true,164853090304,164853090368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921658566830,0,false,-194005031744,-194005031680⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277500793755,0,true,164970238592,164970238656⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921522461797,0,false,-194167413056,-194167412992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591022756,0,true,79392064,79392128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432232796,0,false,-79397888,-79397824⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602426007,0,true,90794432,90794496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420829545,0,false,-90801984,-90801920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620277,0,false,-7552,-7488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622043,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277453700449,0,true,164929705856,164929705920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921569555103,0,false,-194111225216,-194111225152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277578741330,0,true,165037323968,165037324032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921444514222,0,false,-194260419904,-194260419840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070673463514,0,false,-29223095872,-29223095808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070713950310,0,false,-29181519360,-29181519296⟩
    { al := (265287/1638400), au := (331821/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨178031092039,178145042891⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164853090304,164853090368⟩ : DyadicInterval 40),(⟨-194005031744,-194005031680⟩ : DyadicInterval 40),(⟨747675552322,747675571651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164970238592,164970238656⟩ : DyadicInterval 40),(⟨-194167413056,-194167412992⟩ : DyadicInterval 40),(⟨747653332729,747653352058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79394980,90798231⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79392064,79392128⟩ : DyadicInterval 40),(⟨-79397888,-79397824⟩ : DyadicInterval 40),(⟨762123380730,762123400060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90794432,90794496⟩ : DyadicInterval 40),(⟨-90801984,-90801920⟩ : DyadicInterval 40),(⟨762123379829,762123399159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7552,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123406656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177942072673,178067113554⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164929705856,164929705920⟩ : DyadicInterval 40),(⟨-194111225216,-194111225152⟩ : DyadicInterval 40),(⟨747661022811,747661042141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165037323968,165037324032⟩ : DyadicInterval 40),(⟨-194260419904,-194260419840⟩ : DyadicInterval 40),(⟨747640599753,747640619083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29223095872,-29181519296⟩ : DyadicInterval 40),(⟨776714143264,776734950816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165006322624,165104389632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194353412800,-194217438080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2429_ok : ecellOkT e2429 = true := by decide +kernel
theorem e2429_pos {a z : ℝ} (ha1 : ((265287/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((331821/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2429 e2429_ok ha1 ha2 hz1 hz2 hz

-- box ['662793/4096000', '265287/1638400', '7993/8000', '3997/4000']  interval_lower 237750905/1099511627776
noncomputable def e2430 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768964,0,true,164908246976,164908247040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486588,0,false,-194081480256,-194081480192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719816,0,true,165006322624,165006322688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535736,0,false,-194217438144,-194217438080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277273091465,0,true,164774243712,164774243776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921750164087,0,false,-193895764352,-193895764288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277409196498,0,true,164891400384,164891400448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921614059054,0,false,-194058129472,-194058129408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579635495,0,true,68005568,68005632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443620057,0,false,-68009856,-68009792⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591023658,0,true,79392960,79393024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432231894,0,false,-79398784,-79398720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622042,0,false,-5760,-5696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623570,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277350926199,0,true,164841243904,164841243968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921672329353,0,false,-193988613568,-193988613504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277475967101,0,true,164948870720,164948870784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921547288451,0,false,-194137791616,-194137791552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070706742705,0,false,-29188920832,-29188920768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070747206133,0,false,-29147369600,-29147369536⟩
    { al := (662793/4096000), au := (265287/1638400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨177917141188,178031092040⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164774243712,164774243776⟩ : DyadicInterval 40),(⟨-193895764352,-193895764288⟩ : DyadicInterval 40),(⟨747690496144,747690515474⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164891400384,164891400448⟩ : DyadicInterval 40),(⟨-194058129472,-194058129408⟩ : DyadicInterval 40),(⟨747668288182,747668307511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68007719,79395882⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68005568,68005632⟩ : DyadicInterval 40),(⟨-68009856,-68009792⟩ : DyadicInterval 40),(⟨762123381489,762123400818⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79392960,79393024⟩ : DyadicInterval 40),(⟨-79398784,-79398720⟩ : DyadicInterval 40),(⟨762123380730,762123400060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177839298423,177964339325⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164841243904,164841243968⟩ : DyadicInterval 40),(⟨-193988613568,-193988613504⟩ : DyadicInterval 40),(⟨747677798148,747677817478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164948870720,164948870784⟩ : DyadicInterval 40),(⟨-194137791616,-194137791552⟩ : DyadicInterval 40),(⟨747657387062,747657406391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29188920832,-29147369536⟩ : DyadicInterval 40),(⟨776697068384,776717863296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164908246976,165006322688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194217438144,-194081480192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2430_ok : ecellOkT e2430 = true := by decide +kernel
theorem e2430_pos {a z : ℝ} (ha1 : ((662793/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((265287/1638400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2430 e2430_ok ha1 ha2 hz1 hz2 hz

-- box ['265287/1638400', '331821/2048000', '7993/8000', '3997/4000']  interval_lower 59748775/274877906944
noncomputable def e2431 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719815,0,true,165006322624,165006322688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535737,0,false,-194217438144,-194217438080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670667,0,true,165104389568,165104389632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584885,0,false,-194353412800,-194353412736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277386942609,0,true,164872245504,164872245568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921636312943,0,false,-194031580288,-194031580224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277523061885,0,true,164989404032,164989404096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921500193667,0,false,-194193982528,-194193982464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579680744,0,true,68050816,68050880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443574808,0,false,-68055104,-68055040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591076454,0,true,79445760,79445824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432179098,0,false,-79451584,-79451520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622035,0,false,-5760,-5696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623564,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277464827193,0,true,164939282624,164939282688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921558428359,0,false,-194124500480,-194124500416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277589875223,0,true,165046905984,165046906048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921433380329,0,false,-194273705472,-194273705408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070669857109,0,false,-29226799424,-29226799360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070710348752,0,false,-29185217792,-29185217728⟩
    { al := (265287/1638400), au := (331821/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨178031092039,178145042891⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164872245504,164872245568⟩ : DyadicInterval 40),(⟨-194031580288,-194031580224⟩ : DyadicInterval 40),(⟨747671920488,747671939817⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164989404032,164989404096⟩ : DyadicInterval 40),(⟨-194193982528,-194193982464⟩ : DyadicInterval 40),(⟨747649695732,747649715061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68052968,79448678⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68050816,68050880⟩ : DyadicInterval 40),(⟨-68055104,-68055040⟩ : DyadicInterval 40),(⟨762123381483,762123400813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79445760,79445824⟩ : DyadicInterval 40),(⟨-79451584,-79451520⟩ : DyadicInterval 40),(⟨762123380722,762123400052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177953199417,178078247447⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164939282624,164939282688⟩ : DyadicInterval 40),(⟨-194124500480,-194124500416⟩ : DyadicInterval 40),(⟨747659206092,747659225421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165046905984,165046906048⟩ : DyadicInterval 40),(⟨-194273705472,-194273705408⟩ : DyadicInterval 40),(⟨747638780535,747638799865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29226799424,-29185217728⟩ : DyadicInterval 40),(⟨776715992480,776736802592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165006322624,165104389632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194353412800,-194217438080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2431_ok : ecellOkT e2431 = true := by decide +kernel
theorem e2431_pos {a z : ℝ} (ha1 : ((265287/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((331821/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2431 e2431_ok ha1 ha2 hz1 hz2 hz

-- box ['82743/512000', '1324737/8192000', '3997/4000', '1599/1600']  interval_lower 29386805/137438953472
noncomputable def e2432 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867262,0,true,164712069376,164712069440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388290,0,false,-193809614912,-193809614848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818114,0,true,164810162560,164810162624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437438,0,false,-193945539200,-193945539136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277067600332,0,true,164597337088,164597337152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921955655220,0,false,-193650671104,-193650671040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277203691121,0,true,164714500352,164714500416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921819564431,0,false,-193812983104,-193812983040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568225562,0,true,56596288,56596352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099455029990,0,false,-56599296,-56599232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579591095,0,true,67961216,67961280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443664457,0,false,-67965440,-67965376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623575,0,false,-4224,-4160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624863,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277134229616,0,true,164654701120,164654701184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921889025936,0,false,-193730135168,-193730135104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277259263416,0,true,164762340032,164762340096⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921763992136,0,false,-193879269632,-193879269568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070776850282,0,false,-29116929536,-29116929472⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070817262126,0,false,-29075433984,-29075433920⟩
    { al := (82743/512000), au := (1324737/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨177689239486,177803190338⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164597337088,164597337152⟩ : DyadicInterval 40),(⟨-193650671104,-193650671040⟩ : DyadicInterval 40),(⟨747723992888,747724012217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164714500352,164714500416⟩ : DyadicInterval 40),(⟨-193812983104,-193812983040⟩ : DyadicInterval 40),(⟨747701813391,747701832720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56597786,67963319⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56596288,56596352⟩ : DyadicInterval 40),(⟨-56599296,-56599232⟩ : DyadicInterval 40),(⟨762123382142,762123401471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨67961216,67961280⟩ : DyadicInterval 40),(⟨-67965440,-67965376⟩ : DyadicInterval 40),(⟨762123381462,762123400792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177622601840,177747635640⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164654701120,164654701184⟩ : DyadicInterval 40),(⟨-193730135168,-193730135104⟩ : DyadicInterval 40),(⟨747713136100,747713155430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164762340032,164762340096⟩ : DyadicInterval 40),(⟨-193879269632,-193879269568⟩ : DyadicInterval 40),(⟨747692751488,747692770817⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29116929536,-29075433920⟩ : DyadicInterval 40),(⟨776661100576,776681867648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164712069376,164810162624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193945539200,-193809614848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2432_ok : ecellOkT e2432 = true := by decide +kernel
theorem e2432_pos {a z : ℝ} (ha1 : ((82743/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1324737/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2432 e2432_ok ha1 ha2 hz1 hz2 hz

-- box ['1324737/8192000', '662793/4096000', '3997/4000', '1599/1600']  interval_lower 59083151/274877906944
noncomputable def e2433 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818113,0,true,164810162560,164810162624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437439,0,false,-193945539200,-193945539136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768965,0,true,164908246976,164908247040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486587,0,false,-194081480256,-194081480192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277181465720,0,true,164695366912,164695366976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921841789832,0,false,-193786473792,-193786473728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277317570752,0,true,164812532032,164812532096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921705684800,0,false,-193948822848,-193948822784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568263264,0,true,56633984,56634048⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454992288,0,false,-56636992,-56636928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579636341,0,true,68006400,68006464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443619211,0,false,-68010688,-68010624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623569,0,false,-4224,-4160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624859,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277248137731,0,true,164752762624,164752762688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921775117821,0,false,-193865998592,-193865998528⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277373178659,0,true,164860398080,164860398144⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921650076893,0,false,-194015160000,-194015159936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070740007282,0,false,-29154761920,-29154761856⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070780447339,0,false,-29113235968,-29113235904⟩
    { al := (1324737/8192000), au := (662793/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨177803190337,177917141189⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164695366912,164695366976⟩ : DyadicInterval 40),(⟨-193786473792,-193786473728⟩ : DyadicInterval 40),(⟨747705436772,747705456102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164812532032,164812532096⟩ : DyadicInterval 40),(⟨-193948822848,-193948822784⟩ : DyadicInterval 40),(⟨747683240463,747683259792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56635488,68008565⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56633984,56634048⟩ : DyadicInterval 40),(⟨-56636992,-56636928⟩ : DyadicInterval 40),(⟨762123382138,762123401467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68006400,68006464⟩ : DyadicInterval 40),(⟨-68010688,-68010624⟩ : DyadicInterval 40),(⟨762123381489,762123400818⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177736509955,177861550883⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164752762624,164752762688⟩ : DyadicInterval 40),(⟨-193865998592,-193865998528⟩ : DyadicInterval 40),(⟨747694565905,747694585235⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164860398080,164860398144⟩ : DyadicInterval 40),(⟨-194015160000,-194015159936⟩ : DyadicInterval 40),(⟨747674166828,747674186158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29154761920,-29113235904⟩ : DyadicInterval 40),(⟨776680001568,776700783840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164810162560,164908247040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194081480256,-193945539136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2433_ok : ecellOkT e2433 = true := by decide +kernel
theorem e2433_pos {a z : ℝ} (ha1 : ((1324737/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((662793/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2433 e2433_ok ha1 ha2 hz1 hz2 hz

-- box ['82743/512000', '1324737/8192000', '1599/1600', '1999/2000']  interval_lower 234917793/1099511627776
noncomputable def e2434 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867262,0,true,164712069376,164712069440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388290,0,false,-193809614912,-193809614848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818114,0,true,164810162560,164810162624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437438,0,false,-193945539200,-193945539136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277089811487,0,true,164616459968,164616460032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921933444065,0,false,-193677160128,-193677160064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277225916519,0,true,164733633472,164733633536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921797339033,0,false,-193839493056,-193839492992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556906062,0,true,45277312,45277376⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466349490,0,false,-45279232,-45279168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568264056,0,true,56634816,56634880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454991496,0,false,-56637760,-56637696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624858,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625912,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277145335049,0,true,164664261952,164664262016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921877920503,0,false,-193743380352,-193743380288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277270375997,0,true,164771906112,164771906176⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921752879555,0,false,-193892525184,-193892525120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070773257238,0,false,-29120619008,-29120618944⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070813673919,0,false,-29079118400,-29079118336⟩
    { al := (82743/512000), au := (1324737/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨177689239486,177803190338⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164616459968,164616460032⟩ : DyadicInterval 40),(⟨-193677160128,-193677160064⟩ : DyadicInterval 40),(⟨747720374181,747720393511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164733633472,164733633536⟩ : DyadicInterval 40),(⟨-193839493056,-193839492992⟩ : DyadicInterval 40),(⟨747698189541,747698208871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45278286,56636280⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45277312,45277376⟩ : DyadicInterval 40),(⟨-45279232,-45279168⟩ : DyadicInterval 40),(⟨762123382647,762123401976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56634816,56634880⟩ : DyadicInterval 40),(⟨-56637760,-56637696⟩ : DyadicInterval 40),(⟨762123382106,762123401435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177633707273,177758748221⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164664261952,164664262016⟩ : DyadicInterval 40),(⟨-193743380352,-193743380288⟩ : DyadicInterval 40),(⟨747711326138,747711345468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164771906112,164771906176⟩ : DyadicInterval 40),(⟨-193892525184,-193892525120⟩ : DyadicInterval 40),(⟨747690939064,747690958394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29120619008,-29079118336⟩ : DyadicInterval 40),(⟨776662942784,776683712384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164712069376,164810162624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193945539200,-193809614848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2434_ok : ecellOkT e2434 = true := by decide +kernel
theorem e2434_pos {a z : ℝ} (ha1 : ((82743/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1324737/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2434 e2434_ok ha1 ha2 hz1 hz2 hz

-- box ['1324737/8192000', '662793/4096000', '1599/1600', '1999/2000']  interval_lower 236155343/1099511627776
noncomputable def e2435 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818113,0,true,164810162560,164810162624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437439,0,false,-193945539200,-193945539136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768965,0,true,164908246976,164908247040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486587,0,false,-194081480256,-194081480192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277203691118,0,true,164714500352,164714500416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921819564434,0,false,-193812983104,-193812983040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277339810395,0,true,164831675648,164831675712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921683445157,0,false,-193975353024,-193975352960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556936225,0,true,45307456,45307520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466319327,0,false,-45309440,-45309376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568301761,0,true,56672512,56672576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454953791,0,false,-56675456,-56675392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624854,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625909,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277259250284,0,true,164762328768,164762328832⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921764005268,0,false,-193879253952,-193879253888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277384298359,0,true,164869969472,164869969536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921638957193,0,false,-194028425728,-194028425664⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070736409632,0,false,-29158456192,-29158456128⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070776854529,0,false,-29116925184,-29116925120⟩
    { al := (1324737/8192000), au := (662793/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨177803190337,177917141189⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164714500352,164714500416⟩ : DyadicInterval 40),(⟨-193812983104,-193812983040⟩ : DyadicInterval 40),(⟨747701813391,747701832721⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164831675648,164831675712⟩ : DyadicInterval 40),(⟨-193975353024,-193975352960⟩ : DyadicInterval 40),(⟨747679611941,747679631270⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45308449,56673985⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45307456,45307520⟩ : DyadicInterval 40),(⟨-45309440,-45309376⟩ : DyadicInterval 40),(⟨762123382676,762123402005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56672512,56672576⟩ : DyadicInterval 40),(⟨-56675456,-56675392⟩ : DyadicInterval 40),(⟨762123382102,762123401431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177747622508,177872670583⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164762328768,164762328832⟩ : DyadicInterval 40),(⟨-193879253952,-193879253888⟩ : DyadicInterval 40),(⟨747692753600,747692772929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164869969472,164869969536⟩ : DyadicInterval 40),(⟨-194028425728,-194028425664⟩ : DyadicInterval 40),(⟨747672352058,747672371387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29158456192,-29116925120⟩ : DyadicInterval 40),(⟨776681846176,776702630976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164810162560,164908247040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194081480256,-193945539136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2435_ok : ecellOkT e2435 = true := by decide +kernel
theorem e2435_pos {a z : ℝ} (ha1 : ((1324737/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((662793/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2435 e2435_ok ha1 ha2 hz1 hz2 hz

-- box ['662793/4096000', '265287/1638400', '3997/4000', '1599/1600']  interval_lower 237573367/1099511627776
noncomputable def e2436 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768964,0,true,164908246976,164908247040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486588,0,false,-194081480256,-194081480192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719816,0,true,165006322624,165006322688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535736,0,false,-194217438144,-194217438080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277295331108,0,true,164793388032,164793388096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921727924444,0,false,-193922293248,-193922293184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277431450384,0,true,164910554944,164910555008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921591805168,0,false,-194084679296,-194084679232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568300970,0,true,56671680,56671744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454954582,0,false,-56674688,-56674624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579681591,0,true,68051648,68051712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443573961,0,false,-68055936,-68055872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623563,0,false,-4224,-4160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624855,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277362045850,0,true,164850815360,164850815424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921661209702,0,false,-194001878848,-194001878784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277487093900,0,true,164958447424,164958447488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921536161652,0,false,-194151067200,-194151067136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070703140678,0,false,-29192619776,-29192619712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070743608949,0,false,-29151063424,-29151063360⟩
    { al := (662793/4096000), au := (265287/1638400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨177917141188,178031092040⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164793388032,164793388096⟩ : DyadicInterval 40),(⟨-193922293248,-193922293184⟩ : DyadicInterval 40),(⟨747686868525,747686887855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164910554944,164910555008⟩ : DyadicInterval 40),(⟨-194084679296,-194084679232⟩ : DyadicInterval 40),(⟨747664655406,747664674735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56673194,68053815⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56671680,56671744⟩ : DyadicInterval 40),(⟨-56674688,-56674624⟩ : DyadicInterval 40),(⟨762123382134,762123401463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68051648,68051712⟩ : DyadicInterval 40),(⟨-68055936,-68055872⟩ : DyadicInterval 40),(⟨762123381483,762123400812⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177850418074,177975466124⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164850815360,164850815424⟩ : DyadicInterval 40),(⟨-194001878848,-194001878784⟩ : DyadicInterval 40),(⟨747675983623,747676002953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164958447424,164958447488⟩ : DyadicInterval 40),(⟨-194151067200,-194151067136⟩ : DyadicInterval 40),(⟨747655570041,747655589371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29192619776,-29151063360⟩ : DyadicInterval 40),(⟨776698915296,776719712768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164908246976,165006322688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194217438144,-194081480192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2436_ok : ecellOkT e2436 = true := by decide +kernel
theorem e2436_pos {a z : ℝ} (ha1 : ((662793/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((265287/1638400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2436 e2436_ok ha1 ha2 hz1 hz2 hz

-- box ['265287/1638400', '331821/2048000', '3997/4000', '1599/1600']  interval_lower 119408537/549755813888
noncomputable def e2437 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719815,0,true,165006322624,165006322688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535737,0,false,-194217438144,-194217438080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670667,0,true,165104389568,165104389632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584885,0,false,-194353412800,-194353412736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277409196495,0,true,164891400384,164891400448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921614059057,0,false,-194058129472,-194058129408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277545330016,0,true,165008569088,165008569152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921477925536,0,false,-194220552640,-194220552576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568338678,0,true,56709376,56709440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454916874,0,false,-56712384,-56712320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579726845,0,true,68096960,68097024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443528707,0,false,-68101184,-68101120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623558,0,false,-4224,-4160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624851,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277475953964,0,true,164948859392,164948859456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921547301588,0,false,-194137775936,-194137775872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277601009141,0,true,165056487936,165056488000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921422246411,0,false,-194286991232,-194286991168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070666250470,0,false,-29230503232,-29230503168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070706746959,0,false,-29188916480,-29188916416⟩
    { al := (265287/1638400), au := (331821/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨178031092039,178145042891⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164891400384,164891400448⟩ : DyadicInterval 40),(⟨-194058129472,-194058129408⟩ : DyadicInterval 40),(⟨747668288182,747668307512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165008569088,165008569152⟩ : DyadicInterval 40),(⟨-194220552640,-194220552576⟩ : DyadicInterval 40),(⟨747646058299,747646077628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56710902,68099069⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56709376,56709440⟩ : DyadicInterval 40),(⟨-56712384,-56712320⟩ : DyadicInterval 40),(⟨762123382130,762123401460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68096960,68097024⟩ : DyadicInterval 40),(⟨-68101184,-68101120⟩ : DyadicInterval 40),(⟨762123381446,762123400775⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4224,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123404992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177964326188,178089381365⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164948859392,164948859456⟩ : DyadicInterval 40),(⟨-194137775936,-194137775872⟩ : DyadicInterval 40),(⟨747657389216,747657408546⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165056487936,165056488000⟩ : DyadicInterval 40),(⟨-194286991232,-194286991168⟩ : DyadicInterval 40),(⟨747636961199,747636980528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29230503232,-29188916416⟩ : DyadicInterval 40),(⟨776717841824,776738654496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165006322624,165104389632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194353412800,-194217438080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2437_ok : ecellOkT e2437 = true := by decide +kernel
theorem e2437_pos {a z : ℝ} (ha1 : ((265287/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((331821/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2437 e2437_ok ha1 ha2 hz1 hz2 hz

-- box ['662793/4096000', '265287/1638400', '1599/1600', '1999/2000']  interval_lower 237395833/1099511627776
noncomputable def e2438 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768964,0,true,164908246976,164908247040⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486588,0,false,-194081480256,-194081480192⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719816,0,true,165006322624,165006322688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535736,0,false,-194217438144,-194217438080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277317570750,0,true,164812531968,164812532032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921705684802,0,false,-193948822784,-193948822720⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277453704271,0,true,164929709120,164929709184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921569551281,0,false,-194111229824,-194111229760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556966390,0,true,45337664,45337728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466289162,0,false,-45339584,-45339520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568339470,0,true,56710208,56710272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454916082,0,false,-56713216,-56713152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624850,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625907,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277373165523,0,true,164860386816,164860386880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921650090029,0,false,-194015144384,-194015144320⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277498220720,0,true,164968024000,164968024064⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921525034832,0,false,-194164343040,-194164342976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070699538419,0,false,-29196318976,-29196318912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070740011533,0,false,-29154757504,-29154757440⟩
    { al := (662793/4096000), au := (265287/1638400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨177917141188,178031092040⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164812531968,164812532032⟩ : DyadicInterval 40),(⟨-193948822784,-193948822720⟩ : DyadicInterval 40),(⟨747683240474,747683259803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164929709120,164929709184⟩ : DyadicInterval 40),(⟨-194111229824,-194111229760⟩ : DyadicInterval 40),(⟨747661022223,747661041552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45338614,56711694⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45337664,45337728⟩ : DyadicInterval 40),(⟨-45339584,-45339520⟩ : DyadicInterval 40),(⟨762123382642,762123401971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56710208,56710272⟩ : DyadicInterval 40),(⟨-56713216,-56713152⟩ : DyadicInterval 40),(⟨762123382130,762123401459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177861537747,177986592944⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164860386816,164860386880⟩ : DyadicInterval 40),(⟨-194015144384,-194015144320⟩ : DyadicInterval 40),(⟨747674168970,747674188300⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164968024000,164968024064⟩ : DyadicInterval 40),(⟨-194164343040,-194164342976⟩ : DyadicInterval 40),(⟨747653752967,747653772297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29196318976,-29154757440⟩ : DyadicInterval 40),(⟨776700762336,776721562368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164908246976,165006322688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194217438144,-194081480192⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2438_ok : ecellOkT e2438 = true := by decide +kernel
theorem e2438_pos {a z : ℝ} (ha1 : ((662793/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((265287/1638400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2438 e2438_ok ha1 ha2 hz1 hz2 hz

-- box ['265287/1638400', '331821/2048000', '1599/1600', '1999/2000']  interval_lower 119319667/549755813888
noncomputable def e2439 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277542719815,0,true,165006322624,165006322688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921480535737,0,false,-194217438144,-194217438080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670667,0,true,165104389568,165104389632⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584885,0,false,-194353412800,-194353412736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277431450382,0,true,164910554944,164910555008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921591805170,0,false,-194084679296,-194084679232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277567598146,0,true,165027733888,165027733952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921455657406,0,false,-194247123392,-194247123328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556996556,0,true,45367808,45367872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466258996,0,false,-45369728,-45369664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568377181,0,true,56747904,56747968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454878371,0,false,-56750912,-56750848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624846,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625904,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277487080763,0,true,164958436096,164958436160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921536174789,0,false,-194151051520,-194151051456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277612143088,0,true,165066069888,165066069952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921411112464,0,false,-194300277184,-194300277120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070662643596,0,false,-29234207296,-29234207232⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070703144932,0,false,-29192615424,-29192615360⟩
    { al := (265287/1638400), au := (331821/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨178031092039,178145042891⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165006322624,165006322688⟩ : DyadicInterval 40),(⟨-194217438144,-194217438080⟩ : DyadicInterval 40),(⟨747646484700,747646504030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164910554944,164910555008⟩ : DyadicInterval 40),(⟨-194084679296,-194084679232⟩ : DyadicInterval 40),(⟨747664655406,747664674735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165027733888,165027733952⟩ : DyadicInterval 40),(⟨-194247123392,-194247123328⟩ : DyadicInterval 40),(⟨747642420357,747642439687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45368780,56749405⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45367808,45367872⟩ : DyadicInterval 40),(⟨-45369728,-45369664⟩ : DyadicInterval 40),(⟨762123382639,762123401969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56747904,56747968⟩ : DyadicInterval 40),(⟨-56750912,-56750848⟩ : DyadicInterval 40),(⟨762123382126,762123401456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177975452987,178100515312⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164958436096,164958436160⟩ : DyadicInterval 40),(⟨-194151051520,-194151051456⟩ : DyadicInterval 40),(⟨747655572196,747655591526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165066069888,165066069952⟩ : DyadicInterval 40),(⟨-194300277184,-194300277120⟩ : DyadicInterval 40),(⟨747635141706,747635161036⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29234207296,-29192615360⟩ : DyadicInterval 40),(⟨776719691296,776740506528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165006322624,165104389632⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194353412800,-194217438080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2439_ok : ecellOkT e2439 = true := by decide +kernel
theorem e2439_pos {a z : ℝ} (ha1 : ((265287/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((331821/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2439 e2439_ok ha1 ha2 hz1 hz2 hz

-- box ['331821/2048000', '1328133/8192000', '999/1000', '7993/8000']  interval_lower 60105123/274877906944
noncomputable def e2440 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670666,0,true,165104389568,165104389632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584886,0,false,-194353412800,-194353412736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621518,0,true,165202447744,165202447808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634034,0,false,-194489404352,-194489404288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277478525623,0,true,164951072832,164951072896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921544729929,0,false,-194140844224,-194140844160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277614644899,0,true,165068222912,165068222976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921408610653,0,false,-194303262592,-194303262528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591075551,0,true,79444864,79444928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432180001,0,false,-79450688,-79450624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602486348,0,true,90854784,90854848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420769204,0,false,-90862336,-90862272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620267,0,false,-7552,-7488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622036,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277567594326,0,true,165027730560,165027730624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921455661226,0,false,-194247118848,-194247118784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277692642325,0,true,165135345216,165135345280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921330613227,0,false,-194396340416,-194396340352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070636558933,0,false,-29260995136,-29260995072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070677073941,0,false,-29219388224,-29219388160⟩
    { al := (331821/2048000), au := (1328133/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨178145042890,178258993742⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231325,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164951072832,164951072896⟩ : DyadicInterval 40),(⟨-194140844224,-194140844160⟩ : DyadicInterval 40),(⟨747656969254,747656988584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165068222912,165068222976⟩ : DyadicInterval 40),(⟨-194303262592,-194303262528⟩ : DyadicInterval 40),(⟨747634732879,747634752209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79447775,90858572⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79444864,79444928⟩ : DyadicInterval 40),(⟨-79450688,-79450624⟩ : DyadicInterval 40),(⟨762123380723,762123400052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90854784,90854848⟩ : DyadicInterval 40),(⟨-90862336,-90862272⟩ : DyadicInterval 40),(⟨762123379819,762123399149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7552,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123406656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178055966550,178181014549⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165027730560,165027730624⟩ : DyadicInterval 40),(⟨-194247118848,-194247118784⟩ : DyadicInterval 40),(⟨747642421011,747642440340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165135345216,165135345280⟩ : DyadicInterval 40),(⟨-194396340416,-194396340352⟩ : DyadicInterval 40),(⟨747621983457,747622002786⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29260995136,-29219388160⟩ : DyadicInterval 40),(⟨776733077696,776753900448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165104389568,165202447808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194489404352,-194353412736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2440_ok : ecellOkT e2440 = true := by decide +kernel
theorem e2440_pos {a z : ℝ} (ha1 : ((331821/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1328133/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2440 e2440_ok ha1 ha2 hz1 hz2 hz

-- box ['1328133/8192000', '664491/4096000', '999/1000', '7993/8000']  interval_lower 241670975/1099511627776
noncomputable def e2441 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621517,0,true,165202447744,165202447808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634035,0,false,-194489404352,-194489404288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572369,0,true,165300497216,165300497280⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683183,0,false,-194625412672,-194625412608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277592362523,0,true,165049046592,165049046656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921430893029,0,false,-194276673472,-194276673408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277728496043,0,true,165166198528,165166198592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921294759509,0,false,-194439128896,-194439128832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591128348,0,true,79497664,79497728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432127204,0,false,-79503488,-79503424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602546694,0,true,90915136,90915200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420708858,0,false,-90922688,-90922624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620257,0,false,-7552,-7488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622028,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277681488196,0,true,165125746560,165125746624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921341767356,0,false,-194383029184,-194383029120⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277806543326,0,true,165233357760,165233357824⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921216712226,0,false,-194532277696,-194532277632⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070599630751,0,false,-29298919936,-29298919872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070640173978,0,false,-29257282560,-29257282496⟩
    { al := (1328133/8192000), au := (664491/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨178258993741,178372944593⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231326,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165049046592,165049046656⟩ : DyadicInterval 40),(⟨-194276673472,-194276673408⟩ : DyadicInterval 40),(⟨747638374102,747638393431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165166198528,165166198592⟩ : DyadicInterval 40),(⟨-194439128896,-194439128832⟩ : DyadicInterval 40),(⟨747616120899,747616140228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79500572,90918918⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79497664,79497728⟩ : DyadicInterval 40),(⟨-79503488,-79503424⟩ : DyadicInterval 40),(⟨762123380715,762123400044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90915136,90915200⟩ : DyadicInterval 40),(⟨-90922688,-90922624⟩ : DyadicInterval 40),(⟨762123379809,762123399139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7552,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123406656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178169860420,178294915550⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165125746560,165125746624⟩ : DyadicInterval 40),(⟨-194383029184,-194383029120⟩ : DyadicInterval 40),(⟨747623807036,747623826366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165233357760,165233357824⟩ : DyadicInterval 40),(⟨-194532277696,-194532277632⟩ : DyadicInterval 40),(⟨747603355007,747603374336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29298919936,-29257282496⟩ : DyadicInterval 40),(⟨776752024864,776772862848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165202447744,165300497280⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194625412672,-194489404288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2441_ok : ecellOkT e2441 = true := by decide +kernel
theorem e2441_pos {a z : ℝ} (ha1 : ((1328133/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((664491/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2441 e2441_ok ha1 ha2 hz1 hz2 hz

-- box ['331821/2048000', '1328133/8192000', '7993/8000', '3997/4000']  interval_lower 240242317/1099511627776
noncomputable def e2442 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670666,0,true,165104389568,165104389632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584886,0,false,-194353412800,-194353412736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621518,0,true,165202447744,165202447808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634034,0,false,-194489404352,-194489404288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277500793753,0,true,164970238592,164970238656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921522461799,0,false,-194167413056,-194167412992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277636927273,0,true,165087398912,165087398976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921386328279,0,false,-194329852288,-194329852224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579725998,0,true,68096064,68096128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443529554,0,false,-68100352,-68100288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591129252,0,true,79498560,79498624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432126300,0,false,-79504384,-79504320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622027,0,false,-5760,-5696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623559,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277578728191,0,true,165037312640,165037312704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921444527361,0,false,-194260404224,-194260404160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277703783343,0,true,165144932544,165144932608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921319472209,0,false,-194409636096,-194409636032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070632947911,0,false,-29264703552,-29264703488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070673467771,0,false,-29223091520,-29223091456⟩
    { al := (331821/2048000), au := (1328133/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨178145042890,178258993742⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231325,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164970238592,164970238656⟩ : DyadicInterval 40),(⟨-194167413056,-194167412992⟩ : DyadicInterval 40),(⟨747653332729,747653352059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165087398912,165087398976⟩ : DyadicInterval 40),(⟨-194329852288,-194329852224⟩ : DyadicInterval 40),(⟨747631091156,747631110486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68098222,79501476⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68096064,68096128⟩ : DyadicInterval 40),(⟨-68100352,-68100288⟩ : DyadicInterval 40),(⟨762123381478,762123400807⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79498560,79498624⟩ : DyadicInterval 40),(⟨-79504384,-79504320⟩ : DyadicInterval 40),(⟨762123380715,762123400044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178067100415,178192155567⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165037312640,165037312704⟩ : DyadicInterval 40),(⟨-194260404224,-194260404160⟩ : DyadicInterval 40),(⟨747640601911,747640621241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165144932544,165144932608⟩ : DyadicInterval 40),(⟨-194409636096,-194409636032⟩ : DyadicInterval 40),(⟨747620161855,747620181184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29264703552,-29223091456⟩ : DyadicInterval 40),(⟨776734929344,776755754656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165104389568,165202447808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194489404352,-194353412736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2442_ok : ecellOkT e2442 = true := by decide +kernel
theorem e2442_pos {a z : ℝ} (ha1 : ((331821/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1328133/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2442 e2442_ok ha1 ha2 hz1 hz2 hz

-- box ['1328133/8192000', '664491/4096000', '7993/8000', '3997/4000']  interval_lower 60373143/274877906944
noncomputable def e2443 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621517,0,true,165202447744,165202447808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634035,0,false,-194489404352,-194489404288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572369,0,true,165300497216,165300497280⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683183,0,false,-194625412672,-194625412608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277614644897,0,true,165068222912,165068222976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921408610655,0,false,-194303262592,-194303262528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277750792661,0,true,165185385088,165185385152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921272462891,0,false,-194465738944,-194465738880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579771253,0,true,68141312,68141376⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443484299,0,false,-68145600,-68145536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591182056,0,true,79551360,79551424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432073496,0,false,-79557184,-79557120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622019,0,false,-5760,-5696⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623553,0,false,-4224,-4160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277692629183,0,true,165135333952,165135334016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921330626369,0,false,-194396324672,-194396324608⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277817691463,0,true,165242950336,165242950400⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921205564089,0,false,-194545583552,-194545583488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070596015112,0,false,-29302633216,-29302633152⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070636563193,0,false,-29260990720,-29260990656⟩
    { al := (1328133/8192000), au := (664491/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨178258993741,178372944593⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231326,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165068222912,165068222976⟩ : DyadicInterval 40),(⟨-194303262592,-194303262528⟩ : DyadicInterval 40),(⟨747634732879,747634752209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165185385088,165185385152⟩ : DyadicInterval 40),(⟨-194465738944,-194465738880⟩ : DyadicInterval 40),(⟨747612474498,747612493828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68143477,79554280⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68141312,68141376⟩ : DyadicInterval 40),(⟨-68145600,-68145536⟩ : DyadicInterval 40),(⟨762123381472,762123400801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79551360,79551424⟩ : DyadicInterval 40),(⟨-79557184,-79557120⟩ : DyadicInterval 40),(⟨762123380707,762123400037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5760,-4160⟩ : DyadicInterval 40),(⟨762123385696,762123405760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178181001407,178306063687⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165135333952,165135334016⟩ : DyadicInterval 40),(⟨-194396324672,-194396324608⟩ : DyadicInterval 40),(⟨747621985554,747622004883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165242950336,165242950400⟩ : DyadicInterval 40),(⟨-194545583552,-194545583488⟩ : DyadicInterval 40),(⟨747601531083,747601550412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29302633216,-29260990656⟩ : DyadicInterval 40),(⟨776753878944,776774719488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165202447744,165300497280⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194625412672,-194489404288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2443_ok : ecellOkT e2443 = true := by decide +kernel
theorem e2443_pos {a z : ℝ} (ha1 : ((1328133/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((664491/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2443 e2443_ok ha1 ha2 hz1 hz2 hz

-- box ['664491/4096000', '1329831/8192000', '999/1000', '7993/8000']  interval_lower 121462349/549755813888
noncomputable def e2444 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572368,0,true,165300497216,165300497280⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683184,0,false,-194625412672,-194625412608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523220,0,true,165398537920,165398537984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732332,0,false,-194761437824,-194761437760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277706199423,0,true,165147011648,165147011712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921317056129,0,false,-194412519488,-194412519424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277842347187,0,true,165264165440,165264165504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921180908365,0,false,-194575011968,-194575011904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591181151,0,true,79550464,79550528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432074401,0,false,-79556288,-79556224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602607044,0,true,90975488,90975552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420648508,0,false,-90983040,-90982976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620247,0,false,-7552,-7488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622021,0,false,-5760,-5696⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277795382072,0,true,165223753856,165223753920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921227873480,0,false,-194518956352,-194518956288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277920444329,0,true,165331361600,165331361664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921102811223,0,false,-194668231872,-194668231808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070562678970,0,false,-29336870208,-29336870144⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070603250418,0,false,-29295202496,-29295202432⟩
    { al := (664491/4096000), au := (1329831/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨178372944592,178486895444⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165147011648,165147011712⟩ : DyadicInterval 40),(⟨-194412519488,-194412519424⟩ : DyadicInterval 40),(⟨747619766826,747619786155⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165264165440,165264165504⟩ : DyadicInterval 40),(⟨-194575011968,-194575011904⟩ : DyadicInterval 40),(⟨747597496787,747597516117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79553375,90979268⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79550464,79550528⟩ : DyadicInterval 40),(⟨-79556288,-79556224⟩ : DyadicInterval 40),(⟨762123380707,762123400037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90975488,90975552⟩ : DyadicInterval 40),(⟨-90983040,-90982976⟩ : DyadicInterval 40),(⟨762123379799,762123399129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7552,-5696⟩ : DyadicInterval 40),(⟨762123386464,762123406656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178283754296,178408816553⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165223753856,165223753920⟩ : DyadicInterval 40),(⟨-194518956352,-194518956288⟩ : DyadicInterval 40),(⟨747605180939,747605200268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165331361600,165331361664⟩ : DyadicInterval 40),(⟨-194668231872,-194668231808⟩ : DyadicInterval 40),(⟨747584714456,747584733786⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29336870208,-29295202432⟩ : DyadicInterval 40),(⟨776770984832,776791837984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165300497216,165398537984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194761437824,-194625412608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2444_ok : ecellOkT e2444 = true := by decide +kernel
theorem e2444_pos {a z : ℝ} (ha1 : ((664491/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1329831/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2444 e2444_ok ha1 ha2 hz1 hz2 hz

-- box ['1329831/8192000', '33267/204800', '999/1000', '7993/8000']  interval_lower 122090705/549755813888
noncomputable def e2445 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523219,0,true,165398537920,165398537984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732333,0,false,-194761437824,-194761437760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474072,0,true,165496569856,165496569920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781480,0,false,-194897479808,-194897479744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277820036323,0,true,165244968000,165244968064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921203219229,0,false,-194548382272,-194548382208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277956198332,0,true,165362123584,165362123648⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921067057220,0,false,-194710911872,-194710911808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591233957,0,true,79603264,79603328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432021595,0,false,-79609088,-79609024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602667400,0,true,91035840,91035904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420588152,0,false,-91043456,-91043392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620237,0,false,-7552,-7488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622013,0,false,-5824,-5760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277909275950,0,true,165321752384,165321752448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921113979602,0,false,-194654900352,-194654900288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278034345326,0,true,165429356608,165429356672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920988910226,0,false,-194804202752,-194804202688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070525703592,0,false,-29374846144,-29374846080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070566303261,0,false,-29333147968,-29333147904⟩
    { al := (1329831/8192000), au := (33267/204800), zl := (999/1000), zu := (7993/8000),
      A := ⟨178486895443,178600846296⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165244968000,165244968064⟩ : DyadicInterval 40),(⟨-194548382272,-194548382208⟩ : DyadicInterval 40),(⟨747601147424,747601166753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165362123584,165362123648⟩ : DyadicInterval 40),(⟨-194710911872,-194710911808⟩ : DyadicInterval 40),(⟨747578860606,747578879936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨79606181,91039624⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79603264,79603328⟩ : DyadicInterval 40),(⟨-79609088,-79609024⟩ : DyadicInterval 40),(⟨762123380700,762123400029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨91035840,91035904⟩ : DyadicInterval 40),(⟨-91043456,-91043392⟩ : DyadicInterval 40),(⟨762123379821,762123399151⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7552,-5760⟩ : DyadicInterval 40),(⟨762123386496,762123406656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178397648174,178522717550⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165321752384,165321752448⟩ : DyadicInterval 40),(⟨-194654900352,-194654900288⟩ : DyadicInterval 40),(⟨747586542754,747586562083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165429356608,165429356672⟩ : DyadicInterval 40),(⟨-194804202752,-194804202688⟩ : DyadicInterval 40),(⟨747566061799,747566081129⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29374846144,-29333147904⟩ : DyadicInterval 40),(⟨776789957568,776810825952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165398537920,165496569920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194897479808,-194761437760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2445_ok : ecellOkT e2445 = true := by decide +kernel
theorem e2445_pos {a z : ℝ} (ha1 : ((1329831/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((33267/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2445 e2445_ok ha1 ha2 hz1 hz2 hz

-- box ['664491/4096000', '1329831/8192000', '7993/8000', '3997/4000']  interval_lower 242745471/1099511627776
noncomputable def e2446 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572368,0,true,165300497216,165300497280⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683184,0,false,-194625412672,-194625412608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523220,0,true,165398537920,165398537984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732332,0,false,-194761437824,-194761437760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277728496041,0,true,165166198528,165166198592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921294759511,0,false,-194439128896,-194439128832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277864658049,0,true,165283362496,165283362560⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921158597503,0,false,-194601642304,-194601642240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579816513,0,true,68186560,68186624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443439039,0,false,-68190912,-68190848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591234862,0,true,79604160,79604224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099432020690,0,false,-79609984,-79609920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622012,0,false,-5824,-5760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623548,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277806530181,0,true,165233346432,165233346496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921216725371,0,false,-194532262016,-194532261952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277931599585,0,true,165340959424,165340959488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921091655967,0,false,-194681547840,-194681547776⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070559058711,0,false,-29340588416,-29340588352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070599635015,0,false,-29298915520,-29298915456⟩
    { al := (664491/4096000), au := (1329831/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨178372944592,178486895444⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165166198528,165166198592⟩ : DyadicInterval 40),(⟨-194439128896,-194439128832⟩ : DyadicInterval 40),(⟨747616120899,747616140229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165283362496,165283362560⟩ : DyadicInterval 40),(⟨-194601642304,-194601642240⟩ : DyadicInterval 40),(⟨747593845712,747593865042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68188737,79607086⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68186560,68186624⟩ : DyadicInterval 40),(⟨-68190912,-68190848⟩ : DyadicInterval 40),(⟨762123381498,762123400828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79604160,79604224⟩ : DyadicInterval 40),(⟨-79609984,-79609920⟩ : DyadicInterval 40),(⟨762123380700,762123400029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5824,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123405792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178294902405,178419971809⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165233346432,165233346496⟩ : DyadicInterval 40),(⟨-194532262016,-194532261952⟩ : DyadicInterval 40),(⟨747603357171,747603376501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165340959424,165340959488⟩ : DyadicInterval 40),(⟨-194681547840,-194681547776⟩ : DyadicInterval 40),(⟨747582888181,747582907510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29340588416,-29298915456⟩ : DyadicInterval 40),(⟨776772841344,776793697088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165300497216,165398537984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194761437824,-194625412608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2446_ok : ecellOkT e2446 = true := by decide +kernel
theorem e2446_pos {a z : ℝ} (ha1 : ((664491/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1329831/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2446 e2446_ok ha1 ha2 hz1 hz2 hz

-- box ['1329831/8192000', '33267/204800', '7993/8000', '3997/4000']  interval_lower 244001777/1099511627776
noncomputable def e2447 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523219,0,true,165398537920,165398537984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732333,0,false,-194761437824,-194761437760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474072,0,true,165496569856,165496569920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781480,0,false,-194897479808,-194897479744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277842347185,0,true,165264165440,165264165504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921180908367,0,false,-194575011968,-194575011904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277978523438,0,true,165381331200,165381331264⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921044732114,0,false,-194737562496,-194737562432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579861775,0,true,68231872,68231936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443393777,0,false,-68236160,-68236096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099591287674,0,true,79656960,79657024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431967878,0,false,-79662784,-79662720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622004,0,false,-5824,-5760⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623542,0,false,-4288,-4224⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277920431182,0,true,165331350272,165331350336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921102824370,0,false,-194668216128,-194668216064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278045507705,0,true,165438959744,165438959808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920977747847,0,false,-194817528960,-194817528896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070522078709,0,false,-29378569152,-29378569088⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070562683237,0,false,-29336865856,-29336865792⟩
    { al := (1329831/8192000), au := (33267/204800), zl := (7993/8000), zu := (3997/4000),
      A := ⟨178486895443,178600846296⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165264165440,165264165504⟩ : DyadicInterval 40),(⟨-194575011968,-194575011904⟩ : DyadicInterval 40),(⟨747597496787,747597516117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165381331200,165381331264⟩ : DyadicInterval 40),(⟨-194737562496,-194737562432⟩ : DyadicInterval 40),(⟨747575204814,747575224143⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨68233999,79659898⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68231872,68231936⟩ : DyadicInterval 40),(⟨-68236160,-68236096⟩ : DyadicInterval 40),(⟨762123381461,762123400790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨79656960,79657024⟩ : DyadicInterval 40),(⟨-79662784,-79662720⟩ : DyadicInterval 40),(⟨762123380692,762123400021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5824,-4224⟩ : DyadicInterval 40),(⟨762123385728,762123405792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178408803406,178533879929⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165331350272,165331350336⟩ : DyadicInterval 40),(⟨-194668216128,-194668216064⟩ : DyadicInterval 40),(⟨747584716597,747584735927⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165438959744,165438959808⟩ : DyadicInterval 40),(⟨-194817528960,-194817528896⟩ : DyadicInterval 40),(⟨747564233185,747564252514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29378569152,-29336865792⟩ : DyadicInterval 40),(⟨776791816512,776812687456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165398537920,165496569920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194897479808,-194761437760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2447_ok : ecellOkT e2447 = true := by decide +kernel
theorem e2447_pos {a z : ℝ} (ha1 : ((1329831/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((33267/204800 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2447 e2447_ok ha1 ha2 hz1 hz2 hz

-- box ['331821/2048000', '1328133/8192000', '3997/4000', '1599/1600']  interval_lower 30007983/137438953472
noncomputable def e2448 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670666,0,true,165104389568,165104389632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584886,0,false,-194353412800,-194353412736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621518,0,true,165202447744,165202447808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634034,0,false,-194489404352,-194489404288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277523061883,0,true,164989404032,164989404096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921500193669,0,false,-194193982528,-194193982464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277659209647,0,true,165106574528,165106574592⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921364045905,0,false,-194356442688,-194356442624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568376388,0,true,56747136,56747200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454879164,0,false,-56750080,-56750016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579772102,0,true,68142208,68142272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443483450,0,false,-68146496,-68146432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623552,0,false,-4288,-4224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624848,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277589862083,0,true,165046894656,165046894720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921433393469,0,false,-194273689792,-194273689728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277714924381,0,true,165154519744,165154519808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921308331171,0,false,-194422932032,-194422931968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070629336658,0,false,-29268412224,-29268412160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070669861366,0,false,-29226795072,-29226795008⟩
    { al := (331821/2048000), au := (1328133/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨178145042890,178258993742⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231325,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164989404032,164989404096⟩ : DyadicInterval 40),(⟨-194193982528,-194193982464⟩ : DyadicInterval 40),(⟨747649695732,747649715062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165106574528,165106574592⟩ : DyadicInterval 40),(⟨-194356442688,-194356442624⟩ : DyadicInterval 40),(⟨747627449024,747627468354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56748612,68144326⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56747136,56747200⟩ : DyadicInterval 40),(⟨-56750080,-56750016⟩ : DyadicInterval 40),(⟨762123382094,762123401424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68142208,68142272⟩ : DyadicInterval 40),(⟨-68146496,-68146432⟩ : DyadicInterval 40),(⟨762123381472,762123400801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178078234307,178203296605⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165046894656,165046894720⟩ : DyadicInterval 40),(⟨-194273689792,-194273689728⟩ : DyadicInterval 40),(⟨747638782693,747638802023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165154519744,165154519808⟩ : DyadicInterval 40),(⟨-194422932032,-194422931968⟩ : DyadicInterval 40),(⟨747618340199,747618359528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29268412224,-29226795008⟩ : DyadicInterval 40),(⟨776736781120,776757608992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165104389568,165202447808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194489404352,-194353412736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2448_ok : ecellOkT e2448 = true := by decide +kernel
theorem e2448_pos {a z : ℝ} (ha1 : ((331821/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1328133/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2448 e2448_ok ha1 ha2 hz1 hz2 hz

-- box ['1328133/8192000', '664491/4096000', '3997/4000', '1599/1600']  interval_lower 241313553/1099511627776
noncomputable def e2449 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621517,0,true,165202447744,165202447808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634035,0,false,-194489404352,-194489404288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572369,0,true,165300497216,165300497280⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683183,0,false,-194625412672,-194625412608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277636927271,0,true,165087398912,165087398976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921386328281,0,false,-194329852288,-194329852224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277773089279,0,true,165204571264,165204571328⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921250166273,0,false,-194492349568,-194492349504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568414103,0,true,56784832,56784896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454841449,0,false,-56787840,-56787776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579817362,0,true,68187456,68187520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443438190,0,false,-68191744,-68191680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623547,0,false,-4288,-4224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624844,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277703770200,0,true,165144921216,165144921280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921319485352,0,false,-194409620416,-194409620352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277828839627,0,true,165252542848,165252542912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921194415925,0,false,-194558889600,-194558889536⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070592399239,0,false,-29306346752,-29306346688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070632952172,0,false,-29264699136,-29264699072⟩
    { al := (1328133/8192000), au := (664491/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨178258993741,178372944593⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231326,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165087398912,165087398976⟩ : DyadicInterval 40),(⟨-194329852288,-194329852224⟩ : DyadicInterval 40),(⟨747631091157,747631110486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165204571264,165204571328⟩ : DyadicInterval 40),(⟨-194492349568,-194492349504⟩ : DyadicInterval 40),(⟨747608827633,747608846962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56786327,68189586⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56784832,56784896⟩ : DyadicInterval 40),(⟨-56787840,-56787776⟩ : DyadicInterval 40),(⟨762123382123,762123401452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68187456,68187520⟩ : DyadicInterval 40),(⟨-68191744,-68191680⟩ : DyadicInterval 40),(⟨762123381466,762123400796⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178192142424,178317211851⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165144921216,165144921280⟩ : DyadicInterval 40),(⟨-194409620416,-194409620352⟩ : DyadicInterval 40),(⟨747620164016,747620183346⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165252542848,165252542912⟩ : DyadicInterval 40),(⟨-194558889600,-194558889536⟩ : DyadicInterval 40),(⟨747599707040,747599726369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29306346752,-29264699072⟩ : DyadicInterval 40),(⟨776755733152,776776576256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165202447744,165300497280⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194625412672,-194489404288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2449_ok : ecellOkT e2449 = true := by decide +kernel
theorem e2449_pos {a z : ℝ} (ha1 : ((1328133/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((664491/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2449 e2449_ok ha1 ha2 hz1 hz2 hz

-- box ['331821/2048000', '1328133/8192000', '1599/1600', '1999/2000']  interval_lower 119942785/549755813888
noncomputable def e2450 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277656670666,0,true,165104389568,165104389632⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921366584886,0,false,-194353412800,-194353412736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621518,0,true,165202447744,165202447808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634034,0,false,-194489404352,-194489404288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277545330014,0,true,165008569088,165008569152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921477925538,0,false,-194220552640,-194220552576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277681492022,0,true,165125749888,165125749952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921341763530,0,false,-194383033728,-194383033664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557026725,0,true,45397952,45398016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466228827,0,false,-45399936,-45399872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568414895,0,true,56785600,56785664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454840657,0,false,-56788608,-56788544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624843,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625902,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277600996001,0,true,165056476672,165056476736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921422259551,0,false,-194286975552,-194286975488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277726065452,0,true,165164106944,165164107008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921297190100,0,false,-194436228096,-194436228032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070625725168,0,false,-29272121152,-29272121088⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070666254728,0,false,-29230498816,-29230498752⟩
    { al := (331821/2048000), au := (1328133/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨178145042890,178258993742⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165104389568,165104389632⟩ : DyadicInterval 40),(⟨-194353412800,-194353412736⟩ : DyadicInterval 40),(⟨747627864054,747627883384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231325,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165008569088,165008569152⟩ : DyadicInterval 40),(⟨-194220552640,-194220552576⟩ : DyadicInterval 40),(⟨747646058299,747646077629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165125749888,165125749952⟩ : DyadicInterval 40),(⟨-194383033728,-194383033664⟩ : DyadicInterval 40),(⟨747623806381,747623825710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45398949,56787119⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45397952,45398016⟩ : DyadicInterval 40),(⟨-45399936,-45399872⟩ : DyadicInterval 40),(⟨762123382669,762123401998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56785600,56785664⟩ : DyadicInterval 40),(⟨-56788608,-56788544⟩ : DyadicInterval 40),(⟨762123382123,762123401452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178089368225,178214437676⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165056476672,165056476736⟩ : DyadicInterval 40),(⟨-194286975552,-194286975488⟩ : DyadicInterval 40),(⟨747636963320,747636982649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165164106944,165164107008⟩ : DyadicInterval 40),(⟨-194436228096,-194436228032⟩ : DyadicInterval 40),(⟨747616518360,747616537690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29272121152,-29230498752⟩ : DyadicInterval 40),(⟨776738632992,776759463456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165104389568,165202447808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194489404352,-194353412736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2450_ok : ecellOkT e2450 = true := by decide +kernel
theorem e2450_pos {a z : ℝ} (ha1 : ((331821/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1328133/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2450 e2450_ok ha1 ha2 hz1 hz2 hz

-- box ['1328133/8192000', '664491/4096000', '1599/1600', '1999/2000']  interval_lower 241134895/1099511627776
noncomputable def e2451 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277770621517,0,true,165202447744,165202447808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921252634035,0,false,-194489404352,-194489404288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572369,0,true,165300497216,165300497280⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683183,0,false,-194625412672,-194625412608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277659209645,0,true,165106574528,165106574592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921364045907,0,false,-194356442688,-194356442624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277795385897,0,true,165223757120,165223757184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921227869655,0,false,-194518960896,-194518960832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557056897,0,true,45428160,45428224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466198655,0,false,-45430080,-45430016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568452613,0,true,56823360,56823424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454802939,0,false,-56826368,-56826304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624839,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625899,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277714911238,0,true,165154508480,165154508544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921308344314,0,false,-194422916352,-194422916288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277839987816,0,true,165262135296,165262135360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921183267736,0,false,-194572195840,-194572195776⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070588783131,0,false,-29310060544,-29310060480⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070629340919,0,false,-29268407808,-29268407744⟩
    { al := (1328133/8192000), au := (664491/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨178258993741,178372944593⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165202447744,165202447808⟩ : DyadicInterval 40),(⟨-194489404352,-194489404288⟩ : DyadicInterval 40),(⟨747609231326,747609250655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165106574528,165106574592⟩ : DyadicInterval 40),(⟨-194356442688,-194356442624⟩ : DyadicInterval 40),(⟨747627449025,747627468354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165223757120,165223757184⟩ : DyadicInterval 40),(⟨-194518960896,-194518960832⟩ : DyadicInterval 40),(⟨747605180320,747605199649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45429121,56824837⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45428160,45428224⟩ : DyadicInterval 40),(⟨-45430080,-45430016⟩ : DyadicInterval 40),(⟨762123382634,762123401964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56823360,56823424⟩ : DyadicInterval 40),(⟨-56826368,-56826304⟩ : DyadicInterval 40),(⟨762123382119,762123401448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178203283462,178328360040⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165154508480,165154508544⟩ : DyadicInterval 40),(⟨-194422916352,-194422916288⟩ : DyadicInterval 40),(⟨747618342324,747618361653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165262135296,165262135360⟩ : DyadicInterval 40),(⟨-194572195840,-194572195776⟩ : DyadicInterval 40),(⟨747597882878,747597902208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29310060544,-29268407744⟩ : DyadicInterval 40),(⟨776757587488,776778433152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165202447744,165300497280⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194625412672,-194489404288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2451_ok : ecellOkT e2451 = true := by decide +kernel
theorem e2451_pos {a z : ℝ} (ha1 : ((1328133/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((664491/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2451 e2451_ok ha1 ha2 hz1 hz2 hz

-- box ['664491/4096000', '1329831/8192000', '3997/4000', '1599/1600']  interval_lower 242566313/1099511627776
noncomputable def e2452 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572368,0,true,165300497216,165300497280⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683184,0,false,-194625412672,-194625412608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523220,0,true,165398537920,165398537984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732332,0,false,-194761437824,-194761437760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277750792659,0,true,165185385088,165185385152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921272462893,0,false,-194465738880,-194465738816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277886968911,0,true,165302559232,165302559296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921136286641,0,false,-194628273280,-194628273216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568451820,0,true,56822528,56822592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454803732,0,false,-56825536,-56825472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579862625,0,true,68232704,68232768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443392927,0,false,-68236992,-68236928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623541,0,false,-4288,-4224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624840,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277817678322,0,true,165242939008,165242939072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921205577230,0,false,-194545567872,-194545567808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277942754868,0,true,165350557184,165350557248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921080500684,0,false,-194694864064,-194694864000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070555438217,0,false,-29344306816,-29344306752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070596019375,0,false,-29302628800,-29302628736⟩
    { al := (664491/4096000), au := (1329831/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨178372944592,178486895444⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165185385088,165185385152⟩ : DyadicInterval 40),(⟨-194465738880,-194465738816⟩ : DyadicInterval 40),(⟨747612474472,747612493801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165302559232,165302559296⟩ : DyadicInterval 40),(⟨-194628273280,-194628273216⟩ : DyadicInterval 40),(⟨747590194161,747590213491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56824044,68234849⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56822528,56822592⟩ : DyadicInterval 40),(⟨-56825536,-56825472⟩ : DyadicInterval 40),(⟨762123382119,762123401448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68232704,68232768⟩ : DyadicInterval 40),(⟨-68236992,-68236928⟩ : DyadicInterval 40),(⟨762123381461,762123400790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178306050546,178431127092⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165242939008,165242939072⟩ : DyadicInterval 40),(⟨-194545567872,-194545567808⟩ : DyadicInterval 40),(⟨747601533247,747601552576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165350557184,165350557248⟩ : DyadicInterval 40),(⟨-194694864064,-194694864000⟩ : DyadicInterval 40),(⟨747581061812,747581081142⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29344306816,-29302628736⟩ : DyadicInterval 40),(⟨776774697984,776795556288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165300497216,165398537984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194761437824,-194625412608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2452_ok : ecellOkT e2452 = true := by decide +kernel
theorem e2452_pos {a z : ℝ} (ha1 : ((664491/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1329831/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2452 e2452_ok ha1 ha2 hz1 hz2 hz

-- box ['1329831/8192000', '33267/204800', '3997/4000', '1599/1600']  interval_lower 60955493/274877906944
noncomputable def e2453 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523219,0,true,165398537920,165398537984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732333,0,false,-194761437824,-194761437760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474072,0,true,165496569856,165496569920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781480,0,false,-194897479808,-194897479744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277864658047,0,true,165283362496,165283362560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921158597505,0,false,-194601642304,-194601642240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278000848544,0,true,165400538496,165400538560⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921022407008,0,false,-194764213760,-194764213696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568489538,0,true,56860288,56860352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454766014,0,false,-56863296,-56863232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099579907892,0,true,68277952,68278016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099443347660,0,false,-68282240,-68282176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623535,0,false,-4288,-4224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624836,0,false,-2944,-2880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277931586437,0,true,165340948096,165340948160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921091669115,0,false,-194681532160,-194681532096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278056670112,0,true,165448562816,165448562880⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920966585440,0,false,-194830855296,-194830855232⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070518453590,0,false,-29382292480,-29382292416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070559062979,0,false,-29340584000,-29340583936⟩
    { al := (1329831/8192000), au := (33267/204800), zl := (3997/4000), zu := (1599/1600),
      A := ⟨178486895443,178600846296⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165283362496,165283362560⟩ : DyadicInterval 40),(⟨-194601642304,-194601642240⟩ : DyadicInterval 40),(⟨747593845712,747593865042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165400538496,165400538560⟩ : DyadicInterval 40),(⟨-194764213760,-194764213696⟩ : DyadicInterval 40),(⟨747571548544,747571567874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨56861762,68280116⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56860288,56860352⟩ : DyadicInterval 40),(⟨-56863296,-56863232⟩ : DyadicInterval 40),(⟨762123382115,762123401444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨68277952,68278016⟩ : DyadicInterval 40),(⟨-68282240,-68282176⟩ : DyadicInterval 40),(⟨762123381455,762123400784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4288,-2880⟩ : DyadicInterval 40),(⟨762123385056,762123405024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178419958661,178545042336⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165340948096,165340948160⟩ : DyadicInterval 40),(⟨-194681532160,-194681532096⟩ : DyadicInterval 40),(⟨747582890348,747582909678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165448562816,165448562880⟩ : DyadicInterval 40),(⟨-194830855296,-194830855232⟩ : DyadicInterval 40),(⟨747562404423,747562423752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29382292480,-29340583936⟩ : DyadicInterval 40),(⟨776793675584,776814549120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165398537920,165496569920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194897479808,-194761437760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2453_ok : ecellOkT e2453 = true := by decide +kernel
theorem e2453_pos {a z : ℝ} (ha1 : ((1329831/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((33267/204800 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2453 e2453_ok ha1 ha2 hz1 hz2 hz

-- box ['664491/4096000', '1329831/8192000', '1599/1600', '1999/2000']  interval_lower 242387215/1099511627776
noncomputable def e2454 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277884572368,0,true,165300497216,165300497280⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921138683184,0,false,-194625412672,-194625412608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523220,0,true,165398537920,165398537984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732332,0,false,-194761437824,-194761437760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277773089277,0,true,165204571264,165204571328⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921250166275,0,false,-194492349568,-194492349504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277909279773,0,true,165321755648,165321755712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921113975779,0,false,-194654904896,-194654904832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557087070,0,true,45458304,45458368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466168482,0,false,-45460288,-45460224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568490332,0,true,56861056,56861120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454765220,0,false,-56864064,-56864000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624835,0,false,-2944,-2880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625897,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277828826482,0,true,165252531520,165252531584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921194429070,0,false,-194558873920,-194558873856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277953910180,0,true,165360154944,165360155008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921069345372,0,false,-194708180416,-194708180352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070551817488,0,false,-29348025472,-29348025408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070592403504,0,false,-29306342336,-29306342272⟩
    { al := (664491/4096000), au := (1329831/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨178372944592,178486895444⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165300497216,165300497280⟩ : DyadicInterval 40),(⟨-194625412672,-194625412608⟩ : DyadicInterval 40),(⟨747590586422,747590605752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165204571264,165204571328⟩ : DyadicInterval 40),(⟨-194492349568,-194492349504⟩ : DyadicInterval 40),(⟨747608827633,747608846963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165321755648,165321755712⟩ : DyadicInterval 40),(⟨-194654904896,-194654904832⟩ : DyadicInterval 40),(⟨747586542135,747586561464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45459294,56862556⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45458304,45458368⟩ : DyadicInterval 40),(⟨-45460288,-45460224⟩ : DyadicInterval 40),(⟨762123382664,762123401993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56861056,56861120⟩ : DyadicInterval 40),(⟨-56864064,-56864000⟩ : DyadicInterval 40),(⟨762123382115,762123401444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2944,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178317198706,178442282404⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165252531520,165252531584⟩ : DyadicInterval 40),(⟨-194558873920,-194558873856⟩ : DyadicInterval 40),(⟨747599709204,747599728534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165360154944,165360155008⟩ : DyadicInterval 40),(⟨-194708180416,-194708180352⟩ : DyadicInterval 40),(⟨747579235260,747579254589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29348025472,-29306342272⟩ : DyadicInterval 40),(⟨776776554752,776797415616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165300497216,165398537984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194761437824,-194625412608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2454_ok : ecellOkT e2454 = true := by decide +kernel
theorem e2454_pos {a z : ℝ} (ha1 : ((664491/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1329831/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2454 e2454_ok ha1 ha2 hz1 hz2 hz

-- box ['1329831/8192000', '33267/204800', '1599/1600', '1999/2000']  interval_lower 60910585/274877906944
noncomputable def e2455 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277998523219,0,true,165398537920,165398537984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921024732333,0,false,-194761437824,-194761437760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1278112474072,0,true,165496569856,165496569920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨920910781480,0,false,-194897479808,-194897479744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277886968909,0,true,165302559232,165302559296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921136286643,0,false,-194628273280,-194628273216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1278023173649,0,true,165419745408,165419745472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921000081903,0,false,-194790865664,-194790865600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099557117245,0,true,45488512,45488576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466138307,0,false,-45490432,-45490368⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568528055,0,true,56898752,56898816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454727497,0,false,-56901760,-56901696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624831,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625894,0,false,-1920,-1856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277942741721,0,true,165350545856,165350545920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921080513831,0,false,-194694848320,-194694848256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1278067832543,0,true,165458165824,165458165888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨920955423009,0,false,-194844181824,-194844181760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070514828237,0,false,-29386016000,-29386015936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070555442485,0,false,-29344302400,-29344302336⟩
    { al := (1329831/8192000), au := (33267/204800), zl := (1599/1600), zu := (1999/2000),
      A := ⟨178486895443,178600846296⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165398537920,165398537984⟩ : DyadicInterval 40),(⟨-194761437824,-194761437760⟩ : DyadicInterval 40),(⟨747571929408,747571948737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165496569856,165496569920⟩ : DyadicInterval 40),(⟨-194897479808,-194897479744⟩ : DyadicInterval 40),(⟨747553260280,747553279609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165302559232,165302559296⟩ : DyadicInterval 40),(⟨-194628273280,-194628273216⟩ : DyadicInterval 40),(⟨747590194162,747590213491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165419745408,165419745472⟩ : DyadicInterval 40),(⟨-194790865664,-194790865600⟩ : DyadicInterval 40),(⟨747567891835,747567911165⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨45489469,56900279⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45488512,45488576⟩ : DyadicInterval 40),(⟨-45490432,-45490368⟩ : DyadicInterval 40),(⟨762123382629,762123401959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨56898752,56898816⟩ : DyadicInterval 40),(⟨-56901760,-56901696⟩ : DyadicInterval 40),(⟨762123382111,762123401440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-1856⟩ : DyadicInterval 40),(⟨762123384544,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨178431113945,178556204767⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165350545856,165350545920⟩ : DyadicInterval 40),(⟨-194694848320,-194694848256⟩ : DyadicInterval 40),(⟨747581063953,747581083283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨165458165824,165458165888⟩ : DyadicInterval 40),(⟨-194844181824,-194844181760⟩ : DyadicInterval 40),(⟨747560575542,747560594871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29386016000,-29344302336⟩ : DyadicInterval 40),(⟨776795534784,776816410880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨165398537920,165496569920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194897479808,-194761437760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2455_ok : ecellOkT e2455 = true := by decide +kernel
theorem e2455_pos {a z : ℝ} (ha1 : ((1329831/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((33267/204800 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2455 e2455_ok ha1 ha2 hz1 hz2 hz

-- box ['82743/512000', '1324737/8192000', '1999/2000', '7997/8000']  interval_lower 117370443/549755813888
noncomputable def e2456 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867262,0,true,164712069376,164712069440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388290,0,false,-193809614912,-193809614848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818114,0,true,164810162560,164810162624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437438,0,false,-193945539200,-193945539136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277112022642,0,true,164635582464,164635582528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921911232910,0,false,-193703649856,-193703649792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277248141918,0,true,164752766208,164752766272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921775113634,0,false,-193866003584,-193866003520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545586509,0,true,33958208,33958272⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477669043,0,false,-33959296,-33959232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556936961,0,true,45308224,45308288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466318591,0,false,-45310144,-45310080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625908,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626728,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277156440502,0,true,164673822784,164673822848⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921866815050,0,false,-193756625792,-193756625728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277281488604,0,true,164781472128,164781472192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921741766948,0,false,-193905780928,-193905780864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070769663961,0,false,-29124308736,-29124308672⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070810085482,0,false,-29082803008,-29082802944⟩
    { al := (82743/512000), au := (1324737/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨177689239486,177803190338⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164635582464,164635582528⟩ : DyadicInterval 40),(⟨-193703649856,-193703649792⟩ : DyadicInterval 40),(⟨747716755071,747716774401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164752766208,164752766272⟩ : DyadicInterval 40),(⟨-193866003584,-193866003520⟩ : DyadicInterval 40),(⟨747694565233,747694584563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33958733,45309185⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33958208,33958272⟩ : DyadicInterval 40),(⟨-33959296,-33959232⟩ : DyadicInterval 40),(⟨762123383047,762123402376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45308224,45308288⟩ : DyadicInterval 40),(⟨-45310144,-45310080⟩ : DyadicInterval 40),(⟨762123382644,762123401973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177644812726,177769860828⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164673822784,164673822848⟩ : DyadicInterval 40),(⟨-193756625792,-193756625728⟩ : DyadicInterval 40),(⟨747709516050,747709535380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164781472128,164781472192⟩ : DyadicInterval 40),(⟨-193905780928,-193905780864⟩ : DyadicInterval 40),(⟨747689126524,747689145853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29124308736,-29082802944⟩ : DyadicInterval 40),(⟨776664785088,776685557248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164712069376,164810162624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193945539200,-193809614848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2456_ok : ecellOkT e2456 = true := by decide +kernel
theorem e2456_pos {a z : ℝ} (ha1 : ((82743/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1324737/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2456 e2456_ok ha1 ha2 hz1 hz2 hz

-- box ['1324737/8192000', '662793/4096000', '1999/2000', '7997/8000']  interval_lower 235978031/1099511627776
noncomputable def e2457 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818113,0,true,164810162560,164810162624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437439,0,false,-193945539200,-193945539136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768965,0,true,164908246976,164908247040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486587,0,false,-194081480256,-194081480192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277225916517,0,true,164733633472,164733633536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921797339035,0,false,-193839493056,-193839492992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277362050038,0,true,164850819008,164850819072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921661205514,0,false,-194001883840,-194001883776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545609131,0,true,33980800,33980864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477646421,0,false,-33981888,-33981824⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099556967126,0,true,45338368,45338432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099466288426,0,false,-45340288,-45340224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625906,0,false,-1920,-1856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626726,0,false,-1088,-1024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277270362866,0,true,164771894848,164771894912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921752892686,0,false,-193892509504,-193892509440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277395418092,0,true,164879540736,164879540800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921627837460,0,false,-194041691584,-194041691520⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070732811747,0,false,-29162150784,-29162150720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070773261485,0,false,-29120614656,-29120614592⟩
    { al := (1324737/8192000), au := (662793/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨177803190337,177917141189⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164733633472,164733633536⟩ : DyadicInterval 40),(⟨-193839493056,-193839492992⟩ : DyadicInterval 40),(⟨747698189541,747698208871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164850819008,164850819072⟩ : DyadicInterval 40),(⟨-194001883840,-194001883776⟩ : DyadicInterval 40),(⟨747675982913,747676002242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33981355,45339350⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33980800,33980864⟩ : DyadicInterval 40),(⟨-33981888,-33981824⟩ : DyadicInterval 40),(⟨762123383045,762123402374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨45338368,45338432⟩ : DyadicInterval 40),(⟨-45340288,-45340224⟩ : DyadicInterval 40),(⟨762123382642,762123401971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1920,-1024⟩ : DyadicInterval 40),(⟨762123384128,762123403840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177758735090,177883790316⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164771894848,164771894912⟩ : DyadicInterval 40),(⟨-193892509504,-193892509440⟩ : DyadicInterval 40),(⟨747690941176,747690960506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164879540736,164879540800⟩ : DyadicInterval 40),(⟨-194041691584,-194041691520⟩ : DyadicInterval 40),(⟨747670537179,747670556508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29162150784,-29120614592⟩ : DyadicInterval 40),(⟨776683690912,776704478272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164810162560,164908247040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194081480256,-193945539136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2457_ok : ecellOkT e2457 = true := by decide +kernel
theorem e2457_pos {a z : ℝ} (ha1 : ((1324737/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((662793/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2457 e2457_ok ha1 ha2 hz1 hz2 hz

-- box ['82743/512000', '1324737/8192000', '7997/8000', '3999/4000']  interval_lower 117281953/549755813888
noncomputable def e2458 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277200867262,0,true,164712069376,164712069440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921822388290,0,false,-193809614912,-193809614848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818114,0,true,164810162560,164810162624⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437438,0,false,-193945539200,-193945539136⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277134233797,0,true,164654704704,164654704768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921889021755,0,false,-193730140160,-193730140096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277270367317,0,true,164771898688,164771898752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921752888235,0,false,-193892514816,-193892514752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534266900,0,true,22638848,22638912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488988652,0,false,-22639360,-22639296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545609811,0,true,33981504,33981568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477645741,0,false,-33982592,-33982528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626725,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627310,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277167545988,0,true,164683383488,164683383552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921855709564,0,false,-193769871360,-193769871296⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277292601240,0,true,164791038080,164791038144⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921730654312,0,false,-193919036864,-193919036800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070766070450,0,false,-29127998720,-29127998656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070806496809,0,false,-29086487872,-29086487808⟩
    { al := (82743/512000), au := (1324737/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨177689239486,177803190338⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164712069376,164712069440⟩ : DyadicInterval 40),(⟨-193809614912,-193809614848⟩ : DyadicInterval 40),(⟨747702273777,747702293107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164654704704,164654704768⟩ : DyadicInterval 40),(⟨-193730140160,-193730140096⟩ : DyadicInterval 40),(⟨747713135430,747713154760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164771898688,164771898752⟩ : DyadicInterval 40),(⟨-193892514816,-193892514752⟩ : DyadicInterval 40),(⟨747690940446,747690959776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22639124,33982035⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22638848,22638912⟩ : DyadicInterval 40),(⟨-22639360,-22639296⟩ : DyadicInterval 40),(⟨762123383341,762123402670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33981504,33981568⟩ : DyadicInterval 40),(⟨-33982592,-33982528⟩ : DyadicInterval 40),(⟨762123383045,762123402374⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177655918212,177780973464⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164683383488,164683383552⟩ : DyadicInterval 40),(⟨-193769871360,-193769871296⟩ : DyadicInterval 40),(⟨747707705855,747707725184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164791038080,164791038144⟩ : DyadicInterval 40),(⟨-193919036864,-193919036800⟩ : DyadicInterval 40),(⟨747687313865,747687333195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29127998720,-29086487808⟩ : DyadicInterval 40),(⟨776666627520,776687402240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164712069376,164810162624⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-193945539200,-193809614848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2458_ok : ecellOkT e2458 = true := by decide +kernel
theorem e2458_pos {a z : ℝ} (ha1 : ((82743/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1324737/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2458 e2458_ok ha1 ha2 hz1 hz2 hz

-- box ['1324737/8192000', '662793/4096000', '7997/8000', '3999/4000']  interval_lower 235800823/1099511627776
noncomputable def e2459 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1277314818113,0,true,164810162560,164810162624⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨921708437439,0,false,-193945539200,-193945539136⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1277428768965,0,true,164908246976,164908247040⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨921594486587,0,false,-194081480256,-194081480192⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1277248141916,0,true,164752766208,164752766272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨921775113636,0,false,-193866003584,-193866003520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1277384289680,0,true,164869961984,164869962048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨921638965872,0,false,-194028415360,-194028415296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099534281982,0,true,22653952,22654016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488973570,0,false,-22654464,-22654400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099545632436,0,true,34004096,34004160⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099477623116,0,false,-34005248,-34005184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626724,0,false,-1088,-1024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627310,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1277281475471,0,true,164781460864,164781460928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨921741780081,0,false,-193905765248,-193905765184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1277406537844,0,true,164889112000,164889112064⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨921616717708,0,false,-194054957632,-194054957568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1070729213630,0,false,-29165845632,-29165845568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1070769668209,0,false,-29124304384,-29124304320⟩
    { al := (1324737/8192000), au := (662793/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨177803190337,177917141189⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164810162560,164810162624⟩ : DyadicInterval 40),(⟨-193945539200,-193945539136⟩ : DyadicInterval 40),(⟨747683689542,747683708872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164908246976,164908247040⟩ : DyadicInterval 40),(⟨-194081480256,-194081480192⟩ : DyadicInterval 40),(⟨747665093174,747665112504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164752766208,164752766272⟩ : DyadicInterval 40),(⟨-193866003584,-193866003520⟩ : DyadicInterval 40),(⟨747694565234,747694584563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164869961984,164869962048⟩ : DyadicInterval 40),(⟨-194028415360,-194028415296⟩ : DyadicInterval 40),(⟨747672353479,747672372808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22654206,34004660⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22653952,22654016⟩ : DyadicInterval 40),(⟨-22654464,-22654400⟩ : DyadicInterval 40),(⟨762123383341,762123402670⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨34004096,34004160⟩ : DyadicInterval 40),(⟨-34005248,-34005184⟩ : DyadicInterval 40),(⟨762123383076,762123402405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1088,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨177769847695,177894910068⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164781460864,164781460928⟩ : DyadicInterval 40),(⟨-193905765248,-193905765184⟩ : DyadicInterval 40),(⟨747689128636,747689147965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨164889112000,164889112064⟩ : DyadicInterval 40),(⟨-194054957632,-194054957568⟩ : DyadicInterval 40),(⟨747668722147,747668741476⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-29165845632,-29124304320⟩ : DyadicInterval 40),(⟨776685535776,776706325696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨164810162560,164908247040⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-194081480256,-193945539136⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2459_ok : ecellOkT e2459 = true := by decide +kernel
theorem e2459_pos {a z : ℝ} (ha1 : ((1324737/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((662793/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2459 e2459_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B040

end


