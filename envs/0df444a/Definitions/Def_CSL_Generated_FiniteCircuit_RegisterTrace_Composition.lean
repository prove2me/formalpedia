-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Composition
-- name    : CSL_Generated_FiniteCircuit_RegisterTrace_Composition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:07:23.605735+00:00
-- url     : https://prove2.me/theorems/e018f9f6-76ff-4176-8240-8c345f306cf2
-- title:
--   Coded sorting library: Generated / FiniteCircuit / RegisterTrace / Composition
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.RegisterTrace.Composition` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.RegisterTrace.Composition

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_GatesChunks
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps0000To0255
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps0256To0511
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps0512To0767
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps0768To1023
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps1024To1279
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps1280To1535
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps1536To1791
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps1792To2047
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps2048To2303
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps2304To2559
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps2560To2815
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps2816To3071
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps3072To3327
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps3328To3583
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps3584To3839
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps3840To4095
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps4096To4351
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps4352To4607
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps4608To4863
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps4864To5119
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps5120To5375
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps5376To5582

namespace CSL.Construction.FiniteSSA.Verified
open CSL.Construction.FiniteCertificate CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem Block000.wellFormed : ∀ e ∈ Block000.steps, WellFormed e :=
  wellFormed_of_checks Block000.steps Block000.checkedBounds Block000.checkedNodup Block000.checkedNoSelf

theorem Block000.program : gatesChunk0.toList = Block000.steps.map SSACertificate.Step.gate := by rfl

theorem Block001.wellFormed : ∀ e ∈ Block001.steps, WellFormed e :=
  wellFormed_of_checks Block001.steps Block001.checkedBounds Block001.checkedNodup Block001.checkedNoSelf

theorem Block001.program : gatesChunk1.toList = Block001.steps.map SSACertificate.Step.gate := by rfl

theorem Block002.wellFormed : ∀ e ∈ Block002.steps, WellFormed e :=
  wellFormed_of_checks Block002.steps Block002.checkedBounds Block002.checkedNodup Block002.checkedNoSelf

theorem Block002.program : gatesChunk2.toList = Block002.steps.map SSACertificate.Step.gate := by rfl

theorem Block003.wellFormed : ∀ e ∈ Block003.steps, WellFormed e :=
  wellFormed_of_checks Block003.steps Block003.checkedBounds Block003.checkedNodup Block003.checkedNoSelf

theorem Block003.program : gatesChunk3.toList = Block003.steps.map SSACertificate.Step.gate := by rfl

theorem Block004.wellFormed : ∀ e ∈ Block004.steps, WellFormed e :=
  wellFormed_of_checks Block004.steps Block004.checkedBounds Block004.checkedNodup Block004.checkedNoSelf

theorem Block004.program : gatesChunk4.toList = Block004.steps.map SSACertificate.Step.gate := by rfl

theorem Block005.wellFormed : ∀ e ∈ Block005.steps, WellFormed e :=
  wellFormed_of_checks Block005.steps Block005.checkedBounds Block005.checkedNodup Block005.checkedNoSelf

theorem Block005.program : gatesChunk5.toList = Block005.steps.map SSACertificate.Step.gate := by rfl

theorem Block006.wellFormed : ∀ e ∈ Block006.steps, WellFormed e :=
  wellFormed_of_checks Block006.steps Block006.checkedBounds Block006.checkedNodup Block006.checkedNoSelf

theorem Block006.program : gatesChunk6.toList = Block006.steps.map SSACertificate.Step.gate := by rfl

theorem Block007.wellFormed : ∀ e ∈ Block007.steps, WellFormed e :=
  wellFormed_of_checks Block007.steps Block007.checkedBounds Block007.checkedNodup Block007.checkedNoSelf

theorem Block007.program : gatesChunk7.toList = Block007.steps.map SSACertificate.Step.gate := by rfl

theorem Block008.wellFormed : ∀ e ∈ Block008.steps, WellFormed e :=
  wellFormed_of_checks Block008.steps Block008.checkedBounds Block008.checkedNodup Block008.checkedNoSelf

theorem Block008.program : gatesChunk8.toList = Block008.steps.map SSACertificate.Step.gate := by rfl

theorem Block009.wellFormed : ∀ e ∈ Block009.steps, WellFormed e :=
  wellFormed_of_checks Block009.steps Block009.checkedBounds Block009.checkedNodup Block009.checkedNoSelf

theorem Block009.program : gatesChunk9.toList = Block009.steps.map SSACertificate.Step.gate := by rfl

theorem Block010.wellFormed : ∀ e ∈ Block010.steps, WellFormed e :=
  wellFormed_of_checks Block010.steps Block010.checkedBounds Block010.checkedNodup Block010.checkedNoSelf

theorem Block010.program : gatesChunk10.toList = Block010.steps.map SSACertificate.Step.gate := by rfl

theorem Block011.wellFormed : ∀ e ∈ Block011.steps, WellFormed e :=
  wellFormed_of_checks Block011.steps Block011.checkedBounds Block011.checkedNodup Block011.checkedNoSelf

theorem Block011.program : gatesChunk11.toList = Block011.steps.map SSACertificate.Step.gate := by rfl

theorem Block012.wellFormed : ∀ e ∈ Block012.steps, WellFormed e :=
  wellFormed_of_checks Block012.steps Block012.checkedBounds Block012.checkedNodup Block012.checkedNoSelf

theorem Block012.program : gatesChunk12.toList = Block012.steps.map SSACertificate.Step.gate := by rfl

theorem Block013.wellFormed : ∀ e ∈ Block013.steps, WellFormed e :=
  wellFormed_of_checks Block013.steps Block013.checkedBounds Block013.checkedNodup Block013.checkedNoSelf

theorem Block013.program : gatesChunk13.toList = Block013.steps.map SSACertificate.Step.gate := by rfl

theorem Block014.wellFormed : ∀ e ∈ Block014.steps, WellFormed e :=
  wellFormed_of_checks Block014.steps Block014.checkedBounds Block014.checkedNodup Block014.checkedNoSelf

theorem Block014.program : gatesChunk14.toList = Block014.steps.map SSACertificate.Step.gate := by rfl

theorem Block015.wellFormed : ∀ e ∈ Block015.steps, WellFormed e :=
  wellFormed_of_checks Block015.steps Block015.checkedBounds Block015.checkedNodup Block015.checkedNoSelf

theorem Block015.program : gatesChunk15.toList = Block015.steps.map SSACertificate.Step.gate := by rfl

theorem Block016.wellFormed : ∀ e ∈ Block016.steps, WellFormed e :=
  wellFormed_of_checks Block016.steps Block016.checkedBounds Block016.checkedNodup Block016.checkedNoSelf

theorem Block016.program : gatesChunk16.toList = Block016.steps.map SSACertificate.Step.gate := by rfl

theorem Block017.wellFormed : ∀ e ∈ Block017.steps, WellFormed e :=
  wellFormed_of_checks Block017.steps Block017.checkedBounds Block017.checkedNodup Block017.checkedNoSelf

theorem Block017.program : gatesChunk17.toList = Block017.steps.map SSACertificate.Step.gate := by rfl

theorem Block018.wellFormed : ∀ e ∈ Block018.steps, WellFormed e :=
  wellFormed_of_checks Block018.steps Block018.checkedBounds Block018.checkedNodup Block018.checkedNoSelf

theorem Block018.program : gatesChunk18.toList = Block018.steps.map SSACertificate.Step.gate := by rfl

theorem Block019.wellFormed : ∀ e ∈ Block019.steps, WellFormed e :=
  wellFormed_of_checks Block019.steps Block019.checkedBounds Block019.checkedNodup Block019.checkedNoSelf

theorem Block019.program : gatesChunk19.toList = Block019.steps.map SSACertificate.Step.gate := by rfl

theorem Block020.wellFormed : ∀ e ∈ Block020.steps, WellFormed e :=
  wellFormed_of_checks Block020.steps Block020.checkedBounds Block020.checkedNodup Block020.checkedNoSelf

theorem Block020.program : gatesChunk20.toList = Block020.steps.map SSACertificate.Step.gate := by rfl

theorem Block021.wellFormed : ∀ e ∈ Block021.steps, WellFormed e :=
  wellFormed_of_checks Block021.steps Block021.checkedBounds Block021.checkedNodup Block021.checkedNoSelf

theorem Block021.program : gatesChunk21.toList = Block021.steps.map SSACertificate.Step.gate := by rfl

theorem Block022.wellFormed : ∀ e ∈ Block022.steps, WellFormed e :=
  wellFormed_of_checks Block022.steps Block022.checkedBounds Block022.checkedNodup Block022.checkedNoSelf

theorem Block022.program : gatesChunk22.toList = Block022.steps.map SSACertificate.Step.gate := by rfl

theorem Block023.wellFormed : ∀ e ∈ Block023.steps, WellFormed e :=
  wellFormed_of_checks Block023.steps Block023.checkedBounds Block023.checkedNodup Block023.checkedNoSelf

theorem Block023.program : gatesChunk23.toList = Block023.steps.map SSACertificate.Step.gate := by rfl

theorem Block024.wellFormed : ∀ e ∈ Block024.steps, WellFormed e :=
  wellFormed_of_checks Block024.steps Block024.checkedBounds Block024.checkedNodup Block024.checkedNoSelf

theorem Block024.program : gatesChunk24.toList = Block024.steps.map SSACertificate.Step.gate := by rfl

theorem Block025.wellFormed : ∀ e ∈ Block025.steps, WellFormed e :=
  wellFormed_of_checks Block025.steps Block025.checkedBounds Block025.checkedNodup Block025.checkedNoSelf

theorem Block025.program : gatesChunk25.toList = Block025.steps.map SSACertificate.Step.gate := by rfl

theorem Block026.wellFormed : ∀ e ∈ Block026.steps, WellFormed e :=
  wellFormed_of_checks Block026.steps Block026.checkedBounds Block026.checkedNodup Block026.checkedNoSelf

theorem Block026.program : gatesChunk26.toList = Block026.steps.map SSACertificate.Step.gate := by rfl

theorem Block027.wellFormed : ∀ e ∈ Block027.steps, WellFormed e :=
  wellFormed_of_checks Block027.steps Block027.checkedBounds Block027.checkedNodup Block027.checkedNoSelf

theorem Block027.program : gatesChunk27.toList = Block027.steps.map SSACertificate.Step.gate := by rfl

theorem Block028.wellFormed : ∀ e ∈ Block028.steps, WellFormed e :=
  wellFormed_of_checks Block028.steps Block028.checkedBounds Block028.checkedNodup Block028.checkedNoSelf

theorem Block028.program : gatesChunk28.toList = Block028.steps.map SSACertificate.Step.gate := by rfl

theorem Block029.wellFormed : ∀ e ∈ Block029.steps, WellFormed e :=
  wellFormed_of_checks Block029.steps Block029.checkedBounds Block029.checkedNodup Block029.checkedNoSelf

theorem Block029.program : gatesChunk29.toList = Block029.steps.map SSACertificate.Step.gate := by rfl

theorem Block030.wellFormed : ∀ e ∈ Block030.steps, WellFormed e :=
  wellFormed_of_checks Block030.steps Block030.checkedBounds Block030.checkedNodup Block030.checkedNoSelf

theorem Block030.program : gatesChunk30.toList = Block030.steps.map SSACertificate.Step.gate := by rfl

theorem Block031.wellFormed : ∀ e ∈ Block031.steps, WellFormed e :=
  wellFormed_of_checks Block031.steps Block031.checkedBounds Block031.checkedNodup Block031.checkedNoSelf

theorem Block031.program : gatesChunk31.toList = Block031.steps.map SSACertificate.Step.gate := by rfl

theorem Block032.wellFormed : ∀ e ∈ Block032.steps, WellFormed e :=
  wellFormed_of_checks Block032.steps Block032.checkedBounds Block032.checkedNodup Block032.checkedNoSelf

theorem Block032.program : gatesChunk32.toList = Block032.steps.map SSACertificate.Step.gate := by rfl

theorem Block033.wellFormed : ∀ e ∈ Block033.steps, WellFormed e :=
  wellFormed_of_checks Block033.steps Block033.checkedBounds Block033.checkedNodup Block033.checkedNoSelf

theorem Block033.program : gatesChunk33.toList = Block033.steps.map SSACertificate.Step.gate := by rfl

theorem Block034.wellFormed : ∀ e ∈ Block034.steps, WellFormed e :=
  wellFormed_of_checks Block034.steps Block034.checkedBounds Block034.checkedNodup Block034.checkedNoSelf

theorem Block034.program : gatesChunk34.toList = Block034.steps.map SSACertificate.Step.gate := by rfl

theorem Block035.wellFormed : ∀ e ∈ Block035.steps, WellFormed e :=
  wellFormed_of_checks Block035.steps Block035.checkedBounds Block035.checkedNodup Block035.checkedNoSelf

theorem Block035.program : gatesChunk35.toList = Block035.steps.map SSACertificate.Step.gate := by rfl

theorem Block036.wellFormed : ∀ e ∈ Block036.steps, WellFormed e :=
  wellFormed_of_checks Block036.steps Block036.checkedBounds Block036.checkedNodup Block036.checkedNoSelf

theorem Block036.program : gatesChunk36.toList = Block036.steps.map SSACertificate.Step.gate := by rfl

theorem Block037.wellFormed : ∀ e ∈ Block037.steps, WellFormed e :=
  wellFormed_of_checks Block037.steps Block037.checkedBounds Block037.checkedNodup Block037.checkedNoSelf

theorem Block037.program : gatesChunk37.toList = Block037.steps.map SSACertificate.Step.gate := by rfl

theorem Block038.wellFormed : ∀ e ∈ Block038.steps, WellFormed e :=
  wellFormed_of_checks Block038.steps Block038.checkedBounds Block038.checkedNodup Block038.checkedNoSelf

theorem Block038.program : gatesChunk38.toList = Block038.steps.map SSACertificate.Step.gate := by rfl

theorem Block039.wellFormed : ∀ e ∈ Block039.steps, WellFormed e :=
  wellFormed_of_checks Block039.steps Block039.checkedBounds Block039.checkedNodup Block039.checkedNoSelf

theorem Block039.program : gatesChunk39.toList = Block039.steps.map SSACertificate.Step.gate := by rfl

theorem Block040.wellFormed : ∀ e ∈ Block040.steps, WellFormed e :=
  wellFormed_of_checks Block040.steps Block040.checkedBounds Block040.checkedNodup Block040.checkedNoSelf

theorem Block040.program : gatesChunk40.toList = Block040.steps.map SSACertificate.Step.gate := by rfl

theorem Block041.wellFormed : ∀ e ∈ Block041.steps, WellFormed e :=
  wellFormed_of_checks Block041.steps Block041.checkedBounds Block041.checkedNodup Block041.checkedNoSelf

theorem Block041.program : gatesChunk41.toList = Block041.steps.map SSACertificate.Step.gate := by rfl

theorem Block042.wellFormed : ∀ e ∈ Block042.steps, WellFormed e :=
  wellFormed_of_checks Block042.steps Block042.checkedBounds Block042.checkedNodup Block042.checkedNoSelf

theorem Block042.program : gatesChunk42.toList = Block042.steps.map SSACertificate.Step.gate := by rfl

theorem Block043.wellFormed : ∀ e ∈ Block043.steps, WellFormed e :=
  wellFormed_of_checks Block043.steps Block043.checkedBounds Block043.checkedNodup Block043.checkedNoSelf

theorem Block043.program : gatesChunk43.toList = Block043.steps.map SSACertificate.Step.gate := by rfl

theorem Block044.wellFormed : ∀ e ∈ Block044.steps, WellFormed e :=
  wellFormed_of_checks Block044.steps Block044.checkedBounds Block044.checkedNodup Block044.checkedNoSelf

theorem Block044.program : gatesChunk44.toList = Block044.steps.map SSACertificate.Step.gate := by rfl

theorem Block045.wellFormed : ∀ e ∈ Block045.steps, WellFormed e :=
  wellFormed_of_checks Block045.steps Block045.checkedBounds Block045.checkedNodup Block045.checkedNoSelf

theorem Block045.program : gatesChunk45.toList = Block045.steps.map SSACertificate.Step.gate := by rfl

theorem Block046.wellFormed : ∀ e ∈ Block046.steps, WellFormed e :=
  wellFormed_of_checks Block046.steps Block046.checkedBounds Block046.checkedNodup Block046.checkedNoSelf

theorem Block046.program : gatesChunk46.toList = Block046.steps.map SSACertificate.Step.gate := by rfl

theorem Block047.wellFormed : ∀ e ∈ Block047.steps, WellFormed e :=
  wellFormed_of_checks Block047.steps Block047.checkedBounds Block047.checkedNodup Block047.checkedNoSelf

theorem Block047.program : gatesChunk47.toList = Block047.steps.map SSACertificate.Step.gate := by rfl

theorem Block048.wellFormed : ∀ e ∈ Block048.steps, WellFormed e :=
  wellFormed_of_checks Block048.steps Block048.checkedBounds Block048.checkedNodup Block048.checkedNoSelf

theorem Block048.program : gatesChunk48.toList = Block048.steps.map SSACertificate.Step.gate := by rfl

theorem Block049.wellFormed : ∀ e ∈ Block049.steps, WellFormed e :=
  wellFormed_of_checks Block049.steps Block049.checkedBounds Block049.checkedNodup Block049.checkedNoSelf

theorem Block049.program : gatesChunk49.toList = Block049.steps.map SSACertificate.Step.gate := by rfl

theorem Block050.wellFormed : ∀ e ∈ Block050.steps, WellFormed e :=
  wellFormed_of_checks Block050.steps Block050.checkedBounds Block050.checkedNodup Block050.checkedNoSelf

theorem Block050.program : gatesChunk50.toList = Block050.steps.map SSACertificate.Step.gate := by rfl

theorem Block051.wellFormed : ∀ e ∈ Block051.steps, WellFormed e :=
  wellFormed_of_checks Block051.steps Block051.checkedBounds Block051.checkedNodup Block051.checkedNoSelf

theorem Block051.program : gatesChunk51.toList = Block051.steps.map SSACertificate.Step.gate := by rfl

theorem Block052.wellFormed : ∀ e ∈ Block052.steps, WellFormed e :=
  wellFormed_of_checks Block052.steps Block052.checkedBounds Block052.checkedNodup Block052.checkedNoSelf

theorem Block052.program : gatesChunk52.toList = Block052.steps.map SSACertificate.Step.gate := by rfl

theorem Block053.wellFormed : ∀ e ∈ Block053.steps, WellFormed e :=
  wellFormed_of_checks Block053.steps Block053.checkedBounds Block053.checkedNodup Block053.checkedNoSelf

theorem Block053.program : gatesChunk53.toList = Block053.steps.map SSACertificate.Step.gate := by rfl

theorem Block054.wellFormed : ∀ e ∈ Block054.steps, WellFormed e :=
  wellFormed_of_checks Block054.steps Block054.checkedBounds Block054.checkedNodup Block054.checkedNoSelf

theorem Block054.program : gatesChunk54.toList = Block054.steps.map SSACertificate.Step.gate := by rfl

theorem Block055.wellFormed : ∀ e ∈ Block055.steps, WellFormed e :=
  wellFormed_of_checks Block055.steps Block055.checkedBounds Block055.checkedNodup Block055.checkedNoSelf

theorem Block055.program : gatesChunk55.toList = Block055.steps.map SSACertificate.Step.gate := by rfl

theorem Block056.wellFormed : ∀ e ∈ Block056.steps, WellFormed e :=
  wellFormed_of_checks Block056.steps Block056.checkedBounds Block056.checkedNodup Block056.checkedNoSelf

theorem Block056.program : gatesChunk56.toList = Block056.steps.map SSACertificate.Step.gate := by rfl

theorem Block057.wellFormed : ∀ e ∈ Block057.steps, WellFormed e :=
  wellFormed_of_checks Block057.steps Block057.checkedBounds Block057.checkedNodup Block057.checkedNoSelf

theorem Block057.program : gatesChunk57.toList = Block057.steps.map SSACertificate.Step.gate := by rfl

theorem Block058.wellFormed : ∀ e ∈ Block058.steps, WellFormed e :=
  wellFormed_of_checks Block058.steps Block058.checkedBounds Block058.checkedNodup Block058.checkedNoSelf

theorem Block058.program : gatesChunk58.toList = Block058.steps.map SSACertificate.Step.gate := by rfl

theorem Block059.wellFormed : ∀ e ∈ Block059.steps, WellFormed e :=
  wellFormed_of_checks Block059.steps Block059.checkedBounds Block059.checkedNodup Block059.checkedNoSelf

theorem Block059.program : gatesChunk59.toList = Block059.steps.map SSACertificate.Step.gate := by rfl

theorem Block060.wellFormed : ∀ e ∈ Block060.steps, WellFormed e :=
  wellFormed_of_checks Block060.steps Block060.checkedBounds Block060.checkedNodup Block060.checkedNoSelf

theorem Block060.program : gatesChunk60.toList = Block060.steps.map SSACertificate.Step.gate := by rfl

theorem Block061.wellFormed : ∀ e ∈ Block061.steps, WellFormed e :=
  wellFormed_of_checks Block061.steps Block061.checkedBounds Block061.checkedNodup Block061.checkedNoSelf

theorem Block061.program : gatesChunk61.toList = Block061.steps.map SSACertificate.Step.gate := by rfl

theorem Block062.wellFormed : ∀ e ∈ Block062.steps, WellFormed e :=
  wellFormed_of_checks Block062.steps Block062.checkedBounds Block062.checkedNodup Block062.checkedNoSelf

theorem Block062.program : gatesChunk62.toList = Block062.steps.map SSACertificate.Step.gate := by rfl

theorem Block063.wellFormed : ∀ e ∈ Block063.steps, WellFormed e :=
  wellFormed_of_checks Block063.steps Block063.checkedBounds Block063.checkedNodup Block063.checkedNoSelf

theorem Block063.program : gatesChunk63.toList = Block063.steps.map SSACertificate.Step.gate := by rfl

theorem Block064.wellFormed : ∀ e ∈ Block064.steps, WellFormed e :=
  wellFormed_of_checks Block064.steps Block064.checkedBounds Block064.checkedNodup Block064.checkedNoSelf

theorem Block064.program : gatesChunk64.toList = Block064.steps.map SSACertificate.Step.gate := by rfl

theorem Block065.wellFormed : ∀ e ∈ Block065.steps, WellFormed e :=
  wellFormed_of_checks Block065.steps Block065.checkedBounds Block065.checkedNodup Block065.checkedNoSelf

theorem Block065.program : gatesChunk65.toList = Block065.steps.map SSACertificate.Step.gate := by rfl

theorem Block066.wellFormed : ∀ e ∈ Block066.steps, WellFormed e :=
  wellFormed_of_checks Block066.steps Block066.checkedBounds Block066.checkedNodup Block066.checkedNoSelf

theorem Block066.program : gatesChunk66.toList = Block066.steps.map SSACertificate.Step.gate := by rfl

theorem Block067.wellFormed : ∀ e ∈ Block067.steps, WellFormed e :=
  wellFormed_of_checks Block067.steps Block067.checkedBounds Block067.checkedNodup Block067.checkedNoSelf

theorem Block067.program : gatesChunk67.toList = Block067.steps.map SSACertificate.Step.gate := by rfl

theorem Block068.wellFormed : ∀ e ∈ Block068.steps, WellFormed e :=
  wellFormed_of_checks Block068.steps Block068.checkedBounds Block068.checkedNodup Block068.checkedNoSelf

theorem Block068.program : gatesChunk68.toList = Block068.steps.map SSACertificate.Step.gate := by rfl

theorem Block069.wellFormed : ∀ e ∈ Block069.steps, WellFormed e :=
  wellFormed_of_checks Block069.steps Block069.checkedBounds Block069.checkedNodup Block069.checkedNoSelf

theorem Block069.program : gatesChunk69.toList = Block069.steps.map SSACertificate.Step.gate := by rfl

theorem Block070.wellFormed : ∀ e ∈ Block070.steps, WellFormed e :=
  wellFormed_of_checks Block070.steps Block070.checkedBounds Block070.checkedNodup Block070.checkedNoSelf

theorem Block070.program : gatesChunk70.toList = Block070.steps.map SSACertificate.Step.gate := by rfl

theorem Block071.wellFormed : ∀ e ∈ Block071.steps, WellFormed e :=
  wellFormed_of_checks Block071.steps Block071.checkedBounds Block071.checkedNodup Block071.checkedNoSelf

theorem Block071.program : gatesChunk71.toList = Block071.steps.map SSACertificate.Step.gate := by rfl

theorem Block072.wellFormed : ∀ e ∈ Block072.steps, WellFormed e :=
  wellFormed_of_checks Block072.steps Block072.checkedBounds Block072.checkedNodup Block072.checkedNoSelf

theorem Block072.program : gatesChunk72.toList = Block072.steps.map SSACertificate.Step.gate := by rfl

theorem Block073.wellFormed : ∀ e ∈ Block073.steps, WellFormed e :=
  wellFormed_of_checks Block073.steps Block073.checkedBounds Block073.checkedNodup Block073.checkedNoSelf

theorem Block073.program : gatesChunk73.toList = Block073.steps.map SSACertificate.Step.gate := by rfl

theorem Block074.wellFormed : ∀ e ∈ Block074.steps, WellFormed e :=
  wellFormed_of_checks Block074.steps Block074.checkedBounds Block074.checkedNodup Block074.checkedNoSelf

theorem Block074.program : gatesChunk74.toList = Block074.steps.map SSACertificate.Step.gate := by rfl

theorem Block075.wellFormed : ∀ e ∈ Block075.steps, WellFormed e :=
  wellFormed_of_checks Block075.steps Block075.checkedBounds Block075.checkedNodup Block075.checkedNoSelf

theorem Block075.program : gatesChunk75.toList = Block075.steps.map SSACertificate.Step.gate := by rfl

theorem Block076.wellFormed : ∀ e ∈ Block076.steps, WellFormed e :=
  wellFormed_of_checks Block076.steps Block076.checkedBounds Block076.checkedNodup Block076.checkedNoSelf

theorem Block076.program : gatesChunk76.toList = Block076.steps.map SSACertificate.Step.gate := by rfl

theorem Block077.wellFormed : ∀ e ∈ Block077.steps, WellFormed e :=
  wellFormed_of_checks Block077.steps Block077.checkedBounds Block077.checkedNodup Block077.checkedNoSelf

theorem Block077.program : gatesChunk77.toList = Block077.steps.map SSACertificate.Step.gate := by rfl

theorem Block078.wellFormed : ∀ e ∈ Block078.steps, WellFormed e :=
  wellFormed_of_checks Block078.steps Block078.checkedBounds Block078.checkedNodup Block078.checkedNoSelf

theorem Block078.program : gatesChunk78.toList = Block078.steps.map SSACertificate.Step.gate := by rfl

theorem Block079.wellFormed : ∀ e ∈ Block079.steps, WellFormed e :=
  wellFormed_of_checks Block079.steps Block079.checkedBounds Block079.checkedNodup Block079.checkedNoSelf

theorem Block079.program : gatesChunk79.toList = Block079.steps.map SSACertificate.Step.gate := by rfl

theorem Block080.wellFormed : ∀ e ∈ Block080.steps, WellFormed e :=
  wellFormed_of_checks Block080.steps Block080.checkedBounds Block080.checkedNodup Block080.checkedNoSelf

theorem Block080.program : gatesChunk80.toList = Block080.steps.map SSACertificate.Step.gate := by rfl

theorem Block081.wellFormed : ∀ e ∈ Block081.steps, WellFormed e :=
  wellFormed_of_checks Block081.steps Block081.checkedBounds Block081.checkedNodup Block081.checkedNoSelf

theorem Block081.program : gatesChunk81.toList = Block081.steps.map SSACertificate.Step.gate := by rfl

theorem Block082.wellFormed : ∀ e ∈ Block082.steps, WellFormed e :=
  wellFormed_of_checks Block082.steps Block082.checkedBounds Block082.checkedNodup Block082.checkedNoSelf

theorem Block082.program : gatesChunk82.toList = Block082.steps.map SSACertificate.Step.gate := by rfl

theorem Block083.wellFormed : ∀ e ∈ Block083.steps, WellFormed e :=
  wellFormed_of_checks Block083.steps Block083.checkedBounds Block083.checkedNodup Block083.checkedNoSelf

theorem Block083.program : gatesChunk83.toList = Block083.steps.map SSACertificate.Step.gate := by rfl

theorem Block084.wellFormed : ∀ e ∈ Block084.steps, WellFormed e :=
  wellFormed_of_checks Block084.steps Block084.checkedBounds Block084.checkedNodup Block084.checkedNoSelf

theorem Block084.program : gatesChunk84.toList = Block084.steps.map SSACertificate.Step.gate := by rfl

theorem Block085.wellFormed : ∀ e ∈ Block085.steps, WellFormed e :=
  wellFormed_of_checks Block085.steps Block085.checkedBounds Block085.checkedNodup Block085.checkedNoSelf

theorem Block085.program : gatesChunk85.toList = Block085.steps.map SSACertificate.Step.gate := by rfl

theorem Block086.wellFormed : ∀ e ∈ Block086.steps, WellFormed e :=
  wellFormed_of_checks Block086.steps Block086.checkedBounds Block086.checkedNodup Block086.checkedNoSelf

theorem Block086.program : gatesChunk86.toList = Block086.steps.map SSACertificate.Step.gate := by rfl

theorem Block087.wellFormed : ∀ e ∈ Block087.steps, WellFormed e :=
  wellFormed_of_checks Block087.steps Block087.checkedBounds Block087.checkedNodup Block087.checkedNoSelf

theorem Block087.program : gatesChunk87.toList = Block087.steps.map SSACertificate.Step.gate := by rfl

theorem Block088.wellFormed : ∀ e ∈ Block088.steps, WellFormed e :=
  wellFormed_of_checks Block088.steps Block088.checkedBounds Block088.checkedNodup Block088.checkedNoSelf

theorem Block088.program : gatesChunk88.toList = Block088.steps.map SSACertificate.Step.gate := by rfl

theorem Block089.wellFormed : ∀ e ∈ Block089.steps, WellFormed e :=
  wellFormed_of_checks Block089.steps Block089.checkedBounds Block089.checkedNodup Block089.checkedNoSelf

theorem Block089.program : gatesChunk89.toList = Block089.steps.map SSACertificate.Step.gate := by rfl

theorem Block090.wellFormed : ∀ e ∈ Block090.steps, WellFormed e :=
  wellFormed_of_checks Block090.steps Block090.checkedBounds Block090.checkedNodup Block090.checkedNoSelf

theorem Block090.program : gatesChunk90.toList = Block090.steps.map SSACertificate.Step.gate := by rfl

theorem Block091.wellFormed : ∀ e ∈ Block091.steps, WellFormed e :=
  wellFormed_of_checks Block091.steps Block091.checkedBounds Block091.checkedNodup Block091.checkedNoSelf

theorem Block091.program : gatesChunk91.toList = Block091.steps.map SSACertificate.Step.gate := by rfl

theorem Block092.wellFormed : ∀ e ∈ Block092.steps, WellFormed e :=
  wellFormed_of_checks Block092.steps Block092.checkedBounds Block092.checkedNodup Block092.checkedNoSelf

theorem Block092.program : gatesChunk92.toList = Block092.steps.map SSACertificate.Step.gate := by rfl

theorem Block093.wellFormed : ∀ e ∈ Block093.steps, WellFormed e :=
  wellFormed_of_checks Block093.steps Block093.checkedBounds Block093.checkedNodup Block093.checkedNoSelf

theorem Block093.program : gatesChunk93.toList = Block093.steps.map SSACertificate.Step.gate := by rfl

theorem Block094.wellFormed : ∀ e ∈ Block094.steps, WellFormed e :=
  wellFormed_of_checks Block094.steps Block094.checkedBounds Block094.checkedNodup Block094.checkedNoSelf

theorem Block094.program : gatesChunk94.toList = Block094.steps.map SSACertificate.Step.gate := by rfl

theorem Block095.wellFormed : ∀ e ∈ Block095.steps, WellFormed e :=
  wellFormed_of_checks Block095.steps Block095.checkedBounds Block095.checkedNodup Block095.checkedNoSelf

theorem Block095.program : gatesChunk95.toList = Block095.steps.map SSACertificate.Step.gate := by rfl

theorem Block096.wellFormed : ∀ e ∈ Block096.steps, WellFormed e :=
  wellFormed_of_checks Block096.steps Block096.checkedBounds Block096.checkedNodup Block096.checkedNoSelf

theorem Block096.program : gatesChunk96.toList = Block096.steps.map SSACertificate.Step.gate := by rfl

theorem Block097.wellFormed : ∀ e ∈ Block097.steps, WellFormed e :=
  wellFormed_of_checks Block097.steps Block097.checkedBounds Block097.checkedNodup Block097.checkedNoSelf

theorem Block097.program : gatesChunk97.toList = Block097.steps.map SSACertificate.Step.gate := by rfl

theorem Block098.wellFormed : ∀ e ∈ Block098.steps, WellFormed e :=
  wellFormed_of_checks Block098.steps Block098.checkedBounds Block098.checkedNodup Block098.checkedNoSelf

theorem Block098.program : gatesChunk98.toList = Block098.steps.map SSACertificate.Step.gate := by rfl

theorem Block099.wellFormed : ∀ e ∈ Block099.steps, WellFormed e :=
  wellFormed_of_checks Block099.steps Block099.checkedBounds Block099.checkedNodup Block099.checkedNoSelf

theorem Block099.program : gatesChunk99.toList = Block099.steps.map SSACertificate.Step.gate := by rfl

theorem Block100.wellFormed : ∀ e ∈ Block100.steps, WellFormed e :=
  wellFormed_of_checks Block100.steps Block100.checkedBounds Block100.checkedNodup Block100.checkedNoSelf

theorem Block100.program : gatesChunk100.toList = Block100.steps.map SSACertificate.Step.gate := by rfl

theorem Block101.wellFormed : ∀ e ∈ Block101.steps, WellFormed e :=
  wellFormed_of_checks Block101.steps Block101.checkedBounds Block101.checkedNodup Block101.checkedNoSelf

theorem Block101.program : gatesChunk101.toList = Block101.steps.map SSACertificate.Step.gate := by rfl

theorem Block102.wellFormed : ∀ e ∈ Block102.steps, WellFormed e :=
  wellFormed_of_checks Block102.steps Block102.checkedBounds Block102.checkedNodup Block102.checkedNoSelf

theorem Block102.program : gatesChunk102.toList = Block102.steps.map SSACertificate.Step.gate := by rfl

theorem Block103.wellFormed : ∀ e ∈ Block103.steps, WellFormed e :=
  wellFormed_of_checks Block103.steps Block103.checkedBounds Block103.checkedNodup Block103.checkedNoSelf

theorem Block103.program : gatesChunk103.toList = Block103.steps.map SSACertificate.Step.gate := by rfl

theorem Block104.wellFormed : ∀ e ∈ Block104.steps, WellFormed e :=
  wellFormed_of_checks Block104.steps Block104.checkedBounds Block104.checkedNodup Block104.checkedNoSelf

theorem Block104.program : gatesChunk104.toList = Block104.steps.map SSACertificate.Step.gate := by rfl

theorem Block105.wellFormed : ∀ e ∈ Block105.steps, WellFormed e :=
  wellFormed_of_checks Block105.steps Block105.checkedBounds Block105.checkedNodup Block105.checkedNoSelf

theorem Block105.program : gatesChunk105.toList = Block105.steps.map SSACertificate.Step.gate := by rfl

theorem Block106.wellFormed : ∀ e ∈ Block106.steps, WellFormed e :=
  wellFormed_of_checks Block106.steps Block106.checkedBounds Block106.checkedNodup Block106.checkedNoSelf

theorem Block106.program : gatesChunk106.toList = Block106.steps.map SSACertificate.Step.gate := by rfl

theorem Block107.wellFormed : ∀ e ∈ Block107.steps, WellFormed e :=
  wellFormed_of_checks Block107.steps Block107.checkedBounds Block107.checkedNodup Block107.checkedNoSelf

theorem Block107.program : gatesChunk107.toList = Block107.steps.map SSACertificate.Step.gate := by rfl

theorem Block108.wellFormed : ∀ e ∈ Block108.steps, WellFormed e :=
  wellFormed_of_checks Block108.steps Block108.checkedBounds Block108.checkedNodup Block108.checkedNoSelf

theorem Block108.program : gatesChunk108.toList = Block108.steps.map SSACertificate.Step.gate := by rfl

theorem Block109.wellFormed : ∀ e ∈ Block109.steps, WellFormed e :=
  wellFormed_of_checks Block109.steps Block109.checkedBounds Block109.checkedNodup Block109.checkedNoSelf

theorem Block109.program : gatesChunk109.toList = Block109.steps.map SSACertificate.Step.gate := by rfl

theorem Block110.wellFormed : ∀ e ∈ Block110.steps, WellFormed e :=
  wellFormed_of_checks Block110.steps Block110.checkedBounds Block110.checkedNodup Block110.checkedNoSelf

theorem Block110.program : gatesChunk110.toList = Block110.steps.map SSACertificate.Step.gate := by rfl

theorem Block111.wellFormed : ∀ e ∈ Block111.steps, WellFormed e :=
  wellFormed_of_checks Block111.steps Block111.checkedBounds Block111.checkedNodup Block111.checkedNoSelf

theorem Block111.program : gatesChunk111.toList = Block111.steps.map SSACertificate.Step.gate := by rfl

theorem Block112.wellFormed : ∀ e ∈ Block112.steps, WellFormed e :=
  wellFormed_of_checks Block112.steps Block112.checkedBounds Block112.checkedNodup Block112.checkedNoSelf

theorem Block112.program : gatesChunk112.toList = Block112.steps.map SSACertificate.Step.gate := by rfl

theorem Block113.wellFormed : ∀ e ∈ Block113.steps, WellFormed e :=
  wellFormed_of_checks Block113.steps Block113.checkedBounds Block113.checkedNodup Block113.checkedNoSelf

theorem Block113.program : gatesChunk113.toList = Block113.steps.map SSACertificate.Step.gate := by rfl

theorem Block114.wellFormed : ∀ e ∈ Block114.steps, WellFormed e :=
  wellFormed_of_checks Block114.steps Block114.checkedBounds Block114.checkedNodup Block114.checkedNoSelf

theorem Block114.program : gatesChunk114.toList = Block114.steps.map SSACertificate.Step.gate := by rfl

theorem Block115.wellFormed : ∀ e ∈ Block115.steps, WellFormed e :=
  wellFormed_of_checks Block115.steps Block115.checkedBounds Block115.checkedNodup Block115.checkedNoSelf

theorem Block115.program : gatesChunk115.toList = Block115.steps.map SSACertificate.Step.gate := by rfl

theorem Block116.wellFormed : ∀ e ∈ Block116.steps, WellFormed e :=
  wellFormed_of_checks Block116.steps Block116.checkedBounds Block116.checkedNodup Block116.checkedNoSelf

theorem Block116.program : gatesChunk116.toList = Block116.steps.map SSACertificate.Step.gate := by rfl

theorem Block117.wellFormed : ∀ e ∈ Block117.steps, WellFormed e :=
  wellFormed_of_checks Block117.steps Block117.checkedBounds Block117.checkedNodup Block117.checkedNoSelf

theorem Block117.program : gatesChunk117.toList = Block117.steps.map SSACertificate.Step.gate := by rfl

theorem Block118.wellFormed : ∀ e ∈ Block118.steps, WellFormed e :=
  wellFormed_of_checks Block118.steps Block118.checkedBounds Block118.checkedNodup Block118.checkedNoSelf

theorem Block118.program : gatesChunk118.toList = Block118.steps.map SSACertificate.Step.gate := by rfl

theorem Block119.wellFormed : ∀ e ∈ Block119.steps, WellFormed e :=
  wellFormed_of_checks Block119.steps Block119.checkedBounds Block119.checkedNodup Block119.checkedNoSelf

theorem Block119.program : gatesChunk119.toList = Block119.steps.map SSACertificate.Step.gate := by rfl

theorem Block120.wellFormed : ∀ e ∈ Block120.steps, WellFormed e :=
  wellFormed_of_checks Block120.steps Block120.checkedBounds Block120.checkedNodup Block120.checkedNoSelf

theorem Block120.program : gatesChunk120.toList = Block120.steps.map SSACertificate.Step.gate := by rfl

theorem Block121.wellFormed : ∀ e ∈ Block121.steps, WellFormed e :=
  wellFormed_of_checks Block121.steps Block121.checkedBounds Block121.checkedNodup Block121.checkedNoSelf

theorem Block121.program : gatesChunk121.toList = Block121.steps.map SSACertificate.Step.gate := by rfl

theorem Block122.wellFormed : ∀ e ∈ Block122.steps, WellFormed e :=
  wellFormed_of_checks Block122.steps Block122.checkedBounds Block122.checkedNodup Block122.checkedNoSelf

theorem Block122.program : gatesChunk122.toList = Block122.steps.map SSACertificate.Step.gate := by rfl

theorem Block123.wellFormed : ∀ e ∈ Block123.steps, WellFormed e :=
  wellFormed_of_checks Block123.steps Block123.checkedBounds Block123.checkedNodup Block123.checkedNoSelf

theorem Block123.program : gatesChunk123.toList = Block123.steps.map SSACertificate.Step.gate := by rfl

theorem Block124.wellFormed : ∀ e ∈ Block124.steps, WellFormed e :=
  wellFormed_of_checks Block124.steps Block124.checkedBounds Block124.checkedNodup Block124.checkedNoSelf

theorem Block124.program : gatesChunk124.toList = Block124.steps.map SSACertificate.Step.gate := by rfl

theorem Block125.wellFormed : ∀ e ∈ Block125.steps, WellFormed e :=
  wellFormed_of_checks Block125.steps Block125.checkedBounds Block125.checkedNodup Block125.checkedNoSelf

theorem Block125.program : gatesChunk125.toList = Block125.steps.map SSACertificate.Step.gate := by rfl

theorem Block126.wellFormed : ∀ e ∈ Block126.steps, WellFormed e :=
  wellFormed_of_checks Block126.steps Block126.checkedBounds Block126.checkedNodup Block126.checkedNoSelf

theorem Block126.program : gatesChunk126.toList = Block126.steps.map SSACertificate.Step.gate := by rfl

theorem Block127.wellFormed : ∀ e ∈ Block127.steps, WellFormed e :=
  wellFormed_of_checks Block127.steps Block127.checkedBounds Block127.checkedNodup Block127.checkedNoSelf

theorem Block127.program : gatesChunk127.toList = Block127.steps.map SSACertificate.Step.gate := by rfl

theorem Block128.wellFormed : ∀ e ∈ Block128.steps, WellFormed e :=
  wellFormed_of_checks Block128.steps Block128.checkedBounds Block128.checkedNodup Block128.checkedNoSelf

theorem Block128.program : gatesChunk128.toList = Block128.steps.map SSACertificate.Step.gate := by rfl

theorem Block129.wellFormed : ∀ e ∈ Block129.steps, WellFormed e :=
  wellFormed_of_checks Block129.steps Block129.checkedBounds Block129.checkedNodup Block129.checkedNoSelf

theorem Block129.program : gatesChunk129.toList = Block129.steps.map SSACertificate.Step.gate := by rfl

theorem Block130.wellFormed : ∀ e ∈ Block130.steps, WellFormed e :=
  wellFormed_of_checks Block130.steps Block130.checkedBounds Block130.checkedNodup Block130.checkedNoSelf

theorem Block130.program : gatesChunk130.toList = Block130.steps.map SSACertificate.Step.gate := by rfl

theorem Block131.wellFormed : ∀ e ∈ Block131.steps, WellFormed e :=
  wellFormed_of_checks Block131.steps Block131.checkedBounds Block131.checkedNodup Block131.checkedNoSelf

theorem Block131.program : gatesChunk131.toList = Block131.steps.map SSACertificate.Step.gate := by rfl

theorem Block132.wellFormed : ∀ e ∈ Block132.steps, WellFormed e :=
  wellFormed_of_checks Block132.steps Block132.checkedBounds Block132.checkedNodup Block132.checkedNoSelf

theorem Block132.program : gatesChunk132.toList = Block132.steps.map SSACertificate.Step.gate := by rfl

theorem Block133.wellFormed : ∀ e ∈ Block133.steps, WellFormed e :=
  wellFormed_of_checks Block133.steps Block133.checkedBounds Block133.checkedNodup Block133.checkedNoSelf

theorem Block133.program : gatesChunk133.toList = Block133.steps.map SSACertificate.Step.gate := by rfl

theorem Block134.wellFormed : ∀ e ∈ Block134.steps, WellFormed e :=
  wellFormed_of_checks Block134.steps Block134.checkedBounds Block134.checkedNodup Block134.checkedNoSelf

theorem Block134.program : gatesChunk134.toList = Block134.steps.map SSACertificate.Step.gate := by rfl

theorem Block135.wellFormed : ∀ e ∈ Block135.steps, WellFormed e :=
  wellFormed_of_checks Block135.steps Block135.checkedBounds Block135.checkedNodup Block135.checkedNoSelf

theorem Block135.program : gatesChunk135.toList = Block135.steps.map SSACertificate.Step.gate := by rfl

theorem Block136.wellFormed : ∀ e ∈ Block136.steps, WellFormed e :=
  wellFormed_of_checks Block136.steps Block136.checkedBounds Block136.checkedNodup Block136.checkedNoSelf

theorem Block136.program : gatesChunk136.toList = Block136.steps.map SSACertificate.Step.gate := by rfl

theorem Block137.wellFormed : ∀ e ∈ Block137.steps, WellFormed e :=
  wellFormed_of_checks Block137.steps Block137.checkedBounds Block137.checkedNodup Block137.checkedNoSelf

theorem Block137.program : gatesChunk137.toList = Block137.steps.map SSACertificate.Step.gate := by rfl

theorem Block138.wellFormed : ∀ e ∈ Block138.steps, WellFormed e :=
  wellFormed_of_checks Block138.steps Block138.checkedBounds Block138.checkedNodup Block138.checkedNoSelf

theorem Block138.program : gatesChunk138.toList = Block138.steps.map SSACertificate.Step.gate := by rfl

theorem Block139.wellFormed : ∀ e ∈ Block139.steps, WellFormed e :=
  wellFormed_of_checks Block139.steps Block139.checkedBounds Block139.checkedNodup Block139.checkedNoSelf

theorem Block139.program : gatesChunk139.toList = Block139.steps.map SSACertificate.Step.gate := by rfl

theorem Block140.wellFormed : ∀ e ∈ Block140.steps, WellFormed e :=
  wellFormed_of_checks Block140.steps Block140.checkedBounds Block140.checkedNodup Block140.checkedNoSelf

theorem Block140.program : gatesChunk140.toList = Block140.steps.map SSACertificate.Step.gate := by rfl

theorem Block141.wellFormed : ∀ e ∈ Block141.steps, WellFormed e :=
  wellFormed_of_checks Block141.steps Block141.checkedBounds Block141.checkedNodup Block141.checkedNoSelf

theorem Block141.program : gatesChunk141.toList = Block141.steps.map SSACertificate.Step.gate := by rfl

theorem Block142.wellFormed : ∀ e ∈ Block142.steps, WellFormed e :=
  wellFormed_of_checks Block142.steps Block142.checkedBounds Block142.checkedNodup Block142.checkedNoSelf

theorem Block142.program : gatesChunk142.toList = Block142.steps.map SSACertificate.Step.gate := by rfl

theorem Block143.wellFormed : ∀ e ∈ Block143.steps, WellFormed e :=
  wellFormed_of_checks Block143.steps Block143.checkedBounds Block143.checkedNodup Block143.checkedNoSelf

theorem Block143.program : gatesChunk143.toList = Block143.steps.map SSACertificate.Step.gate := by rfl

theorem Block144.wellFormed : ∀ e ∈ Block144.steps, WellFormed e :=
  wellFormed_of_checks Block144.steps Block144.checkedBounds Block144.checkedNodup Block144.checkedNoSelf

theorem Block144.program : gatesChunk144.toList = Block144.steps.map SSACertificate.Step.gate := by rfl

theorem Block145.wellFormed : ∀ e ∈ Block145.steps, WellFormed e :=
  wellFormed_of_checks Block145.steps Block145.checkedBounds Block145.checkedNodup Block145.checkedNoSelf

theorem Block145.program : gatesChunk145.toList = Block145.steps.map SSACertificate.Step.gate := by rfl

theorem Block146.wellFormed : ∀ e ∈ Block146.steps, WellFormed e :=
  wellFormed_of_checks Block146.steps Block146.checkedBounds Block146.checkedNodup Block146.checkedNoSelf

theorem Block146.program : gatesChunk146.toList = Block146.steps.map SSACertificate.Step.gate := by rfl

theorem Block147.wellFormed : ∀ e ∈ Block147.steps, WellFormed e :=
  wellFormed_of_checks Block147.steps Block147.checkedBounds Block147.checkedNodup Block147.checkedNoSelf

theorem Block147.program : gatesChunk147.toList = Block147.steps.map SSACertificate.Step.gate := by rfl

theorem Block148.wellFormed : ∀ e ∈ Block148.steps, WellFormed e :=
  wellFormed_of_checks Block148.steps Block148.checkedBounds Block148.checkedNodup Block148.checkedNoSelf

theorem Block148.program : gatesChunk148.toList = Block148.steps.map SSACertificate.Step.gate := by rfl

theorem Block149.wellFormed : ∀ e ∈ Block149.steps, WellFormed e :=
  wellFormed_of_checks Block149.steps Block149.checkedBounds Block149.checkedNodup Block149.checkedNoSelf

theorem Block149.program : gatesChunk149.toList = Block149.steps.map SSACertificate.Step.gate := by rfl

theorem Block150.wellFormed : ∀ e ∈ Block150.steps, WellFormed e :=
  wellFormed_of_checks Block150.steps Block150.checkedBounds Block150.checkedNodup Block150.checkedNoSelf

theorem Block150.program : gatesChunk150.toList = Block150.steps.map SSACertificate.Step.gate := by rfl

theorem Block151.wellFormed : ∀ e ∈ Block151.steps, WellFormed e :=
  wellFormed_of_checks Block151.steps Block151.checkedBounds Block151.checkedNodup Block151.checkedNoSelf

theorem Block151.program : gatesChunk151.toList = Block151.steps.map SSACertificate.Step.gate := by rfl

theorem Block152.wellFormed : ∀ e ∈ Block152.steps, WellFormed e :=
  wellFormed_of_checks Block152.steps Block152.checkedBounds Block152.checkedNodup Block152.checkedNoSelf

theorem Block152.program : gatesChunk152.toList = Block152.steps.map SSACertificate.Step.gate := by rfl

theorem Block153.wellFormed : ∀ e ∈ Block153.steps, WellFormed e :=
  wellFormed_of_checks Block153.steps Block153.checkedBounds Block153.checkedNodup Block153.checkedNoSelf

theorem Block153.program : gatesChunk153.toList = Block153.steps.map SSACertificate.Step.gate := by rfl

theorem Block154.wellFormed : ∀ e ∈ Block154.steps, WellFormed e :=
  wellFormed_of_checks Block154.steps Block154.checkedBounds Block154.checkedNodup Block154.checkedNoSelf

theorem Block154.program : gatesChunk154.toList = Block154.steps.map SSACertificate.Step.gate := by rfl

theorem Block155.wellFormed : ∀ e ∈ Block155.steps, WellFormed e :=
  wellFormed_of_checks Block155.steps Block155.checkedBounds Block155.checkedNodup Block155.checkedNoSelf

theorem Block155.program : gatesChunk155.toList = Block155.steps.map SSACertificate.Step.gate := by rfl

theorem Block156.wellFormed : ∀ e ∈ Block156.steps, WellFormed e :=
  wellFormed_of_checks Block156.steps Block156.checkedBounds Block156.checkedNodup Block156.checkedNoSelf

theorem Block156.program : gatesChunk156.toList = Block156.steps.map SSACertificate.Step.gate := by rfl

theorem Block157.wellFormed : ∀ e ∈ Block157.steps, WellFormed e :=
  wellFormed_of_checks Block157.steps Block157.checkedBounds Block157.checkedNodup Block157.checkedNoSelf

theorem Block157.program : gatesChunk157.toList = Block157.steps.map SSACertificate.Step.gate := by rfl

theorem Block158.wellFormed : ∀ e ∈ Block158.steps, WellFormed e :=
  wellFormed_of_checks Block158.steps Block158.checkedBounds Block158.checkedNodup Block158.checkedNoSelf

theorem Block158.program : gatesChunk158.toList = Block158.steps.map SSACertificate.Step.gate := by rfl

theorem Block159.wellFormed : ∀ e ∈ Block159.steps, WellFormed e :=
  wellFormed_of_checks Block159.steps Block159.checkedBounds Block159.checkedNodup Block159.checkedNoSelf

theorem Block159.program : gatesChunk159.toList = Block159.steps.map SSACertificate.Step.gate := by rfl

theorem Block160.wellFormed : ∀ e ∈ Block160.steps, WellFormed e :=
  wellFormed_of_checks Block160.steps Block160.checkedBounds Block160.checkedNodup Block160.checkedNoSelf

theorem Block160.program : gatesChunk160.toList = Block160.steps.map SSACertificate.Step.gate := by rfl

theorem Block161.wellFormed : ∀ e ∈ Block161.steps, WellFormed e :=
  wellFormed_of_checks Block161.steps Block161.checkedBounds Block161.checkedNodup Block161.checkedNoSelf

theorem Block161.program : gatesChunk161.toList = Block161.steps.map SSACertificate.Step.gate := by rfl

theorem Block162.wellFormed : ∀ e ∈ Block162.steps, WellFormed e :=
  wellFormed_of_checks Block162.steps Block162.checkedBounds Block162.checkedNodup Block162.checkedNoSelf

theorem Block162.program : gatesChunk162.toList = Block162.steps.map SSACertificate.Step.gate := by rfl

theorem Block163.wellFormed : ∀ e ∈ Block163.steps, WellFormed e :=
  wellFormed_of_checks Block163.steps Block163.checkedBounds Block163.checkedNodup Block163.checkedNoSelf

theorem Block163.program : gatesChunk163.toList = Block163.steps.map SSACertificate.Step.gate := by rfl

theorem Block164.wellFormed : ∀ e ∈ Block164.steps, WellFormed e :=
  wellFormed_of_checks Block164.steps Block164.checkedBounds Block164.checkedNodup Block164.checkedNoSelf

theorem Block164.program : gatesChunk164.toList = Block164.steps.map SSACertificate.Step.gate := by rfl

theorem Block165.wellFormed : ∀ e ∈ Block165.steps, WellFormed e :=
  wellFormed_of_checks Block165.steps Block165.checkedBounds Block165.checkedNodup Block165.checkedNoSelf

theorem Block165.program : gatesChunk165.toList = Block165.steps.map SSACertificate.Step.gate := by rfl

theorem Block166.wellFormed : ∀ e ∈ Block166.steps, WellFormed e :=
  wellFormed_of_checks Block166.steps Block166.checkedBounds Block166.checkedNodup Block166.checkedNoSelf

theorem Block166.program : gatesChunk166.toList = Block166.steps.map SSACertificate.Step.gate := by rfl

theorem Block167.wellFormed : ∀ e ∈ Block167.steps, WellFormed e :=
  wellFormed_of_checks Block167.steps Block167.checkedBounds Block167.checkedNodup Block167.checkedNoSelf

theorem Block167.program : gatesChunk167.toList = Block167.steps.map SSACertificate.Step.gate := by rfl

theorem Block168.wellFormed : ∀ e ∈ Block168.steps, WellFormed e :=
  wellFormed_of_checks Block168.steps Block168.checkedBounds Block168.checkedNodup Block168.checkedNoSelf

theorem Block168.program : gatesChunk168.toList = Block168.steps.map SSACertificate.Step.gate := by rfl

theorem Block169.wellFormed : ∀ e ∈ Block169.steps, WellFormed e :=
  wellFormed_of_checks Block169.steps Block169.checkedBounds Block169.checkedNodup Block169.checkedNoSelf

theorem Block169.program : gatesChunk169.toList = Block169.steps.map SSACertificate.Step.gate := by rfl

theorem Block170.wellFormed : ∀ e ∈ Block170.steps, WellFormed e :=
  wellFormed_of_checks Block170.steps Block170.checkedBounds Block170.checkedNodup Block170.checkedNoSelf

theorem Block170.program : gatesChunk170.toList = Block170.steps.map SSACertificate.Step.gate := by rfl

theorem Block171.wellFormed : ∀ e ∈ Block171.steps, WellFormed e :=
  wellFormed_of_checks Block171.steps Block171.checkedBounds Block171.checkedNodup Block171.checkedNoSelf

theorem Block171.program : gatesChunk171.toList = Block171.steps.map SSACertificate.Step.gate := by rfl

theorem Block172.wellFormed : ∀ e ∈ Block172.steps, WellFormed e :=
  wellFormed_of_checks Block172.steps Block172.checkedBounds Block172.checkedNodup Block172.checkedNoSelf

theorem Block172.program : gatesChunk172.toList = Block172.steps.map SSACertificate.Step.gate := by rfl

theorem Block173.wellFormed : ∀ e ∈ Block173.steps, WellFormed e :=
  wellFormed_of_checks Block173.steps Block173.checkedBounds Block173.checkedNodup Block173.checkedNoSelf

theorem Block173.program : gatesChunk173.toList = Block173.steps.map SSACertificate.Step.gate := by rfl

theorem Block174.wellFormed : ∀ e ∈ Block174.steps, WellFormed e :=
  wellFormed_of_checks Block174.steps Block174.checkedBounds Block174.checkedNodup Block174.checkedNoSelf

theorem Block174.program : gatesChunk174.toList = Block174.steps.map SSACertificate.Step.gate := by rfl

def part000_002 : List Step := Block000.steps ++ Block001.steps
theorem part000_002_sound : ArrayBlockSound rows 661 Block000.before Block001.after part000_002 :=
  sound_append rows 661 Block000.before Block000.after Block001.after
    Block000.steps Block001.steps Block000.sound Block001.sound
theorem part000_002_wellFormed : ∀ e ∈ part000_002, WellFormed e :=
  wellFormed_append Block000.steps Block001.steps Block000.wellFormed Block001.wellFormed

def part003_005 : List Step := Block003.steps ++ Block004.steps
theorem part003_005_sound : ArrayBlockSound rows 661 Block003.before Block004.after part003_005 :=
  sound_append rows 661 Block003.before Block003.after Block004.after
    Block003.steps Block004.steps Block003.sound Block004.sound
theorem part003_005_wellFormed : ∀ e ∈ part003_005, WellFormed e :=
  wellFormed_append Block003.steps Block004.steps Block003.wellFormed Block004.wellFormed

def part002_005 : List Step := Block002.steps ++ part003_005
theorem part002_005_sound : ArrayBlockSound rows 661 Block002.before Block004.after part002_005 :=
  sound_append rows 661 Block002.before Block002.after Block004.after
    Block002.steps part003_005 Block002.sound part003_005_sound
theorem part002_005_wellFormed : ∀ e ∈ part002_005, WellFormed e :=
  wellFormed_append Block002.steps part003_005 Block002.wellFormed part003_005_wellFormed

def part000_005 : List Step := part000_002 ++ part002_005
theorem part000_005_sound : ArrayBlockSound rows 661 Block000.before Block004.after part000_005 :=
  sound_append rows 661 Block000.before Block001.after Block004.after
    part000_002 part002_005 part000_002_sound part002_005_sound
theorem part000_005_wellFormed : ∀ e ∈ part000_005, WellFormed e :=
  wellFormed_append part000_002 part002_005 part000_002_wellFormed part002_005_wellFormed

def part005_007 : List Step := Block005.steps ++ Block006.steps
theorem part005_007_sound : ArrayBlockSound rows 661 Block005.before Block006.after part005_007 :=
  sound_append rows 661 Block005.before Block005.after Block006.after
    Block005.steps Block006.steps Block005.sound Block006.sound
theorem part005_007_wellFormed : ∀ e ∈ part005_007, WellFormed e :=
  wellFormed_append Block005.steps Block006.steps Block005.wellFormed Block006.wellFormed

def part008_010 : List Step := Block008.steps ++ Block009.steps
theorem part008_010_sound : ArrayBlockSound rows 661 Block008.before Block009.after part008_010 :=
  sound_append rows 661 Block008.before Block008.after Block009.after
    Block008.steps Block009.steps Block008.sound Block009.sound
theorem part008_010_wellFormed : ∀ e ∈ part008_010, WellFormed e :=
  wellFormed_append Block008.steps Block009.steps Block008.wellFormed Block009.wellFormed

def part007_010 : List Step := Block007.steps ++ part008_010
theorem part007_010_sound : ArrayBlockSound rows 661 Block007.before Block009.after part007_010 :=
  sound_append rows 661 Block007.before Block007.after Block009.after
    Block007.steps part008_010 Block007.sound part008_010_sound
theorem part007_010_wellFormed : ∀ e ∈ part007_010, WellFormed e :=
  wellFormed_append Block007.steps part008_010 Block007.wellFormed part008_010_wellFormed

def part005_010 : List Step := part005_007 ++ part007_010
theorem part005_010_sound : ArrayBlockSound rows 661 Block005.before Block009.after part005_010 :=
  sound_append rows 661 Block005.before Block006.after Block009.after
    part005_007 part007_010 part005_007_sound part007_010_sound
theorem part005_010_wellFormed : ∀ e ∈ part005_010, WellFormed e :=
  wellFormed_append part005_007 part007_010 part005_007_wellFormed part007_010_wellFormed

def part000_010 : List Step := part000_005 ++ part005_010
theorem part000_010_sound : ArrayBlockSound rows 661 Block000.before Block009.after part000_010 :=
  sound_append rows 661 Block000.before Block004.after Block009.after
    part000_005 part005_010 part000_005_sound part005_010_sound
theorem part000_010_wellFormed : ∀ e ∈ part000_010, WellFormed e :=
  wellFormed_append part000_005 part005_010 part000_005_wellFormed part005_010_wellFormed

def part010_012 : List Step := Block010.steps ++ Block011.steps
theorem part010_012_sound : ArrayBlockSound rows 661 Block010.before Block011.after part010_012 :=
  sound_append rows 661 Block010.before Block010.after Block011.after
    Block010.steps Block011.steps Block010.sound Block011.sound
theorem part010_012_wellFormed : ∀ e ∈ part010_012, WellFormed e :=
  wellFormed_append Block010.steps Block011.steps Block010.wellFormed Block011.wellFormed

def part013_015 : List Step := Block013.steps ++ Block014.steps
theorem part013_015_sound : ArrayBlockSound rows 661 Block013.before Block014.after part013_015 :=
  sound_append rows 661 Block013.before Block013.after Block014.after
    Block013.steps Block014.steps Block013.sound Block014.sound
theorem part013_015_wellFormed : ∀ e ∈ part013_015, WellFormed e :=
  wellFormed_append Block013.steps Block014.steps Block013.wellFormed Block014.wellFormed

def part012_015 : List Step := Block012.steps ++ part013_015
theorem part012_015_sound : ArrayBlockSound rows 661 Block012.before Block014.after part012_015 :=
  sound_append rows 661 Block012.before Block012.after Block014.after
    Block012.steps part013_015 Block012.sound part013_015_sound
theorem part012_015_wellFormed : ∀ e ∈ part012_015, WellFormed e :=
  wellFormed_append Block012.steps part013_015 Block012.wellFormed part013_015_wellFormed

def part010_015 : List Step := part010_012 ++ part012_015
theorem part010_015_sound : ArrayBlockSound rows 661 Block010.before Block014.after part010_015 :=
  sound_append rows 661 Block010.before Block011.after Block014.after
    part010_012 part012_015 part010_012_sound part012_015_sound
theorem part010_015_wellFormed : ∀ e ∈ part010_015, WellFormed e :=
  wellFormed_append part010_012 part012_015 part010_012_wellFormed part012_015_wellFormed

def part016_018 : List Step := Block016.steps ++ Block017.steps
theorem part016_018_sound : ArrayBlockSound rows 661 Block016.before Block017.after part016_018 :=
  sound_append rows 661 Block016.before Block016.after Block017.after
    Block016.steps Block017.steps Block016.sound Block017.sound
theorem part016_018_wellFormed : ∀ e ∈ part016_018, WellFormed e :=
  wellFormed_append Block016.steps Block017.steps Block016.wellFormed Block017.wellFormed

def part015_018 : List Step := Block015.steps ++ part016_018
theorem part015_018_sound : ArrayBlockSound rows 661 Block015.before Block017.after part015_018 :=
  sound_append rows 661 Block015.before Block015.after Block017.after
    Block015.steps part016_018 Block015.sound part016_018_sound
theorem part015_018_wellFormed : ∀ e ∈ part015_018, WellFormed e :=
  wellFormed_append Block015.steps part016_018 Block015.wellFormed part016_018_wellFormed

def part019_021 : List Step := Block019.steps ++ Block020.steps
theorem part019_021_sound : ArrayBlockSound rows 661 Block019.before Block020.after part019_021 :=
  sound_append rows 661 Block019.before Block019.after Block020.after
    Block019.steps Block020.steps Block019.sound Block020.sound
theorem part019_021_wellFormed : ∀ e ∈ part019_021, WellFormed e :=
  wellFormed_append Block019.steps Block020.steps Block019.wellFormed Block020.wellFormed

def part018_021 : List Step := Block018.steps ++ part019_021
theorem part018_021_sound : ArrayBlockSound rows 661 Block018.before Block020.after part018_021 :=
  sound_append rows 661 Block018.before Block018.after Block020.after
    Block018.steps part019_021 Block018.sound part019_021_sound
theorem part018_021_wellFormed : ∀ e ∈ part018_021, WellFormed e :=
  wellFormed_append Block018.steps part019_021 Block018.wellFormed part019_021_wellFormed

def part015_021 : List Step := part015_018 ++ part018_021
theorem part015_021_sound : ArrayBlockSound rows 661 Block015.before Block020.after part015_021 :=
  sound_append rows 661 Block015.before Block017.after Block020.after
    part015_018 part018_021 part015_018_sound part018_021_sound
theorem part015_021_wellFormed : ∀ e ∈ part015_021, WellFormed e :=
  wellFormed_append part015_018 part018_021 part015_018_wellFormed part018_021_wellFormed

def part010_021 : List Step := part010_015 ++ part015_021
theorem part010_021_sound : ArrayBlockSound rows 661 Block010.before Block020.after part010_021 :=
  sound_append rows 661 Block010.before Block014.after Block020.after
    part010_015 part015_021 part010_015_sound part015_021_sound
theorem part010_021_wellFormed : ∀ e ∈ part010_021, WellFormed e :=
  wellFormed_append part010_015 part015_021 part010_015_wellFormed part015_021_wellFormed

def part000_021 : List Step := part000_010 ++ part010_021
theorem part000_021_sound : ArrayBlockSound rows 661 Block000.before Block020.after part000_021 :=
  sound_append rows 661 Block000.before Block009.after Block020.after
    part000_010 part010_021 part000_010_sound part010_021_sound
theorem part000_021_wellFormed : ∀ e ∈ part000_021, WellFormed e :=
  wellFormed_append part000_010 part010_021 part000_010_wellFormed part010_021_wellFormed

def part021_023 : List Step := Block021.steps ++ Block022.steps
theorem part021_023_sound : ArrayBlockSound rows 661 Block021.before Block022.after part021_023 :=
  sound_append rows 661 Block021.before Block021.after Block022.after
    Block021.steps Block022.steps Block021.sound Block022.sound
theorem part021_023_wellFormed : ∀ e ∈ part021_023, WellFormed e :=
  wellFormed_append Block021.steps Block022.steps Block021.wellFormed Block022.wellFormed

def part024_026 : List Step := Block024.steps ++ Block025.steps
theorem part024_026_sound : ArrayBlockSound rows 661 Block024.before Block025.after part024_026 :=
  sound_append rows 661 Block024.before Block024.after Block025.after
    Block024.steps Block025.steps Block024.sound Block025.sound
theorem part024_026_wellFormed : ∀ e ∈ part024_026, WellFormed e :=
  wellFormed_append Block024.steps Block025.steps Block024.wellFormed Block025.wellFormed

def part023_026 : List Step := Block023.steps ++ part024_026
theorem part023_026_sound : ArrayBlockSound rows 661 Block023.before Block025.after part023_026 :=
  sound_append rows 661 Block023.before Block023.after Block025.after
    Block023.steps part024_026 Block023.sound part024_026_sound
theorem part023_026_wellFormed : ∀ e ∈ part023_026, WellFormed e :=
  wellFormed_append Block023.steps part024_026 Block023.wellFormed part024_026_wellFormed

def part021_026 : List Step := part021_023 ++ part023_026
theorem part021_026_sound : ArrayBlockSound rows 661 Block021.before Block025.after part021_026 :=
  sound_append rows 661 Block021.before Block022.after Block025.after
    part021_023 part023_026 part021_023_sound part023_026_sound
theorem part021_026_wellFormed : ∀ e ∈ part021_026, WellFormed e :=
  wellFormed_append part021_023 part023_026 part021_023_wellFormed part023_026_wellFormed

def part027_029 : List Step := Block027.steps ++ Block028.steps
theorem part027_029_sound : ArrayBlockSound rows 661 Block027.before Block028.after part027_029 :=
  sound_append rows 661 Block027.before Block027.after Block028.after
    Block027.steps Block028.steps Block027.sound Block028.sound
theorem part027_029_wellFormed : ∀ e ∈ part027_029, WellFormed e :=
  wellFormed_append Block027.steps Block028.steps Block027.wellFormed Block028.wellFormed

def part026_029 : List Step := Block026.steps ++ part027_029
theorem part026_029_sound : ArrayBlockSound rows 661 Block026.before Block028.after part026_029 :=
  sound_append rows 661 Block026.before Block026.after Block028.after
    Block026.steps part027_029 Block026.sound part027_029_sound
theorem part026_029_wellFormed : ∀ e ∈ part026_029, WellFormed e :=
  wellFormed_append Block026.steps part027_029 Block026.wellFormed part027_029_wellFormed

def part030_032 : List Step := Block030.steps ++ Block031.steps
theorem part030_032_sound : ArrayBlockSound rows 661 Block030.before Block031.after part030_032 :=
  sound_append rows 661 Block030.before Block030.after Block031.after
    Block030.steps Block031.steps Block030.sound Block031.sound
theorem part030_032_wellFormed : ∀ e ∈ part030_032, WellFormed e :=
  wellFormed_append Block030.steps Block031.steps Block030.wellFormed Block031.wellFormed

def part029_032 : List Step := Block029.steps ++ part030_032
theorem part029_032_sound : ArrayBlockSound rows 661 Block029.before Block031.after part029_032 :=
  sound_append rows 661 Block029.before Block029.after Block031.after
    Block029.steps part030_032 Block029.sound part030_032_sound
theorem part029_032_wellFormed : ∀ e ∈ part029_032, WellFormed e :=
  wellFormed_append Block029.steps part030_032 Block029.wellFormed part030_032_wellFormed

def part026_032 : List Step := part026_029 ++ part029_032
theorem part026_032_sound : ArrayBlockSound rows 661 Block026.before Block031.after part026_032 :=
  sound_append rows 661 Block026.before Block028.after Block031.after
    part026_029 part029_032 part026_029_sound part029_032_sound
theorem part026_032_wellFormed : ∀ e ∈ part026_032, WellFormed e :=
  wellFormed_append part026_029 part029_032 part026_029_wellFormed part029_032_wellFormed

def part021_032 : List Step := part021_026 ++ part026_032
theorem part021_032_sound : ArrayBlockSound rows 661 Block021.before Block031.after part021_032 :=
  sound_append rows 661 Block021.before Block025.after Block031.after
    part021_026 part026_032 part021_026_sound part026_032_sound
theorem part021_032_wellFormed : ∀ e ∈ part021_032, WellFormed e :=
  wellFormed_append part021_026 part026_032 part021_026_wellFormed part026_032_wellFormed

def part032_034 : List Step := Block032.steps ++ Block033.steps
theorem part032_034_sound : ArrayBlockSound rows 661 Block032.before Block033.after part032_034 :=
  sound_append rows 661 Block032.before Block032.after Block033.after
    Block032.steps Block033.steps Block032.sound Block033.sound
theorem part032_034_wellFormed : ∀ e ∈ part032_034, WellFormed e :=
  wellFormed_append Block032.steps Block033.steps Block032.wellFormed Block033.wellFormed

def part035_037 : List Step := Block035.steps ++ Block036.steps
theorem part035_037_sound : ArrayBlockSound rows 661 Block035.before Block036.after part035_037 :=
  sound_append rows 661 Block035.before Block035.after Block036.after
    Block035.steps Block036.steps Block035.sound Block036.sound
theorem part035_037_wellFormed : ∀ e ∈ part035_037, WellFormed e :=
  wellFormed_append Block035.steps Block036.steps Block035.wellFormed Block036.wellFormed

def part034_037 : List Step := Block034.steps ++ part035_037
theorem part034_037_sound : ArrayBlockSound rows 661 Block034.before Block036.after part034_037 :=
  sound_append rows 661 Block034.before Block034.after Block036.after
    Block034.steps part035_037 Block034.sound part035_037_sound
theorem part034_037_wellFormed : ∀ e ∈ part034_037, WellFormed e :=
  wellFormed_append Block034.steps part035_037 Block034.wellFormed part035_037_wellFormed

def part032_037 : List Step := part032_034 ++ part034_037
theorem part032_037_sound : ArrayBlockSound rows 661 Block032.before Block036.after part032_037 :=
  sound_append rows 661 Block032.before Block033.after Block036.after
    part032_034 part034_037 part032_034_sound part034_037_sound
theorem part032_037_wellFormed : ∀ e ∈ part032_037, WellFormed e :=
  wellFormed_append part032_034 part034_037 part032_034_wellFormed part034_037_wellFormed

def part038_040 : List Step := Block038.steps ++ Block039.steps
theorem part038_040_sound : ArrayBlockSound rows 661 Block038.before Block039.after part038_040 :=
  sound_append rows 661 Block038.before Block038.after Block039.after
    Block038.steps Block039.steps Block038.sound Block039.sound
theorem part038_040_wellFormed : ∀ e ∈ part038_040, WellFormed e :=
  wellFormed_append Block038.steps Block039.steps Block038.wellFormed Block039.wellFormed

def part037_040 : List Step := Block037.steps ++ part038_040
theorem part037_040_sound : ArrayBlockSound rows 661 Block037.before Block039.after part037_040 :=
  sound_append rows 661 Block037.before Block037.after Block039.after
    Block037.steps part038_040 Block037.sound part038_040_sound
theorem part037_040_wellFormed : ∀ e ∈ part037_040, WellFormed e :=
  wellFormed_append Block037.steps part038_040 Block037.wellFormed part038_040_wellFormed

def part041_043 : List Step := Block041.steps ++ Block042.steps
theorem part041_043_sound : ArrayBlockSound rows 661 Block041.before Block042.after part041_043 :=
  sound_append rows 661 Block041.before Block041.after Block042.after
    Block041.steps Block042.steps Block041.sound Block042.sound
theorem part041_043_wellFormed : ∀ e ∈ part041_043, WellFormed e :=
  wellFormed_append Block041.steps Block042.steps Block041.wellFormed Block042.wellFormed

def part040_043 : List Step := Block040.steps ++ part041_043
theorem part040_043_sound : ArrayBlockSound rows 661 Block040.before Block042.after part040_043 :=
  sound_append rows 661 Block040.before Block040.after Block042.after
    Block040.steps part041_043 Block040.sound part041_043_sound
theorem part040_043_wellFormed : ∀ e ∈ part040_043, WellFormed e :=
  wellFormed_append Block040.steps part041_043 Block040.wellFormed part041_043_wellFormed

def part037_043 : List Step := part037_040 ++ part040_043
theorem part037_043_sound : ArrayBlockSound rows 661 Block037.before Block042.after part037_043 :=
  sound_append rows 661 Block037.before Block039.after Block042.after
    part037_040 part040_043 part037_040_sound part040_043_sound
theorem part037_043_wellFormed : ∀ e ∈ part037_043, WellFormed e :=
  wellFormed_append part037_040 part040_043 part037_040_wellFormed part040_043_wellFormed

def part032_043 : List Step := part032_037 ++ part037_043
theorem part032_043_sound : ArrayBlockSound rows 661 Block032.before Block042.after part032_043 :=
  sound_append rows 661 Block032.before Block036.after Block042.after
    part032_037 part037_043 part032_037_sound part037_043_sound
theorem part032_043_wellFormed : ∀ e ∈ part032_043, WellFormed e :=
  wellFormed_append part032_037 part037_043 part032_037_wellFormed part037_043_wellFormed

def part021_043 : List Step := part021_032 ++ part032_043
theorem part021_043_sound : ArrayBlockSound rows 661 Block021.before Block042.after part021_043 :=
  sound_append rows 661 Block021.before Block031.after Block042.after
    part021_032 part032_043 part021_032_sound part032_043_sound
theorem part021_043_wellFormed : ∀ e ∈ part021_043, WellFormed e :=
  wellFormed_append part021_032 part032_043 part021_032_wellFormed part032_043_wellFormed

def part000_043 : List Step := part000_021 ++ part021_043
theorem part000_043_sound : ArrayBlockSound rows 661 Block000.before Block042.after part000_043 :=
  sound_append rows 661 Block000.before Block020.after Block042.after
    part000_021 part021_043 part000_021_sound part021_043_sound
theorem part000_043_wellFormed : ∀ e ∈ part000_043, WellFormed e :=
  wellFormed_append part000_021 part021_043 part000_021_wellFormed part021_043_wellFormed

def part043_045 : List Step := Block043.steps ++ Block044.steps
theorem part043_045_sound : ArrayBlockSound rows 661 Block043.before Block044.after part043_045 :=
  sound_append rows 661 Block043.before Block043.after Block044.after
    Block043.steps Block044.steps Block043.sound Block044.sound
theorem part043_045_wellFormed : ∀ e ∈ part043_045, WellFormed e :=
  wellFormed_append Block043.steps Block044.steps Block043.wellFormed Block044.wellFormed

def part046_048 : List Step := Block046.steps ++ Block047.steps
theorem part046_048_sound : ArrayBlockSound rows 661 Block046.before Block047.after part046_048 :=
  sound_append rows 661 Block046.before Block046.after Block047.after
    Block046.steps Block047.steps Block046.sound Block047.sound
theorem part046_048_wellFormed : ∀ e ∈ part046_048, WellFormed e :=
  wellFormed_append Block046.steps Block047.steps Block046.wellFormed Block047.wellFormed

def part045_048 : List Step := Block045.steps ++ part046_048
theorem part045_048_sound : ArrayBlockSound rows 661 Block045.before Block047.after part045_048 :=
  sound_append rows 661 Block045.before Block045.after Block047.after
    Block045.steps part046_048 Block045.sound part046_048_sound
theorem part045_048_wellFormed : ∀ e ∈ part045_048, WellFormed e :=
  wellFormed_append Block045.steps part046_048 Block045.wellFormed part046_048_wellFormed

def part043_048 : List Step := part043_045 ++ part045_048
theorem part043_048_sound : ArrayBlockSound rows 661 Block043.before Block047.after part043_048 :=
  sound_append rows 661 Block043.before Block044.after Block047.after
    part043_045 part045_048 part043_045_sound part045_048_sound
theorem part043_048_wellFormed : ∀ e ∈ part043_048, WellFormed e :=
  wellFormed_append part043_045 part045_048 part043_045_wellFormed part045_048_wellFormed

def part049_051 : List Step := Block049.steps ++ Block050.steps
theorem part049_051_sound : ArrayBlockSound rows 661 Block049.before Block050.after part049_051 :=
  sound_append rows 661 Block049.before Block049.after Block050.after
    Block049.steps Block050.steps Block049.sound Block050.sound
theorem part049_051_wellFormed : ∀ e ∈ part049_051, WellFormed e :=
  wellFormed_append Block049.steps Block050.steps Block049.wellFormed Block050.wellFormed

def part048_051 : List Step := Block048.steps ++ part049_051
theorem part048_051_sound : ArrayBlockSound rows 661 Block048.before Block050.after part048_051 :=
  sound_append rows 661 Block048.before Block048.after Block050.after
    Block048.steps part049_051 Block048.sound part049_051_sound
theorem part048_051_wellFormed : ∀ e ∈ part048_051, WellFormed e :=
  wellFormed_append Block048.steps part049_051 Block048.wellFormed part049_051_wellFormed

def part052_054 : List Step := Block052.steps ++ Block053.steps
theorem part052_054_sound : ArrayBlockSound rows 661 Block052.before Block053.after part052_054 :=
  sound_append rows 661 Block052.before Block052.after Block053.after
    Block052.steps Block053.steps Block052.sound Block053.sound
theorem part052_054_wellFormed : ∀ e ∈ part052_054, WellFormed e :=
  wellFormed_append Block052.steps Block053.steps Block052.wellFormed Block053.wellFormed

def part051_054 : List Step := Block051.steps ++ part052_054
theorem part051_054_sound : ArrayBlockSound rows 661 Block051.before Block053.after part051_054 :=
  sound_append rows 661 Block051.before Block051.after Block053.after
    Block051.steps part052_054 Block051.sound part052_054_sound
theorem part051_054_wellFormed : ∀ e ∈ part051_054, WellFormed e :=
  wellFormed_append Block051.steps part052_054 Block051.wellFormed part052_054_wellFormed

def part048_054 : List Step := part048_051 ++ part051_054
theorem part048_054_sound : ArrayBlockSound rows 661 Block048.before Block053.after part048_054 :=
  sound_append rows 661 Block048.before Block050.after Block053.after
    part048_051 part051_054 part048_051_sound part051_054_sound
theorem part048_054_wellFormed : ∀ e ∈ part048_054, WellFormed e :=
  wellFormed_append part048_051 part051_054 part048_051_wellFormed part051_054_wellFormed

def part043_054 : List Step := part043_048 ++ part048_054
theorem part043_054_sound : ArrayBlockSound rows 661 Block043.before Block053.after part043_054 :=
  sound_append rows 661 Block043.before Block047.after Block053.after
    part043_048 part048_054 part043_048_sound part048_054_sound
theorem part043_054_wellFormed : ∀ e ∈ part043_054, WellFormed e :=
  wellFormed_append part043_048 part048_054 part043_048_wellFormed part048_054_wellFormed

def part054_056 : List Step := Block054.steps ++ Block055.steps
theorem part054_056_sound : ArrayBlockSound rows 661 Block054.before Block055.after part054_056 :=
  sound_append rows 661 Block054.before Block054.after Block055.after
    Block054.steps Block055.steps Block054.sound Block055.sound
theorem part054_056_wellFormed : ∀ e ∈ part054_056, WellFormed e :=
  wellFormed_append Block054.steps Block055.steps Block054.wellFormed Block055.wellFormed

def part057_059 : List Step := Block057.steps ++ Block058.steps
theorem part057_059_sound : ArrayBlockSound rows 661 Block057.before Block058.after part057_059 :=
  sound_append rows 661 Block057.before Block057.after Block058.after
    Block057.steps Block058.steps Block057.sound Block058.sound
theorem part057_059_wellFormed : ∀ e ∈ part057_059, WellFormed e :=
  wellFormed_append Block057.steps Block058.steps Block057.wellFormed Block058.wellFormed

def part056_059 : List Step := Block056.steps ++ part057_059
theorem part056_059_sound : ArrayBlockSound rows 661 Block056.before Block058.after part056_059 :=
  sound_append rows 661 Block056.before Block056.after Block058.after
    Block056.steps part057_059 Block056.sound part057_059_sound
theorem part056_059_wellFormed : ∀ e ∈ part056_059, WellFormed e :=
  wellFormed_append Block056.steps part057_059 Block056.wellFormed part057_059_wellFormed

def part054_059 : List Step := part054_056 ++ part056_059
theorem part054_059_sound : ArrayBlockSound rows 661 Block054.before Block058.after part054_059 :=
  sound_append rows 661 Block054.before Block055.after Block058.after
    part054_056 part056_059 part054_056_sound part056_059_sound
theorem part054_059_wellFormed : ∀ e ∈ part054_059, WellFormed e :=
  wellFormed_append part054_056 part056_059 part054_056_wellFormed part056_059_wellFormed

def part060_062 : List Step := Block060.steps ++ Block061.steps
theorem part060_062_sound : ArrayBlockSound rows 661 Block060.before Block061.after part060_062 :=
  sound_append rows 661 Block060.before Block060.after Block061.after
    Block060.steps Block061.steps Block060.sound Block061.sound
theorem part060_062_wellFormed : ∀ e ∈ part060_062, WellFormed e :=
  wellFormed_append Block060.steps Block061.steps Block060.wellFormed Block061.wellFormed

def part059_062 : List Step := Block059.steps ++ part060_062
theorem part059_062_sound : ArrayBlockSound rows 661 Block059.before Block061.after part059_062 :=
  sound_append rows 661 Block059.before Block059.after Block061.after
    Block059.steps part060_062 Block059.sound part060_062_sound
theorem part059_062_wellFormed : ∀ e ∈ part059_062, WellFormed e :=
  wellFormed_append Block059.steps part060_062 Block059.wellFormed part060_062_wellFormed

def part063_065 : List Step := Block063.steps ++ Block064.steps
theorem part063_065_sound : ArrayBlockSound rows 661 Block063.before Block064.after part063_065 :=
  sound_append rows 661 Block063.before Block063.after Block064.after
    Block063.steps Block064.steps Block063.sound Block064.sound
theorem part063_065_wellFormed : ∀ e ∈ part063_065, WellFormed e :=
  wellFormed_append Block063.steps Block064.steps Block063.wellFormed Block064.wellFormed

def part062_065 : List Step := Block062.steps ++ part063_065
theorem part062_065_sound : ArrayBlockSound rows 661 Block062.before Block064.after part062_065 :=
  sound_append rows 661 Block062.before Block062.after Block064.after
    Block062.steps part063_065 Block062.sound part063_065_sound
theorem part062_065_wellFormed : ∀ e ∈ part062_065, WellFormed e :=
  wellFormed_append Block062.steps part063_065 Block062.wellFormed part063_065_wellFormed

def part059_065 : List Step := part059_062 ++ part062_065
theorem part059_065_sound : ArrayBlockSound rows 661 Block059.before Block064.after part059_065 :=
  sound_append rows 661 Block059.before Block061.after Block064.after
    part059_062 part062_065 part059_062_sound part062_065_sound
theorem part059_065_wellFormed : ∀ e ∈ part059_065, WellFormed e :=
  wellFormed_append part059_062 part062_065 part059_062_wellFormed part062_065_wellFormed

def part054_065 : List Step := part054_059 ++ part059_065
theorem part054_065_sound : ArrayBlockSound rows 661 Block054.before Block064.after part054_065 :=
  sound_append rows 661 Block054.before Block058.after Block064.after
    part054_059 part059_065 part054_059_sound part059_065_sound
theorem part054_065_wellFormed : ∀ e ∈ part054_065, WellFormed e :=
  wellFormed_append part054_059 part059_065 part054_059_wellFormed part059_065_wellFormed

def part043_065 : List Step := part043_054 ++ part054_065
theorem part043_065_sound : ArrayBlockSound rows 661 Block043.before Block064.after part043_065 :=
  sound_append rows 661 Block043.before Block053.after Block064.after
    part043_054 part054_065 part043_054_sound part054_065_sound
theorem part043_065_wellFormed : ∀ e ∈ part043_065, WellFormed e :=
  wellFormed_append part043_054 part054_065 part043_054_wellFormed part054_065_wellFormed

def part065_067 : List Step := Block065.steps ++ Block066.steps
theorem part065_067_sound : ArrayBlockSound rows 661 Block065.before Block066.after part065_067 :=
  sound_append rows 661 Block065.before Block065.after Block066.after
    Block065.steps Block066.steps Block065.sound Block066.sound
theorem part065_067_wellFormed : ∀ e ∈ part065_067, WellFormed e :=
  wellFormed_append Block065.steps Block066.steps Block065.wellFormed Block066.wellFormed

def part068_070 : List Step := Block068.steps ++ Block069.steps
theorem part068_070_sound : ArrayBlockSound rows 661 Block068.before Block069.after part068_070 :=
  sound_append rows 661 Block068.before Block068.after Block069.after
    Block068.steps Block069.steps Block068.sound Block069.sound
theorem part068_070_wellFormed : ∀ e ∈ part068_070, WellFormed e :=
  wellFormed_append Block068.steps Block069.steps Block068.wellFormed Block069.wellFormed

def part067_070 : List Step := Block067.steps ++ part068_070
theorem part067_070_sound : ArrayBlockSound rows 661 Block067.before Block069.after part067_070 :=
  sound_append rows 661 Block067.before Block067.after Block069.after
    Block067.steps part068_070 Block067.sound part068_070_sound
theorem part067_070_wellFormed : ∀ e ∈ part067_070, WellFormed e :=
  wellFormed_append Block067.steps part068_070 Block067.wellFormed part068_070_wellFormed

def part065_070 : List Step := part065_067 ++ part067_070
theorem part065_070_sound : ArrayBlockSound rows 661 Block065.before Block069.after part065_070 :=
  sound_append rows 661 Block065.before Block066.after Block069.after
    part065_067 part067_070 part065_067_sound part067_070_sound
theorem part065_070_wellFormed : ∀ e ∈ part065_070, WellFormed e :=
  wellFormed_append part065_067 part067_070 part065_067_wellFormed part067_070_wellFormed

def part071_073 : List Step := Block071.steps ++ Block072.steps
theorem part071_073_sound : ArrayBlockSound rows 661 Block071.before Block072.after part071_073 :=
  sound_append rows 661 Block071.before Block071.after Block072.after
    Block071.steps Block072.steps Block071.sound Block072.sound
theorem part071_073_wellFormed : ∀ e ∈ part071_073, WellFormed e :=
  wellFormed_append Block071.steps Block072.steps Block071.wellFormed Block072.wellFormed

def part070_073 : List Step := Block070.steps ++ part071_073
theorem part070_073_sound : ArrayBlockSound rows 661 Block070.before Block072.after part070_073 :=
  sound_append rows 661 Block070.before Block070.after Block072.after
    Block070.steps part071_073 Block070.sound part071_073_sound
theorem part070_073_wellFormed : ∀ e ∈ part070_073, WellFormed e :=
  wellFormed_append Block070.steps part071_073 Block070.wellFormed part071_073_wellFormed

def part074_076 : List Step := Block074.steps ++ Block075.steps
theorem part074_076_sound : ArrayBlockSound rows 661 Block074.before Block075.after part074_076 :=
  sound_append rows 661 Block074.before Block074.after Block075.after
    Block074.steps Block075.steps Block074.sound Block075.sound
theorem part074_076_wellFormed : ∀ e ∈ part074_076, WellFormed e :=
  wellFormed_append Block074.steps Block075.steps Block074.wellFormed Block075.wellFormed

def part073_076 : List Step := Block073.steps ++ part074_076
theorem part073_076_sound : ArrayBlockSound rows 661 Block073.before Block075.after part073_076 :=
  sound_append rows 661 Block073.before Block073.after Block075.after
    Block073.steps part074_076 Block073.sound part074_076_sound
theorem part073_076_wellFormed : ∀ e ∈ part073_076, WellFormed e :=
  wellFormed_append Block073.steps part074_076 Block073.wellFormed part074_076_wellFormed

def part070_076 : List Step := part070_073 ++ part073_076
theorem part070_076_sound : ArrayBlockSound rows 661 Block070.before Block075.after part070_076 :=
  sound_append rows 661 Block070.before Block072.after Block075.after
    part070_073 part073_076 part070_073_sound part073_076_sound
theorem part070_076_wellFormed : ∀ e ∈ part070_076, WellFormed e :=
  wellFormed_append part070_073 part073_076 part070_073_wellFormed part073_076_wellFormed

def part065_076 : List Step := part065_070 ++ part070_076
theorem part065_076_sound : ArrayBlockSound rows 661 Block065.before Block075.after part065_076 :=
  sound_append rows 661 Block065.before Block069.after Block075.after
    part065_070 part070_076 part065_070_sound part070_076_sound
theorem part065_076_wellFormed : ∀ e ∈ part065_076, WellFormed e :=
  wellFormed_append part065_070 part070_076 part065_070_wellFormed part070_076_wellFormed

def part076_078 : List Step := Block076.steps ++ Block077.steps
theorem part076_078_sound : ArrayBlockSound rows 661 Block076.before Block077.after part076_078 :=
  sound_append rows 661 Block076.before Block076.after Block077.after
    Block076.steps Block077.steps Block076.sound Block077.sound
theorem part076_078_wellFormed : ∀ e ∈ part076_078, WellFormed e :=
  wellFormed_append Block076.steps Block077.steps Block076.wellFormed Block077.wellFormed

def part079_081 : List Step := Block079.steps ++ Block080.steps
theorem part079_081_sound : ArrayBlockSound rows 661 Block079.before Block080.after part079_081 :=
  sound_append rows 661 Block079.before Block079.after Block080.after
    Block079.steps Block080.steps Block079.sound Block080.sound
theorem part079_081_wellFormed : ∀ e ∈ part079_081, WellFormed e :=
  wellFormed_append Block079.steps Block080.steps Block079.wellFormed Block080.wellFormed

def part078_081 : List Step := Block078.steps ++ part079_081
theorem part078_081_sound : ArrayBlockSound rows 661 Block078.before Block080.after part078_081 :=
  sound_append rows 661 Block078.before Block078.after Block080.after
    Block078.steps part079_081 Block078.sound part079_081_sound
theorem part078_081_wellFormed : ∀ e ∈ part078_081, WellFormed e :=
  wellFormed_append Block078.steps part079_081 Block078.wellFormed part079_081_wellFormed

def part076_081 : List Step := part076_078 ++ part078_081
theorem part076_081_sound : ArrayBlockSound rows 661 Block076.before Block080.after part076_081 :=
  sound_append rows 661 Block076.before Block077.after Block080.after
    part076_078 part078_081 part076_078_sound part078_081_sound
theorem part076_081_wellFormed : ∀ e ∈ part076_081, WellFormed e :=
  wellFormed_append part076_078 part078_081 part076_078_wellFormed part078_081_wellFormed

def part082_084 : List Step := Block082.steps ++ Block083.steps
theorem part082_084_sound : ArrayBlockSound rows 661 Block082.before Block083.after part082_084 :=
  sound_append rows 661 Block082.before Block082.after Block083.after
    Block082.steps Block083.steps Block082.sound Block083.sound
theorem part082_084_wellFormed : ∀ e ∈ part082_084, WellFormed e :=
  wellFormed_append Block082.steps Block083.steps Block082.wellFormed Block083.wellFormed

def part081_084 : List Step := Block081.steps ++ part082_084
theorem part081_084_sound : ArrayBlockSound rows 661 Block081.before Block083.after part081_084 :=
  sound_append rows 661 Block081.before Block081.after Block083.after
    Block081.steps part082_084 Block081.sound part082_084_sound
theorem part081_084_wellFormed : ∀ e ∈ part081_084, WellFormed e :=
  wellFormed_append Block081.steps part082_084 Block081.wellFormed part082_084_wellFormed

def part085_087 : List Step := Block085.steps ++ Block086.steps
theorem part085_087_sound : ArrayBlockSound rows 661 Block085.before Block086.after part085_087 :=
  sound_append rows 661 Block085.before Block085.after Block086.after
    Block085.steps Block086.steps Block085.sound Block086.sound
theorem part085_087_wellFormed : ∀ e ∈ part085_087, WellFormed e :=
  wellFormed_append Block085.steps Block086.steps Block085.wellFormed Block086.wellFormed

def part084_087 : List Step := Block084.steps ++ part085_087
theorem part084_087_sound : ArrayBlockSound rows 661 Block084.before Block086.after part084_087 :=
  sound_append rows 661 Block084.before Block084.after Block086.after
    Block084.steps part085_087 Block084.sound part085_087_sound
theorem part084_087_wellFormed : ∀ e ∈ part084_087, WellFormed e :=
  wellFormed_append Block084.steps part085_087 Block084.wellFormed part085_087_wellFormed

def part081_087 : List Step := part081_084 ++ part084_087
theorem part081_087_sound : ArrayBlockSound rows 661 Block081.before Block086.after part081_087 :=
  sound_append rows 661 Block081.before Block083.after Block086.after
    part081_084 part084_087 part081_084_sound part084_087_sound
theorem part081_087_wellFormed : ∀ e ∈ part081_087, WellFormed e :=
  wellFormed_append part081_084 part084_087 part081_084_wellFormed part084_087_wellFormed

def part076_087 : List Step := part076_081 ++ part081_087
theorem part076_087_sound : ArrayBlockSound rows 661 Block076.before Block086.after part076_087 :=
  sound_append rows 661 Block076.before Block080.after Block086.after
    part076_081 part081_087 part076_081_sound part081_087_sound
theorem part076_087_wellFormed : ∀ e ∈ part076_087, WellFormed e :=
  wellFormed_append part076_081 part081_087 part076_081_wellFormed part081_087_wellFormed

def part065_087 : List Step := part065_076 ++ part076_087
theorem part065_087_sound : ArrayBlockSound rows 661 Block065.before Block086.after part065_087 :=
  sound_append rows 661 Block065.before Block075.after Block086.after
    part065_076 part076_087 part065_076_sound part076_087_sound
theorem part065_087_wellFormed : ∀ e ∈ part065_087, WellFormed e :=
  wellFormed_append part065_076 part076_087 part065_076_wellFormed part076_087_wellFormed

def part043_087 : List Step := part043_065 ++ part065_087
theorem part043_087_sound : ArrayBlockSound rows 661 Block043.before Block086.after part043_087 :=
  sound_append rows 661 Block043.before Block064.after Block086.after
    part043_065 part065_087 part043_065_sound part065_087_sound
theorem part043_087_wellFormed : ∀ e ∈ part043_087, WellFormed e :=
  wellFormed_append part043_065 part065_087 part043_065_wellFormed part065_087_wellFormed

def part000_087 : List Step := part000_043 ++ part043_087
theorem part000_087_sound : ArrayBlockSound rows 661 Block000.before Block086.after part000_087 :=
  sound_append rows 661 Block000.before Block042.after Block086.after
    part000_043 part043_087 part000_043_sound part043_087_sound
theorem part000_087_wellFormed : ∀ e ∈ part000_087, WellFormed e :=
  wellFormed_append part000_043 part043_087 part000_043_wellFormed part043_087_wellFormed

def part087_089 : List Step := Block087.steps ++ Block088.steps
theorem part087_089_sound : ArrayBlockSound rows 661 Block087.before Block088.after part087_089 :=
  sound_append rows 661 Block087.before Block087.after Block088.after
    Block087.steps Block088.steps Block087.sound Block088.sound
theorem part087_089_wellFormed : ∀ e ∈ part087_089, WellFormed e :=
  wellFormed_append Block087.steps Block088.steps Block087.wellFormed Block088.wellFormed

def part090_092 : List Step := Block090.steps ++ Block091.steps
theorem part090_092_sound : ArrayBlockSound rows 661 Block090.before Block091.after part090_092 :=
  sound_append rows 661 Block090.before Block090.after Block091.after
    Block090.steps Block091.steps Block090.sound Block091.sound
theorem part090_092_wellFormed : ∀ e ∈ part090_092, WellFormed e :=
  wellFormed_append Block090.steps Block091.steps Block090.wellFormed Block091.wellFormed

def part089_092 : List Step := Block089.steps ++ part090_092
theorem part089_092_sound : ArrayBlockSound rows 661 Block089.before Block091.after part089_092 :=
  sound_append rows 661 Block089.before Block089.after Block091.after
    Block089.steps part090_092 Block089.sound part090_092_sound
theorem part089_092_wellFormed : ∀ e ∈ part089_092, WellFormed e :=
  wellFormed_append Block089.steps part090_092 Block089.wellFormed part090_092_wellFormed

def part087_092 : List Step := part087_089 ++ part089_092
theorem part087_092_sound : ArrayBlockSound rows 661 Block087.before Block091.after part087_092 :=
  sound_append rows 661 Block087.before Block088.after Block091.after
    part087_089 part089_092 part087_089_sound part089_092_sound
theorem part087_092_wellFormed : ∀ e ∈ part087_092, WellFormed e :=
  wellFormed_append part087_089 part089_092 part087_089_wellFormed part089_092_wellFormed

def part093_095 : List Step := Block093.steps ++ Block094.steps
theorem part093_095_sound : ArrayBlockSound rows 661 Block093.before Block094.after part093_095 :=
  sound_append rows 661 Block093.before Block093.after Block094.after
    Block093.steps Block094.steps Block093.sound Block094.sound
theorem part093_095_wellFormed : ∀ e ∈ part093_095, WellFormed e :=
  wellFormed_append Block093.steps Block094.steps Block093.wellFormed Block094.wellFormed

def part092_095 : List Step := Block092.steps ++ part093_095
theorem part092_095_sound : ArrayBlockSound rows 661 Block092.before Block094.after part092_095 :=
  sound_append rows 661 Block092.before Block092.after Block094.after
    Block092.steps part093_095 Block092.sound part093_095_sound
theorem part092_095_wellFormed : ∀ e ∈ part092_095, WellFormed e :=
  wellFormed_append Block092.steps part093_095 Block092.wellFormed part093_095_wellFormed

def part096_098 : List Step := Block096.steps ++ Block097.steps
theorem part096_098_sound : ArrayBlockSound rows 661 Block096.before Block097.after part096_098 :=
  sound_append rows 661 Block096.before Block096.after Block097.after
    Block096.steps Block097.steps Block096.sound Block097.sound
theorem part096_098_wellFormed : ∀ e ∈ part096_098, WellFormed e :=
  wellFormed_append Block096.steps Block097.steps Block096.wellFormed Block097.wellFormed

def part095_098 : List Step := Block095.steps ++ part096_098
theorem part095_098_sound : ArrayBlockSound rows 661 Block095.before Block097.after part095_098 :=
  sound_append rows 661 Block095.before Block095.after Block097.after
    Block095.steps part096_098 Block095.sound part096_098_sound
theorem part095_098_wellFormed : ∀ e ∈ part095_098, WellFormed e :=
  wellFormed_append Block095.steps part096_098 Block095.wellFormed part096_098_wellFormed

def part092_098 : List Step := part092_095 ++ part095_098
theorem part092_098_sound : ArrayBlockSound rows 661 Block092.before Block097.after part092_098 :=
  sound_append rows 661 Block092.before Block094.after Block097.after
    part092_095 part095_098 part092_095_sound part095_098_sound
theorem part092_098_wellFormed : ∀ e ∈ part092_098, WellFormed e :=
  wellFormed_append part092_095 part095_098 part092_095_wellFormed part095_098_wellFormed

def part087_098 : List Step := part087_092 ++ part092_098
theorem part087_098_sound : ArrayBlockSound rows 661 Block087.before Block097.after part087_098 :=
  sound_append rows 661 Block087.before Block091.after Block097.after
    part087_092 part092_098 part087_092_sound part092_098_sound
theorem part087_098_wellFormed : ∀ e ∈ part087_098, WellFormed e :=
  wellFormed_append part087_092 part092_098 part087_092_wellFormed part092_098_wellFormed

def part098_100 : List Step := Block098.steps ++ Block099.steps
theorem part098_100_sound : ArrayBlockSound rows 661 Block098.before Block099.after part098_100 :=
  sound_append rows 661 Block098.before Block098.after Block099.after
    Block098.steps Block099.steps Block098.sound Block099.sound
theorem part098_100_wellFormed : ∀ e ∈ part098_100, WellFormed e :=
  wellFormed_append Block098.steps Block099.steps Block098.wellFormed Block099.wellFormed

def part101_103 : List Step := Block101.steps ++ Block102.steps
theorem part101_103_sound : ArrayBlockSound rows 661 Block101.before Block102.after part101_103 :=
  sound_append rows 661 Block101.before Block101.after Block102.after
    Block101.steps Block102.steps Block101.sound Block102.sound
theorem part101_103_wellFormed : ∀ e ∈ part101_103, WellFormed e :=
  wellFormed_append Block101.steps Block102.steps Block101.wellFormed Block102.wellFormed

def part100_103 : List Step := Block100.steps ++ part101_103
theorem part100_103_sound : ArrayBlockSound rows 661 Block100.before Block102.after part100_103 :=
  sound_append rows 661 Block100.before Block100.after Block102.after
    Block100.steps part101_103 Block100.sound part101_103_sound
theorem part100_103_wellFormed : ∀ e ∈ part100_103, WellFormed e :=
  wellFormed_append Block100.steps part101_103 Block100.wellFormed part101_103_wellFormed

def part098_103 : List Step := part098_100 ++ part100_103
theorem part098_103_sound : ArrayBlockSound rows 661 Block098.before Block102.after part098_103 :=
  sound_append rows 661 Block098.before Block099.after Block102.after
    part098_100 part100_103 part098_100_sound part100_103_sound
theorem part098_103_wellFormed : ∀ e ∈ part098_103, WellFormed e :=
  wellFormed_append part098_100 part100_103 part098_100_wellFormed part100_103_wellFormed

def part104_106 : List Step := Block104.steps ++ Block105.steps
theorem part104_106_sound : ArrayBlockSound rows 661 Block104.before Block105.after part104_106 :=
  sound_append rows 661 Block104.before Block104.after Block105.after
    Block104.steps Block105.steps Block104.sound Block105.sound
theorem part104_106_wellFormed : ∀ e ∈ part104_106, WellFormed e :=
  wellFormed_append Block104.steps Block105.steps Block104.wellFormed Block105.wellFormed

def part103_106 : List Step := Block103.steps ++ part104_106
theorem part103_106_sound : ArrayBlockSound rows 661 Block103.before Block105.after part103_106 :=
  sound_append rows 661 Block103.before Block103.after Block105.after
    Block103.steps part104_106 Block103.sound part104_106_sound
theorem part103_106_wellFormed : ∀ e ∈ part103_106, WellFormed e :=
  wellFormed_append Block103.steps part104_106 Block103.wellFormed part104_106_wellFormed

def part107_109 : List Step := Block107.steps ++ Block108.steps
theorem part107_109_sound : ArrayBlockSound rows 661 Block107.before Block108.after part107_109 :=
  sound_append rows 661 Block107.before Block107.after Block108.after
    Block107.steps Block108.steps Block107.sound Block108.sound
theorem part107_109_wellFormed : ∀ e ∈ part107_109, WellFormed e :=
  wellFormed_append Block107.steps Block108.steps Block107.wellFormed Block108.wellFormed

def part106_109 : List Step := Block106.steps ++ part107_109
theorem part106_109_sound : ArrayBlockSound rows 661 Block106.before Block108.after part106_109 :=
  sound_append rows 661 Block106.before Block106.after Block108.after
    Block106.steps part107_109 Block106.sound part107_109_sound
theorem part106_109_wellFormed : ∀ e ∈ part106_109, WellFormed e :=
  wellFormed_append Block106.steps part107_109 Block106.wellFormed part107_109_wellFormed

def part103_109 : List Step := part103_106 ++ part106_109
theorem part103_109_sound : ArrayBlockSound rows 661 Block103.before Block108.after part103_109 :=
  sound_append rows 661 Block103.before Block105.after Block108.after
    part103_106 part106_109 part103_106_sound part106_109_sound
theorem part103_109_wellFormed : ∀ e ∈ part103_109, WellFormed e :=
  wellFormed_append part103_106 part106_109 part103_106_wellFormed part106_109_wellFormed

def part098_109 : List Step := part098_103 ++ part103_109
theorem part098_109_sound : ArrayBlockSound rows 661 Block098.before Block108.after part098_109 :=
  sound_append rows 661 Block098.before Block102.after Block108.after
    part098_103 part103_109 part098_103_sound part103_109_sound
theorem part098_109_wellFormed : ∀ e ∈ part098_109, WellFormed e :=
  wellFormed_append part098_103 part103_109 part098_103_wellFormed part103_109_wellFormed

def part087_109 : List Step := part087_098 ++ part098_109
theorem part087_109_sound : ArrayBlockSound rows 661 Block087.before Block108.after part087_109 :=
  sound_append rows 661 Block087.before Block097.after Block108.after
    part087_098 part098_109 part087_098_sound part098_109_sound
theorem part087_109_wellFormed : ∀ e ∈ part087_109, WellFormed e :=
  wellFormed_append part087_098 part098_109 part087_098_wellFormed part098_109_wellFormed

def part109_111 : List Step := Block109.steps ++ Block110.steps
theorem part109_111_sound : ArrayBlockSound rows 661 Block109.before Block110.after part109_111 :=
  sound_append rows 661 Block109.before Block109.after Block110.after
    Block109.steps Block110.steps Block109.sound Block110.sound
theorem part109_111_wellFormed : ∀ e ∈ part109_111, WellFormed e :=
  wellFormed_append Block109.steps Block110.steps Block109.wellFormed Block110.wellFormed

def part112_114 : List Step := Block112.steps ++ Block113.steps
theorem part112_114_sound : ArrayBlockSound rows 661 Block112.before Block113.after part112_114 :=
  sound_append rows 661 Block112.before Block112.after Block113.after
    Block112.steps Block113.steps Block112.sound Block113.sound
theorem part112_114_wellFormed : ∀ e ∈ part112_114, WellFormed e :=
  wellFormed_append Block112.steps Block113.steps Block112.wellFormed Block113.wellFormed

def part111_114 : List Step := Block111.steps ++ part112_114
theorem part111_114_sound : ArrayBlockSound rows 661 Block111.before Block113.after part111_114 :=
  sound_append rows 661 Block111.before Block111.after Block113.after
    Block111.steps part112_114 Block111.sound part112_114_sound
theorem part111_114_wellFormed : ∀ e ∈ part111_114, WellFormed e :=
  wellFormed_append Block111.steps part112_114 Block111.wellFormed part112_114_wellFormed

def part109_114 : List Step := part109_111 ++ part111_114
theorem part109_114_sound : ArrayBlockSound rows 661 Block109.before Block113.after part109_114 :=
  sound_append rows 661 Block109.before Block110.after Block113.after
    part109_111 part111_114 part109_111_sound part111_114_sound
theorem part109_114_wellFormed : ∀ e ∈ part109_114, WellFormed e :=
  wellFormed_append part109_111 part111_114 part109_111_wellFormed part111_114_wellFormed

def part115_117 : List Step := Block115.steps ++ Block116.steps
theorem part115_117_sound : ArrayBlockSound rows 661 Block115.before Block116.after part115_117 :=
  sound_append rows 661 Block115.before Block115.after Block116.after
    Block115.steps Block116.steps Block115.sound Block116.sound
theorem part115_117_wellFormed : ∀ e ∈ part115_117, WellFormed e :=
  wellFormed_append Block115.steps Block116.steps Block115.wellFormed Block116.wellFormed

def part114_117 : List Step := Block114.steps ++ part115_117
theorem part114_117_sound : ArrayBlockSound rows 661 Block114.before Block116.after part114_117 :=
  sound_append rows 661 Block114.before Block114.after Block116.after
    Block114.steps part115_117 Block114.sound part115_117_sound
theorem part114_117_wellFormed : ∀ e ∈ part114_117, WellFormed e :=
  wellFormed_append Block114.steps part115_117 Block114.wellFormed part115_117_wellFormed

def part118_120 : List Step := Block118.steps ++ Block119.steps
theorem part118_120_sound : ArrayBlockSound rows 661 Block118.before Block119.after part118_120 :=
  sound_append rows 661 Block118.before Block118.after Block119.after
    Block118.steps Block119.steps Block118.sound Block119.sound
theorem part118_120_wellFormed : ∀ e ∈ part118_120, WellFormed e :=
  wellFormed_append Block118.steps Block119.steps Block118.wellFormed Block119.wellFormed

def part117_120 : List Step := Block117.steps ++ part118_120
theorem part117_120_sound : ArrayBlockSound rows 661 Block117.before Block119.after part117_120 :=
  sound_append rows 661 Block117.before Block117.after Block119.after
    Block117.steps part118_120 Block117.sound part118_120_sound
theorem part117_120_wellFormed : ∀ e ∈ part117_120, WellFormed e :=
  wellFormed_append Block117.steps part118_120 Block117.wellFormed part118_120_wellFormed

def part114_120 : List Step := part114_117 ++ part117_120
theorem part114_120_sound : ArrayBlockSound rows 661 Block114.before Block119.after part114_120 :=
  sound_append rows 661 Block114.before Block116.after Block119.after
    part114_117 part117_120 part114_117_sound part117_120_sound
theorem part114_120_wellFormed : ∀ e ∈ part114_120, WellFormed e :=
  wellFormed_append part114_117 part117_120 part114_117_wellFormed part117_120_wellFormed

def part109_120 : List Step := part109_114 ++ part114_120
theorem part109_120_sound : ArrayBlockSound rows 661 Block109.before Block119.after part109_120 :=
  sound_append rows 661 Block109.before Block113.after Block119.after
    part109_114 part114_120 part109_114_sound part114_120_sound
theorem part109_120_wellFormed : ∀ e ∈ part109_120, WellFormed e :=
  wellFormed_append part109_114 part114_120 part109_114_wellFormed part114_120_wellFormed

def part120_122 : List Step := Block120.steps ++ Block121.steps
theorem part120_122_sound : ArrayBlockSound rows 661 Block120.before Block121.after part120_122 :=
  sound_append rows 661 Block120.before Block120.after Block121.after
    Block120.steps Block121.steps Block120.sound Block121.sound
theorem part120_122_wellFormed : ∀ e ∈ part120_122, WellFormed e :=
  wellFormed_append Block120.steps Block121.steps Block120.wellFormed Block121.wellFormed

def part123_125 : List Step := Block123.steps ++ Block124.steps
theorem part123_125_sound : ArrayBlockSound rows 661 Block123.before Block124.after part123_125 :=
  sound_append rows 661 Block123.before Block123.after Block124.after
    Block123.steps Block124.steps Block123.sound Block124.sound
theorem part123_125_wellFormed : ∀ e ∈ part123_125, WellFormed e :=
  wellFormed_append Block123.steps Block124.steps Block123.wellFormed Block124.wellFormed

def part122_125 : List Step := Block122.steps ++ part123_125
theorem part122_125_sound : ArrayBlockSound rows 661 Block122.before Block124.after part122_125 :=
  sound_append rows 661 Block122.before Block122.after Block124.after
    Block122.steps part123_125 Block122.sound part123_125_sound
theorem part122_125_wellFormed : ∀ e ∈ part122_125, WellFormed e :=
  wellFormed_append Block122.steps part123_125 Block122.wellFormed part123_125_wellFormed

def part120_125 : List Step := part120_122 ++ part122_125
theorem part120_125_sound : ArrayBlockSound rows 661 Block120.before Block124.after part120_125 :=
  sound_append rows 661 Block120.before Block121.after Block124.after
    part120_122 part122_125 part120_122_sound part122_125_sound
theorem part120_125_wellFormed : ∀ e ∈ part120_125, WellFormed e :=
  wellFormed_append part120_122 part122_125 part120_122_wellFormed part122_125_wellFormed

def part126_128 : List Step := Block126.steps ++ Block127.steps
theorem part126_128_sound : ArrayBlockSound rows 661 Block126.before Block127.after part126_128 :=
  sound_append rows 661 Block126.before Block126.after Block127.after
    Block126.steps Block127.steps Block126.sound Block127.sound
theorem part126_128_wellFormed : ∀ e ∈ part126_128, WellFormed e :=
  wellFormed_append Block126.steps Block127.steps Block126.wellFormed Block127.wellFormed

def part125_128 : List Step := Block125.steps ++ part126_128
theorem part125_128_sound : ArrayBlockSound rows 661 Block125.before Block127.after part125_128 :=
  sound_append rows 661 Block125.before Block125.after Block127.after
    Block125.steps part126_128 Block125.sound part126_128_sound
theorem part125_128_wellFormed : ∀ e ∈ part125_128, WellFormed e :=
  wellFormed_append Block125.steps part126_128 Block125.wellFormed part126_128_wellFormed

def part129_131 : List Step := Block129.steps ++ Block130.steps
theorem part129_131_sound : ArrayBlockSound rows 661 Block129.before Block130.after part129_131 :=
  sound_append rows 661 Block129.before Block129.after Block130.after
    Block129.steps Block130.steps Block129.sound Block130.sound
theorem part129_131_wellFormed : ∀ e ∈ part129_131, WellFormed e :=
  wellFormed_append Block129.steps Block130.steps Block129.wellFormed Block130.wellFormed

def part128_131 : List Step := Block128.steps ++ part129_131
theorem part128_131_sound : ArrayBlockSound rows 661 Block128.before Block130.after part128_131 :=
  sound_append rows 661 Block128.before Block128.after Block130.after
    Block128.steps part129_131 Block128.sound part129_131_sound
theorem part128_131_wellFormed : ∀ e ∈ part128_131, WellFormed e :=
  wellFormed_append Block128.steps part129_131 Block128.wellFormed part129_131_wellFormed

def part125_131 : List Step := part125_128 ++ part128_131
theorem part125_131_sound : ArrayBlockSound rows 661 Block125.before Block130.after part125_131 :=
  sound_append rows 661 Block125.before Block127.after Block130.after
    part125_128 part128_131 part125_128_sound part128_131_sound
theorem part125_131_wellFormed : ∀ e ∈ part125_131, WellFormed e :=
  wellFormed_append part125_128 part128_131 part125_128_wellFormed part128_131_wellFormed

def part120_131 : List Step := part120_125 ++ part125_131
theorem part120_131_sound : ArrayBlockSound rows 661 Block120.before Block130.after part120_131 :=
  sound_append rows 661 Block120.before Block124.after Block130.after
    part120_125 part125_131 part120_125_sound part125_131_sound
theorem part120_131_wellFormed : ∀ e ∈ part120_131, WellFormed e :=
  wellFormed_append part120_125 part125_131 part120_125_wellFormed part125_131_wellFormed

def part109_131 : List Step := part109_120 ++ part120_131
theorem part109_131_sound : ArrayBlockSound rows 661 Block109.before Block130.after part109_131 :=
  sound_append rows 661 Block109.before Block119.after Block130.after
    part109_120 part120_131 part109_120_sound part120_131_sound
theorem part109_131_wellFormed : ∀ e ∈ part109_131, WellFormed e :=
  wellFormed_append part109_120 part120_131 part109_120_wellFormed part120_131_wellFormed

def part087_131 : List Step := part087_109 ++ part109_131
theorem part087_131_sound : ArrayBlockSound rows 661 Block087.before Block130.after part087_131 :=
  sound_append rows 661 Block087.before Block108.after Block130.after
    part087_109 part109_131 part087_109_sound part109_131_sound
theorem part087_131_wellFormed : ∀ e ∈ part087_131, WellFormed e :=
  wellFormed_append part087_109 part109_131 part087_109_wellFormed part109_131_wellFormed

def part131_133 : List Step := Block131.steps ++ Block132.steps
theorem part131_133_sound : ArrayBlockSound rows 661 Block131.before Block132.after part131_133 :=
  sound_append rows 661 Block131.before Block131.after Block132.after
    Block131.steps Block132.steps Block131.sound Block132.sound
theorem part131_133_wellFormed : ∀ e ∈ part131_133, WellFormed e :=
  wellFormed_append Block131.steps Block132.steps Block131.wellFormed Block132.wellFormed

def part134_136 : List Step := Block134.steps ++ Block135.steps
theorem part134_136_sound : ArrayBlockSound rows 661 Block134.before Block135.after part134_136 :=
  sound_append rows 661 Block134.before Block134.after Block135.after
    Block134.steps Block135.steps Block134.sound Block135.sound
theorem part134_136_wellFormed : ∀ e ∈ part134_136, WellFormed e :=
  wellFormed_append Block134.steps Block135.steps Block134.wellFormed Block135.wellFormed

def part133_136 : List Step := Block133.steps ++ part134_136
theorem part133_136_sound : ArrayBlockSound rows 661 Block133.before Block135.after part133_136 :=
  sound_append rows 661 Block133.before Block133.after Block135.after
    Block133.steps part134_136 Block133.sound part134_136_sound
theorem part133_136_wellFormed : ∀ e ∈ part133_136, WellFormed e :=
  wellFormed_append Block133.steps part134_136 Block133.wellFormed part134_136_wellFormed

def part131_136 : List Step := part131_133 ++ part133_136
theorem part131_136_sound : ArrayBlockSound rows 661 Block131.before Block135.after part131_136 :=
  sound_append rows 661 Block131.before Block132.after Block135.after
    part131_133 part133_136 part131_133_sound part133_136_sound
theorem part131_136_wellFormed : ∀ e ∈ part131_136, WellFormed e :=
  wellFormed_append part131_133 part133_136 part131_133_wellFormed part133_136_wellFormed

def part137_139 : List Step := Block137.steps ++ Block138.steps
theorem part137_139_sound : ArrayBlockSound rows 661 Block137.before Block138.after part137_139 :=
  sound_append rows 661 Block137.before Block137.after Block138.after
    Block137.steps Block138.steps Block137.sound Block138.sound
theorem part137_139_wellFormed : ∀ e ∈ part137_139, WellFormed e :=
  wellFormed_append Block137.steps Block138.steps Block137.wellFormed Block138.wellFormed

def part136_139 : List Step := Block136.steps ++ part137_139
theorem part136_139_sound : ArrayBlockSound rows 661 Block136.before Block138.after part136_139 :=
  sound_append rows 661 Block136.before Block136.after Block138.after
    Block136.steps part137_139 Block136.sound part137_139_sound
theorem part136_139_wellFormed : ∀ e ∈ part136_139, WellFormed e :=
  wellFormed_append Block136.steps part137_139 Block136.wellFormed part137_139_wellFormed

def part140_142 : List Step := Block140.steps ++ Block141.steps
theorem part140_142_sound : ArrayBlockSound rows 661 Block140.before Block141.after part140_142 :=
  sound_append rows 661 Block140.before Block140.after Block141.after
    Block140.steps Block141.steps Block140.sound Block141.sound
theorem part140_142_wellFormed : ∀ e ∈ part140_142, WellFormed e :=
  wellFormed_append Block140.steps Block141.steps Block140.wellFormed Block141.wellFormed

def part139_142 : List Step := Block139.steps ++ part140_142
theorem part139_142_sound : ArrayBlockSound rows 661 Block139.before Block141.after part139_142 :=
  sound_append rows 661 Block139.before Block139.after Block141.after
    Block139.steps part140_142 Block139.sound part140_142_sound
theorem part139_142_wellFormed : ∀ e ∈ part139_142, WellFormed e :=
  wellFormed_append Block139.steps part140_142 Block139.wellFormed part140_142_wellFormed

def part136_142 : List Step := part136_139 ++ part139_142
theorem part136_142_sound : ArrayBlockSound rows 661 Block136.before Block141.after part136_142 :=
  sound_append rows 661 Block136.before Block138.after Block141.after
    part136_139 part139_142 part136_139_sound part139_142_sound
theorem part136_142_wellFormed : ∀ e ∈ part136_142, WellFormed e :=
  wellFormed_append part136_139 part139_142 part136_139_wellFormed part139_142_wellFormed

def part131_142 : List Step := part131_136 ++ part136_142
theorem part131_142_sound : ArrayBlockSound rows 661 Block131.before Block141.after part131_142 :=
  sound_append rows 661 Block131.before Block135.after Block141.after
    part131_136 part136_142 part131_136_sound part136_142_sound
theorem part131_142_wellFormed : ∀ e ∈ part131_142, WellFormed e :=
  wellFormed_append part131_136 part136_142 part131_136_wellFormed part136_142_wellFormed

def part142_144 : List Step := Block142.steps ++ Block143.steps
theorem part142_144_sound : ArrayBlockSound rows 661 Block142.before Block143.after part142_144 :=
  sound_append rows 661 Block142.before Block142.after Block143.after
    Block142.steps Block143.steps Block142.sound Block143.sound
theorem part142_144_wellFormed : ∀ e ∈ part142_144, WellFormed e :=
  wellFormed_append Block142.steps Block143.steps Block142.wellFormed Block143.wellFormed

def part145_147 : List Step := Block145.steps ++ Block146.steps
theorem part145_147_sound : ArrayBlockSound rows 661 Block145.before Block146.after part145_147 :=
  sound_append rows 661 Block145.before Block145.after Block146.after
    Block145.steps Block146.steps Block145.sound Block146.sound
theorem part145_147_wellFormed : ∀ e ∈ part145_147, WellFormed e :=
  wellFormed_append Block145.steps Block146.steps Block145.wellFormed Block146.wellFormed

def part144_147 : List Step := Block144.steps ++ part145_147
theorem part144_147_sound : ArrayBlockSound rows 661 Block144.before Block146.after part144_147 :=
  sound_append rows 661 Block144.before Block144.after Block146.after
    Block144.steps part145_147 Block144.sound part145_147_sound
theorem part144_147_wellFormed : ∀ e ∈ part144_147, WellFormed e :=
  wellFormed_append Block144.steps part145_147 Block144.wellFormed part145_147_wellFormed

def part142_147 : List Step := part142_144 ++ part144_147
theorem part142_147_sound : ArrayBlockSound rows 661 Block142.before Block146.after part142_147 :=
  sound_append rows 661 Block142.before Block143.after Block146.after
    part142_144 part144_147 part142_144_sound part144_147_sound
theorem part142_147_wellFormed : ∀ e ∈ part142_147, WellFormed e :=
  wellFormed_append part142_144 part144_147 part142_144_wellFormed part144_147_wellFormed

def part148_150 : List Step := Block148.steps ++ Block149.steps
theorem part148_150_sound : ArrayBlockSound rows 661 Block148.before Block149.after part148_150 :=
  sound_append rows 661 Block148.before Block148.after Block149.after
    Block148.steps Block149.steps Block148.sound Block149.sound
theorem part148_150_wellFormed : ∀ e ∈ part148_150, WellFormed e :=
  wellFormed_append Block148.steps Block149.steps Block148.wellFormed Block149.wellFormed

def part147_150 : List Step := Block147.steps ++ part148_150
theorem part147_150_sound : ArrayBlockSound rows 661 Block147.before Block149.after part147_150 :=
  sound_append rows 661 Block147.before Block147.after Block149.after
    Block147.steps part148_150 Block147.sound part148_150_sound
theorem part147_150_wellFormed : ∀ e ∈ part147_150, WellFormed e :=
  wellFormed_append Block147.steps part148_150 Block147.wellFormed part148_150_wellFormed

def part151_153 : List Step := Block151.steps ++ Block152.steps
theorem part151_153_sound : ArrayBlockSound rows 661 Block151.before Block152.after part151_153 :=
  sound_append rows 661 Block151.before Block151.after Block152.after
    Block151.steps Block152.steps Block151.sound Block152.sound
theorem part151_153_wellFormed : ∀ e ∈ part151_153, WellFormed e :=
  wellFormed_append Block151.steps Block152.steps Block151.wellFormed Block152.wellFormed

def part150_153 : List Step := Block150.steps ++ part151_153
theorem part150_153_sound : ArrayBlockSound rows 661 Block150.before Block152.after part150_153 :=
  sound_append rows 661 Block150.before Block150.after Block152.after
    Block150.steps part151_153 Block150.sound part151_153_sound
theorem part150_153_wellFormed : ∀ e ∈ part150_153, WellFormed e :=
  wellFormed_append Block150.steps part151_153 Block150.wellFormed part151_153_wellFormed

def part147_153 : List Step := part147_150 ++ part150_153
theorem part147_153_sound : ArrayBlockSound rows 661 Block147.before Block152.after part147_153 :=
  sound_append rows 661 Block147.before Block149.after Block152.after
    part147_150 part150_153 part147_150_sound part150_153_sound
theorem part147_153_wellFormed : ∀ e ∈ part147_153, WellFormed e :=
  wellFormed_append part147_150 part150_153 part147_150_wellFormed part150_153_wellFormed

def part142_153 : List Step := part142_147 ++ part147_153
theorem part142_153_sound : ArrayBlockSound rows 661 Block142.before Block152.after part142_153 :=
  sound_append rows 661 Block142.before Block146.after Block152.after
    part142_147 part147_153 part142_147_sound part147_153_sound
theorem part142_153_wellFormed : ∀ e ∈ part142_153, WellFormed e :=
  wellFormed_append part142_147 part147_153 part142_147_wellFormed part147_153_wellFormed

def part131_153 : List Step := part131_142 ++ part142_153
theorem part131_153_sound : ArrayBlockSound rows 661 Block131.before Block152.after part131_153 :=
  sound_append rows 661 Block131.before Block141.after Block152.after
    part131_142 part142_153 part131_142_sound part142_153_sound
theorem part131_153_wellFormed : ∀ e ∈ part131_153, WellFormed e :=
  wellFormed_append part131_142 part142_153 part131_142_wellFormed part142_153_wellFormed

def part153_155 : List Step := Block153.steps ++ Block154.steps
theorem part153_155_sound : ArrayBlockSound rows 661 Block153.before Block154.after part153_155 :=
  sound_append rows 661 Block153.before Block153.after Block154.after
    Block153.steps Block154.steps Block153.sound Block154.sound
theorem part153_155_wellFormed : ∀ e ∈ part153_155, WellFormed e :=
  wellFormed_append Block153.steps Block154.steps Block153.wellFormed Block154.wellFormed

def part156_158 : List Step := Block156.steps ++ Block157.steps
theorem part156_158_sound : ArrayBlockSound rows 661 Block156.before Block157.after part156_158 :=
  sound_append rows 661 Block156.before Block156.after Block157.after
    Block156.steps Block157.steps Block156.sound Block157.sound
theorem part156_158_wellFormed : ∀ e ∈ part156_158, WellFormed e :=
  wellFormed_append Block156.steps Block157.steps Block156.wellFormed Block157.wellFormed

def part155_158 : List Step := Block155.steps ++ part156_158
theorem part155_158_sound : ArrayBlockSound rows 661 Block155.before Block157.after part155_158 :=
  sound_append rows 661 Block155.before Block155.after Block157.after
    Block155.steps part156_158 Block155.sound part156_158_sound
theorem part155_158_wellFormed : ∀ e ∈ part155_158, WellFormed e :=
  wellFormed_append Block155.steps part156_158 Block155.wellFormed part156_158_wellFormed

def part153_158 : List Step := part153_155 ++ part155_158
theorem part153_158_sound : ArrayBlockSound rows 661 Block153.before Block157.after part153_158 :=
  sound_append rows 661 Block153.before Block154.after Block157.after
    part153_155 part155_158 part153_155_sound part155_158_sound
theorem part153_158_wellFormed : ∀ e ∈ part153_158, WellFormed e :=
  wellFormed_append part153_155 part155_158 part153_155_wellFormed part155_158_wellFormed

def part159_161 : List Step := Block159.steps ++ Block160.steps
theorem part159_161_sound : ArrayBlockSound rows 661 Block159.before Block160.after part159_161 :=
  sound_append rows 661 Block159.before Block159.after Block160.after
    Block159.steps Block160.steps Block159.sound Block160.sound
theorem part159_161_wellFormed : ∀ e ∈ part159_161, WellFormed e :=
  wellFormed_append Block159.steps Block160.steps Block159.wellFormed Block160.wellFormed

def part158_161 : List Step := Block158.steps ++ part159_161
theorem part158_161_sound : ArrayBlockSound rows 661 Block158.before Block160.after part158_161 :=
  sound_append rows 661 Block158.before Block158.after Block160.after
    Block158.steps part159_161 Block158.sound part159_161_sound
theorem part158_161_wellFormed : ∀ e ∈ part158_161, WellFormed e :=
  wellFormed_append Block158.steps part159_161 Block158.wellFormed part159_161_wellFormed

def part162_164 : List Step := Block162.steps ++ Block163.steps
theorem part162_164_sound : ArrayBlockSound rows 661 Block162.before Block163.after part162_164 :=
  sound_append rows 661 Block162.before Block162.after Block163.after
    Block162.steps Block163.steps Block162.sound Block163.sound
theorem part162_164_wellFormed : ∀ e ∈ part162_164, WellFormed e :=
  wellFormed_append Block162.steps Block163.steps Block162.wellFormed Block163.wellFormed

def part161_164 : List Step := Block161.steps ++ part162_164
theorem part161_164_sound : ArrayBlockSound rows 661 Block161.before Block163.after part161_164 :=
  sound_append rows 661 Block161.before Block161.after Block163.after
    Block161.steps part162_164 Block161.sound part162_164_sound
theorem part161_164_wellFormed : ∀ e ∈ part161_164, WellFormed e :=
  wellFormed_append Block161.steps part162_164 Block161.wellFormed part162_164_wellFormed

def part158_164 : List Step := part158_161 ++ part161_164
theorem part158_164_sound : ArrayBlockSound rows 661 Block158.before Block163.after part158_164 :=
  sound_append rows 661 Block158.before Block160.after Block163.after
    part158_161 part161_164 part158_161_sound part161_164_sound
theorem part158_164_wellFormed : ∀ e ∈ part158_164, WellFormed e :=
  wellFormed_append part158_161 part161_164 part158_161_wellFormed part161_164_wellFormed

def part153_164 : List Step := part153_158 ++ part158_164
theorem part153_164_sound : ArrayBlockSound rows 661 Block153.before Block163.after part153_164 :=
  sound_append rows 661 Block153.before Block157.after Block163.after
    part153_158 part158_164 part153_158_sound part158_164_sound
theorem part153_164_wellFormed : ∀ e ∈ part153_164, WellFormed e :=
  wellFormed_append part153_158 part158_164 part153_158_wellFormed part158_164_wellFormed

def part164_166 : List Step := Block164.steps ++ Block165.steps
theorem part164_166_sound : ArrayBlockSound rows 661 Block164.before Block165.after part164_166 :=
  sound_append rows 661 Block164.before Block164.after Block165.after
    Block164.steps Block165.steps Block164.sound Block165.sound
theorem part164_166_wellFormed : ∀ e ∈ part164_166, WellFormed e :=
  wellFormed_append Block164.steps Block165.steps Block164.wellFormed Block165.wellFormed

def part167_169 : List Step := Block167.steps ++ Block168.steps
theorem part167_169_sound : ArrayBlockSound rows 661 Block167.before Block168.after part167_169 :=
  sound_append rows 661 Block167.before Block167.after Block168.after
    Block167.steps Block168.steps Block167.sound Block168.sound
theorem part167_169_wellFormed : ∀ e ∈ part167_169, WellFormed e :=
  wellFormed_append Block167.steps Block168.steps Block167.wellFormed Block168.wellFormed

def part166_169 : List Step := Block166.steps ++ part167_169
theorem part166_169_sound : ArrayBlockSound rows 661 Block166.before Block168.after part166_169 :=
  sound_append rows 661 Block166.before Block166.after Block168.after
    Block166.steps part167_169 Block166.sound part167_169_sound
theorem part166_169_wellFormed : ∀ e ∈ part166_169, WellFormed e :=
  wellFormed_append Block166.steps part167_169 Block166.wellFormed part167_169_wellFormed

def part164_169 : List Step := part164_166 ++ part166_169
theorem part164_169_sound : ArrayBlockSound rows 661 Block164.before Block168.after part164_169 :=
  sound_append rows 661 Block164.before Block165.after Block168.after
    part164_166 part166_169 part164_166_sound part166_169_sound
theorem part164_169_wellFormed : ∀ e ∈ part164_169, WellFormed e :=
  wellFormed_append part164_166 part166_169 part164_166_wellFormed part166_169_wellFormed

def part170_172 : List Step := Block170.steps ++ Block171.steps
theorem part170_172_sound : ArrayBlockSound rows 661 Block170.before Block171.after part170_172 :=
  sound_append rows 661 Block170.before Block170.after Block171.after
    Block170.steps Block171.steps Block170.sound Block171.sound
theorem part170_172_wellFormed : ∀ e ∈ part170_172, WellFormed e :=
  wellFormed_append Block170.steps Block171.steps Block170.wellFormed Block171.wellFormed

def part169_172 : List Step := Block169.steps ++ part170_172
theorem part169_172_sound : ArrayBlockSound rows 661 Block169.before Block171.after part169_172 :=
  sound_append rows 661 Block169.before Block169.after Block171.after
    Block169.steps part170_172 Block169.sound part170_172_sound
theorem part169_172_wellFormed : ∀ e ∈ part169_172, WellFormed e :=
  wellFormed_append Block169.steps part170_172 Block169.wellFormed part170_172_wellFormed

def part173_175 : List Step := Block173.steps ++ Block174.steps
theorem part173_175_sound : ArrayBlockSound rows 661 Block173.before Block174.after part173_175 :=
  sound_append rows 661 Block173.before Block173.after Block174.after
    Block173.steps Block174.steps Block173.sound Block174.sound
theorem part173_175_wellFormed : ∀ e ∈ part173_175, WellFormed e :=
  wellFormed_append Block173.steps Block174.steps Block173.wellFormed Block174.wellFormed

def part172_175 : List Step := Block172.steps ++ part173_175
theorem part172_175_sound : ArrayBlockSound rows 661 Block172.before Block174.after part172_175 :=
  sound_append rows 661 Block172.before Block172.after Block174.after
    Block172.steps part173_175 Block172.sound part173_175_sound
theorem part172_175_wellFormed : ∀ e ∈ part172_175, WellFormed e :=
  wellFormed_append Block172.steps part173_175 Block172.wellFormed part173_175_wellFormed

def part169_175 : List Step := part169_172 ++ part172_175
theorem part169_175_sound : ArrayBlockSound rows 661 Block169.before Block174.after part169_175 :=
  sound_append rows 661 Block169.before Block171.after Block174.after
    part169_172 part172_175 part169_172_sound part172_175_sound
theorem part169_175_wellFormed : ∀ e ∈ part169_175, WellFormed e :=
  wellFormed_append part169_172 part172_175 part169_172_wellFormed part172_175_wellFormed

def part164_175 : List Step := part164_169 ++ part169_175
theorem part164_175_sound : ArrayBlockSound rows 661 Block164.before Block174.after part164_175 :=
  sound_append rows 661 Block164.before Block168.after Block174.after
    part164_169 part169_175 part164_169_sound part169_175_sound
theorem part164_175_wellFormed : ∀ e ∈ part164_175, WellFormed e :=
  wellFormed_append part164_169 part169_175 part164_169_wellFormed part169_175_wellFormed

def part153_175 : List Step := part153_164 ++ part164_175
theorem part153_175_sound : ArrayBlockSound rows 661 Block153.before Block174.after part153_175 :=
  sound_append rows 661 Block153.before Block163.after Block174.after
    part153_164 part164_175 part153_164_sound part164_175_sound
theorem part153_175_wellFormed : ∀ e ∈ part153_175, WellFormed e :=
  wellFormed_append part153_164 part164_175 part153_164_wellFormed part164_175_wellFormed

def part131_175 : List Step := part131_153 ++ part153_175
theorem part131_175_sound : ArrayBlockSound rows 661 Block131.before Block174.after part131_175 :=
  sound_append rows 661 Block131.before Block152.after Block174.after
    part131_153 part153_175 part131_153_sound part153_175_sound
theorem part131_175_wellFormed : ∀ e ∈ part131_175, WellFormed e :=
  wellFormed_append part131_153 part153_175 part131_153_wellFormed part153_175_wellFormed

def part087_175 : List Step := part087_131 ++ part131_175
theorem part087_175_sound : ArrayBlockSound rows 661 Block087.before Block174.after part087_175 :=
  sound_append rows 661 Block087.before Block130.after Block174.after
    part087_131 part131_175 part087_131_sound part131_175_sound
theorem part087_175_wellFormed : ∀ e ∈ part087_175, WellFormed e :=
  wellFormed_append part087_131 part131_175 part087_131_wellFormed part131_175_wellFormed

def part000_175 : List Step := part000_087 ++ part087_175
theorem part000_175_sound : ArrayBlockSound rows 661 Block000.before Block174.after part000_175 :=
  sound_append rows 661 Block000.before Block086.after Block174.after
    part000_087 part087_175 part000_087_sound part087_175_sound
theorem part000_175_wellFormed : ∀ e ∈ part000_175, WellFormed e :=
  wellFormed_append part000_087 part087_175 part000_087_wellFormed part087_175_wellFormed

abbrev allSteps := part000_175
theorem allSteps_sound : ArrayBlockSound rows 661 Block000.before Block174.after allSteps := part000_175_sound
theorem allSteps_wellFormed : ∀ e ∈ allSteps, WellFormed e := part000_175_wellFormed

theorem program_eq : gates.toList = allSteps.map SSACertificate.Step.gate := by
  simp only [allSteps, part000_175, part087_175, part131_175, part153_175, part164_175, part169_175, part172_175, part173_175, part169_172, part170_172, part164_169, part166_169, part167_169, part164_166, part153_164, part158_164, part161_164, part162_164, part158_161, part159_161, part153_158, part155_158, part156_158, part153_155, part131_153, part142_153, part147_153, part150_153, part151_153, part147_150, part148_150, part142_147, part144_147, part145_147, part142_144, part131_142, part136_142, part139_142, part140_142, part136_139, part137_139, part131_136, part133_136, part134_136, part131_133, part087_131, part109_131, part120_131, part125_131, part128_131, part129_131, part125_128, part126_128, part120_125, part122_125, part123_125, part120_122, part109_120, part114_120, part117_120, part118_120, part114_117, part115_117, part109_114, part111_114, part112_114, part109_111, part087_109, part098_109, part103_109, part106_109, part107_109, part103_106, part104_106, part098_103, part100_103, part101_103, part098_100, part087_098, part092_098, part095_098, part096_098, part092_095, part093_095, part087_092, part089_092, part090_092, part087_089, part000_087, part043_087, part065_087, part076_087, part081_087, part084_087, part085_087, part081_084, part082_084, part076_081, part078_081, part079_081, part076_078, part065_076, part070_076, part073_076, part074_076, part070_073, part071_073, part065_070, part067_070, part068_070, part065_067, part043_065, part054_065, part059_065, part062_065, part063_065, part059_062, part060_062, part054_059, part056_059, part057_059, part054_056, part043_054, part048_054, part051_054, part052_054, part048_051, part049_051, part043_048, part045_048, part046_048, part043_045, part000_043, part021_043, part032_043, part037_043, part040_043, part041_043, part037_040, part038_040, part032_037, part034_037, part035_037, part032_034, part021_032, part026_032, part029_032, part030_032, part026_029, part027_029, part021_026, part023_026, part024_026, part021_023, part000_021, part010_021, part015_021, part018_021, part019_021, part015_018, part016_018, part010_015, part012_015, part013_015, part010_012, part000_010, part005_010, part007_010, part008_010, part005_007, part000_005, part002_005, part003_005, part000_002, List.map_append]
  rw [← Block000.program, ← Block001.program, ← Block002.program, ← Block003.program, ← Block004.program, ← Block005.program, ← Block006.program, ← Block007.program, ← Block008.program, ← Block009.program, ← Block010.program, ← Block011.program, ← Block012.program, ← Block013.program, ← Block014.program, ← Block015.program, ← Block016.program, ← Block017.program, ← Block018.program, ← Block019.program, ← Block020.program, ← Block021.program, ← Block022.program, ← Block023.program, ← Block024.program, ← Block025.program, ← Block026.program, ← Block027.program, ← Block028.program, ← Block029.program, ← Block030.program, ← Block031.program, ← Block032.program, ← Block033.program, ← Block034.program, ← Block035.program, ← Block036.program, ← Block037.program, ← Block038.program, ← Block039.program, ← Block040.program, ← Block041.program, ← Block042.program, ← Block043.program, ← Block044.program, ← Block045.program, ← Block046.program, ← Block047.program, ← Block048.program, ← Block049.program, ← Block050.program, ← Block051.program, ← Block052.program, ← Block053.program, ← Block054.program, ← Block055.program, ← Block056.program, ← Block057.program, ← Block058.program, ← Block059.program, ← Block060.program, ← Block061.program, ← Block062.program, ← Block063.program, ← Block064.program, ← Block065.program, ← Block066.program, ← Block067.program, ← Block068.program, ← Block069.program, ← Block070.program, ← Block071.program, ← Block072.program, ← Block073.program, ← Block074.program, ← Block075.program, ← Block076.program, ← Block077.program, ← Block078.program, ← Block079.program, ← Block080.program, ← Block081.program, ← Block082.program, ← Block083.program, ← Block084.program, ← Block085.program, ← Block086.program, ← Block087.program, ← Block088.program, ← Block089.program, ← Block090.program, ← Block091.program, ← Block092.program, ← Block093.program, ← Block094.program, ← Block095.program, ← Block096.program, ← Block097.program, ← Block098.program, ← Block099.program, ← Block100.program, ← Block101.program, ← Block102.program, ← Block103.program, ← Block104.program, ← Block105.program, ← Block106.program, ← Block107.program, ← Block108.program, ← Block109.program, ← Block110.program, ← Block111.program, ← Block112.program, ← Block113.program, ← Block114.program, ← Block115.program, ← Block116.program, ← Block117.program, ← Block118.program, ← Block119.program, ← Block120.program, ← Block121.program, ← Block122.program, ← Block123.program, ← Block124.program, ← Block125.program, ← Block126.program, ← Block127.program, ← Block128.program, ← Block129.program, ← Block130.program, ← Block131.program, ← Block132.program, ← Block133.program, ← Block134.program, ← Block135.program, ← Block136.program, ← Block137.program, ← Block138.program, ← Block139.program, ← Block140.program, ← Block141.program, ← Block142.program, ← Block143.program, ← Block144.program, ← Block145.program, ← Block146.program, ← Block147.program, ← Block148.program, ← Block149.program, ← Block150.program, ← Block151.program, ← Block152.program, ← Block153.program, ← Block154.program, ← Block155.program, ← Block156.program, ← Block157.program, ← Block158.program, ← Block159.program, ← Block160.program, ← Block161.program, ← Block162.program, ← Block163.program, ← Block164.program, ← Block165.program, ← Block166.program, ← Block167.program, ← Block168.program, ← Block169.program, ← Block170.program, ← Block171.program, ← Block172.program, ← Block173.program, ← Block174.program]
  simpa only [List.append_assoc] using gates_toList_chunks

end
end CSL.Construction.FiniteSSA.Verified

namespace CSL.Construction.FiniteCertificate
open CSL.Construction.FiniteSSA.Verified
noncomputable section

theorem concreteOperandsBound : ∀ g ∈ gates.toList,
    g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount := by
  intro g hg
  rw [program_eq] at hg
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
  exact ⟨(allSteps_wellFormed e he).1, (allSteps_wellFormed e he).2.1⟩

theorem concreteSourcesNodup : ∀ g ∈ gates.toList, g.sources.Nodup := by
  intro g hg
  rw [program_eq] at hg
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
  exact (allSteps_wellFormed e he).2.2.1

theorem concreteNoSelf : ∀ g ∈ gates.toList, g.destination ∉ g.sources := by
  intro g hg
  rw [program_eq] at hg
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
  exact (allSteps_wellFormed e he).2.2.2

end
end CSL.Construction.FiniteCertificate

#print axioms CSL.Construction.FiniteSSA.Verified.allSteps_sound
#print axioms CSL.Construction.FiniteSSA.Verified.program_eq
#print axioms CSL.Construction.FiniteCertificate.concreteOperandsBound
#print axioms CSL.Construction.FiniteCertificate.concreteSourcesNodup
#print axioms CSL.Construction.FiniteCertificate.concreteNoSelf


