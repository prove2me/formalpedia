-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_GatesChunks
-- name    : CSL_Generated_FiniteCircuit_GatesChunks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:10:47.521988+00:00
-- url     : https://prove2.me/theorems/b15d06e1-ba23-4364-9d04-46c74c03aa1d
-- title:
--   Coded sorting library: Generated / FiniteCircuit / GatesChunks
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.GatesChunks` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.GatesChunks

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_Data
import Definitions.Def_CSL_Circuit_Local_SSAArrayConcat

namespace CSL.Construction.FiniteCertificate
open CSL.Construction.FiniteSSA.Verified
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact literal chunk decomposition of the original scalar word. This proof
only rewrites concatenation; it does not evaluate gate values or coefficients. -/
theorem gates_toList_chunks : gates.toList =
      gatesChunk0.toList ++
      gatesChunk1.toList ++
      gatesChunk2.toList ++
      gatesChunk3.toList ++
      gatesChunk4.toList ++
      gatesChunk5.toList ++
      gatesChunk6.toList ++
      gatesChunk7.toList ++
      gatesChunk8.toList ++
      gatesChunk9.toList ++
      gatesChunk10.toList ++
      gatesChunk11.toList ++
      gatesChunk12.toList ++
      gatesChunk13.toList ++
      gatesChunk14.toList ++
      gatesChunk15.toList ++
      gatesChunk16.toList ++
      gatesChunk17.toList ++
      gatesChunk18.toList ++
      gatesChunk19.toList ++
      gatesChunk20.toList ++
      gatesChunk21.toList ++
      gatesChunk22.toList ++
      gatesChunk23.toList ++
      gatesChunk24.toList ++
      gatesChunk25.toList ++
      gatesChunk26.toList ++
      gatesChunk27.toList ++
      gatesChunk28.toList ++
      gatesChunk29.toList ++
      gatesChunk30.toList ++
      gatesChunk31.toList ++
      gatesChunk32.toList ++
      gatesChunk33.toList ++
      gatesChunk34.toList ++
      gatesChunk35.toList ++
      gatesChunk36.toList ++
      gatesChunk37.toList ++
      gatesChunk38.toList ++
      gatesChunk39.toList ++
      gatesChunk40.toList ++
      gatesChunk41.toList ++
      gatesChunk42.toList ++
      gatesChunk43.toList ++
      gatesChunk44.toList ++
      gatesChunk45.toList ++
      gatesChunk46.toList ++
      gatesChunk47.toList ++
      gatesChunk48.toList ++
      gatesChunk49.toList ++
      gatesChunk50.toList ++
      gatesChunk51.toList ++
      gatesChunk52.toList ++
      gatesChunk53.toList ++
      gatesChunk54.toList ++
      gatesChunk55.toList ++
      gatesChunk56.toList ++
      gatesChunk57.toList ++
      gatesChunk58.toList ++
      gatesChunk59.toList ++
      gatesChunk60.toList ++
      gatesChunk61.toList ++
      gatesChunk62.toList ++
      gatesChunk63.toList ++
      gatesChunk64.toList ++
      gatesChunk65.toList ++
      gatesChunk66.toList ++
      gatesChunk67.toList ++
      gatesChunk68.toList ++
      gatesChunk69.toList ++
      gatesChunk70.toList ++
      gatesChunk71.toList ++
      gatesChunk72.toList ++
      gatesChunk73.toList ++
      gatesChunk74.toList ++
      gatesChunk75.toList ++
      gatesChunk76.toList ++
      gatesChunk77.toList ++
      gatesChunk78.toList ++
      gatesChunk79.toList ++
      gatesChunk80.toList ++
      gatesChunk81.toList ++
      gatesChunk82.toList ++
      gatesChunk83.toList ++
      gatesChunk84.toList ++
      gatesChunk85.toList ++
      gatesChunk86.toList ++
      gatesChunk87.toList ++
      gatesChunk88.toList ++
      gatesChunk89.toList ++
      gatesChunk90.toList ++
      gatesChunk91.toList ++
      gatesChunk92.toList ++
      gatesChunk93.toList ++
      gatesChunk94.toList ++
      gatesChunk95.toList ++
      gatesChunk96.toList ++
      gatesChunk97.toList ++
      gatesChunk98.toList ++
      gatesChunk99.toList ++
      gatesChunk100.toList ++
      gatesChunk101.toList ++
      gatesChunk102.toList ++
      gatesChunk103.toList ++
      gatesChunk104.toList ++
      gatesChunk105.toList ++
      gatesChunk106.toList ++
      gatesChunk107.toList ++
      gatesChunk108.toList ++
      gatesChunk109.toList ++
      gatesChunk110.toList ++
      gatesChunk111.toList ++
      gatesChunk112.toList ++
      gatesChunk113.toList ++
      gatesChunk114.toList ++
      gatesChunk115.toList ++
      gatesChunk116.toList ++
      gatesChunk117.toList ++
      gatesChunk118.toList ++
      gatesChunk119.toList ++
      gatesChunk120.toList ++
      gatesChunk121.toList ++
      gatesChunk122.toList ++
      gatesChunk123.toList ++
      gatesChunk124.toList ++
      gatesChunk125.toList ++
      gatesChunk126.toList ++
      gatesChunk127.toList ++
      gatesChunk128.toList ++
      gatesChunk129.toList ++
      gatesChunk130.toList ++
      gatesChunk131.toList ++
      gatesChunk132.toList ++
      gatesChunk133.toList ++
      gatesChunk134.toList ++
      gatesChunk135.toList ++
      gatesChunk136.toList ++
      gatesChunk137.toList ++
      gatesChunk138.toList ++
      gatesChunk139.toList ++
      gatesChunk140.toList ++
      gatesChunk141.toList ++
      gatesChunk142.toList ++
      gatesChunk143.toList ++
      gatesChunk144.toList ++
      gatesChunk145.toList ++
      gatesChunk146.toList ++
      gatesChunk147.toList ++
      gatesChunk148.toList ++
      gatesChunk149.toList ++
      gatesChunk150.toList ++
      gatesChunk151.toList ++
      gatesChunk152.toList ++
      gatesChunk153.toList ++
      gatesChunk154.toList ++
      gatesChunk155.toList ++
      gatesChunk156.toList ++
      gatesChunk157.toList ++
      gatesChunk158.toList ++
      gatesChunk159.toList ++
      gatesChunk160.toList ++
      gatesChunk161.toList ++
      gatesChunk162.toList ++
      gatesChunk163.toList ++
      gatesChunk164.toList ++
      gatesChunk165.toList ++
      gatesChunk166.toList ++
      gatesChunk167.toList ++
      gatesChunk168.toList ++
      gatesChunk169.toList ++
      gatesChunk170.toList ++
      gatesChunk171.toList ++
      gatesChunk172.toList ++
      gatesChunk173.toList ++
      gatesChunk174.toList := by
  simp only [gates, concat_toList, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

end CSL.Construction.FiniteCertificate
#print axioms CSL.Construction.FiniteCertificate.gates_toList_chunks


