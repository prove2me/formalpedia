-- Prove2me | Definitions.Def_OAIEGC000
-- name    : OAIEGC000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T03:03:14.642935+00:00
-- url     : https://prove2.me/theorems/0fc1a3a2-f7cf-42a3-8f7c-7ec879ad54e9
-- title:
--   Definitions bundle OAIEGC000 of the split of OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, carved from OpenAI's openai/math development (OpenAI, *A finitely generated counterexample to the Eilenberg–Ganea conjecture*, OpenAI Math Release, September 23, 2026, result family 249, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 7 definitions. The definitions and types are `OAI.EilenbergGanea.SeedChainCertificate.d₂`, `OAI.EilenbergGanea.SeedChainCertificate.edge`, `OAI.EilenbergGanea.SeedChainCertificate.edgeData`, `OAI.EilenbergGanea.SeedChainCertificate.h1CodeData`, `OAI.EilenbergGanea.SeedChainCertificate.h1Coeff`, `OAI.EilenbergGanea.SeedChainCertificate.h₁`, `OAI.EilenbergGanea.SeedChainCertificate.h₁'`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory, in whole or in part: [`SeedChains`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedChains.lean), [`SeedContraction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedContraction.lean).
--
--   **Imports.** It imports the bundles `OAIEG003`, `OAIEG004`, `OAIEG005`, `OAIEG006`, `OAIEG007`, `OAIEG008`, `OAIEG009`, `OAIEG010` and `OAIEG011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIEGC001`; the statements `OAI.EilenbergGanea.SeedChainCertificate.corrected_identities`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_0`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_1`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_10`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_2`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_3`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_4`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_5`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_6`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_7`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_8`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_9`, `OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_2`, `OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_3`, `OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_4`, `OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_5`, `OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_6`, `OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_7` and `OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_8`; the proofs of `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_0`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_1`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_10`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_2`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_3`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_4`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_5`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_6`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_7`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_8`, `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_9`, `OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_2`, `OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_3`, `OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_4`, `OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_5`, `OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_6`, `OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_7` and `OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_8`.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIEG003
import Definitions.Def_OAIEG004
import Definitions.Def_OAIEG005
import Definitions.Def_OAIEG006
import Definitions.Def_OAIEG007
import Definitions.Def_OAIEG008
import Definitions.Def_OAIEG009
import Definitions.Def_OAIEG010
import Definitions.Def_OAIEG011

section
-- module Solutions.OAIEG.SeedChains
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

def edgeData : List (Fin 103 × Fin 103) := [edgeData_0,edgeData_1,edgeData_2,edgeData_3,edgeData_4,edgeData_5,edgeData_6,edgeData_7,edgeData_8,edgeData_9,edgeData_10,edgeData_11,edgeData_12,edgeData_13,edgeData_14,edgeData_15,edgeData_16,edgeData_17,edgeData_18,edgeData_19,edgeData_20,edgeData_21,edgeData_22,edgeData_23].flatten

def edge (e : Fin 372) : Fin 103 × Fin 103 := edgeData.getD e.val (0,0)
end EilenbergGanea.SeedChainCertificate


end

end OAI
end

section
-- module Solutions.OAIEG.SeedContraction
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

def h1CodeData : List (ℕ) := [h1CodeData_0,h1CodeData_1,h1CodeData_2,h1CodeData_3,h1CodeData_4,h1CodeData_5,h1CodeData_6,h1CodeData_7,h1CodeData_8,h1CodeData_9,h1CodeData_10,h1CodeData_11,h1CodeData_12,h1CodeData_13,h1CodeData_14,h1CodeData_15,h1CodeData_16,h1CodeData_17,h1CodeData_18,h1CodeData_19,h1CodeData_20,h1CodeData_21,h1CodeData_22,h1CodeData_23].flatten

def h1Coeff (e : Fin 372) (t : Fin 270) : ℤ :=
  (((h1CodeData.getD e.val 0 >>> (5*t.val)) % 32 : ℕ) : ℤ) - 16

noncomputable def d₂ := FiniteIntegralContraction.rowsMap d2Row
noncomputable def h₁ := FiniteIntegralContraction.matrixMap h1Coeff
noncomputable def h₁' := FiniteIntegralContraction.corrected d₁ h₀ h₁

end EilenbergGanea.SeedChainCertificate


end

end OAI
end


