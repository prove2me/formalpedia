-- Prove2me | Definitions.Def_OAIEGC001
-- name    : OAIEGC001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T04:55:07.470203+00:00
-- url     : https://prove2.me/theorems/d7734f26-767c-4fac-94a6-fa734deebd9b
-- title:
--   Definitions bundle OAIEGC001 of the split of OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, carved from OpenAI's openai/math development (OpenAI, *A finitely generated counterexample to the Eilenberg–Ganea conjecture*, OpenAI Math Release, September 23, 2026, result family 249, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 1 definition and 5 theorems. The definitions and types are `OAI.EilenbergGanea.SeedChainCertificate.triangle`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory, in whole or in part: [`Integral_Contraction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicTopology/Integral/Contraction.lean), [`SeedChains`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedChains.lean), [`SeedContraction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedContraction.lean).
--
--   **Imports.** It imports the bundle `OAIEGC000` of this split; the published statements `OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert` and `OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert`.
--
--   **Imported by** (directly, in this split): the bundle `OAIEGC002`; the proof of `OAI.EilenbergGanea.SeedChainCertificate.corrected_identities`.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIEGC000
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d1_basis_cert
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d2_basis_cert

section
-- module Solutions.OAIEG.Integral_Contraction
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

open Classical
namespace FiniteIntegralContraction
variable {I J K : Type*}

variable [Fintype I] [Fintype J] [Fintype K]
    (edge : J → I × I) (face : K → J × J × J)
    (r₁ : I → List (J × ℤ)) (r₂ : J → List (K × ℤ))
    (a₀ : I → J → ℤ) (a₁ : J → K → ℤ) (root : I)

omit [Fintype I] [Fintype J] in
 theorem rows_single_one (h : ∀ i e, rowEval (r₁ i) (fun j => if j = e then 1 else 0) =
    (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0)) (e : J) :
    rowsMap r₁ (Pi.single e 1) = Pi.single (edge e).2 1 - Pi.single (edge e).1 1 := by
  funext i
  have he : (Pi.single e 1 : J → ℤ) = fun j => if j = e then 1 else 0 := by funext j; simp [Pi.single_apply]
  rw [rowsMap_apply,he]
  simpa only [Pi.sub_apply,Pi.single_apply] using h i e

omit [Fintype J] [Fintype K] in
 theorem rows_single_two (h : ∀ j t, rowEval (r₂ j) (fun i => if i = t then 1 else 0) =
    (if j = (face t).1 then 1 else 0) - (if j = (face t).2.1 then 1 else 0) +
      (if j = (face t).2.2 then 1 else 0)) (t : K) :
    rowsMap r₂ (Pi.single t 1) = Pi.single (face t).1 1 - Pi.single (face t).2.1 1 +
      Pi.single (face t).2.2 1 := by
  funext j
  have he : (Pi.single t 1 : K → ℤ) = fun i => if i = t then 1 else 0 := by funext i; simp [Pi.single_apply]
  rw [rowsMap_apply,he]
  simpa only [Pi.sub_apply,Pi.add_apply,Pi.single_apply] using h j t

end FiniteIntegralContraction



end

end OAI
end

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
def triangle (t : Fin 270) : Fin 103 × Fin 103 × Fin 103 :=
  ((edge (triangleEdges t).2.2).1,(edge (triangleEdges t).2.2).2,
    (edge (triangleEdges t).1).2)

theorem triangle_edges_valid : ∀ t : Fin 270,
    edge (triangleEdges t).1 = ((triangle t).2.1,(triangle t).2.2) ∧
    edge (triangleEdges t).2.1 = ((triangle t).1,(triangle t).2.2) ∧
    edge (triangleEdges t).2.2 = ((triangle t).1,(triangle t).2.1) := by decide +kernel

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

attribute [local instance] OAI.EilenbergGanea.SeedChainCertificate.instDecidableEqFinOfNatNat_solutions
attribute [local instance] OAI.EilenbergGanea.SeedChainCertificate.instDecidableEqFinOfNatNat_solutions_1
theorem d₁_single (e : Fin 372) :
    d₁ (Pi.single e 1) = Pi.single (edge e).2 1 - Pi.single (edge e).1 1 :=
by
  apply FiniteIntegralContraction.rows_single_one edge d1Row
  intro i e
  simpa only [rowEval,FiniteIntegralContraction.rowEval,fin_ite] using d1_basis_cert i e

attribute [local instance] OAI.EilenbergGanea.SeedChainCertificate.instDecidableEqFinOfNatNat_solutions_2
theorem d₂_single (t : Fin 270) :
    d₂ (Pi.single t 1) = Pi.single (triangleEdges t).1 1 -
      Pi.single (triangleEdges t).2.1 1 + Pi.single (triangleEdges t).2.2 1 :=
by
  apply FiniteIntegralContraction.rows_single_two triangleEdges d2Row
  intro e t
  simpa only [rowEval,FiniteIntegralContraction.rowEval,fin_ite] using d2_basis_cert e t

end EilenbergGanea.SeedChainCertificate


end

end OAI
end


