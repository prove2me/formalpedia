-- Prove2me | Definitions.Def_OAIQ368Chrom069
-- name    : OAIQ368Chrom069
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T20:22:41.400398+00:00
-- url     : https://prove2.me/theorems/2ef7cb61-84db-4c81-8ff2-5c25f3a964a0
-- title:
--   Definitions bundle OAIQ368Chrom069 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 2 definitions and 1 theorem. The definitions and types are `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.historyWitness`, `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.ofAdmissibleWitness`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_QuantumTorus_Admissible`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/Admissible.lean), [`Chromatic_Witness_ElementaryProductDegree`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/ElementaryProductDegree.lean), [`Chromatic_Witness_HistoryMainWitness`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/HistoryMainWitness.lean).
--
--   **Imports.** It imports the published bundle `Def_ElementaryPositivity`; the bundles `OAIQ368Chrom063`, `OAIQ368Chrom067` and `OAIQ368Chrom068` of this split; the published statement `OAI.ElementaryPositivity.TriangularDynamics.admissible_polynomial_expansion`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom070`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom063
import Definitions.Def_OAIQ368Chrom067
import Definitions.Def_OAIQ368Chrom068
import Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_admissible_polynomial_expansion

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_Admissible
attribute [-instance] _root_.OAI.ElementaryPositivity.FiniteSearch.instDecidableTest _root_.OAI.ElementaryPositivity.FiniteSearch.instDecidableWordOK _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.NaturalUnitIntervalGraph
variable {n : ℕ} (G : ElementaryPositivity.NaturalUnitIntervalGraph n)

theorem reflect_inversionChromatic (r : ℕ) :
    CoefficientReflection.reflect G.edgeCount (G.inversionChromatic r) = G.chromatic r := by
  unfold inversionChromatic chromatic
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro f hf
  have hproper : G.Proper f := (Finset.mem_filter.mp hf).2
  have hc := G.coloringInversions_add_ascents f hproper
  have hk : G.coloringInversions f ≤ G.edgeCount := by omega
  have he : G.edgeCount - G.coloringInversions f = G.coloringAscents f := by omega
  have hm : (∏ i : Fin n, MvPolynomial.X (R := Polynomial ℕ) (f i)) =
      MvPolynomial.map Polynomial.C (∏ i : Fin n, MvPolynomial.X (R := ℕ) (f i)) := by
    simp
  rw [hm, CoefficientReflection.reflect_C_X_pow_mul_map _ _ hk, he]

end ElementaryPositivity.NaturalUnitIntervalGraph

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_ElementaryProductDegree
attribute [-instance] _root_.OAI.ElementaryPositivity.FiniteSearch.instDecidableTest _root_.OAI.ElementaryPositivity.FiniteSearch.instDecidableWordOK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
open scoped BigOperators
variable {n:ℕ} (G:ElementaryPositivity.NaturalUnitIntervalGraph n)

def ofAdmissibleWitness
    (lam:{w:Equiv.Perm (Fin n) // G.Admissible w} → Nat.Partition n)
    (hexp:∀r:ℕ,G.inversionChromatic r=
      ∑w:{w:Equiv.Perm (Fin n) // G.Admissible w},
        MvPolynomial.C (Polynomial.X^G.graphInversions w.val)*
          MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (lam w)) : G.PermutationWitness where
  theta σ:=lam (G.reversalEquiv σ)
  expansion r:=by
    rw [←G.reflect_inversionChromatic r,hexp r,map_sum]
    rw [←Equiv.sum_comp G.reversalEquiv]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [CoefficientReflection.reflect_C_X_pow_mul_esymmPart _ _ _ (G.graphInversions_le_edges _)]
    congr 2
    congr 1
    change G.edgeCount-G.graphInversions (reversePerm σ.val)=G.graphInversions σ.val
    have H:=G.graphInversions_add_reverse σ.val
    omega
end ElementaryPositivity.NaturalUnitIntervalGraph

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_HistoryMainWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph

noncomputable def historyWitness {n:ℕ} (G:ElementaryPositivity.NaturalUnitIntervalGraph n) : G.PermutationWitness:=
  G.ofAdmissibleWitness (TriangularDynamics.admissiblePartition G)
    (TriangularDynamics.admissible_polynomial_expansion G)
end ElementaryPositivity.NaturalUnitIntervalGraph

end

end OAI
end


