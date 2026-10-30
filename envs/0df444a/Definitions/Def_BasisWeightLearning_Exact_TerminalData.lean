-- Prove2me | Definitions.Def_BasisWeightLearning_Exact_TerminalData
-- name    : BasisWeightLearning_Exact_TerminalData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:21:27.665349+00:00
-- url     : https://prove2.me/theorems/2404d4bb-87c6-45c5-8759-ab1390a66a3b
-- title:
--   Assumption (A2) and the terminal efficient family
-- statement:
--   Terminal data consist of a finite family $U_{T+1}^*$ of continuation functions and an assigned polynomial weight $w(u)$ for each function. Validity requires the family to be nonempty and already efficient in the function-space sense, and requires $\Phi w(u)=u$ for each member. The terminal weight set is its image $W_{T+1}^*=\{w(u):u\in U_{T+1}^*\}$. This permits a singleton arbitrary polynomial terminal reward and the finite efficient families allowed for soft termination. There is no hypothesis relating the two frontier recursions.
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 14 (printed p. 14), (A2), following Eq. (9) on p. 11.

import Definitions.Def_BasisWeightLearning_Exact_PolynomialWeights
import Definitions.Def_BasisWeightLearning_Exact_FunctionFrontier

namespace BasisWeightLearning.Exact
structure TerminalData where
  functions : Finset ValueFunction
  weight : ValueFunction → Weight

def TerminalData.Valid (B : TerminalData) : Prop :=
  B.functions.Nonempty ∧
  functionFrontier (B.functions : Set ValueFunction) = (B.functions : Set ValueFunction) ∧
  ∀ u ∈ B.functions, evaluate (B.weight u) = u

noncomputable def TerminalData.weights (B : TerminalData) : Set Weight :=
  B.weight '' (B.functions : Set ValueFunction)
end BasisWeightLearning.Exact


