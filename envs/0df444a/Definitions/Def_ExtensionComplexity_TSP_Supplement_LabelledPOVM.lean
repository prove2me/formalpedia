-- Prove2me | Definitions.Def_ExtensionComplexity_TSP_Supplement_LabelledPOVM
-- name    : ExtensionComplexity_TSP_Supplement_LabelledPOVM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:33:13.671819+00:00
-- url     : https://prove2.me/theorems/4aea1d49-4fa9-4cc7-b5c2-bb7be60d5066
-- title:
--   Finite real-labelled POVMs and expected output (§4)
-- statement:
--   Let $r$ be the message dimension. A measurement consists of a finite outcome index set $\{0,\ldots,q-1\}$, real labels $\theta_o$, and real symmetric positive semidefinite effects $E_o$ satisfying
--
--   $$
--   \sum_{o=0}^{q-1}E_o=I_r.
--   $$
--
--   For a state $\rho$, outcome $o$ has probability $\operatorname{Tr}(E_o\rho)$, and the expected output is
--
--   $$
--   \sum_{o=0}^{q-1}\theta_o\operatorname{Tr}(E_o\rho).
--   $$
--
--   This separates the general measurement from the protocol restriction to nonnegative labels. Each finite outcome set can be enumerated this way; repeated labels can be merged by summing their effects, preserving the distribution of the reported real value. Zero effects and arbitrary finite outcome counts are allowed.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, DOI 10.1145/2716307, p. 17:17, §4, measurement paragraph

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Supplement_QuantumState

namespace ExtensionComplexity.TSP.Supplement

/-- A finite real-labelled POVM (§4, p. 17:17). Equal labels may be merged by
summing their effects. Nonnegativity of labels is imposed by the protocol layer. -/
structure LabelledPOVM (r : ℕ) where
  outcomeCount : ℕ
  label : Fin outcomeCount → ℝ
  effect : Fin outcomeCount → Matrix (Fin r) (Fin r) ℝ
  positive : ∀ o, (effect o).PosSemidef
  complete : ∑ o, effect o = 1

/-- The Born probability of an outcome when measuring the state ρ. -/
noncomputable def LabelledPOVM.probability {r : ℕ} (E : LabelledPOVM r)
    (ρ : QuantumState r) (o : Fin E.outcomeCount) : ℝ :=
  (E.effect o * ρ.density).trace

/-- Expected output, with the actual labels and Born probabilities. -/
noncomputable def LabelledPOVM.expectation {r : ℕ} (E : LabelledPOVM r)
    (ρ : QuantumState r) : ℝ :=
  ∑ o, E.label o * E.probability ρ o

end ExtensionComplexity.TSP.Supplement


