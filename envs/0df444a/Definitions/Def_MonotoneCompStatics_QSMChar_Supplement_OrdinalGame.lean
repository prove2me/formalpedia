-- Prove2me | Definitions.Def_MonotoneCompStatics_QSMChar_Supplement_OrdinalGame
-- name    : MonotoneCompStatics_QSMChar_Supplement_OrdinalGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:07:09.82582+00:00
-- url     : https://prove2.me/theorems/4768cdc1-5c36-4a27-b4da-360d0d04f57d
-- title:
--   Games with ordinal strategic complementarities
-- statement:
--   For a pure game with lattice actions $S_i$, the ordinal strategic-complementarity conditions are:
--   $$S_i\text{ compact};\quad\pi_i(\cdot,x_{-i})\text{ upper semicontinuous};\quad\pi_i(a,\cdot)\text{ continuous};$$
--   $$\pi_i(\cdot,x_{-i})\text{ quasisupermodular};\quad\pi_i(a,x_{-i})\text{ has single crossing in }(a;x_{-i}).$$
--   These are the three printed conditions of the game definition, with both ordinal implications retained. **Formalization Note** Each action space has its order interval topology and opponent spaces have the product topology. The theorems separately require a nonempty player set and nonempty action types. Arbitrarily many players and infinite action lattices are admitted; no cardinal supermodularity is assumed.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), DOI 10.2307/2951479, p.175, PDF 20, conditions (1)–(3); p.159 footnote 3 and Appendix p.179

import Mathlib
import Definitions.Def_MonotoneCompStatics_QSMChar_Supplement_NormalFormGame
import Definitions.Def_MonotoneCompStatics_QSMChar_Supplement_OrderTopology
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing

namespace MonotoneCompStatics.QSMChar.Supplement

/-- The paper's three ordinal strategic-complementarity hypotheses. -/
def StrategicComplementarities {I : Type*} {S : I → Type*}
    [∀ i, Lattice (S i)] (G : NormalFormGame I S) : Prop :=
  letI : ∀ i, TopologicalSpace (S i) := fun i => intervalTopology (S i)
  (∀ i, IsCompact (Set.univ : Set (S i))) ∧
  (∀ i o, UpperSemicontinuous (fun a => G.payoff i a o)) ∧
  (∀ i a, Continuous (fun o => G.payoff i a o)) ∧
  (∀ i o, MonotoneCompStatics.Monotonicity.QuasiSupermodularOn
    (fun a => G.payoff i a o) Set.univ) ∧
  (∀ i, MonotoneCompStatics.Monotonicity.SingleCrossing (G.payoff i))

end MonotoneCompStatics.QSMChar.Supplement


