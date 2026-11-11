-- Prove2me | Definitions.Def_FlexRigidity_IsCPMap
-- name    : FlexRigidity_IsCPMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:31.302744+00:00
-- url     : https://prove2.me/theorems/64aa50da-540f-4365-92e1-077c484a8da1
-- title:
--   Completely positive maps $\mathrm{CP}(Q,Q')$
-- statement:
--   A superoperator $\Phi$ from operators on a finite register $Q$ to operators on $Q'$ is **completely positive** when it has a finite Kraus decomposition
--   $$\Phi(X)=\sum_{j=1}^m K_jXK_j^\dagger,\qquad K_j:Q\to Q',$$
--   with no normalization condition on the $K_j$. In finite dimension these are exactly the completely positive linear maps (Choi–Kraus), the class $\mathrm{CP}(Q,Q')$ of the paper; the trace-preserving ones are the channels $\mathrm{CPTP}(Q,Q')$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), §2.2, p. 18

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Completely positive maps** `CP(Q, Q′)` (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, §2.2, p. 18): a superoperator `Φ` from operators on
`ι` to operators on `κ` is completely positive when `Φ(X) = Σ_j K_j X K_j†` for a finite family of
Kraus operators `K_j : κ × ι`, with no normalization.

**Formalization Note** In finite dimension a linear map is completely positive exactly when it
has a finite Kraus decomposition (Choi–Kraus), so this is the paper's `CP(Q, Q′)`. The CPTP maps
are `QAlgorithms.IsChannel` (normalized Kraus family). -/
def IsCPMap {ι κ : Type} [Fintype ι] [Fintype κ] (Φ : Superop ι κ) : Prop :=
  ∃ (m : ℕ) (K : Fin m → Matrix κ ι ℂ), ∀ X, Φ X = krausApply K X

end FlexRigidity


