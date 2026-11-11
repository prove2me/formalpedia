-- Prove2me | Definitions.Def_FlexRigidity_IsProjMeas
-- name    : FlexRigidity_IsProjMeas
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:42.693804+00:00
-- url     : https://prove2.me/theorems/a1ebf972-138a-46e3-95fe-d369b11c8d7d
-- title:
--   Projective measurements
-- statement:
--   A family $\{T_a\}_{a\in A}$ of operators on a finite register is a **projective measurement** when every $T_a$ is an orthogonal projector ($T_a^\dagger=T_a=T_a^2$) and $\sum_aT_a=I$. Mutual orthogonality of the projectors follows. Alice's preparation measurements $\{T^x_a\}_a$, Bob's $\{N^y_b\}_b$ and the device projectors of the stored-output form are of this kind.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Fact 5.2 and Postulate Set 5.3, pp. 38–39

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

/-- **Projective measurements** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact
sha256 8c67699d…, Fact 5.2 and Postulate Set 5.3, pp. 38–39; Definition 2.4, p. 18): a family
`{T_a}_a` of orthogonal projectors (`T_a† = T_a`, `T_a² = T_a`) summing to the identity. Mutual
orthogonality of the projectors follows. -/
def IsProjMeas {A ι : Type} [Fintype A] [Fintype ι] [DecidableEq ι]
    (T : A → Matrix ι ι ℂ) : Prop :=
  (∀ a, (T a)ᴴ = T a ∧ T a * T a = T a) ∧ ∑ a, T a = 1

end FlexRigidity


