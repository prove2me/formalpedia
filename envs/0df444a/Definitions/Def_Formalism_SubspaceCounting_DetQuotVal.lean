-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_DetQuotVal
-- name    : Formalism_SubspaceCounting_DetQuotVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:24:37.713148+00:00
-- url     : https://prove2.me/theorems/a01c4a0e-ac04-4d84-b6dd-631789e98240
-- title:
--   Det Quot Val
-- statement:
--   Definitions and structural lemmas for Det Quot Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/DetQuotVal.lean

import Definitions.Def_Formalism_SubspaceCounting_StatementW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.G0
def DetQuotVal : Prop :=
  ∀ {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (r : ℕ) (vec : ι → Bool)
    (S' : Finset ι) (A : Fin r → ι) (d : ι → ℕ) (H : MvPolynomial (ι × Fin r) K) (m' th : ℕ),
    Function.Injective A → (∀ l, vec (A l) = true) → MultiHom H d → m' ≤ th →
    ValGE vec S' (fun i => d i + m' * (if i ∈ Set.range A then 1 else 0))
      ((detLetters (K := K) A) ^ m' * H) th →
    ValGE vec S' d H (th - m')
end Formalism.G0


