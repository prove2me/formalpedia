-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TrueRing
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_TrueRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:30:42.146166+00:00
-- url     : https://prove2.me/theorems/414ce359-2bf9-4793-b61f-11850bda3a9e
-- title:
--   True Ring
-- statement:
--   Definitions and structural lemmas for True Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TrueRing.lean

import Definitions.Def_Formalism_MahlerMeasure_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
open MvPolynomial
namespace QuotientRingDecomposition
variable {R : Type} [CommRing R] {r Q : ℕ}
noncomputable def E (e : Fin r → Fin Q) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => ((e i : ℕ)))
def modQ (hQ : 0 < Q) (m : Fin r →₀ ℕ) : Fin r → Fin Q := fun i => ⟨m i % Q, Nat.mod_lt _ hQ⟩
noncomputable def divQ (Q : ℕ) (m : Fin r →₀ ℕ) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m i / Q)
end QuotientRingDecomposition
end Formalism.GM


