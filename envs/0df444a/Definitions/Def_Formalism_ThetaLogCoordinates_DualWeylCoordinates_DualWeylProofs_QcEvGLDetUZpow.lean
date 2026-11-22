-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:30.348142+00:00
-- url     : https://prove2.me/theorems/d9c8b58b-9ace-4b11-8f8a-682a450fa6c8
-- title:
--   Qc Ev GLDet UZpow
-- statement:
--   Definitions and structural lemmas for Qc Ev GLDet UZpow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
def qc_par {i N : ℕ} (p : (Σ _ : {S : Finset (Fin N) // S.card = i}, Equiv.Perm (Fin i))) :
    Fin i ↪ Fin N :=
  p.2.toEmbedding.trans (p.1.1.orderEmbOfFin p.1.2).toEmbedding
def qc_dU {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : Rˣ := Units.map (evGL g).toMonoidHom (detU n)
end Formalism.InvariantFactorPaths.ColumnFamilies


