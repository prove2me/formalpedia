-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryFin
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryFin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:54.980694+00:00
-- url     : https://prove2.me/theorems/eafa5ee2-1b41-474a-9ca1-e65c04588ef3
-- title:
--   Card Unitary Fin
-- statement:
--   Definitions and structural lemmas for Card Unitary Fin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
open Matrix
variable {k : Type*} [Field k]
def cj {n n' : Type*} (σ : k ≃+* k) (X : Matrix n n' k) : Matrix n' n k := (X.map σ).transpose
def emb {m : ℕ} (Y : Matrix (Fin m) (Fin m) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => Y i' j') j) i
end Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
namespace Formalism.HermitianLattices.Ext.L3
end Formalism.HermitianLattices.Ext.L3


