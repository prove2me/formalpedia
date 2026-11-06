-- Prove2me | Definitions.Def_QEC_Semantics_Channels_ChoiKraus
-- name    : QEC_Semantics_Channels_ChoiKraus
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:14:18.793734+00:00
-- url     : https://prove2.me/theorems/40457c60-fa06-4a60-a184-ca431f46bbf3
-- title:
--   Choi Kraus
-- statement:
--   Definitions and structural lemmas for Choi Kraus, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean

import Definitions.Def_QEC_Semantics_Channels_Choi
import Definitions.Def_QEC_Semantics_Channels_Kraus
set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
noncomputable def krausOperatorOfChoiVector {n : Nat} {betaK : Type*} [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) :
    KrausOperator H K :=
  Matrix.toLin bH.toBasis bK.toBasis (fun p i => star (v (i, p)))
noncomputable def finiteKrausFamilyOfChoiVectors {m n : Nat} {betaK : Type*}
    [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin m → (Fin n × betaK → Complex)) :
    FiniteKrausFamily (Fin m) H K where
  operator a := krausOperatorOfChoiVector bH bK (v a)
namespace QuantumChannel
end QuantumChannel
end
end Semantics
end QEC


