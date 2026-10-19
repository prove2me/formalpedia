-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapA06_Model
-- name    : QAlgorithms_Papers_RoadmapA06_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:25:12.951023+00:00
-- url     : https://prove2.me/theorems/798a8db4-8ea7-462f-8c68-45b14985cea7
-- title:
--   Explicit decoders using fixed-point amplitude amplification based on QSVT: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Explicit decoders using fixed-point amplitude amplification based on QSVT, arXiv:2405.06051v6, https://arxiv.org/abs/2405.06051v6. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_GeneralizedYK
noncomputable section

open scoped Matrix ComplexConjugate ENNReal

namespace QAlgorithms.Papers.RoadmapA06

/-- The state `omega^{RE}` of Eq. (45), arXiv:2405.06051v6, PDF p.12.
It is obtained from Eq. (9)'s normalized purification by tracing out `DB'`.
The finite indices of `R` and `B'` copy the bases of `A` and `B`. -/
def decouplingState {A B E D : ℕ} [NeZero A] [NeZero B] [NeZero E] [NeZero D]
    (V : Matrix (Fin E × Fin D) (Fin A × Fin B) ℂ) :
    Matrix (Fin A × Fin E) (Fin A × Fin E) ℂ :=
  traceRight ((pureDensity (communicationState V)).submatrix
    (fun p : (Fin A × Fin E) × (Fin D × Fin B) => (p.1.1, (p.1.2, p.2)))
    (fun p : (Fin A × Fin E) × (Fin D × Fin B) => (p.1.1, (p.1.2, p.2))))

/-- The chosen `U_F : ABF -> ED` in its input and output computational bases
(Eqs. (19)--(20), PDF p.6). Both sides are flattened most significant factor first.
The compatible layout is included in this operation, hence in its gate cost. -/
def dilationMatrix {A B E D F : ℕ}
    (layout : (Fin A × Fin B) × Fin F ≃ Fin E × Fin D)
    (U : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) :
    Matrix (Fin (E * D)) (Fin ((A * B) * F)) ℂ :=
  U.submatrix finProdFinEquiv.symm
    (fun j : Fin ((A * B) * F) =>
      let p : Fin (A * B) × Fin F := finProdFinEquiv.symm j
      layout (finProdFinEquiv.symm p.1, p.2))

/-- `C(U_F)` of Theorem 4 (PDF p.12), using the single- and two-qubit
unitary gate model of p.4. Frozen `ChannelCircuit` explicitly embeds a finite
register of dimension `d` in `ceil(log_2 d)` qubits, initializes added qubits,
and discards garbage. The source permits polynomially many ancillary qubits:
`ancillaBudget` is one polynomial allowance, chosen before every instance in
the theorem, evaluated at the number of qubits of `ED`. The value is infinity
if there is no realization within that allowance; finiteness is a conclusion
below, not an assumption. -/
def dilationGateComplexity {A B E D F : ℕ}
    (ancillaBudget : Polynomial ℕ)
    (layout : (Fin A × Fin B) × Fin F ≃ Fin E × Fin D)
    (U : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) : ℕ∞ :=
  circuitComplexity (ancillaBudget.eval (Nat.clog 2 (E * D)))
    (conjSuperop (dilationMatrix layout U))


end QAlgorithms.Papers.RoadmapA06


