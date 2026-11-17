-- Prove2me | Definitions.Def_AsymSpecConn_Supplement_singletonUpperQuantum
-- name    : AsymSpecConn_Supplement_singletonUpperQuantum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:21:45.016053+00:00
-- url     : https://prove2.me/theorems/dcc42d82-005e-44f8-b45c-803d77b7b34c
-- title:
--   Singleton upper quantum functional and weighted flattening-rank product
-- statement:
--   For a probability vector $\theta\in\mathcal P([k])$, the **singleton upper quantum functional** $F^\theta$ assigns zero to the zero tensor and, to a nonzero complex tensor $t$, assigns
--
--   $$
--   F^\theta(t)=2^{\max\{\sum_i\theta_i H(\lambda^{(i)}): (\lambda^{(1)},\ldots,\lambda^{(k)})\text{ lies in the entanglement polytope of }t\}}.
--   $$
--
--   The associated weighted flattening-rank product is $w_\theta(t)=\prod_i R_i(t)^{\theta_i}$, with $0^0=1$.
--
--   This functional is the equivalent moment-polytope form of the isotypic-support supremum used in §5.2 and is the object in Theorem 5.4.
--
--   **Formalization Note** The imported entropy uses natural logarithms, so exponentiating its maximum gives the same value as $2$ raised to the source's base-two entropy. Chosen bases convert abstract finite-dimensional legs to coordinate arrays; the value is invariant under invertible changes of basis.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac698c902a02f2df11dd0671a5d9ca373aed822ae44b7e2640fc152c7d), Definition 5.3 and Theorem 5.4 p.39

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_QuantumFunctional
import Definitions.Def_AsymSpecConn_Fw
import Definitions.Def_AsymSpecConn_irreducibleSet
import Definitions.Def_AsymSpecConn_flatRank

set_option autoImplicit false

open scoped NNReal ENNReal

namespace AsymSpecConn.Supplement

/-- Coordinate dimensions obtained from Mathlib's chosen bases of the legs of a concrete
complex tensor. -/
noncomputable def coordDim {k : ℕ} (X : MME.TensorObj ℂ k) (i : Fin k) : ℕ :=
  Fintype.card (Module.Free.ChooseBasisIndex ℂ (X.V i))

/-- A concrete tensor written as an ordinary coordinate array using arbitrary chosen bases.
Changing those bases does not change the entanglement polytope, hence does not change the
quantum functional. -/
noncomputable def tensorCoordinates {k : ℕ} (X : MME.TensorObj ℂ k) :
    MomentPolytopes.QuantumFunctionals.Ten k 1 (coordDim X) :=
  fun x =>
    let basis := Basis.piTensorProduct (fun i => Module.Free.chooseBasis ℂ (X.V i))
    basis.repr X.t (fun i => (Fintype.equivFin (Module.Free.ChooseBasisIndex ℂ (X.V i))).symm (x.2 i))

/-- The singleton upper quantum functional `F^theta` of §5.2 (p.39) on a concrete tensor:
zero at the zero tensor, and `exp(max ∑_i theta_i H(p_i))` otherwise.

**Formalization Note** The imported moment-polytope definition uses natural logarithms, so
`exp(E_nat)` equals the source's `2^(E_base2)`. The entanglement-polytope maximum is equivalent
to the source's Schur--Weyl isotypic-support supremum. Boundary weights `theta_i = 0` are retained. -/
noncomputable def singletonUpperQuantumObj {k : ℕ} (theta : Fin k → ℝ)
    (X : MME.TensorObj ℂ k) : ℝ≥0 := by
  classical
  exact if X.t = 0 then 0 else
    Real.toNNReal (Real.exp
      (MomentPolytopes.QuantumFunctionals.logQuantumFunctional theta (tensorCoordinates X)))

/-- The singleton upper quantum functional on tensor-equivalence classes. The selected quotient
representative is immaterial because the moment-polytope value is invariant under invertible
changes of basis and deletion of unused ambient directions. -/
noncomputable def singletonUpperQuantum {k : ℕ} (theta : Fin k → ℝ) :
    MME.TensorQ ℂ k → ℝ≥0 :=
  fun s => singletonUpperQuantumObj theta (Quotient.out s)

/-- `w_theta = ∏_i R_i^{theta_i}` from Corollary 5.2 and Theorem 5.4, with `0^0=1`. -/
noncomputable def singletonRankWeight {k : ℕ} (hk : 2 ≤ k) (theta : Fin k → ℝ) :
    MME.TensorQ ℂ k → ℝ≥0 :=
  fun s => ∏ i, (AsymSpecConn.flatRankQ hk i s : ℝ≥0) ^ theta i

end AsymSpecConn.Supplement


