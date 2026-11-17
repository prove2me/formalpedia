-- Prove2me | Definitions.Def_PersistQMem_Supplement_IsMajoranaCrossFamily
-- name    : PersistQMem_Supplement_IsMajoranaCrossFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:14:48.548038+00:00
-- url     : https://prove2.me/theorems/6f8dd821-69e5-4480-80cf-2c6c9c29981d
-- title:
--   Quadratic Majorana cross family and moment certificate
-- statement:
--   For two $n$-mode fermionic factors, use the canonical global Jordan–Wigner Majoranas $c_1,\ldots,c_{4n}$ on the joint $2n$-qubit source. The requested cross observables are
--
--   $$
--   C_{ab,cd}=(i c_a c_b)(i c_{2n+c}c_{2n+d}),\qquad a<b,\ c<d,
--   $$
--
--   and `IsMajoranaCrossFamily n G` says that $G$ enumerates all $M=[n(2n-1)]^2$ such observables. The associated positive source map is
--
--   $$
--   \mathcal A(X)=\sum_{r=1}^{4n}c_rXc_r,
--   $$
--
--   and the explicit certificate is $\widehat H_p(L)=\frac{(2p)!}{p!}((1+e)L/2)^p$.
--
--   These objects retain the full joint source, so entangled states and coherence between parity sectors are not factored or discarded.
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §2.3, (12)–(17), pp.6–7 (PDF pp.9–10), and §9.2

import Mathlib
import Definitions.Def_PersistQMem_Supplement_IsWeightPauliFamily
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace PersistQMem
namespace Supplement

/-- The Jordan--Wigner Pauli word of Majorana generator `r` on `m` fermionic modes:
`Z` on earlier modes and `X` (even `r`) or `Y` (odd `r`) at mode `r/2`. -/
def majoranaWord (m : Nat) (r : Fin (2 * m)) : PauliWord m :=
  fun i =>
    if i.val < r.val / 2 then 3
    else if i.val = r.val / 2 then if r.val % 2 = 0 then 1 else 2
    else 0

/-- Canonical Jordan--Wigner Majorana reflection on `m` modes. -/
noncomputable def majoranaMatrix (m : Nat) (r : Fin (2 * m)) :
    Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) Complex :=
  pauliMatrix (majoranaWord m r)

/-- The `r`-th global Majorana on the joint source of two `n`-mode systems.  There are `4n`
generators acting on `2n` qubits. -/
noncomputable def globalMajorana (n : Nat) (r : Fin (4 * n)) :
    Matrix (Fin (2 ^ (2 * n))) (Fin (2 ^ (2 * n))) Complex :=
  majoranaMatrix (2 * n) (Fin.cast (by omega) r)

/-- An ordered pair `a < b` of local Majorana indices in one `n`-mode factor. -/
abbrev MajoranaPair (n : Nat) := {q : Fin (2 * n) × Fin (2 * n) // q.1 < q.2}

/-- A pair of local quadratic labels, one for subsystem `A` and one for subsystem `B`. -/
abbrev CrossLabel (n : Nat) := MajoranaPair n × MajoranaPair n

def leftGlobalIndex (n : Nat) (a : Fin (2 * n)) : Fin (4 * n) :=
  ⟨a.val, by omega⟩

def rightGlobalIndex (n : Nat) (a : Fin (2 * n)) : Fin (4 * n) :=
  ⟨2 * n + a.val, by omega⟩

/-- The cross observable `C_{ab,cd} = (i c_a c_b)(i c_{2n+c} c_{2n+d})`.  With the global
Jordan--Wigner generators this equals `G^A_ab tensor G^B_cd`, including the parity string on the
second factor. -/
noncomputable def crossObservable (n : Nat) (q : CrossLabel n) :
    Matrix (Fin (2 ^ (2 * n))) (Fin (2 ^ (2 * n))) Complex :=
  let a := q.1.1.1
  let b := q.1.1.2
  let c := q.2.1.1
  let d := q.2.1.2
  (Complex.I • (globalMajorana n (leftGlobalIndex n a) *
      globalMajorana n (leftGlobalIndex n b))) *
    (Complex.I • (globalMajorana n (rightGlobalIndex n c) *
      globalMajorana n (rightGlobalIndex n d)))

/-- `M = [n(2n-1)]^2`, the number of quadratic cross observables. -/
def crossCount (n : Nat) : Nat := (n * (2 * n - 1)) ^ 2

/-- `G` is an enumeration, without repetition, of all quadratic Majorana cross observables. -/
def IsMajoranaCrossFamily (n : Nat)
    (G : Fin (crossCount n) ->
      Matrix (Fin (2 ^ (2 * n))) (Fin (2 ^ (2 * n))) Complex) : Prop :=
  exists e : Fin (crossCount n) ≃ CrossLabel n,
    forall j, G j = crossObservable n (e j)

/-- The Clifford conjugation map on `m` modes,
`A_m(X) = sum_{r=1}^{2m} c_r X c_r`. -/
noncomputable def cliffordMap (m : Nat) :
    Module.End Complex (Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) Complex) where
  toFun X := ∑ r, majoranaMatrix m r * X * majoranaMatrix m r
  map_add' X Y := by simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' a X := by
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    rw [Finset.smul_sum]
    simp

/-- The positive joint-source map `A(X) = sum_r c_r X c_r` of (14), with `L = 4n`. -/
noncomputable def majoranaMap (n : Nat) :
    Module.End Complex (Matrix (Fin (2 ^ (2 * n))) (Fin (2 ^ (2 * n))) Complex) :=
  cliffordMap (2 * n)

/-- A rank-one density matrix, i.e. a pure state. -/
def IsPureDensity {D : Nat} (rho : Matrix (Fin D) (Fin D) Complex) : Prop :=
  WildeQIT.IsDensityOperator rho /\ rho.rank = 1

/-- The explicit all-size certificate
`Hhat_p(L) = (2p)!/p! * (((1+e)L)/2)^p` from (17). -/
noncomputable def majoranaCertificate (p L : Nat) : Real :=
  ((Nat.factorial (2 * p) : Nat) : Real) / (Nat.factorial p : Nat) *
    (((1 + Real.exp 1) * (L : Real) / 2) ^ p)

end Supplement
end PersistQMem


