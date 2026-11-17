-- Prove2me | Definitions.Def_GroupIsoPoly_Supplement_IsStableDerived
-- name    : GroupIsoPoly_Supplement_IsStableDerived
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:26:22.808894+00:00
-- url     : https://prove2.me/theorems/6659748c-e298-40c2-8f07-e30f72682abf
-- title:
--   Nondegeneracy and the stable range for derived classical groups
-- statement:
--   For a classical datum over $K$ of dimension $n$, **nondegenerate and in the stable range** means:
--
--   1. $\mathrm{SL}(n,K)$: $n\ge64$;
--   2. $\mathrm{Sp}$: $A$ alternating ($A_{ii}=0$, $A^{\mathsf T}=-A$), $\det A\ne0$, $n\ge64$, and Witt index $\ge32$;
--   3. $\mathrm{SU}$: $\sigma$ an automorphism of $K$ with $\sigma^2=\mathrm{id}\ne\sigma$ (so $K$ is a quadratic extension of the fixed field of $\sigma$), $H$ $\sigma$-Hermitian ($H_{ji}=\sigma(H_{ij})$), $\det H\ne0$, $n\ge64$, and Witt index $\ge32$;
--   4. $\Omega(Q)$: the polar form $b_Q(v,w)=Q(v+w)-Q(v)-Q(w)$ has trivial radical, $n$ is even in characteristic $2$, $n\ge64$, and some totally singular subspace ($Q=0$ on it) has dimension $\ge32$.
--
--   The **Witt index** $\ge r$ means some subspace of dimension $\ge r$ is totally isotropic (the form vanishes on it), using totally singular subspaces for a quadratic form.
--
--   This is the stable range of Remark 1 (natural dimension at least $64$, Witt index at least $32$), the standing hypothesis of Theorems 6.1–6.3 and C.9.
--
--   **Formalization Note** For a nondegenerate alternating form the Witt index is $n/2$, so the Witt clause for $\mathrm{Sp}$ is implied by $n\ge64$; it is kept as the paper states it, as is the parity clause in characteristic $2$.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), §6.1 and Remark 1, p.45 (PDF p.49)

import Mathlib
import Definitions.Def_GroupIsoPoly_Supplement_classicalGroup

set_option autoImplicit false

namespace GroupIsoPoly

namespace Supplement

variable {K : Type*} [Field K] {n : ℕ}

/-- The form `f` on `K^n` has Witt index at least `r`: some `K`-subspace of dimension at least `r` is
totally isotropic (`f` vanishes identically on it). -/
def WittIndexGE (r : ℕ) (f : (Fin n → K) → (Fin n → K) → K) : Prop :=
  ∃ W : Submodule K (Fin n → K), r ≤ Module.finrank K W ∧ ∀ v ∈ W, ∀ w ∈ W, f v w = 0

/-- **Nondegeneracy and the stable range** for a derived classical group datum.

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), §6.1 and Remark 1, p.45 (PDF p.49): "Recall that the
Witt index of a bilinear form is the largest dimension of a subspace on which the form vanishes
identically, using totally singular subspaces for a quadratic form. Orthogonal groups in
characteristic 2 have even natural dimension. We define the stable range of a classical group to mean
natural dimensions at least 64, and Witt indices at least 32 for symplectic, unitary, and orthogonal
factors."

* `SL(n, K)`: `n ≥ 64`;
* `Sp`: `A` alternating (`A_ii = 0`, `Aᵀ = −A`) and nondegenerate (`det A ≠ 0`), `n ≥ 64`, Witt index
  `≥ 32` (automatic: it is `n/2`);
* `SU`: `σ` an involutive automorphism of `K` different from the identity (so `K` is a quadratic
  extension of the fixed field of `σ`), `H` `σ`-Hermitian (`H_ji = σ(H_ij)`) and nondegenerate
  (`det H ≠ 0`), `n ≥ 64`, Witt index `≥ 32`;
* `Ω(Q)`: `Q` nondegenerate (its polar form `b_Q(v, w) = Q(v+w) − Q(v) − Q(w)` has trivial radical),
  `n` even in characteristic 2, `n ≥ 64`, and a totally singular subspace (`Q = 0` on it) of
  dimension `≥ 32`.

**Formalization Note.** In characteristic 2 a quadratic form with nondegenerate polar form already has
even dimension; the parity clause is kept as the paper states it. -/
def IsStableDerived : ClassicalDatum K n → Prop
  | .sl => 64 ≤ n
  | .sp A => 64 ≤ n ∧ (∀ i, A i i = 0) ∧ A.transpose = -A ∧ A.det ≠ 0 ∧
      WittIndexGE 32 (bilinOf A)
  | .su σ H => 64 ≤ n ∧ (∀ x, σ (σ x) = x) ∧ σ ≠ RingEquiv.refl K ∧
      (∀ i j, H j i = σ (H i j)) ∧ H.det ≠ 0 ∧ WittIndexGE 32 (sesqOf σ H)
  | .omega Q => 64 ≤ n ∧ (∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0) ∧
      (ringChar K = 2 → Even n) ∧ WittIndexGE 32 (fun v _ => Q v)

end Supplement

end GroupIsoPoly


