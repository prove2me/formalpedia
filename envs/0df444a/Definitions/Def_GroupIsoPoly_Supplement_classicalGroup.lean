-- Prove2me | Definitions.Def_GroupIsoPoly_Supplement_classicalGroup
-- name    : GroupIsoPoly_Supplement_classicalGroup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:25:51.37621+00:00
-- url     : https://prove2.me/theorems/1d6e6749-930a-40ce-b83f-2fbe67849fe7
-- title:
--   The derived classical groups $\mathrm{SL}$, $\mathrm{Sp}$, $\mathrm{SU}$, $\Omega(Q)$ in their natural representations
-- statement:
--   Let $K$ be a field. A **classical datum** of dimension $n$ is one of:
--
--   1. `sl`: the special linear group $\mathrm{SL}(n,K)=\{g\in\mathrm{GL}(n,K):\det g=1\}$;
--   2. `sp A`: the symplectic group $\{g:g^{\mathsf T}Ag=A\}$ of the form $b_A(v,w)=v^{\mathsf T}Aw$;
--   3. `su σ H`: the special unitary group $\mathrm{SU}=\mathrm U\cap\mathrm{SL}$, where $\mathrm U=\{g:h(gv,gw)=h(v,w)\}$ is the isometry group of the $\sigma$-sesquilinear form $h(v,w)=\sigma(v)^{\mathsf T}Hw$;
--   4. `omega Q`: the group $\Omega(Q)=[\mathrm O(Q),\mathrm O(Q)]$, the commutator subgroup of the orthogonal group $\mathrm O(Q)=\{g:Q(gv)=Q(v)\ \forall v\}$ of a quadratic form $Q$ on $K^n$.
--
--   Each group is a subgroup of $\mathrm{GL}(n,K)$ acting on its **natural module** $K^n$. Nondegeneracy of the forms and the stable range are imposed separately (`IsStableDerived`).
--
--   These are the groups of §6.1, the factors of the products $D$ in Theorems 6.3 and C.9.
--
--   **Formalization Note** $\Omega(Q)$ is defined as $[\mathrm O(Q),\mathrm O(Q)]$, which the paper identifies with $\Omega(Q)$ in the stable range. Isometry groups are defined by preservation of the form on all pairs of vectors; the closure proofs are structural.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), §6.1, p.45 (PDF p.49)

import Mathlib

set_option autoImplicit false

namespace GroupIsoPoly

namespace Supplement

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The action of a matrix `g ∈ GL(n, K)` on a column vector `v ∈ K^n`. -/
def glAct (g : GL (Fin n) K) (v : Fin n → K) : Fin n → K :=
  (g : Matrix (Fin n) (Fin n) K) *ᵥ v

/-- The isometry group `{g ∈ GL(n, K) : f(gv, gw) = f(v, w) for all v, w}` of a two-argument form
`f` on `K^n`. -/
def isomGroup (f : (Fin n → K) → (Fin n → K) → K) : Subgroup (GL (Fin n) K) where
  carrier := {g | ∀ v w, f (glAct g v) (glAct g w) = f v w}
  mul_mem' := by
    intro a b ha hb v w
    simp only [Set.mem_ofPred_eq, glAct] at *
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]
  one_mem' := by
    intro v w
    simp [glAct]
  inv_mem' := by
    intro a ha v w
    simp only [Set.mem_ofPred_eq, glAct] at *
    have h := ha ((↑a⁻¹ : Matrix (Fin n) (Fin n) K) *ᵥ v) ((↑a⁻¹ : Matrix (Fin n) (Fin n) K) *ᵥ w)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec] at h
    exact h.symm

/-- The orthogonal group `O(Q) = {g ∈ GL(n, K) : Q(gv) = Q(v) for all v}` of a quadratic form. -/
def orthGroup (Q : QuadraticForm K (Fin n → K)) : Subgroup (GL (Fin n) K) where
  carrier := {g | ∀ v, Q (glAct g v) = Q v}
  mul_mem' := by
    intro a b ha hb v
    simp only [Set.mem_ofPred_eq, glAct] at *
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
  one_mem' := by
    intro v
    simp [glAct]
  inv_mem' := by
    intro a ha v
    simp only [Set.mem_ofPred_eq, glAct] at *
    have h := ha ((↑a⁻¹ : Matrix (Fin n) (Fin n) K) *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h
    exact h.symm

/-- The bilinear form `b_A(v, w) = vᵀ A w` of a matrix `A`. -/
def bilinOf (A : Matrix (Fin n) (Fin n) K) (v w : Fin n → K) : K :=
  v ⬝ᵥ (A *ᵥ w)

/-- The `σ`-sesquilinear form `h(v, w) = σ(v)ᵀ H w` of a matrix `H` (semilinear in the first
argument). -/
def sesqOf (σ : K ≃+* K) (H : Matrix (Fin n) (Fin n) K) (v w : Fin n → K) : K :=
  (fun i => σ (v i)) ⬝ᵥ (H *ᵥ w)

/-- **Data of a derived classical group in its natural representation on `K^n`.**

* `sl`: the special linear group `SL(n, K)`;
* `sp A`: the symplectic group of the alternating form with Gram matrix `A`;
* `su σ H`: the special unitary group of the `σ`-Hermitian form with Gram matrix `H`, where `σ` is the
  nontrivial automorphism of the quadratic extension `K/K^σ`;
* `omega Q`: the group `Ω(Q) = [O(Q), O(Q)]` of a quadratic form `Q`.

The conditions making these forms nondegenerate and in the stable range are in `IsStableDerived`. -/
inductive ClassicalDatum (K : Type*) [Field K] (n : ℕ) where
  | sl : ClassicalDatum K n
  | sp (A : Matrix (Fin n) (Fin n) K) : ClassicalDatum K n
  | su (σ : K ≃+* K) (H : Matrix (Fin n) (Fin n) K) : ClassicalDatum K n
  | omega (Q : QuadraticForm K (Fin n → K)) : ClassicalDatum K n

/-- **The derived classical groups `SL(n, F)`, `Sp(2m, F)`, `SU(n, K)`, `Ω(Q)` as subgroups of
`GL(n, K)`.**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), §6.1, p.45 (PDF p.49): "The special linear group
SL(n, F). The symplectic group Sp(2m, F), preserving a nondegenerate alternating form on F^2m. The
unitary group U(n, K), preserving a nondegenerate σ-Hermitian form on K^n, and its determinant-one
subgroup SU(n, K). The orthogonal group O(Q), preserving a specified nondegenerate quadratic form Q on
F^n, and the subgroup Ω(Q). In the stable range considered below, Ω(Q) = [O(Q), O(Q)]."

**Formalization Note.** `SL` is the kernel of the determinant; `Sp` and `U` are isometry groups of the
form `vᵀAw`, resp. `σ(v)ᵀHw`; `SU = U ∩ SL`; `Ω(Q)` is defined as the commutator subgroup of `O(Q)`,
the paper's identification in the stable range. The group is given in its natural representation:
its elements are the matrices themselves. -/
def classicalGroup : ClassicalDatum K n → Subgroup (GL (Fin n) K)
  | .sl => (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker
  | .sp A => isomGroup (bilinOf A)
  | .su σ H => isomGroup (sesqOf σ H) ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker
  | .omega Q => ⁅orthGroup Q, orthGroup Q⁆

end Supplement

end GroupIsoPoly


