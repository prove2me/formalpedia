-- Prove2me | Definitions.Def_SubspaceConv_Supplement_spanCount
-- name    : SubspaceConv_Supplement_spanCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:46:26.960211+00:00
-- url     : https://prove2.me/theorems/c7567f11-02f8-4fd4-9e39-1d4ad2318bc8
-- title:
--   Exact-span counts $C(U)$
-- statement:
--   Let $v_1, \dots, v_\ell \in \mathbb F_q^n$ (repetitions and zero vectors allowed). For a subspace $U \le \mathbb F_q^n$,
--
--   $$C(U) = \#\{A \subseteq [\ell] : \operatorname{span}\{v_i : i \in A\} = U\}.$$
--
--   Subsets are sets of indices, so repeated vectors are distinct choices, and the empty set (with span $\{0\}$) is counted in $C(\{0\})$. These are the numbers computed in Theorem 5.
--
--   **Formalization Note** Indices are `Fin ℓ` (0-based), and $A$ ranges over finite sets of indices.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4e583122875209a3e25ee95aa3a7af933526e165d47c274634e604ab2), Theorem 5, p.14–15 (PDF p.15–16)

import Mathlib

set_option autoImplicit false

open Classical

namespace SubspaceConv.Supplement

/-- The **exact-span count** (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), Theorem 5, p.14–15 (PDF p.15–16)): for vectors
`v_1, …, v_ℓ ∈ F^n` and a subspace `U`, `C(U) = #{A ⊆ [ℓ] : span{v_i : i ∈ A} = U}`.

**Formalization Note** Indices are `Fin ℓ` (0-based) and `A` ranges over `Finset (Fin ℓ)`, so
repeated and zero vectors are distinct indexed choices, and the empty set (span `{0}`) is counted
in `C(⊥)`, as on p.15. -/
noncomputable def spanCount {F : Type*} [Field F] {n ℓ : ℕ} (v : Fin ℓ → Fin n → F)
    (U : Submodule F (Fin n → F)) : ℕ :=
  (Finset.univ.filter
    (fun A : Finset (Fin ℓ) => Submodule.span F (v '' (A : Set (Fin ℓ))) = U)).card

end SubspaceConv.Supplement


