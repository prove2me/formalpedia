-- Prove2me | Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
-- name    : AlgebraicGeometry_OModulePresheafEulerChar
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/89412961-9262-5de3-8f32-0939ce0bd932
-- title:
--   Čech ranks and Euler characteristic of an ordered affine cover
-- statement:
--   The standing context is a commutative ring $R$, a scheme $V$ with a morphism $\pi\colon V \to \operatorname{Spec} R$, a datum $F$ of type `OModulePresheaf π` (a presheaf of modules on the opens of $V$: an $R$-module $F(U)$ for each open $U$, carrying also a $\Gamma(V,U)$-module structure compatible with the $R$-action through $\pi$, together with $R$-linear restriction maps semilinear for restriction of functions and satisfying the presheaf identities), and an ordered affine cover $K$ of $V$, that is a finite linearly ordered index type $K.\iota$ together with affine opens $U_i$ whose supremum is $\top$. For such data the alternating Čech complex is already available: the $i$-cochains are the families $(c_s)$ indexed by strictly increasing $s\colon \{0,\dots,i\} \to K.\iota$ with $c_s \in F(\bigcap_j U_{s(j)})$, the differential is the usual alternating sum of face restrictions, `F.H0 K` is the kernel of $d^0$ and `F.HSucc K i` is $\ker d^{i+1}$ modulo the image of $d^i$.
--
--   Two numerical invariants are defined. First, `F.cechFinrank K : ℕ → ℕ` sends $0$ to $\operatorname{finrank}_R$ of `F.H0 K` and $i+1$ to $\operatorname{finrank}_R$ of `F.HSucc K i`; here `Module.finrank` is Mathlib's rank, which takes the value $0$ on modules that are not finite and free of finite rank, so no finiteness hypothesis is imposed. Second,
--   $$\mathtt{F.eulerChar K} \;=\; \sum_{i=0}^{\#K.\iota - 1} (-1)^i \,\mathtt{F.cechFinrank K}\,i \in \mathbb{Z},$$
--   the alternating sum truncated at the number of charts; for a cover with $n$ charts there are no strictly increasing chains of $i+1$ indices once $i \ge n$, and for an empty index type the sum is empty and the value is $0$. The three accompanying lemmas record the defining equations for the two cases of `cechFinrank` and for `eulerChar`. Nothing is asserted beyond these definitions: additivity, independence of the cover and the like are separate theorems about them.
--
--   **Relation to Mathlib.** The ranks are Mathlib's `Module.finrank`, with its convention of value $0$ outside the finite free case. Mathlib has no counterpart of this Čech-theoretic Euler characteristic attached to a presheaf-of-modules datum and an ordered affine cover; it is the project's own, built on the project's `OModulePresheaf` and `Scheme.OrderedAffineCover`.
--
--   **Where it is used.** These invariants belong to the project's self-contained layer of coherent cohomology on schemes over a base ring, where cohomology is computed from a fixed finite ordered affine cover rather than by derived functors; they provide the numerical bookkeeping (ranks of Čech cohomology and their alternating sum) used in the geometric input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OModulePresheafEulerChar.lean

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

def cechFinrank : ℕ → ℕ
  | 0 => Module.finrank R (F.H0 K)
  | i + 1 => Module.finrank R (F.HSucc K i)

theorem cechFinrank_zero : F.cechFinrank K 0 = Module.finrank R (F.H0 K) := rfl

theorem cechFinrank_succ (i : ℕ) : F.cechFinrank K (i + 1) = Module.finrank R (F.HSucc K i) := rfl

def eulerChar : ℤ :=
  ∑ i ∈ Finset.range (Fintype.card K.ι), (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ)

theorem eulerChar_def :
    F.eulerChar K = ∑ i ∈ Finset.range (Fintype.card K.ι), (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ) := rfl

end AlgebraicGeometry.OModulePresheaf

end


