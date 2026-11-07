-- Prove2me | Definitions.Def_SymCircMM_permRep
-- name    : SymCircMM_permRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:29:41.896193+00:00
-- url     : https://prove2.me/theorems/d63dee9c-f4db-407b-aa48-adfc1bb1df93
-- title:
--   The permutation representation, the form $\langle x,y\rangle$, isotypic components and the spaces $A_i$, $B_i$
-- statement:
--   Let $G\le S_n$ be a group of permutations of $[n]$ and $F$ a field.
--
--   1. The **permutation representation** of $G$ is $V=F^n$ with $\rho(g)$ the linear extension of $e_i\mapsto e_{g(i)}$ on the canonical basis.
--   2. The standard bilinear form on $V$ is $\langle x,y\rangle=\sum_{j=1}^n x_jy_j$.
--   3. For a subrepresentation $W$ of $V$, the **$W$-isotypic component** of $V$ is the sum of all subrepresentations of $V$ equivalent to $W$.
--   4. For a subspace $U\le V$, the matrices all of whose rows lie in $U$, and the matrices all of whose columns lie in $U$, form subspaces of $F^{n\times n}$. With $U=U_i$ and $U=U_{i^*}$ these are the spaces $A_i$ and $B_i$ of §4.2.
--
--   The rows of an $A$-matrix and the columns of a $B$-matrix each carry the permutation representation under the action (2); these are the objects of the lower-bound argument.
--
--   **Formalization Note** Vectors are functions $\iota\to F$ and $(\rho(g)v)(j)=v(g^{-1}j)$, which sends $e_i$ to $e_{g(i)}$. Subrepresentations, equivalence and duals are Mathlib's `Subrepresentation`, `Representation.Equiv` and `Representation.dual`.
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), §3, p.8 (PDF p.9); §4.2, pp.10–12 (PDF pp.11–13), display (4)

import Mathlib

set_option autoImplicit false

namespace SymCircMM

variable {ι : Type} [Fintype ι]

/-- The **permutation representation** `(F^n, ρ)` of a group `G ≤ S_n` (Dahan, Dawar, Kush, Pago,
*Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), §3, p.8 (PDF p.9)):
`ρ(g)` is the linear extension of `e_i ↦ e_{g(i)}` on the canonical basis.

**Formalization Note.** Vectors are functions `v : ι → F` (`n = card ι`) and `(ρ g v)(j) = v(g⁻¹ j)`,
which sends `e_i = Pi.single i 1` to `e_{g i}`. `G` is a subgroup of `Equiv.Perm ι`. -/
def permRep (F : Type) [Field F] (G : Subgroup (Equiv.Perm ι)) : Representation F G (ι → F) where
  toFun σ := LinearMap.funLeft F F ((σ : Equiv.Perm ι).symm)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The standard bilinear form `⟨x, y⟩ = ∑_j x_j y_j` on `V = F^n` (§4.2, p.10 (PDF p.11)). -/
def dotForm {F : Type} [Field F] (x y : ι → F) : F := ∑ j, x j * y j

/-- The `W`-**isotypic component** of the permutation representation `V` (§3, p.8 (PDF p.9)): the sum
of all subrepresentations of `V` equivalent to `W`. -/
noncomputable def isotypic {F : Type} [Field F] {G : Subgroup (Equiv.Perm ι)}
    (W : Subrepresentation (permRep F G)) : Submodule F (ι → F) :=
  ⨆ (W' : Subrepresentation (permRep F G))
    (_ : Nonempty (W'.toRepresentation.Equiv W.toRepresentation)), W'.toSubmodule

/-- The matrices all of whose rows lie in `U` (§4.2, "Restrictions", p.12 (PDF p.13): `A_i` for
`U = U_i`). A row of `X` is `X a = (X_{a,j})_j`. -/
def rowsIn {F : Type} [Field F] (U : Submodule F (ι → F)) : Submodule F (Matrix ι ι F) where
  carrier := {X | ∀ a, X a ∈ U}
  add_mem' hX hY a := U.add_mem (hX a) (hY a)
  zero_mem' _ := U.zero_mem
  smul_mem' c _ hX a := U.smul_mem c (hX a)

/-- The matrices all of whose columns lie in `U` (§4.2, "Restrictions", p.12 (PDF p.13): `B_i` for
`U = U_{i*}`). A column of `Y` is `(Y_{j,b})_j`. -/
def colsIn {F : Type} [Field F] (U : Submodule F (ι → F)) : Submodule F (Matrix ι ι F) where
  carrier := {Y | ∀ b, (fun j => Y j b) ∈ U}
  add_mem' hX hY b := U.add_mem (hX b) (hY b)
  zero_mem' _ := U.zero_mem
  smul_mem' c _ hX b := U.smul_mem c (hX b)

end SymCircMM


