-- Prove2me | Definitions.Def_Deformations_MatrixRepresentation
-- name    : Deformations_MatrixRepresentation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/a4004b19-d3fb-55b3-a6ed-a2ba78a5163e
-- title:
--   The linear representation attached to a matrix representation
-- statement:
--   Let $n$ be a finite type with decidable equality, $G$ a group and $k$ a field. For a monoid homomorphism $\rho\colon G \to \mathrm{GL}_n(k)$ (Mathlib's `GL n k`, the units of the ring of $n \times n$ matrices over $k$), [`Deformation.matrixRepresentation ρ`](../def/Deformations_MatrixRepresentation.html#L15) is the linear representation of $G$ on the module $n \to k$ of $k$-valued functions on $n$, i.e. on column vectors $k^n$: it is obtained by composing $\rho$ with the monoid homomorphism sending an invertible matrix to the corresponding unit of $\mathrm{End}_k(k^n)$, and then passing to the underlying endomorphism. Thus it is a monoid homomorphism $G \to (\mathrm{End}_k(k^n))^{\times}$ in the sense of Mathlib's `Representation k G (n → k)`, equivalently a $k[G]$-module structure on $k^n$.
--
--   The accompanying simp lemma [`Deformation.matrixRepresentation_apply`](../def/Deformations_MatrixRepresentation.html#L19) records the expected formula: for $g \in G$, the endomorphism `matrixRepresentation ρ g` is multiplication of a column vector by the matrix underlying $\rho(g)$, namely `Matrix.mulVecLin (ρ g).val`, the $k$-linear map $v \mapsto \rho(g)\,v$. Here $G$ and $k$ are taken in a common universe, while the index type $n$ lies in the lowest universe.
--
--   The point of the construction is that predicates formulated for abstract linear representations — irreducibility, absolute irreducibility, the shape of the commutant — can be applied directly to a homomorphism given in matrix form, without choosing a basis by hand each time.
--
--   **Relation to Mathlib.** Both the target type `Representation k G (n → k)` and the ingredients (`Matrix.GeneralLinearGroup.toLin`, `Matrix.mulVecLin`) are Mathlib's; this module only packages the composite under a name, together with its evaluation formula.
--
--   **Where it is used.** This bridge is what allows representation-theoretic hypotheses — in particular absolute irreducibility, as it enters Burnside-type spanning statements and Schur-type lemmas on commutants — to be imposed on the mod $p$ and mod $p^n$ matrix representations that occur throughout the deformation-theoretic part of the argument. It is the discrete counterpart of the construction attaching a representation to a continuous matrix-valued Galois representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Deformations_MatrixRepresentation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace Deformation

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G]
variable {k : Type u} [Field k]

noncomputable def matrixRepresentation (ρ : G →* GL n k) : Representation k G (n → k) :=
  (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ)

@[simp]
lemma matrixRepresentation_apply (ρ : G →* GL n k) (g : G) :
    matrixRepresentation ρ g = Matrix.mulVecLin (ρ g).val :=
  Matrix.GeneralLinearGroup.coe_toLin _

end Deformation


