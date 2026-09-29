-- Prove2me | Definitions.Def_Deformations_TaylorWilesLocal
-- name    : Deformations_TaylorWilesLocal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/5689b263-b6eb-509c-a756-255cb04c86ce
-- title:
--   Adjoint action, discriminant and trace-zero matrices
-- statement:
--   Over a field $k$, write $M_2(k)$ for the algebra of $2\times 2$ matrices indexed by `Fin 2`. Three objects attached to this algebra are introduced in the `TaylorWiles` namespace. First, [`TaylorWiles.adAction`](../def/Deformations_TaylorWilesLocal.html#L13) assigns to a matrix $M \in M_2(k)$ the $k$-linear endomorphism of $M_2(k)$ given as the difference of left multiplication by $M$ and right multiplication by $M$; equivalently, and this is recorded as a simp lemma, it sends $X$ to $MX - XM$. Thus its kernel is the centraliser of $M$ and its range is the space of commutators $[M,\,\cdot\,]$. Second, [`TaylorWiles.disc`](../def/Deformations_TaylorWilesLocal.html#L18) is the scalar $(\operatorname{tr} M)^2 - 4\det M$, the discriminant of the characteristic polynomial of $M$; over a field where this polynomial splits, its non-vanishing says exactly that $M$ has two distinct eigenvalues, i.e. that $M$ is regular semisimple. Third, for a field $k$ given as an explicit argument, [`TaylorWiles.traceZero`](../def/Deformations_TaylorWilesLocal.html#L22) is the $k$-submodule of $M_2(k)$ defined as the kernel of the trace regarded as a $k$-linear map $M_2(k) \to k$; a companion lemma records that membership in it is equivalent to the vanishing of the trace. This submodule is the underlying space $\mathfrak{sl}_2(k)$ of the adjoint representation $\mathrm{ad}^0$ of a representation into $\mathrm{GL}_2(k)$, on which the group acts by conjugation. All three are plain definitions, with no side conditions on $M$ or on $k$; in particular `disc` is a scalar-valued function defined for every matrix, and no semisimplicity or regularity is built into any of them.
--
--   **Relation to Mathlib.** Built directly from Mathlib's `LinearMap.mulLeft`, `LinearMap.mulRight` and `Matrix.traceLinearMap`; the three notions themselves are the project's own abbreviations for $2\times 2$ matrices over a field.
--
--   **Where it is used.** These are the linear-algebra ingredients of the local analysis at a Taylor–Wiles prime $q$: the condition $\operatorname{disc}(\bar\rho(\mathrm{Frob}_q)) \neq 0$ expresses that Frobenius has distinct eigenvalues, while the kernel and range of the commutator endomorphism on the trace-zero subspace give the local invariants and coboundaries entering the dimension counts for $\mathrm{ad}^0\bar\rho$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Deformations_TaylorWilesLocal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Module

namespace TaylorWiles

variable {k : Type*} [Field k]

local notation "M₂ " k => Matrix (Fin 2) (Fin 2) k

noncomputable def adAction (M : M₂ k) : Module.End k (M₂ k) :=
  LinearMap.mulLeft k M - LinearMap.mulRight k M

@[simp] lemma adAction_apply (M X : M₂ k) : adAction M X = M * X - X * M := rfl

def disc (M : M₂ k) : k := M.trace ^ 2 - 4 * M.det

variable (k) in

noncomputable def traceZero : Submodule k (M₂ k) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 2) k k)

@[simp] lemma mem_traceZero_iff {X : M₂ k} : X ∈ traceZero k ↔ X.trace = 0 :=
  Iff.rfl

end TaylorWiles


