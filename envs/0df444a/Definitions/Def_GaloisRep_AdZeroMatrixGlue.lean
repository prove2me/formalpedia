-- Prove2me | Definitions.Def_GaloisRep_AdZeroMatrixGlue
-- name    : GaloisRep_AdZeroMatrixGlue
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/dc447e3f-d5d5-5f2c-8ca5-b32470e1e02f
-- title:
--   Matrix model for trace-zero endomorphisms of ρˉ​
-- statement:
--   Throughout, $k$ is a field and $\bar\rho$ is a [`ResidualGaloisRep k`](../def/GaloisRep_Residual.html#L22): a $k$-vector space $V$ with $\dim_k V = 2$, together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = \overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ to $\operatorname{End}_k(V)$ which is trivial on the elements fixing some finite-dimensional intermediate field. The underlying module of the adjoint representation $\mathrm{ad}^0\bar\rho$ is the submodule $\ker(\operatorname{tr}) \subseteq \operatorname{End}_k(V)$, where $\operatorname{tr} =$ `LinearMap.trace k ρbar.V`, while on the matrix side [`TaylorWiles.traceZero k`](../def/Deformations_TaylorWilesLocal.html#L22) is the kernel of the trace as a linear form on $M_2(k) =$ `Matrix (Fin 2) (Fin 2) k`, i.e. $\mathfrak{sl}_2(k)$.
--
--   Given in addition a basis $b$ of $V$ indexed by `Fin 2`, the first result identifies $\ker(\operatorname{tr})$ with the preimage (`Submodule.comap`) of [`TaylorWiles.traceZero k`](../def/Deformations_TaylorWilesLocal.html#L22) under the coordinate isomorphism `LinearMap.toMatrix b b : End_k(V) ≃ₗ[k] M₂(k)`; this is the statement that the trace of an endomorphism is the trace of its matrix in the basis $b$. The main definition, [`ResidualGaloisRep.adZeroEquivTraceZero`](../def/GaloisRep_AdZeroMatrixGlue.html#L18), is the $k$-linear equivalence
--   $$\ker\bigl(\operatorname{tr}\colon \operatorname{End}_k(V)\to k\bigr) \;\xrightarrow{\ \sim\ }\; \mathfrak{sl}_2(k)$$
--   obtained by restricting that coordinate isomorphism to the two submodules, which is legitimate precisely because of the preceding identification together with the surjectivity of `LinearMap.toMatrix b b`. A companion lemma records the formula for this equivalence: the matrix underlying the image of a trace-zero endomorphism $f$ is `LinearMap.toMatrix b b f`. Only $k$-linearity is asserted here; no Galois equivariance is part of these statements.
--
--   **Relation to Mathlib.** `LinearMap.trace`, `LinearMap.toMatrix`, `Matrix.traceLinearMap` and `LinearEquiv.ofSubmodules` are Mathlib; the residual representation structure [`ResidualGaloisRep`](../def/GaloisRep_Residual.html#L22), the submodule [`TaylorWiles.traceZero`](../def/Deformations_TaylorWilesLocal.html#L22) of trace-zero $2\times 2$ matrices and the adjoint construction `adZero` are the project's own notions.
--
--   **Where it is used.** The Taylor–Wiles local deformation computations are carried out with explicit $2\times2$ matrices, whereas the adjoint representation attached to a residual representation lives on abstract endomorphisms of $V$; this equivalence transports one picture to the other once a basis of $V$ is chosen, so that invariants and tangent-space dimensions for $\mathrm{ad}^0\bar\rho$ can be computed inside $\mathfrak{sl}_2(k)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_AdZeroMatrixGlue.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_Deformations_TaylorWilesLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ResidualGaloisRep

variable {k : Type} [Field k]

theorem ker_trace_eq_comap_traceZero (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V) :
    LinearMap.ker (LinearMap.trace k ρbar.V)
      = (TaylorWiles.traceZero k).comap (LinearMap.toMatrix b b : Module.End k ρbar.V ≃ₗ[k] Matrix (Fin 2) (Fin 2) k).toLinearMap := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_comap, TaylorWiles.mem_traceZero_iff, LinearEquiv.coe_coe,
    LinearMap.trace_eq_matrix_trace k b f, Matrix.trace, Matrix.traceLinearMap_apply, Matrix.diag]

noncomputable def adZeroEquivTraceZero (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V) :
    LinearMap.ker (LinearMap.trace k ρbar.V) ≃ₗ[k] TaylorWiles.traceZero k :=
  LinearEquiv.ofSubmodules (LinearMap.toMatrix b b) _ _ (by
    rw [ker_trace_eq_comap_traceZero ρbar b, Submodule.map_comap_eq_of_surjective]
    exact (LinearMap.toMatrix b b).surjective)

@[simp]
theorem adZeroEquivTraceZero_apply_coe (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V)
    (f : LinearMap.ker (LinearMap.trace k ρbar.V)) :
    ((ρbar.adZeroEquivTraceZero b f : TaylorWiles.traceZero k) : Matrix (Fin 2) (Fin 2) k) = LinearMap.toMatrix b b (f : Module.End k ρbar.V) :=
  rfl

end ResidualGaloisRep


