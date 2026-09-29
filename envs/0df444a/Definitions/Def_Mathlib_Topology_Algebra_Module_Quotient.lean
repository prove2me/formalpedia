-- Prove2me | Definitions.Def_Mathlib_Topology_Algebra_Module_Quotient
-- name    : Mathlib_Topology_Algebra_Module_Quotient
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/eb1dc4f9-b8f1-5ab7-86b0-803f46defeee
-- title:
--   Continuous linear equivalences of quotient modules
-- statement:
--   Two constructions upgrading standard linear equivalences between quotient modules to homeomorphisms, the quotients carrying the quotient topology.
--
--   [`Submodule.Quotient.continuousLinearEquiv`](../def/Mathlib_Topology_Algebra_Module_Quotient.html#L5) takes a ring $R$, topological $R$-modules $G$ and $H$ (additive commutative groups with $R$-module and topology instances), submodules $G' \le G$ and $H' \le H$, a continuous $R$-linear equivalence $e : G \simeq_L H$ with continuous inverse, and a hypothesis that the image of $G'$ under the underlying linear map of $e$ is exactly $H'$. It produces a continuous $R$-linear equivalence $G/G' \simeq_L H/H'$ whose underlying linear equivalence is the descent of $e$ to the quotients; both it and its inverse are continuous because each is the map induced on the quotient by $e$, respectively $e^{-1}$, followed by the quotient projection.
--
--   [`Submodule.quotientPiContinuousLinearEquiv`](../def/Mathlib_Topology_Algebra_Module_Quotient.html#L20) takes a commutative ring $R$, a finite index type $\iota$, a family $G : \iota \to$ (topological $R$-modules whose additive group structure is a topological additive group), and a family of submodules $p_i \le G_i$. Writing $\prod_i p_i$ for the submodule of $\prod_i G_i$ of those families $f$ with $f_i \in p_i$ for every $i$ (`Submodule.pi Set.univ p`), it produces a continuous $R$-linear equivalence
--   $$\Big(\prod_i G_i\Big)\Big/\prod_i p_i \;\simeq_L\; \prod_i \bigl(G_i/p_i\bigr),$$
--   with underlying linear equivalence Mathlib's `Submodule.quotientPi`. Continuity in the forward direction is coordinatewise; the inverse is expressed as a finite sum over $\iota$ of the maps induced by the coordinate insertions, whence its continuity.
--
--   **Relation to Mathlib.** Both declarations are topological refinements of linear equivalences already in Mathlib: the underlying maps are Mathlib's `Submodule.Quotient.equiv` and `Submodule.quotientPi`, here packaged as `ContinuousLinearEquiv`s by supplying continuity of the map and its inverse.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/Topology/Algebra/Module/Quotient.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard, Pietro Monticone). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_Topology_Algebra_Module_Quotient.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

def Submodule.Quotient.continuousLinearEquiv {R : Type*} [Ring R] (G H : Type*) [AddCommGroup G]
    [Module R G] [AddCommGroup H] [Module R H] [TopologicalSpace G] [TopologicalSpace H]
    (G' : Submodule R G) (H' : Submodule R H) (e : G ≃L[R] H)
    (h : Submodule.map e.toLinearMap G' = H') :
    (G ⧸ G') ≃L[R] (H ⧸ H') where
  toLinearEquiv := Submodule.Quotient.equiv G' H' e.toLinearEquiv (by simp [h])
  continuous_toFun := by
    apply continuous_quot_lift
    simp only [LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp]
    exact Continuous.comp continuous_quot_mk e.continuous
  continuous_invFun := by
    apply continuous_quot_lift
    simp only [LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp]
    exact Continuous.comp continuous_quot_mk e.continuous_invFun

def Submodule.quotientPiContinuousLinearEquiv {R ι : Type*} [CommRing R] {G : ι → Type*}
    [(i : ι) → AddCommGroup (G i)] [(i : ι) → Module R (G i)] [(i : ι) → TopologicalSpace (G i)]
    [(i : ι) → IsTopologicalAddGroup (G i)] [Fintype ι] [DecidableEq ι]
    (p : (i : ι) → Submodule R (G i)) :
    (((i : ι) → G i) ⧸ Submodule.pi Set.univ p) ≃L[R] ((i : ι) → G i ⧸ p i) where
  toLinearEquiv := Submodule.quotientPi p
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_pi (fun i => Continuous.comp continuous_quot_mk (continuous_apply _))
  continuous_invFun := by
    rw [show (quotientPi p).invFun = fun a => (quotientPi p).invFun a from rfl]
    simp only [quotientPi, quotientPi_aux.toFun, quotientPi_aux.invFun, piQuotientLift,
      LinearMap.lsum_apply, LinearMap.coe_sum, LinearMap.coe_comp, LinearMap.coe_proj,
      LinearEquiv.invFun_eq_symm, LinearEquiv.coe_symm_mk, Finset.sum_apply, Function.comp_apply,
      Function.eval]
    refine continuous_finset_sum _ (fun i _ => ?_)
    apply Continuous.comp ?_ (continuous_apply _)
    apply Continuous.quotient_lift <| Continuous.comp (continuous_quot_mk) (continuous_single _)


