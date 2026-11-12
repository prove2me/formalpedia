-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CenterProjConjugation
-- name    : OddOrder_GroupTheory_RepresentationTheory_CenterProjConjugation
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:54:11.655207+00:00
-- url     : https://prove2.me/theorems/8fb3c33b-27e2-4391-b0d6-83424930556d
-- title:
--   Peterfalvi (9.1): a twisting automorphism permutes the isotypic projections
-- statement:
--   For the kernel-FPF dimension fact ($\dagger$) of Peterfalvi (9.1), the Frobenius complement $E$ permutes the nontrivial $U$-isotypic components of the chief factor $W$. This file supplies the single-element bridge, stated abstractly: a linear automorphism $\tau$ of $W$ intertwining $\rho$ with its $c$-twist (for $c\in\mathrm{MulAut}\,U$) carries the range of the $i$-th isotypic projection onto that of the permuted index (`map_range_centerProj`). It consists of lemmas only.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CenterProjConjugation.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CenterProjConjugation.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CenterModuleDecomp
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CenterSimplesOrbit

namespace OddOrder.GroupTheory.CenterModuleDecomp

open Representation MonoidAlgebra

open OddOrder.GroupTheory.CenterClassSum (centerRep)

open OddOrder.GroupTheory.CenterSimplesOrbit (simplesAction centerRep_eq_centerCongr
  centerRep_apply_symm_single)

variable {k U : Type*} [Field k] [Group U] {N : ℕ}
  (φ : Subalgebra.center k (MonoidAlgebra k U) ≃ₐ[k] (Fin N → k))
  {W : Type*} [AddCommGroup W] [Module k W] (ρ : Representation k U W)

/-- **(item 0, ingredient b)**: the basis permutation `domCongrAut c` carries the `i`-th primitive
central idempotent `ε_i = φ.symm (Pi.single i 1)` to the `simplesAction φ c i`-th one.  This is
`CenterSimplesOrbit.centerRep_apply_symm_single` read at the group-algebra level: `centerRep c` is
`domCongrAut c` restricted to the centre (`centerRep_eq_centerCongr`), and `centerCongr` agrees with
`domCongrAut c` on the underlying element (`AlgEquiv.centerCongr_apply`). -/
theorem domCongrAut_centerIdem (c : MulAut U) (i : Fin N) :
    domCongrAut (R := k) (A := k) c
        ((Subalgebra.center k (MonoidAlgebra k U)).val (φ.symm (Pi.single i 1)))
      = (Subalgebra.center k (MonoidAlgebra k U)).val
          (φ.symm (Pi.single (simplesAction φ c i) 1)) := by
  have h := centerRep_apply_symm_single φ c i
  rw [centerRep_eq_centerCongr] at h
  have hcoe := congrArg
    (fun z : Subalgebra.center k (MonoidAlgebra k U) => (z : MonoidAlgebra k U)) h
  simpa only [CenterSplitting.centerCongr_apply, Subalgebra.coe_val] using hcoe

/-- **(item 0, ingredient a)**: the algebra-level intertwining.  A linear automorphism `τ` of `W`
intertwining `ρ` with its `c`-twist (`τ ρ u = ρ (c u) τ`) conjugates the whole group-algebra action:
`τ · asAlgebraHom ρ a = asAlgebraHom ρ (domCongrAut c a) · τ` for every `a ∈ k[U]`.  Proved by
`k`-linearity from the generator case `a = single u b` (where it is `hτ` scaled by `b`). -/
theorem conj_asAlgebraHom (τ : W ≃ₗ[k] W) (c : MulAut U)
    (hτ : ∀ u : U, (τ : Module.End k W) * ρ u = ρ (c u) * (τ : Module.End k W))
    (a : MonoidAlgebra k U) :
    (τ : Module.End k W) * asAlgebraHom ρ a
      = asAlgebraHom ρ (domCongrAut (R := k) (A := k) c a) * (τ : Module.End k W) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, mul_zero, zero_mul]
  | add x y hx hy => simp only [map_add, mul_add, add_mul]; rw [hx, hy]
  | single u b =>
    rw [asAlgebraHom_single,
      show domCongrAut (R := k) (A := k) c (single u b) = single (c u) b from domCongr_single c u b,
      asAlgebraHom_single, mul_smul_comm, smul_mul_assoc, hτ u]

/-- **Peterfalvi (9.1), item 0 — the twisting bridge.**  A linear automorphism `τ` of `W`
intertwining `ρ : Representation k U W` with its `c`-twist (`τ ρ u = ρ (c u) τ`, `c : MulAut U`)
carries the range of the `i`-th isotypic projection onto that of the `simplesAction φ c i`-th one:
`(range (centerProj φ ρ i)).map τ = range (centerProj φ ρ (simplesAction φ c i))`.

This supplies the `hperm` of `finrank_eq_card_mul_finrank_invariants_of_free`: with `τ = ρ_L e`
(`e ∈ E`) and `c = ` conjugation by `e`, the Frobenius complement permutes the isotypic summands by
`simplesAction φ ∘ conjAut`. -/
theorem map_range_centerProj (τ : W ≃ₗ[k] W) (c : MulAut U)
    (hτ : ∀ u : U, (τ : Module.End k W) * ρ u = ρ (c u) * (τ : Module.End k W)) (i : Fin N) :
    (LinearMap.range (centerProj φ ρ i)).map (τ : W →ₗ[k] W)
      = LinearMap.range (centerProj φ ρ (simplesAction φ c i)) := by
  -- The projection intertwining `τ ∘ centerProj i = centerProj (σ i) ∘ τ`.
  have hcompat : (τ : Module.End k W) * centerProj φ ρ i
      = centerProj φ ρ (simplesAction φ c i) * (τ : Module.End k W) := by
    unfold centerProj
    rw [conj_asAlgebraHom ρ τ c hτ, domCongrAut_centerIdem φ c i]
  -- Read off the range, using that `τ` is surjective.
  calc (LinearMap.range (centerProj φ ρ i)).map (τ : W →ₗ[k] W)
      = LinearMap.range ((τ : W →ₗ[k] W) ∘ₗ centerProj φ ρ i) :=
        (LinearMap.range_comp _ _).symm
    _ = LinearMap.range (centerProj φ ρ (simplesAction φ c i) ∘ₗ (τ : W →ₗ[k] W)) := by
        rw [show (τ : W →ₗ[k] W) ∘ₗ centerProj φ ρ i
          = centerProj φ ρ (simplesAction φ c i) ∘ₗ (τ : W →ₗ[k] W) from hcompat]
    _ = (LinearMap.range (τ : W →ₗ[k] W)).map (centerProj φ ρ (simplesAction φ c i)) :=
        LinearMap.range_comp _ _
    _ = LinearMap.range (centerProj φ ρ (simplesAction φ c i)) := by
        rw [LinearMap.range_eq_top.mpr τ.surjective, Submodule.map_top]

end OddOrder.GroupTheory.CenterModuleDecomp


