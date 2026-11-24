-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_IsComplRatCompl
-- name    : Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_IsComplRatCompl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:14.701244+00:00
-- url     : https://prove2.me/theorems/0fb5e7b9-6fb9-4719-90c5-206f3b343963
-- title:
--   Is Compl Rat Compl
-- statement:
--   Definitions and structural lemmas for Is Compl Rat Compl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/IsComplRatCompl.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.G.Cmp
variable {LL Kf : Type*} [Field LL] [Field Kf] {e : LL →+* Kf}
  {V0 V1 W0 W1 ι : Type*} [AddCommGroup V0] [Module LL V0] [AddCommGroup V1] [Module LL V1]
  [AddCommGroup W0] [Module Kf W0] [AddCommGroup W1] [Module Kf W1]
def spanK (c0 : V0 →ₛₗ[e] W0) : Submodule Kf W0 := Submodule.span Kf (Set.range c0)
theorem lc_repr_lemma (c0 : V0 →ₛₗ[e] W0) (b : Module.Basis ι LL V0) (x : V0) :
    Finsupp.linearCombination Kf (fun i => c0 (b i)) (Finsupp.mapRange e (map_zero e) (b.repr x)) = c0 x := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (h := fun i a => a • c0 (b i)) (fun i => zero_smul _ _)]
  conv_rhs => rw [← b.linearCombination_repr x]
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, LinearMap.map_smulₛₗ]
theorem span_basis_eq (c0 : V0 →ₛₗ[e] W0) (b : Module.Basis ι LL V0) :
    Submodule.span Kf (Set.range fun i => c0 (b i)) = spanK c0 := by
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨b i, rfl⟩)
  · rw [spanK, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← lc_repr_lemma c0 b x, ← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ _
def complK (c0 : V0 →ₛₗ[e] W0) : Submodule Kf W0 := Classical.choose (Submodule.exists_isCompl (spanK c0))
theorem isCompl_complK (c0 : V0 →ₛₗ[e] W0) : IsCompl (spanK c0) (complK c0) := Classical.choose_spec (Submodule.exists_isCompl (spanK c0))
def extSpan (c0 : V0 →ₛₗ[e] W0) (c1 : V1 →ₛₗ[e] W1) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (KL : V0 →ₗ[LL] V1) :
    Submodule.span Kf (Set.range fun i => c0 (b i)) →ₗ[Kf] W1 :=
  (Finsupp.linearCombination Kf fun i => c1 (KL (b i))) ∘ₗ hli.repr
def extK (c0 : V0 →ₛₗ[e] W0) (c1 : V1 →ₛₗ[e] W1) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (KL : V0 →ₗ[LL] V1) : W0 →ₗ[Kf] W1 :=
  (extSpan c0 c1 b hli KL) ∘ₗ
    (LinearEquiv.ofEq _ _ (span_basis_eq c0 b).symm).toLinearMap ∘ₗ
      Submodule.projectionOnto (spanK c0) (complK c0) (isCompl_complK c0)
section Indep
open TensorProduct
variable {ι' : Type*}
end Indep
section Rat
variable {Cc : Type*} [Field Cc] {s : LL →+* Cc} {M0 M1 : Type*} [AddCommGroup M0] [Module Cc M0]
  [AddCommGroup M1] [Module Cc M1]
def ratDom (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (f : M0 →ₗ[Cc] M1) : Submodule LL V0 where
  carrier := {x | ∃ y, e1 y = f (e0 x)}
  add_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y + z, by rw [map_add, map_add, map_add, hy, hz]⟩
  zero_mem' := ⟨0, by rw [map_zero, map_zero, map_zero]⟩
  smul_mem' := by
    rintro a x ⟨y, hy⟩
    exact ⟨a • y, by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_smul, hy]⟩
def ratPart (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (hinj : Function.Injective e1) (f : M0 →ₗ[Cc] M1) :
    ratDom e0 e1 f →ₗ[LL] V1 where
  toFun x := Classical.choose x.2
  map_add' x y := by
    apply hinj
    rw [map_add, Classical.choose_spec x.2, Classical.choose_spec y.2, Classical.choose_spec (x + y).2]
    rw [Submodule.coe_add, map_add, map_add]
  map_smul' a x := by
    apply hinj
    rw [RingHom.id_apply, LinearMap.map_smulₛₗ, Classical.choose_spec x.2, Classical.choose_spec (a • x).2]
    rw [Submodule.coe_smul, LinearMap.map_smulₛₗ, map_smul]
def ratCompl (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (f : M0 →ₗ[Cc] M1) : Submodule LL V0 :=
  Classical.choose (Submodule.exists_isCompl (ratDom e0 e1 f))
theorem isCompl_ratCompl (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (f : M0 →ₗ[Cc] M1) :
    IsCompl (ratDom e0 e1 f) (ratCompl e0 e1 f) := Classical.choose_spec (Submodule.exists_isCompl (ratDom e0 e1 f))
def ratMap (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (hinj : Function.Injective e1) (f : M0 →ₗ[Cc] M1) :
    V0 →ₗ[LL] V1 :=
  ratPart e0 e1 hinj f ∘ₗ
    Submodule.projectionOnto (ratDom e0 e1 f) (ratCompl e0 e1 f) (isCompl_ratCompl e0 e1 f)
end Rat
end Formalism.L2.G.Cmp
end


