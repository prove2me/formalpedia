-- Prove2me | Definitions.Def_GroupCohomology_TateCohomology
-- name    : GroupCohomology_TateCohomology
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/81a19adb-2b36-54cc-8d33-100e25332f79
-- title:
--   Tate cohomology of a finite group in all degrees
-- statement:
--   Throughout, $k$ is a commutative ring, $G$ a finite group, and representations are $k$-linear. For a representation $\rho$ of $G$ on $V$ with norm $N_G=\sum_{g\in G}\rho(g)$, the module records that $\rho(g)\circ N_G=N_G=N_G\circ\rho(g)$, so that $N_G$ lands in the invariants $V^G$ and factors through the coinvariants $V_G=V/I_GV$; [`Representation.normToInvariants`](../def/GroupCohomology_TateCohomology.html#L30) is the corestriction $V\to V^G$ of $N_G$ and [`Representation.normBar`](../def/GroupCohomology_TateCohomology.html#L40) is the induced map $\bar N_G\colon V_G\to V^G$. The two degrees at the junction of cohomology and homology are then defined as $k$-modules: `tateH0` is $V^G/\operatorname{im}\bar N_G = V^G/N_GV$, and `tateHneg1` is $\ker\bar N_G$, i.e. $\{v\in V: N_Gv=0\}/I_GV$ realised as a submodule of $V_G$. For objects $A$ of `Rep k G` these are written `A.tateH0`, `A.tateHneg1`.
--
--   For a morphism $\varphi\colon A\to B$ of representations, the maps induced on invariants and coinvariants (through Mathlib's invariants and coinvariants functors) commute with the norm, so $\bar N_G$ is natural; from this one gets $k$-linear maps `tateH0Map` $\varphi$ and `tateHneg1Map` $\varphi$, together with the identities for the identity morphism and for a composite $\varphi$ followed by $\psi$ (these are stated as equalities of linear maps rather than packaged as a functor).
--
--   Finally [`Rep.tateCohomology`](../def/GroupCohomology_TateCohomology.html#L140) assembles a $\mathbb{Z}$-graded family of $k$-modules attached to $A$, by cases on the integer: in degree $n+1\ge 1$ it is the group cohomology $H^{n+1}(G,A)$, in degree $0$ and $-1$ the two modules above, and in degree $-(n+2)$ the group homology $H_{n+1}(G,A)$. The four unfolding lemmas state exactly these four values.
--
--   **Relation to Mathlib.** Built directly on Mathlib's `Representation.norm`, `invariants`, `Coinvariants`, `Rep.invariantsFunctor`/`coinvariantsFunctor`, `groupCohomology` and `groupHomology`; Mathlib has no Tate (modified) cohomology, and these carriers, induced maps and the $\mathbb{Z}$-graded family are the project's own.
--
--   **Where it is used.** This module fixes the vocabulary in which Tate cohomology of finite groups is stated in the Galois-cohomological parts of the development, for a general finite group rather than only a cyclic one; the comparison with the two-periodic complexes and with the elementwise description $\ker(\sigma-1)/N$, $\ker N/(\sigma-1)$ in the cyclic case is made elsewhere.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_TateCohomology.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

lemma self_comp_norm' (g : G) : ρ g ∘ₗ ρ.norm = ρ.norm := by
  ext v
  simp only [norm, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply, map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => by
    simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply]

lemma norm_comp_self' (g : G) : ρ.norm ∘ₗ ρ g = ρ.norm := by
  ext v
  simp only [norm, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => by
    simp only [Equiv.coe_mulRight, map_mul, Module.End.mul_apply]

lemma norm_apply_mem_invariants (v : V) : ρ.norm v ∈ ρ.invariants :=
  (mem_invariants ρ _).2 fun g => by
    rw [← LinearMap.comp_apply, self_comp_norm']

noncomputable def normToInvariants : V →ₗ[k] ρ.invariants :=
  LinearMap.codRestrict ρ.invariants ρ.norm (norm_apply_mem_invariants ρ)

@[simp] lemma coe_normToInvariants_apply (v : V) : (ρ.normToInvariants v : V) = ρ.norm v := rfl

lemma normToInvariants_comp_self (g : G) : ρ.normToInvariants ∘ₗ ρ g = ρ.normToInvariants := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  change ρ.norm (ρ g v) = ρ.norm v
  rw [← LinearMap.comp_apply, norm_comp_self']

noncomputable def normBar : ρ.Coinvariants →ₗ[k] ρ.invariants :=
  Coinvariants.lift ρ ρ.normToInvariants (normToInvariants_comp_self ρ)

@[simp] lemma normBar_mk (v : V) : ρ.normBar (Coinvariants.mk ρ v) = ρ.normToInvariants v := rfl

abbrev tateH0 : Type _ := ρ.invariants ⧸ LinearMap.range ρ.normBar

abbrev tateHneg1 : Type _ := LinearMap.ker ρ.normBar

end Representation

namespace Rep

section lowDegrees

variable {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]

abbrev tateH0 (A : Rep.{w} k G) : Type w := A.ρ.tateH0

abbrev tateHneg1 (A : Rep.{w} k G) : Type w := A.ρ.tateHneg1

section maps

variable {A B C : Rep.{w} k G} (φ : A ⟶ B) (ψ : B ⟶ C)

noncomputable abbrev invariantsMap : A.ρ.invariants →ₗ[k] B.ρ.invariants :=
  ((Rep.invariantsFunctor k G).map φ).hom

omit [Fintype G] in
@[simp] lemma coe_invariantsMap_apply (a : A.ρ.invariants) : (invariantsMap φ a : B) = φ.hom a := rfl

noncomputable abbrev coinvariantsMap : A.ρ.Coinvariants →ₗ[k] B.ρ.Coinvariants :=
  ((Rep.coinvariantsFunctor k G).map φ).hom

omit [Fintype G] in
lemma coinvariantsMap_mk (a : A) :
    coinvariantsMap φ (Representation.Coinvariants.mk A.ρ a) = Representation.Coinvariants.mk B.ρ (φ.hom a) := rfl

lemma hom_norm_apply (a : A) : φ.hom (A.ρ.norm a) = B.ρ.norm (φ.hom a) := by
  simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun g _ => Rep.hom_comm_apply φ g a

lemma normBar_comp_coinvariantsMap :
    B.ρ.normBar ∘ₗ coinvariantsMap φ = invariantsMap φ ∘ₗ A.ρ.normBar := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun a => Subtype.ext ?_)
  change B.ρ.norm (φ.hom a) = φ.hom (A.ρ.norm a)
  exact (hom_norm_apply φ a).symm

lemma range_normBar_le_comap_invariantsMap :
    LinearMap.range A.ρ.normBar ≤ (LinearMap.range B.ρ.normBar).comap (invariantsMap φ) := by
  rintro x ⟨y, rfl⟩
  exact ⟨coinvariantsMap φ y, by rw [← LinearMap.comp_apply, normBar_comp_coinvariantsMap, LinearMap.comp_apply]⟩

noncomputable def tateH0Map : A.tateH0 →ₗ[k] B.tateH0 :=
  Submodule.mapQ _ _ (invariantsMap φ) (range_normBar_le_comap_invariantsMap φ)

@[simp] lemma tateH0Map_mk (a : A.ρ.invariants) :
    tateH0Map φ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (invariantsMap φ a) := rfl

noncomputable def tateHneg1Map : A.tateHneg1 →ₗ[k] B.tateHneg1 :=
  (coinvariantsMap φ ∘ₗ (LinearMap.ker A.ρ.normBar).subtype).codRestrict _ (fun x => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.comp_apply (f := B.ρ.normBar),
      normBar_comp_coinvariantsMap, LinearMap.comp_apply, Submodule.subtype_apply, x.2, map_zero])

@[simp] lemma coe_tateHneg1Map_apply (x : A.tateHneg1) :
    (tateHneg1Map φ x : B.ρ.Coinvariants) = coinvariantsMap φ x := rfl

lemma tateH0Map_id : tateH0Map (𝟙 A) = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
  change Submodule.Quotient.mk (invariantsMap (𝟙 A) a) = Submodule.Quotient.mk a
  congr 1

lemma tateH0Map_comp : tateH0Map (φ ≫ ψ) = tateH0Map ψ ∘ₗ tateH0Map φ := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
  change Submodule.Quotient.mk (invariantsMap (φ ≫ ψ) a) =
    Submodule.Quotient.mk (invariantsMap ψ (invariantsMap φ a))
  congr 1

lemma tateHneg1Map_id : tateHneg1Map (𝟙 A) = LinearMap.id := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x : A.ρ.Coinvariants)
  simp only [LinearMap.id_apply, coe_tateHneg1Map_apply]
  rw [← ha]
  rfl

lemma tateHneg1Map_comp : tateHneg1Map (φ ≫ ψ) = tateHneg1Map ψ ∘ₗ tateHneg1Map φ := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x : A.ρ.Coinvariants)
  simp only [LinearMap.comp_apply, coe_tateHneg1Map_apply]
  rw [← ha]
  rfl

end maps

end lowDegrees

section graded

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

noncomputable def tateCohomology (A : Rep.{u} k G) : ℤ → ModuleCat.{u} k
  | (Int.ofNat (n + 1)) => groupCohomology A (n + 1)
  | (Int.ofNat 0) => ModuleCat.of k A.tateH0
  | (Int.negSucc 0) => ModuleCat.of k A.tateHneg1
  | (Int.negSucc (n + 1)) => groupHomology A (n + 1)

lemma tateCohomology_ofNat_succ (A : Rep.{u} k G) (n : ℕ) : A.tateCohomology (n + 1 : ℕ) = groupCohomology A (n + 1) := rfl
lemma tateCohomology_zero (A : Rep.{u} k G) : A.tateCohomology 0 = ModuleCat.of k A.tateH0 := rfl
lemma tateCohomology_neg_one (A : Rep.{u} k G) : A.tateCohomology (-1) = ModuleCat.of k A.tateHneg1 := rfl
lemma tateCohomology_negSucc_succ (A : Rep.{u} k G) (n : ℕ) :
    A.tateCohomology (Int.negSucc (n + 1)) = groupHomology A (n + 1) := rfl

end graded

end Rep


