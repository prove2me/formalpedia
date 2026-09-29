-- Prove2me | Definitions.Def_GroupCohomology_TateResCor
-- name    : GroupCohomology_TateResCor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/291e4cc9-3e70-59b5-9659-d0279757ef86
-- title:
--   Restriction and corestriction on Tate cohomology in degrees 0 and −1
-- statement:
--   Fix a commutative ring $k$, a group $G$, a subgroup $S \le G$ and a representation $\rho$ of $G$ on a $k$-module $V$; $V^S$ and $V_S$ mean the invariants and coinvariants of $\rho$ restricted along `S.subtype`. The module first fixes the coset bookkeeping: `cosetDecomp` is the bijection $(G/S)\times S \to G$, $(q,s)\mapsto \tilde q s$, where $\tilde q$ is the chosen representative `q.out` of the coset $q$; `exists_out_smul_eq` records that $\widetilde{gq} = g\tilde q s$ for some $s\in S$, and `sum_eq_sum_sum` rewrites a sum over a finite $G$ as an iterated sum over $G/S$ and $S$. Two relative norms are then defined as finite sums (formally `finsum`s) of endomorphisms of $V$: $N_{G/S} = \sum_{q\in G/S}\rho(\tilde q)$ (`cosetNorm`) and $N'_{G/S} = \sum_{q\in G/S}\rho(\tilde q^{-1})$ (`cosetTransfer`). For finite $G$ and $S$ the factorisations $N_G = N_{G/S}\circ N_S$ and $N_G = N_S\circ N'_{G/S}$ are proved, together with the two statements that make the norms descend: $N_{G/S}$ carries $V^S$ into $V^G$, and $N'_{G/S}$ followed by the projection $V\to V_S$ is constant on $G$-orbits, hence factors through $V_G$.
--
--   With $\hat H^0 = V^G/\mathrm{im}\,\bar N$ and $\hat H^{-1} = \ker \bar N$, where $\bar N : V_G \to V^G$ is induced by $N_G$, four maps are defined: `tateH0Res`, induced by the inclusion $V^G \subseteq V^S$; `tateH0Cores`, induced by $N_{G/S} : V^S \to V^G$ (`cosetNormInvariants`); `tateHneg1Res`, induced by the map $V_G \to V_S$ coming from $N'_{G/S}$ (`coinvariantsTransfer`); and `tateHneg1Cores`, induced by the natural projection $V_S \to V_G$ (`coinvariantsCores`). In each case the required compatibility with the image, resp. kernel, of $\bar N$ is supplied by the norm factorisations. Finally [`Rep.tateH0Res`](../def/GroupCohomology_TateResCor.html#L218), [`Rep.tateH0Cores`](../def/GroupCohomology_TateResCor.html#L221), [`Rep.tateHneg1Res`](../def/GroupCohomology_TateResCor.html#L224) and [`Rep.tateHneg1Cores`](../def/GroupCohomology_TateResCor.html#L227) phrase the same four maps for an object $A$ of `Rep k G` and its restriction `Rep.res S.subtype A`, with the corresponding formulas on classes.
--
--   **Relation to Mathlib.** Mathlib's `Representation.invariants`, `Representation.Coinvariants` and the norm $\sum_{g\in G}\rho(g)$ are used as given; the modified degree-$0$ and degree-$(-1)$ Tate groups and the relative norms $N_{G/S}$, $N'_{G/S}$ inducing restriction and corestriction on them are the project's own, Mathlib having restriction and corestriction only as the functorial maps on group cohomology and group homology.
--
--   **Where it is used.** These maps form part of the Tate-cohomology toolkit for finite groups used in the Galois-cohomological arguments of the proof, in particular for the composite of corestriction with restriction being multiplication by the index $[G:S]$ and the resulting reduction of vanishing statements to Sylow subgroups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_TateResCor.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace Representation

namespace TateResCor

variable {G : Type v} [Group G] (S : Subgroup G)

noncomputable def cosetDecomp : (G ⧸ S) × S ≃ G where
  toFun p := p.1.out * p.2
  invFun g := ⟨(g : G ⧸ S), ⟨((g : G ⧸ S).out)⁻¹ * g, QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : G ⧸ S))⟩⟩
  left_inv := fun ⟨q, s⟩ => by
    have h : ((q.out * (s : G) : G) : G ⧸ S) = q :=
      (QuotientGroup.mk_mul_of_mem q.out s.2).trans (QuotientGroup.out_eq' q)
    refine Prod.ext h (Subtype.ext ?_)
    show ((q.out * (s : G) : G) : G ⧸ S).out⁻¹ * (q.out * s) = s
    rw [h, inv_mul_cancel_left]
  right_inv g := mul_inv_cancel_left _ _

@[simp] lemma cosetDecomp_apply (p : (G ⧸ S) × S) : cosetDecomp S p = p.1.out * p.2 := rfl

lemma exists_out_smul_eq (g : G) (q : G ⧸ S) : ∃ s : S, (g • q).out = g * q.out * s := by
  rw [← MulAction.Quotient.coe_smul_out S g q, smul_eq_mul]
  exact QuotientGroup.mk_out_eq_mul S (g * q.out)

lemma sum_eq_sum_sum {M : Type*} [AddCommMonoid M] [Fintype G] [Fintype S] [Fintype (G ⧸ S)] (f : G → M) :
    ∑ g : G, f g = ∑ q : G ⧸ S, ∑ s : S, f (q.out * s) := by
  rw [← Fintype.sum_prod_type (fun p : (G ⧸ S) × S => f (p.1.out * p.2))]
  exact (Fintype.sum_equiv (cosetDecomp S) _ _ fun p => rfl).symm

section coinvariants

variable {k : Type u} {V : Type w} [CommRing k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

lemma mk_surjective : Function.Surjective (Coinvariants.mk ρ) :=
  Submodule.Quotient.mk_surjective _

lemma mk_self_apply (g : G) (v : V) : Coinvariants.mk ρ (ρ g v) = Coinvariants.mk ρ v :=
  (Coinvariants.mk_eq_iff ρ).2 (Coinvariants.mem_ker_of_eq g v _ rfl)

end coinvariants

section maps

variable {k : Type u} {G : Type v} {V : Type w} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (S : Subgroup G)

noncomputable def cosetNorm : V →ₗ[k] V := ∑ᶠ q : G ⧸ S, ρ q.out

noncomputable def cosetTransfer : V →ₗ[k] V := ∑ᶠ q : G ⧸ S, ρ q.out⁻¹

lemma cosetNorm_eq_sum [Fintype (G ⧸ S)] : cosetNorm ρ S = ∑ q : G ⧸ S, ρ q.out := finsum_eq_sum_of_fintype _

lemma cosetTransfer_eq_sum [Fintype (G ⧸ S)] : cosetTransfer ρ S = ∑ q : G ⧸ S, ρ q.out⁻¹ := finsum_eq_sum_of_fintype _

lemma cosetNorm_apply [Fintype (G ⧸ S)] (v : V) : cosetNorm ρ S v = ∑ q : G ⧸ S, ρ q.out v := by
  rw [cosetNorm_eq_sum, LinearMap.coe_sum, Finset.sum_apply]

lemma cosetTransfer_apply [Fintype (G ⧸ S)] (v : V) : cosetTransfer ρ S v = ∑ q : G ⧸ S, ρ q.out⁻¹ v := by
  rw [cosetTransfer_eq_sum, LinearMap.coe_sum, Finset.sum_apply]

lemma norm_res_subtype_apply [Fintype S] (v : V) : Representation.norm (ρ.comp S.subtype) v = ∑ s : S, ρ s v := by
  simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]

lemma norm_eq_cosetNorm_norm_res [Fintype G] [Fintype S] (v : V) :
    ρ.norm v = cosetNorm ρ S (Representation.norm (ρ.comp S.subtype) v) := by
  letI := Fintype.ofFinite (G ⧸ S)
  rw [cosetNorm_apply, norm_res_subtype_apply]
  simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply, map_sum, ← Module.End.mul_apply, ← map_mul]
  exact sum_eq_sum_sum S fun g => ρ g v

lemma norm_eq_norm_res_cosetTransfer [Fintype G] [Fintype S] (v : V) :
    ρ.norm v = Representation.norm (ρ.comp S.subtype) (cosetTransfer ρ S v) := by
  letI := Fintype.ofFinite (G ⧸ S)
  rw [cosetTransfer_apply, norm_res_subtype_apply]
  simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply, map_sum, ← Module.End.mul_apply, ← map_mul]
  rw [Finset.sum_comm]
  calc ∑ g : G, ρ g v = ∑ g : G, ρ g⁻¹ v := (Fintype.sum_equiv (Equiv.inv G) _ _ fun g => by simp).symm
    _ = ∑ q : G ⧸ S, ∑ s : S, ρ (q.out * s)⁻¹ v := sum_eq_sum_sum S fun g => ρ g⁻¹ v
    _ = ∑ q : G ⧸ S, ∑ s : S, ρ (s * q.out⁻¹) v := Finset.sum_congr rfl fun q _ =>
        Fintype.sum_equiv (Equiv.inv S) _ _ fun s => by simp [mul_inv_rev]

lemma self_cosetNorm_apply [Fintype G] (g : G) (v : V) (hv : ∀ s : S, ρ s v = v) :
    ρ g (cosetNorm ρ S v) = cosetNorm ρ S v := by
  letI := Fintype.ofFinite (G ⧸ S)
  rw [cosetNorm_apply, map_sum]
  simp only [← Module.End.mul_apply, ← map_mul]
  calc ∑ q : G ⧸ S, ρ (g * q.out) v = ∑ q : G ⧸ S, ρ (g • q).out v := Finset.sum_congr rfl fun q _ => by
          obtain ⟨s, hs⟩ := exists_out_smul_eq S g q
          rw [hs, map_mul ρ (g * q.out) (s : G), Module.End.mul_apply, hv]
    _ = ∑ q : G ⧸ S, ρ q.out v := Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => by rw [MulAction.toPerm_apply]

lemma mk_cosetTransfer_self_apply [Fintype G] (g : G) (v : V) :
    Coinvariants.mk (ρ.comp S.subtype) (cosetTransfer ρ S (ρ g v)) =
      Coinvariants.mk (ρ.comp S.subtype) (cosetTransfer ρ S v) := by
  letI := Fintype.ofFinite (G ⧸ S)
  rw [cosetTransfer_apply, cosetTransfer_apply, map_sum, map_sum]
  have key : ∀ q : G ⧸ S, Coinvariants.mk (ρ.comp S.subtype) (ρ q.out⁻¹ (ρ g v)) =
      Coinvariants.mk (ρ.comp S.subtype) (ρ (g⁻¹ • q).out⁻¹ v) := fun q => by
    obtain ⟨s, hs⟩ := exists_out_smul_eq S g⁻¹ q
    have h1 : q.out⁻¹ * g = s * (g⁻¹ • q).out⁻¹ := by
      rw [hs, mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    have h2 : ρ q.out⁻¹ (ρ g v) = ρ s (ρ (g⁻¹ • q).out⁻¹ v) := by
      rw [← Module.End.mul_apply, ← map_mul, h1, map_mul, Module.End.mul_apply]
    rw [h2]
    exact TateResCor.mk_self_apply (ρ.comp S.subtype) s _
  rw [Finset.sum_congr rfl fun q _ => key q]
  exact Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun q => by rw [MulAction.toPerm_apply]

variable [Fintype G] [Fintype S]

omit [Fintype G] [Fintype S] in
lemma invariants_le_invariants_res : ρ.invariants ≤ Representation.invariants (ρ.comp S.subtype) :=
  fun _ hv s => hv s

lemma range_normBar_le_comap_inclusion :
    LinearMap.range ρ.normBar ≤
      (LinearMap.range (Representation.normBar (ρ.comp S.subtype))).comap (Submodule.inclusion (invariants_le_invariants_res ρ S)) := by
  rintro x ⟨y, rfl⟩
  obtain ⟨v, rfl⟩ := TateResCor.mk_surjective _ y
  refine ⟨Coinvariants.mk _ (cosetTransfer ρ S v), Subtype.ext ?_⟩
  simp only [normBar_mk, Submodule.coe_inclusion, coe_normToInvariants_apply]
  exact (norm_eq_norm_res_cosetTransfer ρ S v).symm

noncomputable def tateH0Res : ρ.tateH0 →ₗ[k] Representation.tateH0 (ρ.comp S.subtype) :=
  Submodule.mapQ _ _ (Submodule.inclusion (invariants_le_invariants_res ρ S)) (range_normBar_le_comap_inclusion ρ S)

@[simp] lemma tateH0Res_mk (a : ρ.invariants) :
    tateH0Res ρ S (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (Submodule.inclusion (invariants_le_invariants_res ρ S) a) := rfl

noncomputable def cosetNormInvariants : Representation.invariants (ρ.comp S.subtype) →ₗ[k] ρ.invariants :=
  LinearMap.codRestrict _ (cosetNorm ρ S ∘ₗ (Representation.invariants (ρ.comp S.subtype)).subtype) fun a =>
    (mem_invariants _ _).2 fun g => self_cosetNorm_apply ρ S g a fun s => (mem_invariants _ _).1 a.2 s

omit [Fintype S] in
@[simp] lemma coe_cosetNormInvariants_apply (a : Representation.invariants (ρ.comp S.subtype)) :
    (cosetNormInvariants ρ S a : V) = cosetNorm ρ S a := rfl

lemma range_normBar_res_le_comap_cosetNormInvariants :
    LinearMap.range (Representation.normBar (ρ.comp S.subtype)) ≤ (LinearMap.range ρ.normBar).comap (cosetNormInvariants ρ S) := by
  rintro x ⟨y, rfl⟩
  obtain ⟨v, rfl⟩ := TateResCor.mk_surjective _ y
  refine ⟨Coinvariants.mk _ v, Subtype.ext ?_⟩
  simp only [normBar_mk, coe_cosetNormInvariants_apply, coe_normToInvariants_apply]
  exact norm_eq_cosetNorm_norm_res ρ S v

noncomputable def tateH0Cores : Representation.tateH0 (ρ.comp S.subtype) →ₗ[k] ρ.tateH0 :=
  Submodule.mapQ _ _ (cosetNormInvariants ρ S) (range_normBar_res_le_comap_cosetNormInvariants ρ S)

@[simp] lemma tateH0Cores_mk (a : Representation.invariants (ρ.comp S.subtype)) :
    tateH0Cores ρ S (Submodule.Quotient.mk a) = Submodule.Quotient.mk (cosetNormInvariants ρ S a) := rfl

noncomputable def coinvariantsTransfer : ρ.Coinvariants →ₗ[k] Representation.Coinvariants (ρ.comp S.subtype) :=
  Coinvariants.lift ρ (Coinvariants.mk (ρ.comp S.subtype) ∘ₗ cosetTransfer ρ S) fun g =>
    LinearMap.ext fun v => mk_cosetTransfer_self_apply ρ S g v

omit [Fintype S] in
@[simp] lemma coinvariantsTransfer_mk (v : V) :
    coinvariantsTransfer ρ S (Coinvariants.mk ρ v) = Coinvariants.mk (ρ.comp S.subtype) (cosetTransfer ρ S v) :=
  rfl

noncomputable def tateHneg1Res : ρ.tateHneg1 →ₗ[k] Representation.tateHneg1 (ρ.comp S.subtype) :=
  LinearMap.codRestrict _ (coinvariantsTransfer ρ S ∘ₗ (LinearMap.ker ρ.normBar).subtype) fun x => by
    obtain ⟨v, hv⟩ := TateResCor.mk_surjective _ (x : ρ.Coinvariants)
    have hN : ρ.norm v = 0 := by
      have h := x.2
      rw [LinearMap.mem_ker, ← hv, normBar_mk] at h
      exact congrArg Subtype.val h
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, ← hv, coinvariantsTransfer_mk, normBar_mk]
    exact Subtype.ext ((norm_eq_norm_res_cosetTransfer ρ S v).symm.trans hN)

@[simp] lemma coe_tateHneg1Res_apply (x : ρ.tateHneg1) :
    (tateHneg1Res ρ S x : Representation.Coinvariants (ρ.comp S.subtype)) = coinvariantsTransfer ρ S x := rfl

noncomputable def coinvariantsCores : Representation.Coinvariants (ρ.comp S.subtype) →ₗ[k] ρ.Coinvariants :=
  Coinvariants.lift _ (Coinvariants.mk ρ) fun s => LinearMap.ext fun v => TateResCor.mk_self_apply ρ (s : G) v

omit [Fintype G] [Fintype S] in
@[simp] lemma coinvariantsCores_mk (v : V) :
    coinvariantsCores ρ S (Coinvariants.mk (ρ.comp S.subtype) v) = Coinvariants.mk ρ v :=
  rfl

noncomputable def tateHneg1Cores : Representation.tateHneg1 (ρ.comp S.subtype) →ₗ[k] ρ.tateHneg1 :=
  LinearMap.codRestrict _ (coinvariantsCores ρ S ∘ₗ (LinearMap.ker (Representation.normBar (ρ.comp S.subtype))).subtype) fun x => by
    obtain ⟨v, hv⟩ := TateResCor.mk_surjective _ (x : Representation.Coinvariants (ρ.comp S.subtype))
    have hN : Representation.norm (ρ.comp S.subtype) v = 0 := by
      have h := x.2
      rw [LinearMap.mem_ker, ← hv, normBar_mk] at h
      exact congrArg Subtype.val h
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, ← hv, coinvariantsCores_mk, normBar_mk]
    refine Subtype.ext ((norm_eq_cosetNorm_norm_res ρ S v).trans ?_)
    rw [hN, map_zero]
    rfl

@[simp] lemma coe_tateHneg1Cores_apply (x : Representation.tateHneg1 (ρ.comp S.subtype)) :
    (tateHneg1Cores ρ S x : ρ.Coinvariants) = coinvariantsCores ρ S x := rfl

end maps

end TateResCor

end Representation

namespace Rep

open Representation.TateResCor

variable {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S] (A : Rep.{w} k G)

noncomputable abbrev tateH0Res : A.tateH0 →ₗ[k] (Rep.res S.subtype A).tateH0 :=
  Representation.TateResCor.tateH0Res A.ρ S

noncomputable abbrev tateH0Cores : (Rep.res S.subtype A).tateH0 →ₗ[k] A.tateH0 :=
  Representation.TateResCor.tateH0Cores A.ρ S

noncomputable abbrev tateHneg1Res : A.tateHneg1 →ₗ[k] (Rep.res S.subtype A).tateHneg1 :=
  Representation.TateResCor.tateHneg1Res A.ρ S

noncomputable abbrev tateHneg1Cores : (Rep.res S.subtype A).tateHneg1 →ₗ[k] A.tateHneg1 :=
  Representation.TateResCor.tateHneg1Cores A.ρ S

@[simp] lemma tateH0Res_mk (a : A.ρ.invariants) :
    Rep.tateH0Res S A (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (Submodule.inclusion (invariants_le_invariants_res A.ρ S) a) := rfl

@[simp] lemma tateH0Cores_mk (a : Representation.invariants (A.ρ.comp S.subtype)) :
    Rep.tateH0Cores S A (Submodule.Quotient.mk a) = Submodule.Quotient.mk (cosetNormInvariants A.ρ S a) := rfl

@[simp] lemma coe_tateHneg1Res_apply (x : A.tateHneg1) :
    (Rep.tateHneg1Res S A x : Representation.Coinvariants (A.ρ.comp S.subtype)) = coinvariantsTransfer A.ρ S x := rfl

@[simp] lemma coe_tateHneg1Cores_apply (x : (Rep.res S.subtype A).tateHneg1) :
    (Rep.tateHneg1Cores S A x : A.ρ.Coinvariants) = coinvariantsCores A.ρ S x := rfl

end Rep


