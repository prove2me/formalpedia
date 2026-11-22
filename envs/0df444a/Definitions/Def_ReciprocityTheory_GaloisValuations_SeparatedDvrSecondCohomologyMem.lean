-- Prove2me | Definitions.Def_ReciprocityTheory_GaloisValuations_SeparatedDvrSecondCohomologyMem
-- name    : ReciprocityTheory_GaloisValuations_SeparatedDvrSecondCohomologyMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:17.374801+00:00
-- url     : https://prove2.me/theorems/5d01fa42-0bc3-4a3a-8f95-d23a955d61e2
-- title:
--   Separated Dvr Second Cohomology Mem
-- statement:
--   Definitions and structural lemmas for Separated Dvr Second Cohomology Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/SeparatedDvrSecondCohomologyMem.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Gal
set_option linter.unusedVariables false
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
section ContMaps
variable (R M)
def contMaps (X : Type*) [TopologicalSpace X] : Submodule R (X → M) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.const_smul c
variable {R M}
end ContMaps
def ContAction (rho : Representation R G M) : Prop :=
  Continuous (fun p : G × M => rho p.1 p.2)
variable (rho : Representation R G M)
def H0 : Submodule R M := rho.invariants
def Z1 : Submodule R (G → M) where
  carrier := {f | Continuous f ∧ ∀ g h, f (g * h) = f g + rho g (f h)}
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  add_mem' := fun {f f'} hf hf' => ⟨hf.1.add hf'.1, fun g h => by
    simp only [Pi.add_apply, hf.2, hf'.2, map_add]; abel⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun g h => by
    simp only [Pi.smul_apply, hf.2, map_smul, smul_add]⟩
def d0 : M →ₗ[R] (G → M) := LinearMap.pi fun g => rho g - LinearMap.id
@[simp] theorem amitsur_d0_apply (m : M) (g : G) : d0 rho m g = rho g m - m := rfl
def B1 : Submodule R (G → M) := LinearMap.range (d0 rho)
theorem mem_coboundaries1 (f : G → M) : f ∈ B1 rho ↔ ∃ m, ∀ g, f g = rho g m - m := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, fun g => rfl⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, funext fun g => (hm g).symm⟩
abbrev H1 := Z1 rho ⧸ (B1 rho).comap (Z1 rho).subtype
def Z2 : Submodule R (G × G → M) where
  carrier := {f | Continuous f ∧
    ∀ g h k, rho g (f (h, k)) - f (g * h, k) + f (g, h * k) - f (g, h) = 0}
  zero_mem' := ⟨continuous_const, fun g h k => by simp⟩
  add_mem' := fun {f f'} hf hf' => ⟨hf.1.add hf'.1, fun g h k => by
    have e1 := hf.2 g h k; have e2 := hf'.2 g h k
    simp only [Pi.add_apply, map_add]
    calc _ = (rho g (f (h, k)) - f (g * h, k) + f (g, h * k) - f (g, h)) +
          (rho g (f' (h, k)) - f' (g * h, k) + f' (g, h * k) - f' (g, h)) := by abel
      _ = 0 := by rw [e1, e2, add_zero]⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun g h k => by
    have e := hf.2 g h k
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_sub, ← smul_add, ← smul_sub, e, smul_zero]⟩
def d1 : (G → M) →ₗ[R] (G × G → M) where
  toFun c p := rho p.1 (c p.2) - c (p.1 * p.2) + c p.1
  map_add' c c' := by
    funext p; simp only [Pi.add_apply, map_add]; abel
  map_smul' r c := by
    funext p; simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub, smul_add]
@[simp] theorem d1_apply (c : G → M) (g h : G) :
    d1 rho c (g, h) = rho g (c h) - c (g * h) + c g := rfl
def B2 : Submodule R (G × G → M) := (contMaps R M G).map (d1 rho)
theorem separated_dvr_second_cohomology_mem (f : G × G → M) :
    f ∈ B2 rho ↔ ∃ c : G → M, Continuous c ∧ d1 rho c = f := Iff.rfl
abbrev H2 := Z2 rho ⧸ (B2 rho).comap (Z2 rho).subtype
def Cn (rho : Representation R G M) (n : ℕ) : Submodule R ((Fin n → G) → M) := contMaps R M (Fin n → G)
def dn (n : ℕ) : ((Fin n → G) → M) →ₗ[R] ((Fin (n + 1) → G) → M) where
  toFun f g := rho (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
    (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
  map_add' f f' := by
    funext g
    simp [Finset.sum_add_distrib, add_add_add_comm]
  map_smul' r f := by
    funext g
    simp [Finset.smul_sum, ← smul_assoc, mul_comm r]
def Zn (n : ℕ) : Submodule R ((Fin n → G) → M) := Cn rho n ⊓ LinearMap.ker (dn rho n)
def Bn : (n : ℕ) → Submodule R ((Fin n → G) → M)
  | 0 => ⊥
  | n + 1 => (Cn rho n).map (dn rho n)
abbrev Hn (n : ℕ) := Zn rho n ⧸ (Bn rho n).comap (Zn rho n).subtype
section Restriction
variable {H : Type*} [Group H] [TopologicalSpace H] (phi : H →* G)
def resH0 : H0 rho →ₗ[R] H0 (rho.comp phi) :=
  Submodule.inclusion fun _ hm h => hm (phi h)
variable (hphi : Continuous phi)
include hphi
def restrictCocycles1 : Z1 rho →ₗ[R] Z1 (rho.comp phi) where
  toFun f := ⟨f.1 ∘ phi, f.2.1.comp hphi, fun g h => by
    simp only [Function.comp_apply, map_mul, MonoidHom.coe_comp]
    exact f.2.2 _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] theorem restrictCocycles1_apply (f : Z1 rho) (h : H) : (restrictCocycles1 rho phi hphi f).1 h = f.1 (phi h) := rfl
def resH1 : H1 rho →ₗ[R] H1 (rho.comp phi) :=
  Submodule.mapQ _ _ (restrictCocycles1 rho phi hphi) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hf
    exact (mem_coboundaries1 _ _).2 ⟨m, fun h => hm (phi h)⟩
def restrictCocycles2 : Z2 rho →ₗ[R] Z2 (rho.comp phi) where
  toFun f := ⟨fun p => f.1 (phi p.1, phi p.2), f.2.1.comp (hphi.prodMap hphi), fun g h k => by
    simp only [map_mul, MonoidHom.coe_comp, Function.comp_apply]
    exact f.2.2 _ _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] theorem restrictCocycles2_apply (f : Z2 rho) (g h : H) :
    (restrictCocycles2 rho phi hphi f).1 (g, h) = f.1 (phi g, phi h) := rfl
def resH2 : H2 rho →ₗ[R] H2 (rho.comp phi) :=
  Submodule.mapQ _ _ (restrictCocycles2 rho phi hphi) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho _).1 hf
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ phi, hc.comp hphi, ?_⟩
    funext p
    have e := congrFun hcf (phi p.1, phi p.2)
    simp only [Submodule.coe_subtype] at e
    change _ = f.1 (phi p.1, phi p.2)
    rw [← e]
    simp [d1]
end Restriction
section Map
variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
  (hequiv : ∀ g m, u (rho g m) = rho' g (u m))
include hu hequiv
def cocycles1MapOfEquivariant : Z1 rho →ₗ[R] Z1 rho' where
  toFun f := ⟨u ∘ f.1, hu.comp f.2.1, fun g h => by
    simp only [Function.comp_apply, f.2.2 g h, map_add, hequiv]⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)
def mapH1 : H1 rho →ₗ[R] H1 rho' :=
  Submodule.mapQ _ _ (cocycles1MapOfEquivariant rho rho' u hu hequiv) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hf
    refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
    have e := hm g
    simp only [Submodule.coe_subtype] at e
    change u (f.1 g) = _
    rw [e, map_sub, hequiv]
def cocycles2Map : Z2 rho →ₗ[R] Z2 rho' where
  toFun f := ⟨u ∘ f.1, hu.comp f.2.1, fun g h k => by
    simp only [Function.comp_apply, ← hequiv, ← map_sub, ← map_add, f.2.2 g h k, map_zero]⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)
def mapH2 : H2 rho →ₗ[R] H2 rho' :=
  Submodule.mapQ _ _ (cocycles2Map rho rho' u hu hequiv) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho _).1 hf
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨u ∘ c, hu.comp hc, ?_⟩
    funext p
    have e := congrFun hcf p
    simp only [Submodule.coe_subtype] at e
    change _ = u (f.1 p)
    rw [← e]
    simp [d1, hequiv]
end Map
section Pair
variable {G' : Type*} [Group G'] [TopologicalSpace G']
  {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G' M') (phi : G' →* G) (hphi : Continuous phi)
  (u : M →ₗ[R] M') (hu : Continuous u) (hcompat : ∀ g m, u (rho (phi g) m) = rho' g (u m))
include hphi hu hcompat
def compatiblePairCocycles1 : Z1 rho →ₗ[R] Z1 rho' where
  toFun f := ⟨fun g => u (f.1 (phi g)), hu.comp (f.2.1.comp hphi), fun g h => by
    simp only [map_mul, f.2.2, map_add, hcompat]⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)
@[simp] theorem compatiblePairCocycles1_apply (f : Z1 rho) (g : G') :
    (compatiblePairCocycles1 rho rho' phi hphi u hu hcompat f).1 g = u (f.1 (phi g)) := rfl
def pairH1DecompositionMap : H1 rho →ₗ[R] H1 rho' :=
  Submodule.mapQ _ _ (compatiblePairCocycles1 rho rho' phi hphi u hu hcompat) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hf
    refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
    have e := hm (phi g)
    simp only [Submodule.coe_subtype] at e
    change u (f.1 (phi g)) = _
    rw [e, map_sub, hcompat]
def compatiblePairCocycles2 : Z2 rho →ₗ[R] Z2 rho' where
  toFun f := ⟨fun p => u (f.1 (phi p.1, phi p.2)), hu.comp (f.2.1.comp (hphi.prodMap hphi)),
    fun g h k => by
      have e := congrArg u (f.2.2 (phi g) (phi h) (phi k))
      simp only [map_sub, map_add, map_zero, hcompat] at e
      simpa only [map_mul] using e⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)
@[simp] theorem compatiblePairCocycles2_apply (f : Z2 rho) (g h : G') :
    (compatiblePairCocycles2 rho rho' phi hphi u hu hcompat f).1 (g, h) = u (f.1 (phi g, phi h)) := rfl
def compatiblePairH2 : H2 rho →ₗ[R] H2 rho' :=
  Submodule.mapQ _ _ (compatiblePairCocycles2 rho rho' phi hphi u hu hcompat) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho _).1 hf
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => u (c (phi g)), hu.comp (hc.comp hphi), ?_⟩
    funext p
    have e := congrFun hcf (phi p.1, phi p.2)
    simp only [Submodule.coe_subtype] at e
    change _ = u (f.1 (phi p.1, phi p.2))
    rw [← e]
    simp [d1, hcompat]
end Pair
section MapPair
variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
  (hequiv : ∀ g m, u (rho g m) = rho' g (u m))
end MapPair
end
end ReciprocityTheory.Gal


