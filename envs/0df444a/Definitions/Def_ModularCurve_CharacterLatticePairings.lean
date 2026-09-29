-- Prove2me | Definitions.Def_ModularCurve_CharacterLatticePairings
-- name    : ModularCurve_CharacterLatticePairings
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/453226f8-c87f-58a6-9bcb-8a6b4b298b8b
-- title:
--   Pairings and functoriality of the degree-zero character lattice
-- statement:
--   For a finite type $S$, [`ModularCurve.characterLattice S`](../def/ModularCurve_ComponentGroup.html#L23) is the kernel of $\mathrm{degreeOn}\,S : (S \to \mathbb{Z}) \to \mathbb{Z}$, $a \mapsto \sum_{s} a(s)$, i.e. the lattice $\mathbb{Z}[S]^{0}$ of degree-zero functions. This module equips it with two pairings and with functoriality in $S$. On the multiplicative side, for a commutative group $G$, $a : S \to \mathbb{Z}$ and $w : S \to G$, `zpowProd a w` is $\prod_{s} w(s)^{a(s)}$; it is additive in $a$, sends $-a$ to the inverse, is multiplicative in $w$, and on a constant family $w \equiv c$ equals $c^{\deg a}$, hence equals $1$ as soon as $\deg a = 0$. Accordingly `zpowProdHom a` is the monoid homomorphism $(S \to G) \to G$ so given, and `evalHom`, defined on an element $a$ of `characterLattice S`, is this homomorphism for the underlying function, killing the constant families and additive in $a$. On the additive side, for a module $M$ over a commutative ring $R$, `smulSum` given by $\mathrm{smulSum}\,a\,v = \sum_{s} a(s) \bullet v(s)$ is additive in each variable, $R$-linear in $v$, equals $(\deg a)\bullet m$ on the constant family $v \equiv m$, and vanishes on constants when $a$ lies in the lattice.
--
--   For functoriality, `IsDegreeScaling f d` is the predicate on a $\mathbb{Z}$-linear map $f : (S \to \mathbb{Z}) \to (S' \to \mathbb{Z})$ asserting $\deg(f a) = d \cdot \deg a$ for all $a$; such an $f$ carries the degree-zero lattice into the degree-zero lattice, and `restrictDegZero` is the induced map $\mathbb{Z}[S]^{0} \to \mathbb{Z}[S']^{0}$. Two instances are provided: `permMapFun` $\sigma$, transport along a bijection $\sigma : S \simeq S'$ (value $a(\sigma^{-1}s')$), which scales degree by $1$, and `corrMapFun B`, given by a matrix $B : S \to S' \to \mathbb{Z}$ via $(fa)(s') = \sum_{s} a(s)B(s,s')$, which scales degree by $d$ whenever every row sum $\sum_{s'} B(s,s')$ equals $d$; `permMap` and `corrMap` are the resulting maps on lattices. Two compatibilities record that pairing against a transported function is pairing against the precomposed family $w \circ \sigma$, and against $\mathrm{corrMapFun}\,B\,a$ is pairing $a$ against $s \mapsto \prod_{s'} w(s')^{B(s,s')}$. Auxiliary lemmas compute $\deg$ on a single indicator and on constants, note that differences of indicators lie in the lattice, and expand $g^{\sum_i e_i}$ as a product.
--
--   **Relation to Mathlib.** Built on Mathlib's `LinearMap`, `Submodule` and big-operator API; the lattice itself and `degreeOn` come from the project's component-group definitions, and the pairings and degree-scaling predicate here are the project's own.
--
--   **Where it is used.** The degree-zero lattice $\mathbb{Z}[S]^{0}$ plays the role of the character lattice of the torus $(S \to G)/G$ attached to the set $S$ of components of a fibre, so that the pairings here give the evaluation of characters on torus points and on the associated $R$-module of logarithms, while `permMap` and `corrMap` supply the action of bijections and of correspondences (Hecke-type data with constant row sums) on the lattice. These are the algebraic ingredients underlying the component-group computations on modular curves used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_CharacterLatticePairings.lean

import Mathlib
import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ModularCurve

open Finset

variable (S : Type*) [Fintype S]

theorem degreeOn_single [DecidableEq S] (s : S) (n : ℤ) : degreeOn S (Pi.single s n) = n := by
  simp [degreeOn_apply]

theorem degreeOn_const (n : ℤ) : degreeOn S (fun _ => n) = Fintype.card S • n := by
  simp [degreeOn_apply]

variable {S}

theorem single_sub_single_mem [DecidableEq S] (s t : S) :
    Pi.single s (1 : ℤ) - Pi.single t 1 ∈ characterLattice S := by
  rw [characterLattice, LinearMap.mem_ker, map_sub, degreeOn_single, degreeOn_single, sub_self]

namespace CharacterLattice

section MultiplicativePairing

variable {G : Type*} [CommGroup G]

theorem zpow_finset_sum {ι : Type*} (g : G) (e : ι → ℤ) (t : Finset ι) :
    g ^ (∑ i ∈ t, e i) = ∏ i ∈ t, g ^ e i := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

def zpowProd (a : S → ℤ) (w : S → G) : G := ∏ s, w s ^ a s

@[simp]
theorem zpowProd_def (a : S → ℤ) (w : S → G) : zpowProd a w = ∏ s, w s ^ a s := rfl

theorem zpowProd_add (a b : S → ℤ) (w : S → G) :
    zpowProd (a + b) w = zpowProd a w * zpowProd b w := by
  simp [zpowProd, zpow_add, Finset.prod_mul_distrib]

theorem zpowProd_zero_left (w : S → G) : zpowProd (0 : S → ℤ) w = 1 := by
  simp [zpowProd]

theorem zpowProd_neg (a : S → ℤ) (w : S → G) : zpowProd (-a) w = (zpowProd a w)⁻¹ := by
  simp [zpowProd, Finset.prod_inv_distrib]

theorem zpowProd_mul (a : S → ℤ) (w w' : S → G) :
    zpowProd a (w * w') = zpowProd a w * zpowProd a w' := by
  simp [zpowProd, mul_zpow, Finset.prod_mul_distrib]

theorem zpowProd_one_right (a : S → ℤ) : zpowProd a (1 : S → G) = 1 := by
  simp [zpowProd]

theorem zpowProd_const (a : S → ℤ) (c : G) : zpowProd a (fun _ => c) = c ^ degreeOn S a := by
  rw [zpowProd_def, degreeOn_apply, zpow_finset_sum]

theorem zpowProd_const_of_mem {a : S → ℤ} (ha : a ∈ characterLattice S) (c : G) :
    zpowProd a (fun _ => c) = 1 := by
  rw [zpowProd_const, show degreeOn S a = 0 from ha, zpow_zero]

def zpowProdHom (a : S → ℤ) : (S → G) →* G where
  toFun := zpowProd a
  map_one' := zpowProd_one_right a
  map_mul' := zpowProd_mul a

@[simp]
theorem zpowProdHom_apply (a : S → ℤ) (w : S → G) : zpowProdHom a w = zpowProd a w := rfl

def evalHom (a : characterLattice S) : (S → G) →* G := zpowProdHom (a : S → ℤ)

@[simp]
theorem evalHom_apply (a : characterLattice S) (w : S → G) : evalHom a w = ∏ s, w s ^ (a : S → ℤ) s := rfl

theorem evalHom_const (a : characterLattice S) (c : G) : evalHom a (fun _ => c) = 1 :=
  zpowProd_const_of_mem a.2 c

theorem evalHom_add (a b : characterLattice S) (w : S → G) :
    evalHom (a + b) w = evalHom a w * evalHom b w :=
  zpowProd_add _ _ w

end MultiplicativePairing

section AdditivePairing

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

def smulSum (a : S → ℤ) (v : S → M) : M := ∑ s, a s • v s

@[simp]
theorem smulSum_def (a : S → ℤ) (v : S → M) : smulSum a v = ∑ s, a s • v s := rfl

theorem smulSum_add_left (a b : S → ℤ) (v : S → M) :
    smulSum (a + b) v = smulSum a v + smulSum b v := by
  simp [smulSum, add_smul, Finset.sum_add_distrib]

theorem smulSum_add_right (a : S → ℤ) (v v' : S → M) :
    smulSum a (v + v') = smulSum a v + smulSum a v' := by
  simp [smulSum, smul_add, Finset.sum_add_distrib]

theorem smulSum_smul_right (a : S → ℤ) (r : R) (v : S → M) :
    smulSum a (r • v) = r • smulSum a v := by
  simp only [smulSum_def, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => smul_comm _ _ _

theorem smulSum_const (a : S → ℤ) (m : M) : smulSum a (fun _ => m) = degreeOn S a • m := by
  simp [smulSum, degreeOn_apply, Finset.sum_smul]

theorem smulSum_const_of_mem {a : S → ℤ} (ha : a ∈ characterLattice S) (m : M) :
    smulSum a (fun _ => m) = 0 := by
  rw [smulSum_const, show degreeOn S a = 0 from ha, zero_smul]

end AdditivePairing

section Functoriality

variable {S' : Type*} [Fintype S']

def IsDegreeScaling (f : (S → ℤ) →ₗ[ℤ] (S' → ℤ)) (d : ℤ) : Prop :=
  ∀ a, degreeOn S' (f a) = d * degreeOn S a

theorem IsDegreeScaling.map_mem {f : (S → ℤ) →ₗ[ℤ] (S' → ℤ)} {d : ℤ} (hf : IsDegreeScaling f d)
    {a : S → ℤ} (ha : a ∈ characterLattice S) : f a ∈ characterLattice S' := by
  rw [characterLattice, LinearMap.mem_ker, hf a, show degreeOn S a = 0 from ha, mul_zero]

def restrictDegZero (f : (S → ℤ) →ₗ[ℤ] (S' → ℤ)) (d : ℤ) (hf : IsDegreeScaling f d) :
    characterLattice S →ₗ[ℤ] characterLattice S' :=
  f.restrict fun _ ha => hf.map_mem ha

@[simp]
theorem coe_restrictDegZero_apply (f : (S → ℤ) →ₗ[ℤ] (S' → ℤ)) (d : ℤ) (hf : IsDegreeScaling f d)
    (a : characterLattice S) : (restrictDegZero f d hf a : S' → ℤ) = f a := rfl

omit [Fintype S] [Fintype S'] in

def permMapFun (σ : S ≃ S') : (S → ℤ) →ₗ[ℤ] (S' → ℤ) :=
  LinearMap.funLeft ℤ ℤ σ.symm

omit [Fintype S] [Fintype S'] in
@[simp]
theorem permMapFun_apply (σ : S ≃ S') (a : S → ℤ) (s' : S') : permMapFun σ a s' = a (σ.symm s') := rfl

theorem isDegreeScaling_permMapFun (σ : S ≃ S') : IsDegreeScaling (permMapFun σ) 1 := by
  intro a
  simp only [degreeOn_apply, permMapFun_apply, one_mul]
  exact Fintype.sum_equiv σ.symm _ _ fun _ => rfl

def permMap (σ : S ≃ S') : characterLattice S →ₗ[ℤ] characterLattice S' :=
  restrictDegZero (permMapFun σ) 1 (isDegreeScaling_permMapFun σ)

@[simp]
theorem coe_permMap_apply (σ : S ≃ S') (a : characterLattice S) (s' : S') :
    (permMap σ a : S' → ℤ) s' = (a : S → ℤ) (σ.symm s') := rfl

omit [Fintype S'] in

def corrMapFun (B : S → S' → ℤ) : (S → ℤ) →ₗ[ℤ] (S' → ℤ) where
  toFun a s' := ∑ s, a s * B s s'
  map_add' a b := by ext s'; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by ext s'; simp [Finset.mul_sum, mul_assoc]

omit [Fintype S'] in
@[simp]
theorem corrMapFun_apply (B : S → S' → ℤ) (a : S → ℤ) (s' : S') :
    corrMapFun B a s' = ∑ s, a s * B s s' := rfl

theorem isDegreeScaling_corrMapFun (B : S → S' → ℤ) (d : ℤ) (hB : ∀ s, ∑ s', B s s' = d) :
    IsDegreeScaling (corrMapFun B) d := by
  intro a
  simp only [degreeOn_apply, corrMapFun_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum, hB s, mul_comm]

def corrMap (B : S → S' → ℤ) (d : ℤ) (hB : ∀ s, ∑ s', B s s' = d) :
    characterLattice S →ₗ[ℤ] characterLattice S' :=
  restrictDegZero (corrMapFun B) d (isDegreeScaling_corrMapFun B d hB)

@[simp]
theorem coe_corrMap_apply (B : S → S' → ℤ) (d : ℤ) (hB : ∀ s, ∑ s', B s s' = d)
    (a : characterLattice S) (s' : S') :
    (corrMap B d hB a : S' → ℤ) s' = ∑ s, (a : S → ℤ) s * B s s' := rfl

theorem zpowProd_permMapFun {G : Type*} [CommGroup G] (σ : S ≃ S') (a : S → ℤ) (w : S' → G) :
    zpowProd (permMapFun σ a) w = zpowProd a (w ∘ σ) := by
  simp only [zpowProd, permMapFun_apply, Function.comp_apply]
  exact Fintype.prod_equiv σ.symm _ _ fun _ => by simp

theorem zpowProd_corrMapFun {G : Type*} [CommGroup G] (B : S → S' → ℤ) (a : S → ℤ) (w : S' → G) :
    zpowProd (corrMapFun B a) w = zpowProd a (fun s => ∏ s', w s' ^ B s s') := by
  simp only [zpowProd_def, corrMapFun_apply]
  calc (∏ s', w s' ^ ∑ s, a s * B s s')
      = ∏ s', ∏ s, w s' ^ (a s * B s s') :=
          Finset.prod_congr rfl fun s' _ => zpow_finset_sum (w s') _ _
    _ = ∏ s, ∏ s', w s' ^ (a s * B s s') := Finset.prod_comm
    _ = ∏ s, (∏ s', w s' ^ B s s') ^ a s := by
          refine Finset.prod_congr rfl fun s _ => ?_
          rw [← Finset.prod_zpow]
          exact Finset.prod_congr rfl fun s' _ => by rw [zpow_mul']

end Functoriality

end CharacterLattice

end ModularCurve


