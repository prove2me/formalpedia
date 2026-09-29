-- Prove2me | Definitions.Def_AlgebraicCurve_JacobianH1Autoduality
-- name    : AlgebraicCurve_JacobianH1Autoduality
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/ea35c7d2-a46c-5f3e-b9bb-df3bdd3cfc1c
-- title:
--   Degree sequence, Cartier dual, and Weil pairing data on Pic0
-- statement:
--   The standing context is a field extension $K \subseteq F$ (two fields with an algebra structure), over which the imported divisor layer provides places $v$ of $F/K$ with their orders $\operatorname{ord}_v$ and degrees, the group $\mathrm{Divisor}\,K\,F$ of finitely supported $\mathbb{Z}$-valued functions on places, the degree homomorphism with kernel `Divisor.degZero`, the subgroup `Divisor.principal` of divisors of the form $v \mapsto \operatorname{ord}_v f$ for some $f \neq 0$, and the quotients $\mathrm{Pic}$ and $\mathrm{Pic}^0$. Under `HasPrincipalDivisors` (every nonzero $f$ has a divisor of zero degree recording its orders) it is shown that principal divisors lie in `degZero`, so that `H1Gm K F`, an abbreviation for $\mathrm{Pic}\,K\,F$, carries a degree homomorphism to $\mathbb{Z}$; the map `H1Gm.ofPic0` induced by the inclusion of `degZero` is injective, its range equals the kernel of the degree, and `ofPic0Equiv` is the resulting isomorphism $\mathrm{Pic}^0 \simeq \ker(\deg)$. `H1mu K F n` abbreviates the $n$-torsion subgroup $\mathrm{Pic}^0[n] = \{x : n x = 0\}$, and `HomPic0Gm K F n` abbreviates the group of additive characters $\mathrm{Pic}^0[n] \to K$; each value of such a character is an $n$-th root of unity, and `HomPic0Gm.map` is the contravariant precomposition along an additive map of torsion groups, with the expected functoriality and multiplicativity lemmas.
--
--   `WeilPairingData K F n` is a structure with two fields: an additive homomorphism `toHom` from $\mathrm{Pic}^0[n]$ to the additive copy of $\mathrm{Hom}(\mathrm{Pic}^0[n], K^\times)$, and a proof that it is bijective. Thus autoduality on $n$-torsion is carried as data rather than derived. Its evaluation $e(x,y) = (\mathrm{toHom}\,x)(y) \in K$ satisfies $e(x,y)^n = 1$ and is biadditive, with the usual behaviour under zero, negation and $\mathbb{N}$- or $\mathbb{Z}$-multiples; injectivity of `toHom` gives left non-degeneracy, bijectivity gives the isomorphism `autodualityEquiv`, `evalAddChar y` is the character $x \mapsto e(x,y)$, and `congr` transports a datum along an additive isomorphism of torsion groups with $e'(\varphi x, \varphi y) = e(x,y)$. Finally `PrincipalPolarization K F n` extends `WeilPairingData` by one further field: the pairing is alternating, $e(x,x) = 1$ for all $x$.
--
--   **Relation to Mathlib.** Quotient groups, `Submodule.torsionBy` (used for $\mathrm{Pic}^0[n]$) and `AddChar` are Mathlib's; the carriers `H1Gm`, `H1mu`, `HomPic0Gm` and the structures `WeilPairingData` and `PrincipalPolarization` are the project's own, Mathlib having no Weil pairing or Jacobian autoduality in this setting.
--
--   **Where it is used.** These definitions give the abstract shape in which the $n$-torsion of the Jacobian of a curve is used: the exactness of $0 \to \mathrm{Pic}^0 \to \mathrm{Pic} \to \mathbb{Z}$, the $n$-torsion group $\mathrm{Pic}^0[n]$, its Cartier dual, and a non-degenerate alternating pairing with values in the $n$-th roots of unity, which is what makes $\mathrm{Pic}^0[n]$ a self-dual module in the Galois-representation part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_JacobianH1Autoduality.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.AddChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Divisor

variable {K F}

theorem principal_le_degZero [HasPrincipalDivisors K F] :
    Divisor.principal (K := K) (F := F) ≤ Divisor.degZero (K := K) (F := F) := by
  rintro D ⟨f, hf, hD⟩
  obtain ⟨D', hD'v, hD'deg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  have hDD' : D = D' := Finsupp.ext fun v => by rw [hD v, hD'v v]
  exact hDD' ▸ hD'deg

theorem degree_eq_zero_of_isPrincipal [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : D.IsPrincipal) : Divisor.degree D = 0 :=
  principal_le_degZero (Divisor.mem_principal.mpr hD)

end Divisor

abbrev H1Gm : Type _ := Pic K F

namespace H1Gm

variable {K F}

abbrev mk (D : Divisor K F) : H1Gm K F := QuotientAddGroup.mk D

theorem mk_surjective : Function.Surjective (mk (K := K) (F := F)) :=
  QuotientAddGroup.mk_surjective

variable (K F)

def ofPic0 : Pic0 K F →+ H1Gm K F :=
  QuotientAddGroup.map _ _ (Divisor.degZero (K := K) (F := F)).subtype
    (fun _ hD => hD)

variable {K F} in
@[simp]
theorem ofPic0_mk (D : Divisor.degZero (K := K) (F := F)) :
    ofPic0 K F (Pic0.mk D) = mk (D : Divisor K F) := rfl

theorem ofPic0_injective : Function.Injective (ofPic0 K F) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [ofPic0_mk] at hx

  have hD : (D : Divisor K F) ∈ Divisor.principal (K := K) (F := F) :=
    (QuotientAddGroup.eq_zero_iff (D : Divisor K F)).mp hx
  exact (QuotientAddGroup.eq_zero_iff D).mpr hD

variable [HasPrincipalDivisors K F]

def degree : H1Gm K F →+ ℤ :=
  QuotientAddGroup.lift _ Divisor.degree fun _ hD =>
    Divisor.degree_eq_zero_of_isPrincipal hD

@[simp]
theorem degree_mk (D : Divisor K F) : degree K F (mk D) = Divisor.degree D := rfl

@[simp]
theorem degree_ofPic0 (x : Pic0 K F) : degree K F (ofPic0 K F x) = 0 := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  exact D.2

theorem exact_ofPic0_degree :
    (ofPic0 K F).range = (degree K F).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact degree_ofPic0 K F y
  · intro hx
    obtain ⟨D, rfl⟩ := mk_surjective x
    exact ⟨Pic0.mk ⟨D, hx⟩, rfl⟩

def ofPic0Equiv : Pic0 K F ≃+ (degree K F).ker :=
  AddEquiv.ofBijective
    ((ofPic0 K F).codRestrict (degree K F).ker fun x =>
      (exact_ofPic0_degree K F).le ⟨x, rfl⟩)
    ⟨fun a b h => ofPic0_injective K F (Subtype.ext_iff.mp h),
     fun y => by
      obtain ⟨x, hx⟩ := (exact_ofPic0_degree K F).ge y.2
      exact ⟨x, Subtype.ext hx⟩⟩

end H1Gm

abbrev H1mu (n : ℕ) : Type _ := Pic0.torsion K F n

namespace H1mu

variable {K F}

theorem mem_iff {n : ℕ} {x : Pic0 K F} :
    x ∈ Pic0.torsion K F n ↔ (n : ℤ) • x = 0 :=
  Pic0.mem_torsion

variable (K F)

theorem ofPic0_nsmul_eq_zero_iff {n : ℕ} (x : Pic0 K F) :
    (n : ℤ) • H1Gm.ofPic0 K F x = 0 ↔ (n : ℤ) • x = 0 := by
  rw [← map_zsmul]
  exact ⟨fun h => H1Gm.ofPic0_injective K F (h.trans (map_zero _).symm),
         fun h => h ▸ map_zero _⟩

end H1mu

abbrev HomPic0Gm (n : ℕ) : Type _ := AddChar (Pic0.torsion K F n) K

namespace HomPic0Gm

variable {K F}

theorem nsmul_eq_zero {n : ℕ} (x : Pic0.torsion K F n) : n • x = 0 := by
  ext
  have hx := Pic0.mem_torsion.mp x.2
  show (n • (x : Pic0 K F)) = 0
  rwa [show ((n : ℤ) • (x : Pic0 K F)) = n • (x : Pic0 K F) from natCast_zsmul .. ] at hx

theorem apply_pow_eq_one {n : ℕ} (χ : HomPic0Gm K F n) (x : Pic0.torsion K F n) :
    χ x ^ n = 1 := by
  rw [← χ.map_nsmul_eq_pow, nsmul_eq_zero, χ.map_zero_eq_one]

def map {F' : Type*} [Field F'] [Algebra K F'] {n : ℕ}
    (f : Pic0.torsion K F n →+ Pic0.torsion K F' n) :
    HomPic0Gm K F' n → HomPic0Gm K F n :=
  fun χ => χ.compAddMonoidHom f

@[simp]
theorem map_apply {F' : Type*} [Field F'] [Algebra K F'] {n : ℕ}
    (f : Pic0.torsion K F n →+ Pic0.torsion K F' n) (χ : HomPic0Gm K F' n)
    (x : Pic0.torsion K F n) :
    map f χ x = χ (f x) := rfl

@[simp]
theorem map_one {F' : Type*} [Field F'] [Algebra K F'] {n : ℕ}
    (f : Pic0.torsion K F n →+ Pic0.torsion K F' n) :
    map f (1 : HomPic0Gm K F' n) = 1 := by
  ext x; rfl

theorem map_mul {F' : Type*} [Field F'] [Algebra K F'] {n : ℕ}
    (f : Pic0.torsion K F n →+ Pic0.torsion K F' n) (χ χ' : HomPic0Gm K F' n) :
    map f (χ * χ') = map f χ * map f χ' := by
  ext x; rfl

@[simp]
theorem map_id {n : ℕ} (χ : HomPic0Gm K F n) :
    map (AddMonoidHom.id (Pic0.torsion K F n)) χ = χ := by
  ext x; rfl

theorem map_comp {F' F'' : Type*} [Field F'] [Field F''] [Algebra K F'] [Algebra K F''] {n : ℕ}
    (f : Pic0.torsion K F n →+ Pic0.torsion K F' n)
    (g : Pic0.torsion K F' n →+ Pic0.torsion K F'' n) (χ : HomPic0Gm K F'' n) :
    map (g.comp f) χ = map f (map (F := F') g χ) := by
  ext x; rfl

end HomPic0Gm

structure WeilPairingData (n : ℕ) where

  toHom : Pic0.torsion K F n →+ Additive (HomPic0Gm K F n)

  bijective : Function.Bijective toHom

namespace WeilPairingData

variable {K F}

def eval {n : ℕ} (e : WeilPairingData K F n) (x y : Pic0.torsion K F n) : K :=
  (Additive.toMul (e.toHom x)) y

theorem eval_pow_eq_one {n : ℕ} (e : WeilPairingData K F n) (x y : Pic0.torsion K F n) :
    e.eval x y ^ n = 1 :=
  HomPic0Gm.apply_pow_eq_one _ y

theorem eval_add_left {n : ℕ} (e : WeilPairingData K F n) (x x' y : Pic0.torsion K F n) :
    e.eval (x + x') y = e.eval x y * e.eval x' y := by
  unfold eval
  rw [map_add, toMul_add, AddChar.mul_apply]

theorem eval_add_right {n : ℕ} (e : WeilPairingData K F n) (x y y' : Pic0.torsion K F n) :
    e.eval x (y + y') = e.eval x y * e.eval x y' :=
  (Additive.toMul (e.toHom x)).map_add_eq_mul y y'

theorem eq_zero_of_forall_eval_eq_one {n : ℕ} (e : WeilPairingData K F n)
    {x : Pic0.torsion K F n} (h : ∀ y, e.eval x y = 1) : x = 0 := by
  apply e.bijective.injective
  rw [map_zero]
  ext y
  exact h y

end WeilPairingData

end AlgebraicCurve

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace WeilPairingData

variable {n : ℕ} (e : WeilPairingData K F n)

def autodualityEquiv : Pic0.torsion K F n ≃+ Additive (HomPic0Gm K F n) :=
  AddEquiv.ofBijective e.toHom e.bijective

@[simp]
theorem autodualityEquiv_apply (x : Pic0.torsion K F n) :
    e.autodualityEquiv x = e.toHom x := rfl

theorem toMul_autodualityEquiv_apply (x y : Pic0.torsion K F n) :
    Additive.toMul (e.autodualityEquiv x) y = e.eval x y := rfl

theorem autodualityEquiv_symm_apply (χ : Additive (HomPic0Gm K F n)) :
    e.toHom (e.autodualityEquiv.symm χ) = χ :=
  e.autodualityEquiv.apply_symm_apply χ

@[simp]
theorem eval_zero_left (y : Pic0.torsion K F n) : e.eval 0 y = 1 := by
  unfold eval; rw [map_zero]; rfl

@[simp]
theorem eval_zero_right (x : Pic0.torsion K F n) : e.eval x 0 = 1 :=
  (Additive.toMul (e.toHom x)).map_zero_eq_one

@[simp]
theorem eval_neg_left (x y : Pic0.torsion K F n) :
    e.eval (-x) y = (e.eval x y)⁻¹ := by
  unfold eval; rw [map_neg, toMul_neg, AddChar.inv_apply']

@[simp]
theorem eval_neg_right (x y : Pic0.torsion K F n) :
    e.eval x (-y) = (e.eval x y)⁻¹ :=
  (Additive.toMul (e.toHom x)).map_neg_eq_inv y

theorem eval_nsmul_left (k : ℕ) (x y : Pic0.torsion K F n) :
    e.eval (k • x) y = e.eval x y ^ k := by
  unfold eval; rw [map_nsmul, toMul_nsmul]; rfl

theorem eval_nsmul_right (k : ℕ) (x y : Pic0.torsion K F n) :
    e.eval x (k • y) = e.eval x y ^ k :=
  (Additive.toMul (e.toHom x)).map_nsmul_eq_pow k y

theorem eval_zsmul_left (k : ℤ) (x y : Pic0.torsion K F n) :
    e.eval (k • x) y = e.eval x y ^ k := by
  unfold eval; rw [map_zsmul, toMul_zsmul, AddChar.zpow_apply]

theorem eval_zsmul_right (k : ℤ) (x y : Pic0.torsion K F n) :
    e.eval x (k • y) = e.eval x y ^ k :=
  (Additive.toMul (e.toHom x)).map_zsmul_eq_zpow k y

@[simps]
def evalAddChar (y : Pic0.torsion K F n) : AddChar (Pic0.torsion K F n) K where
  toFun x := e.eval x y
  map_zero_eq_one' := e.eval_zero_left y
  map_add_eq_mul' x x' := e.eval_add_left x x' y

theorem evalAddChar_add (y y' : Pic0.torsion K F n) :
    e.evalAddChar (y + y') = e.evalAddChar y * e.evalAddChar y' := by
  ext x; exact e.eval_add_right x y y'

@[simp]
theorem evalAddChar_zero : e.evalAddChar 0 = 1 := by
  ext x; exact e.eval_zero_right x

private def congrHom {F' : Type*} [Field F'] [Algebra K F']
    (φ : Pic0.torsion K F n ≃+ Pic0.torsion K F' n) :
    Pic0.torsion K F' n →+ Additive (HomPic0Gm K F' n) where
  toFun x' := Additive.ofMul ((Additive.toMul (e.toHom (φ.symm x'))).compAddMonoidHom
    φ.symm.toAddMonoidHom)
  map_zero' := by
    ext y'
    show (Additive.toMul (e.toHom (φ.symm 0))) (φ.symm y') = 1
    rw [map_zero, map_zero]; rfl
  map_add' x₁ x₂ := by
    ext y'
    show (Additive.toMul (e.toHom (φ.symm (x₁ + x₂)))) (φ.symm y')
        = (Additive.toMul (e.toHom (φ.symm x₁))) (φ.symm y')
          * (Additive.toMul (e.toHom (φ.symm x₂))) (φ.symm y')
    rw [map_add, map_add, toMul_add, AddChar.mul_apply]

private theorem congrHom_apply {F' : Type*} [Field F'] [Algebra K F']
    (φ : Pic0.torsion K F n ≃+ Pic0.torsion K F' n) (x' y' : Pic0.torsion K F' n) :
    Additive.toMul (e.congrHom φ x') y' = e.eval (φ.symm x') (φ.symm y') := rfl

def congr {F' : Type*} [Field F'] [Algebra K F']
    (φ : Pic0.torsion K F n ≃+ Pic0.torsion K F' n) :
    WeilPairingData K F' n where
  toHom := e.congrHom φ
  bijective := by
    refine ⟨fun a b h => ?_, fun χ => ?_⟩
    · apply φ.symm.injective
      apply e.bijective.injective
      ext y
      have h' := DFunLike.congr_fun (congrArg Additive.toMul h) (φ y)
      rwa [e.congrHom_apply, e.congrHom_apply, AddEquiv.symm_apply_apply] at h'
    · obtain ⟨x, hx⟩ :=
        e.bijective.surjective (Additive.ofMul
          ((Additive.toMul χ).compAddMonoidHom φ.toAddMonoidHom))
      refine ⟨φ x, ?_⟩
      ext y'
      rw [e.congrHom_apply, AddEquiv.symm_apply_apply]
      have hx' := DFunLike.congr_fun (congrArg Additive.toMul hx) (φ.symm y')
      rw [show Additive.toMul (e.toHom x) (φ.symm y') = e.eval x (φ.symm y') from rfl] at hx'
      rw [hx']
      show ((Additive.toMul χ).compAddMonoidHom φ.toAddMonoidHom) (φ.symm y')
          = Additive.toMul χ y'
      rw [AddChar.compAddMonoidHom_apply, AddEquiv.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_coe, AddEquiv.apply_symm_apply]

@[simp]
theorem congr_eval {F' : Type*} [Field F'] [Algebra K F']
    (φ : Pic0.torsion K F n ≃+ Pic0.torsion K F' n)
    (x y : Pic0.torsion K F n) :
    (e.congr φ).eval (φ x) (φ y) = e.eval x y := by
  show e.eval (φ.symm (φ x)) (φ.symm (φ y)) = e.eval x y
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]

end WeilPairingData

structure PrincipalPolarization (K F : Type*) [Field K] [Field F] [Algebra K F]
    (n : ℕ) extends WeilPairingData K F n where

  alternating : ∀ x : Pic0.torsion K F n, toWeilPairingData.eval x x = 1

end AlgebraicCurve


