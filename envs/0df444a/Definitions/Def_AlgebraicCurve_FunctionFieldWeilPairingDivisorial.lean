-- Prove2me | Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
-- name    : AlgebraicCurve_FunctionFieldWeilPairingDivisorial
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/23e2e402-ddc8-5814-9dc5-8ab63d5f77b9
-- title:
--   Divisorial Weil pairing on n-torsion of Pic0
-- statement:
--   Throughout, $F$ is a field extension of a field $K$, places are the project's `Place K F` (valuation subrings of $F$ containing $K$, not all of $F$, with principal ideals), divisors are finitely supported $\mathbb{Z}$-valued functions on places, and for $f\in F$ and a divisor $D$ one has $\mathrm{evalFun}\,f\,D=\prod_{v\in\operatorname{supp}D} (\mathrm{evalAt}_v f)^{D(v)}\in K$, where $\mathrm{evalAt}_v$ is residue evaluation pulled back along $K\to k(v)$. A `WeilDatum K F n` consists of divisors $D_1,D_2$ and nonzero $f_1,f_2\in F$ with $\operatorname{ord}_v f_i=n\,D_i(v)$ for all $v$, with $D_1(v)=0$ or $D_2(v)=0$ for each $v$, and with every place in the joint support rational; its `pairing` is $\mathrm{evalFun}\,f_1\,D_2/\mathrm{evalFun}\,f_2\,D_1$. The first part of the module shows $n\cdot D_i$ is principal, hence of degree $0$ when principal divisors have degree $0$, so that (for $n\neq0$) $D_1,D_2$ define classes `classLeft`, `classRight` in the $n$-torsion subgroup of $\mathrm{Pic}^0$; it records their behaviour under the exchange `symm` and under `addLeft` (addition of the left divisor and multiplication of $f_1$ when the right data agree), the vanishing of $\operatorname{ord}_v f_1$ on $\operatorname{supp}D_2$ and symmetrically, the nonvanishing of the relevant residue evaluations, hence $\mathrm{pairing}\neq0$, $\mathrm{pairing}(\mathrm{symm})=\mathrm{pairing}^{-1}$, multiplicativity under `addLeft`, and $\mathrm{pairing}^n=1$ granted the hypothesis `WeilReciprocity K F`. A section on the $K$-automorphisms $\sigma$ of $F$ transports places, residue fields and evaluations, defines `galSmul` (apply $\sigma$ to divisors and functions) and proves that it leaves the pairing unchanged while moving the classes by $\sigma$; `Pic0.smul_mem_torsion` records stability of the $n$-torsion. `pairing_eq_of_addPrincipalLeft` is the change-of-representative statement: if $D_1'=D_1+\operatorname{div}(h)$, $D_2'=D_2$, $f_1'=f_1h^n$, $f_2'=f_2$, then the two pairings agree, granted Weil reciprocity; `gate_pairing_eq_of_addPrincipalLeft_refl` is its instance with $h=1$, whose statement is the identity $d.\mathrm{pairing}=d.\mathrm{pairing}$.
--
--   The structure `DivisorialWeilPairingData K F n` (for $n\neq 0$ and with principal divisors of degree zero) is data: a function $\mathrm{pair}:\mathrm{Pic}^0[n]\times\mathrm{Pic}^0[n]\to K$, a field `compatible` asserting that on the two classes of every Weil datum it returns that datum's pairing, and a field `move` asserting a moving lemma — every $n$-torsion class is represented by a degree-zero divisor with rational support avoiding any prescribed finite set of places. From this data alone are derived: existence of a Weil datum with prescribed pair of classes, and of two data sharing $D_2$ and $f_2$ with prescribed left classes; nonvanishing of $\mathrm{pair}$; biadditivity $\mathrm{pair}(x+x',y)=\mathrm{pair}(x,y)\mathrm{pair}(x',y)$ and its right analogue; $\mathrm{pair}(x,y)\mathrm{pair}(y,x)=1$; normalisation at $0$; $\mathrm{pair}(x,y)^n=1$ granted Weil reciprocity; $\mathrm{pair}(x,x)=1$ for odd $n$ granted Weil reciprocity; and $\sigma$-invariance. Finally `toChar` and `toHom` package the pairing as an additive map from $\mathrm{Pic}^0[n]$ to the additive copy of the group of $K$-valued additive characters of $\mathrm{Pic}^0[n]$, `Perfect` is bijectivity of that map, `toWeilPairingData` converts a perfect divisorial pairing into the abstract `WeilPairingData` carrier with the same values, and `ExistsPerfectDivisorialWeilPairing K F n` is the proposition that some such perfect datum exists, from which nonemptiness of `WeilPairingData K F n` follows.
--
--   **Relation to Mathlib.** Mathlib has no Weil pairing on the Jacobian of a curve and no divisor-theoretic framework of this kind; places, divisors, $\mathrm{Pic}^0$ and its torsion are the project's own notions, built on Mathlib's valuation subrings (with their pointwise group action), local-ring residue fields and `Finsupp`. The target group of characters is Mathlib's `AddChar`, viewed additively through `Additive`.
--
--   **Where it is used.** The perfect, Galois-invariant, $\mu_n$-valued pairing assembled here is the divisorial construction of the autoduality of the $n$-torsion of a Jacobian, delivered in the abstract form (`WeilPairingData`) used elsewhere for the Galois modules attached to Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean

import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_JacobianH1Autoduality
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Divisor

theorem evalFun_one (D : Divisor K F) : evalFun (1 : F) D = 1 := by
  rw [evalFun_def]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [Place.evalAt_one, one_zpow]

end Divisor

namespace WeilDatum

variable {n : ℕ}

private theorem isPrincipal_smul_left (d : WeilDatum K F n) :
    Divisor.IsPrincipal ((n : ℤ) • d.D₁) :=
  ⟨d.f₁, d.f₁_ne_zero, fun v => by rw [Finsupp.smul_apply, smul_eq_mul, d.ord_f₁ v]⟩

theorem isPrincipal_smul_right (d : WeilDatum K F n) :
    Divisor.IsPrincipal ((n : ℤ) • d.D₂) :=
  d.symm.isPrincipal_smul_left

theorem degree_D₁_eq_zero (d : WeilDatum K F n) [HasPrincipalDivisors K F] (hn : n ≠ 0) :
    Divisor.degree d.D₁ = 0 := by
  have h := Divisor.degree_eq_zero_of_isPrincipal d.isPrincipal_smul_left
  rw [map_zsmul, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn)

theorem degree_D₂_eq_zero (d : WeilDatum K F n) [HasPrincipalDivisors K F] (hn : n ≠ 0) :
    Divisor.degree d.D₂ = 0 :=
  d.symm.degree_D₁_eq_zero hn

end WeilDatum

namespace WeilDatum

variable {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]

def degZeroLeft (d : WeilDatum K F n) : Divisor.degZero (K := K) (F := F) :=
  ⟨d.D₁, Divisor.mem_degZero.mpr (d.degree_D₁_eq_zero (NeZero.ne n))⟩

def degZeroRight (d : WeilDatum K F n) : Divisor.degZero (K := K) (F := F) :=
  ⟨d.D₂, Divisor.mem_degZero.mpr (d.degree_D₂_eq_zero (NeZero.ne n))⟩

@[simp] theorem coe_degZeroLeft (d : WeilDatum K F n) :
    (d.degZeroLeft : Divisor K F) = d.D₁ := rfl

@[simp] theorem coe_degZeroRight (d : WeilDatum K F n) :
    (d.degZeroRight : Divisor K F) = d.D₂ := rfl

omit [NeZero n] [HasPrincipalDivisors K F] in

theorem mk_mem_torsion (D : Divisor.degZero (K := K) (F := F))
    (h : Divisor.IsPrincipal ((n : ℤ) • (D : Divisor K F))) :
    Pic0.mk D ∈ Pic0.torsion K F n := by
  rw [Pic0.mem_torsion]
  have h1 : (n : ℤ) • Pic0.mk D = Pic0.mk ((n : ℤ) • D) := by
    show (n : ℤ) • (QuotientAddGroup.mk D) = QuotientAddGroup.mk ((n : ℤ) • D)
    exact (QuotientAddGroup.mk_zsmul
      ((Divisor.principal (K := K) (F := F)).addSubgroupOf
        (Divisor.degZero (K := K) (F := F))) D (n : ℤ)).symm
  rw [h1]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  have hcoe : (((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) : Divisor K F)
      = (n : ℤ) • (D : Divisor K F) := rfl
  show ((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) ∈
    (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))
  rw [AddSubgroup.mem_addSubgroupOf, hcoe]
  exact Divisor.mem_principal.mpr h

def classLeft (d : WeilDatum K F n) : Pic0.torsion K F n :=
  ⟨Pic0.mk d.degZeroLeft, mk_mem_torsion d.degZeroLeft (by
    rw [coe_degZeroLeft]; exact d.isPrincipal_smul_left)⟩

def classRight (d : WeilDatum K F n) : Pic0.torsion K F n :=
  ⟨Pic0.mk d.degZeroRight, mk_mem_torsion d.degZeroRight (by
    rw [coe_degZeroRight]; exact d.isPrincipal_smul_right)⟩

@[simp] theorem coe_classLeft (d : WeilDatum K F n) :
    (d.classLeft : Pic0 K F) = Pic0.mk d.degZeroLeft := rfl

@[simp] theorem coe_classRight (d : WeilDatum K F n) :
    (d.classRight : Pic0 K F) = Pic0.mk d.degZeroRight := rfl

theorem classLeft_symm (d : WeilDatum K F n) : d.symm.classLeft = d.classRight := rfl

theorem classRight_symm (d : WeilDatum K F n) : d.symm.classRight = d.classLeft := rfl

theorem classLeft_addLeft (d d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (hf : d.f₂ = d'.f₂) :
    (d.addLeft d' hD hf).classLeft = d.classLeft + d'.classLeft := by
  refine Subtype.ext ?_
  show Pic0.mk (d.addLeft d' hD hf).degZeroLeft = Pic0.mk d.degZeroLeft + Pic0.mk d'.degZeroLeft
  rw [← Pic0.mk_add]
  exact congrArg Pic0.mk (Subtype.ext rfl)

theorem classRight_addLeft (d d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (hf : d.f₂ = d'.f₂) :
    (d.addLeft d' hD hf).classRight = d.classRight :=
  rfl

end WeilDatum

namespace WeilDatum

variable {n : ℕ} (d : WeilDatum K F n)

theorem ord_f₁_eq_zero_of_mem_support {v : Place K F} (hv : v ∈ d.D₂.support) :
    v.ord d.f₁ = 0 := by
  rw [d.ord_f₁ v, (d.disjoint v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero]

theorem ord_f₂_eq_zero_of_mem_support {v : Place K F} (hv : v ∈ d.D₁.support) :
    v.ord d.f₂ = 0 := by
  rw [d.ord_f₂ v, (d.disjoint v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero]

theorem rational_of_mem_support_left {v : Place K F} (hv : v ∈ d.D₁.support) :
    v.IsRational :=
  d.rational v (Or.inl (Finsupp.mem_support_iff.mp hv))

theorem rational_of_mem_support_right {v : Place K F} (hv : v ∈ d.D₂.support) :
    v.IsRational :=
  d.rational v (Or.inr (Finsupp.mem_support_iff.mp hv))

theorem evalAt_f₁_ne_zero {v : Place K F} (hv : v ∈ d.D₂.support) :
    v.evalAt d.f₁ ≠ 0 :=
  v.evalAt_ne_zero_of_ord_eq_zero (d.rational_of_mem_support_right hv) d.f₁_ne_zero
    (d.ord_f₁_eq_zero_of_mem_support hv)

theorem evalAt_f₂_ne_zero {v : Place K F} (hv : v ∈ d.D₁.support) :
    v.evalAt d.f₂ ≠ 0 :=
  v.evalAt_ne_zero_of_ord_eq_zero (d.rational_of_mem_support_left hv) d.f₂_ne_zero
    (d.ord_f₂_eq_zero_of_mem_support hv)

end WeilDatum

section GaloisAction

open scoped Pointwise

namespace Place

variable (σ : F ≃ₐ[K] F) (v : Place K F)

theorem mem_smul_toValuationSubring_iff (f : F) :
    σ f ∈ (σ • v).toValuationSubring ↔ f ∈ v.toValuationSubring := by
  rw [smul_toValuationSubring]
  constructor
  · intro h
    have h1 := (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
      (g := σ) (S := v.toValuationSubring) (x := σ f)).mp h
    have h2 : σ⁻¹ • σ f = f := by
      rw [AlgEquiv.smul_def, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    rwa [h2] at h1
  · intro h
    have h1 := ValuationSubring.smul_mem_pointwise_smul σ f v.toValuationSubring h
    rwa [AlgEquiv.smul_def] at h1

theorem isRational_smul (hv : v.IsRational) : (σ • v).IsRational := by
  intro x
  obtain ⟨a, ha⟩ := hv ((smulResidueAlgEquiv σ v).symm x)
  exact ⟨a, by rw [← (smulResidueAlgEquiv σ v).commutes a, ha, AlgEquiv.apply_symm_apply]⟩

theorem residue_smul {f : F} (hf : f ∈ v.toValuationSubring) :
    residue (σ • v).toValuationSubring
        (⟨σ f, (mem_smul_toValuationSubring_iff σ v f).mpr hf⟩ :
          (σ • v).toValuationSubring)
      = smulResidueAlgEquiv σ v (residue v.toValuationSubring ⟨f, hf⟩) := by
  have h1 : (smulResidueAlgEquiv σ v) (residue v.toValuationSubring ⟨f, hf⟩)
      = IsLocalRing.ResidueField.mapEquiv (smulRingEquiv σ v.toValuationSubring)
          (residue v.toValuationSubring ⟨f, hf⟩) := rfl
  rw [h1, IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  exact congrArg _ (Subtype.ext rfl)

theorem evalAt_smul (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    (σ • v).evalAt (σ f) = v.evalAt f := by
  have hv' : (σ • v).IsRational := isRational_smul σ v hv
  have hmem : σ f ∈ (σ • v).toValuationSubring :=
    (mem_smul_toValuationSubring_iff σ v f).mpr hf
  apply (σ • v).algebraMap_residueField_injective
  rw [(σ • v).algebraMap_evalAt hv' hmem, residue_smul σ v hf, ← v.algebraMap_evalAt hv hf]
  exact (smulResidueAlgEquiv σ v).commutes (v.evalAt f)

end Place

namespace Divisor

variable (σ : F ≃ₐ[K] F)

theorem evalFun_smul {f : F} (D : Divisor K F)
    (hrat : ∀ v ∈ D.support, Place.IsRational v)
    (hmem : ∀ v ∈ D.support, f ∈ v.toValuationSubring) :
    evalFun (σ f) (σ • D) = evalFun f D := by
  classical
  rw [show evalFun (σ f) (σ • D) = (σ • D).prod fun v n => v.evalAt (σ f) ^ n from rfl,
    Divisor.smul_def, Finsupp.prod_mapDomain_index_inj (MulAction.injective σ)]
  refine Finsupp.prod_congr fun v hv => ?_
  congr 1
  exact Place.evalAt_smul σ v (hrat v hv) (hmem v hv)

end Divisor

namespace WeilDatum

variable {n : ℕ} (σ : F ≃ₐ[K] F)

def galSmul (d : WeilDatum K F n) : WeilDatum K F n where
  D₁ := σ • d.D₁
  D₂ := σ • d.D₂
  f₁ := σ d.f₁
  f₂ := σ d.f₂
  f₁_ne_zero := by
    simpa using d.f₁_ne_zero
  f₂_ne_zero := by
    simpa using d.f₂_ne_zero
  ord_f₁ := by
    intro v
    rw [show v = σ • (σ⁻¹ • v) from (smul_inv_smul σ v).symm, Place.ord_smul,
      Divisor.smul_apply_smul]
    exact d.ord_f₁ (σ⁻¹ • v)
  ord_f₂ := by
    intro v
    rw [show v = σ • (σ⁻¹ • v) from (smul_inv_smul σ v).symm, Place.ord_smul,
      Divisor.smul_apply_smul]
    exact d.ord_f₂ (σ⁻¹ • v)
  disjoint := by
    intro v
    rw [Divisor.smul_apply, Divisor.smul_apply]
    exact d.disjoint (σ⁻¹ • v)
  rational := by
    intro v hv
    rw [Divisor.smul_apply, Divisor.smul_apply] at hv
    have h1 : (σ⁻¹ • v).IsRational := d.rational (σ⁻¹ • v) hv
    have h2 := Place.isRational_smul σ (σ⁻¹ • v) h1
    rwa [smul_inv_smul] at h2

theorem galSmul_pairing (d : WeilDatum K F n) : (d.galSmul σ).pairing = d.pairing := by
  show Divisor.evalFun (σ d.f₁) (σ • d.D₂) / Divisor.evalFun (σ d.f₂) (σ • d.D₁) = d.pairing
  rw [Divisor.evalFun_smul σ d.D₂ (fun v hv => d.rational_of_mem_support_right hv)
      (fun v hv => v.mem_toValuationSubring_of_ord_nonneg_alt d.f₁_ne_zero (d.ord_f₁_eq_zero_of_mem_support hv).ge),
    Divisor.evalFun_smul σ d.D₁ (fun v hv => d.rational_of_mem_support_left hv)
      (fun v hv => v.mem_toValuationSubring_of_ord_nonneg_alt d.f₂_ne_zero (d.ord_f₂_eq_zero_of_mem_support hv).ge)]
  rfl

variable [NeZero n] [HasPrincipalDivisors K F]

theorem coe_classLeft_galSmul (d : WeilDatum K F n) :
    ((d.galSmul σ).classLeft : Pic0 K F) = σ • (d.classLeft : Pic0 K F) := by
  rw [coe_classLeft, coe_classLeft, Pic0.smul_mk]
  exact congrArg Pic0.mk (Subtype.ext rfl)

theorem coe_classRight_galSmul (d : WeilDatum K F n) :
    ((d.galSmul σ).classRight : Pic0 K F) = σ • (d.classRight : Pic0 K F) := by
  rw [coe_classRight, coe_classRight, Pic0.smul_mk]
  exact congrArg Pic0.mk (Subtype.ext rfl)

end WeilDatum

theorem Pic0.smul_mem_torsion (σ : F ≃ₐ[K] F) {n : ℕ} {x : Pic0 K F}
    (hx : x ∈ Pic0.torsion K F n) : σ • x ∈ Pic0.torsion K F n := by
  rw [Pic0.mem_torsion] at hx ⊢
  have hx' : n • x = 0 := by
    rwa [show ((n : ℤ) • x : Pic0 K F) = n • x from natCast_zsmul ..] at hx
  rw [show ((n : ℤ) • (σ • x) : Pic0 K F) = n • (σ • x) from natCast_zsmul ..]
  have key : ∀ (m : ℕ) (y : Pic0 K F), m • (σ • y) = σ • (m • y) := by
    intro m y
    induction m with
    | zero =>
        rw [zero_nsmul, zero_nsmul]
        exact (smul_zero σ).symm
    | succ k ih =>
        rw [succ_nsmul, succ_nsmul, ih]
        exact (smul_add σ _ _).symm
  rw [key n x, hx']
  rw [show (0 : Pic0 K F) = Pic0.mk 0 from rfl, Pic0.smul_mk]
  exact congrArg Pic0.mk (map_zero _)

end GaloisAction

namespace WeilDatum

variable {n : ℕ}

theorem pairing_eq_of_addPrincipalLeft (hrec : WeilReciprocity K F)
    (d d' : WeilDatum K F n) {E : Divisor K F} {h : F} (hh : h ≠ 0)
    (hE : ∀ v : Place K F, E v = v.ord h)
    (hD₁ : d'.D₁ = d.D₁ + E) (hD₂ : d'.D₂ = d.D₂)
    (hf₁ : d'.f₁ = d.f₁ * h ^ (n : ℤ)) (hf₂ : d'.f₂ = d.f₂) :
    d'.pairing = d.pairing := by
  classical

  have hE0 : ∀ v : Place K F, d.D₂ v ≠ 0 → E v = 0 := by
    intro v hv
    have h1 : d.D₁ v = 0 := (d.disjoint v).resolve_right hv
    have h2 : d'.D₁ v = 0 := (d'.disjoint v).resolve_right (by rw [hD₂]; exact hv)
    have h3 : d'.D₁ v = d.D₁ v + E v := by rw [hD₁]; rfl
    rw [h1, h2, zero_add] at h3
    exact h3.symm
  have hordh : ∀ v ∈ d.D₂.support, v.ord h = 0 := by
    intro v hv
    rw [← hE v]
    exact hE0 v (Finsupp.mem_support_iff.mp hv)
  have hratD₂ : ∀ v ∈ d.D₂.support, Place.IsRational v :=
    fun v hv => d.rational_of_mem_support_right hv

  have hratE : ∀ v ∈ E.support, Place.IsRational v := by
    intro v hv
    have hEv : E v ≠ 0 := Finsupp.mem_support_iff.mp hv
    by_cases hD₁v : d.D₁ v = 0
    · refine d'.rational v (Or.inl ?_)
      rw [hD₁]
      show d.D₁ v + E v ≠ 0
      rw [hD₁v, zero_add]
      exact hEv
    · exact d.rational v (Or.inl hD₁v)

  have hordf₂E : ∀ v ∈ E.support, v.ord d.f₂ = 0 := by
    intro v hv
    have hEv : E v ≠ 0 := Finsupp.mem_support_iff.mp hv
    have hD₂v : d.D₂ v = 0 := by
      by_contra hne
      exact hEv (hE0 v hne)
    rw [d.ord_f₂ v, hD₂v, mul_zero]
  have hevalf₂E : ∀ v ∈ E.support, v.evalAt d.f₂ ≠ 0 := fun v hv =>
    v.evalAt_ne_zero_of_ord_eq_zero (hratE v hv) d.f₂_ne_zero (hordf₂E v hv)

  have hnum : Divisor.evalFun d'.f₁ d'.D₂
      = Divisor.evalFun d.f₁ d.D₂ * Divisor.evalFun h d.D₂ ^ (n : ℤ) := by
    rw [hf₁, hD₂,
      Divisor.evalFun_mul_of_forall_mem hratD₂
        (fun v hv => v.mem_toValuationSubring_of_ord_nonneg_alt d.f₁_ne_zero (d.ord_f₁_eq_zero_of_mem_support hv).ge)
        (fun v hv => v.mem_toValuationSubring_of_ord_nonneg_alt (zpow_ne_zero _ hh)
          (by rw [Place.ord_zpow, hordh v hv, mul_zero])),
      Divisor.evalFun_zpow_left_of_ord_eq_zero hh (n : ℤ) hratD₂ hordh]

  have hrecip : Divisor.evalFun h d.D₂ ^ (n : ℤ) = Divisor.evalFun d.f₂ E := by
    rw [← Divisor.evalFun_zsmul_divisor]
    refine (hrec d.f₂ h ((n : ℤ) • d.D₂) E d.f₂_ne_zero hh
      (fun v => ?_) (fun v => (hE v).symm ▸ rfl) (fun v => ?_) (fun v hv => ?_) hratE).symm
    · rw [Finsupp.smul_apply, smul_eq_mul, d.ord_f₂ v]
    · by_cases hD₂v : d.D₂ v = 0
      · exact Or.inl (by rw [d.ord_f₂ v, hD₂v, mul_zero])
      · exact Or.inr (by rw [← hE v]; exact hE0 v hD₂v)
    · exact hratD₂ v (Divisor.support_smul_subset _ _ hv)

  have hden : Divisor.evalFun d'.f₂ d'.D₁
      = Divisor.evalFun d.f₂ d.D₁ * Divisor.evalFun d.f₂ E := by
    rw [hf₂, hD₁]
    exact Divisor.evalFun_add_of_forall_ne_zero d.f₂ (fun v hv => d.evalAt_f₂_ne_zero hv) hevalf₂E

  have hEne : Divisor.evalFun d.f₂ E ≠ 0 := Divisor.evalFun_ne_zero_of_forall_ne_zero hevalf₂E
  show Divisor.evalFun d'.f₁ d'.D₂ / Divisor.evalFun d'.f₂ d'.D₁ = d.pairing
  rw [hnum, hrecip, hden]
  rw [show d.pairing = Divisor.evalFun d.f₁ d.D₂ / Divisor.evalFun d.f₂ d.D₁ from rfl]
  rw [mul_div_mul_right _ _ hEne]

theorem gate_pairing_eq_of_addPrincipalLeft_refl (hrec : WeilReciprocity K F)
    (d : WeilDatum K F n) :
    d.pairing = d.pairing := by
  have h0 : ∀ v : Place K F, (0 : Divisor K F) v = v.ord (1 : F) := by
    intro v
    rw [Place.ord_one]
    rfl
  have h1 : d.D₁ = d.D₁ + 0 := by rw [add_zero]
  have h2 : d.f₁ = d.f₁ * (1 : F) ^ (n : ℤ) := by rw [one_zpow, mul_one]
  exact pairing_eq_of_addPrincipalLeft hrec d d one_ne_zero h0 h1 rfl h2 rfl

end WeilDatum

namespace WeilDatum

variable {n : ℕ} (d : WeilDatum K F n)

theorem evalFun_f₁_ne_zero : Divisor.evalFun d.f₁ d.D₂ ≠ 0 :=
  Divisor.evalFun_ne_zero_of_forall_ne_zero fun _ hv => d.evalAt_f₁_ne_zero hv

theorem evalFun_f₂_ne_zero : Divisor.evalFun d.f₂ d.D₁ ≠ 0 :=
  Divisor.evalFun_ne_zero_of_forall_ne_zero fun _ hv => d.evalAt_f₂_ne_zero hv

private theorem pairing_ne_zero : d.pairing ≠ 0 :=
  div_ne_zero d.evalFun_f₁_ne_zero d.evalFun_f₂_ne_zero

theorem evalFun_f₁_pow :
    Divisor.evalFun d.f₁ d.D₂ ^ n = Divisor.evalFun d.f₁ ((n : ℤ) • d.D₂) :=
  (Divisor.evalFun_natCast_smul_divisor d.f₁ d.D₂ n).symm

theorem evalFun_f₂_pow :
    Divisor.evalFun d.f₂ d.D₁ ^ n = Divisor.evalFun d.f₂ ((n : ℤ) • d.D₁) :=
  (Divisor.evalFun_natCast_smul_divisor d.f₂ d.D₁ n).symm

private theorem pairing_pow_eq_one (h : WeilReciprocity K F) : d.pairing ^ n = 1 := by
  have key : Divisor.evalFun d.f₁ ((n : ℤ) • d.D₂)
      = Divisor.evalFun d.f₂ ((n : ℤ) • d.D₁) := by
    refine h d.f₁ d.f₂ ((n : ℤ) • d.D₁) ((n : ℤ) • d.D₂) d.f₁_ne_zero d.f₂_ne_zero
      (fun v => ?_) (fun v => ?_) (fun v => ?_) (fun v hv => ?_) (fun v hv => ?_)
    · rw [Finsupp.smul_apply, smul_eq_mul, d.ord_f₁ v]
    · rw [Finsupp.smul_apply, smul_eq_mul, d.ord_f₂ v]
    · rcases d.disjoint v with h1 | h2
      · exact Or.inl (by rw [d.ord_f₁ v, h1, mul_zero])
      · exact Or.inr (by rw [d.ord_f₂ v, h2, mul_zero])
    · exact d.rational_of_mem_support_left (Divisor.support_smul_subset _ _ hv)
    · exact d.rational_of_mem_support_right (Divisor.support_smul_subset _ _ hv)
  rw [pairing, div_pow, d.evalFun_f₁_pow, d.evalFun_f₂_pow, key, div_self]
  rw [← d.evalFun_f₂_pow]
  exact pow_ne_zero n d.evalFun_f₂_ne_zero

theorem symm_pairing_eq_inv : d.symm.pairing = d.pairing⁻¹ := by
  rw [pairing, pairing, inv_div]
  rfl

theorem pairing_mul_symm_pairing : d.pairing * d.symm.pairing = 1 := by
  rw [d.symm_pairing_eq_inv, mul_inv_cancel₀ d.pairing_ne_zero]

private theorem addLeft_pairing (d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (hf : d.f₂ = d'.f₂) :
    (d.addLeft d' hD hf).pairing = d.pairing * d'.pairing := by
  have hnum : Divisor.evalFun (d.f₁ * d'.f₁) d.D₂
      = Divisor.evalFun d.f₁ d.D₂ * Divisor.evalFun d'.f₁ d.D₂ := by
    refine Divisor.evalFun_mul_of_forall_mem (fun v hv => d.rational_of_mem_support_right hv)
      (fun v hv => ?_) (fun v hv => ?_)
    · exact v.mem_toValuationSubring_of_ord_nonneg_alt d.f₁_ne_zero (d.ord_f₁_eq_zero_of_mem_support hv).ge
    · exact v.mem_toValuationSubring_of_ord_nonneg_alt d'.f₁_ne_zero
        (d'.ord_f₁_eq_zero_of_mem_support (hD ▸ hv)).ge
  have hden : Divisor.evalFun d.f₂ (d.D₁ + d'.D₁)
      = Divisor.evalFun d.f₂ d.D₁ * Divisor.evalFun d.f₂ d'.D₁ := by
    refine Divisor.evalFun_add_of_forall_ne_zero d.f₂ (fun v hv => d.evalAt_f₂_ne_zero hv) (fun v hv => ?_)
    exact hf ▸ d'.evalAt_f₂_ne_zero hv
  show Divisor.evalFun (d.f₁ * d'.f₁) d.D₂ / Divisor.evalFun d.f₂ (d.D₁ + d'.D₁)
      = d.pairing * d'.pairing
  simp only [pairing]
  rw [hnum, hden, div_mul_div_comm, hD, hf]

end WeilDatum

section Carrier

variable (K F) in

structure DivisorialWeilPairingData (n : ℕ) [NeZero n] [HasPrincipalDivisors K F] where

  pair : Pic0.torsion K F n → Pic0.torsion K F n → K

  compatible : ∀ d : WeilDatum K F n, pair d.classLeft d.classRight = d.pairing

  move : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
    ∃ D : Divisor.degZero (K := K) (F := F),
      Pic0.mk D = (x : Pic0 K F) ∧
      (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
      (∀ v ∈ (D : Divisor K F).support, v ∉ S)

namespace DivisorialWeilPairingData

variable {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]
variable (e : DivisorialWeilPairingData K F n)

omit [NeZero n] [HasPrincipalDivisors K F] in

theorem exists_witness (x : Pic0.torsion K F n) (D : Divisor.degZero (K := K) (F := F))
    (hD : Pic0.mk D = (x : Pic0 K F)) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v := by
  have hx : (n : ℤ) • (x : Pic0 K F) = 0 := Pic0.mem_torsion.mp x.2
  have h1 : Pic0.mk ((n : ℤ) • D) = 0 := by
    have h2 : Pic0.mk ((n : ℤ) • D) = (n : ℤ) • Pic0.mk D := by
      show QuotientAddGroup.mk ((n : ℤ) • D) = (n : ℤ) • (QuotientAddGroup.mk D)
      exact QuotientAddGroup.mk_zsmul
        ((Divisor.principal (K := K) (F := F)).addSubgroupOf
          (Divisor.degZero (K := K) (F := F))) D (n : ℤ)
    rw [h2, hD, hx]
  have h3 : ((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) ∈
      (Divisor.principal (K := K) (F := F)).addSubgroupOf
        (Divisor.degZero (K := K) (F := F)) :=
    (QuotientAddGroup.eq_zero_iff _).mp h1
  rw [AddSubgroup.mem_addSubgroupOf] at h3
  have h4 : Divisor.IsPrincipal ((n : ℤ) • (D : Divisor K F)) := Divisor.mem_principal.mp h3
  obtain ⟨f, hf0, hford⟩ := h4
  refine ⟨f, hf0, fun v => ?_⟩
  have := hford v
  rw [Finsupp.smul_apply, smul_eq_mul] at this
  exact this.symm

include e in

theorem exists_datum (x y : Pic0.torsion K F n) :
    ∃ d : WeilDatum K F n, d.classLeft = x ∧ d.classRight = y := by
  classical
  obtain ⟨D₁, hD₁mk, hD₁rat, -⟩ := e.move x ∅
  obtain ⟨D₂, hD₂mk, hD₂rat, hD₂avoid⟩ := e.move y (D₁ : Divisor K F).support
  obtain ⟨f₁, hf₁0, hf₁⟩ := exists_witness x D₁ hD₁mk
  obtain ⟨f₂, hf₂0, hf₂⟩ := exists_witness y D₂ hD₂mk
  refine ⟨⟨(D₁ : Divisor K F), (D₂ : Divisor K F), f₁, f₂, hf₁0, hf₂0, hf₁, hf₂, ?_, ?_⟩,
    ?_, ?_⟩
  ·
    intro v
    by_cases hv : (D₂ : Divisor K F) v = 0
    · exact Or.inr hv
    · refine Or.inl ?_
      by_contra hv1
      exact hD₂avoid v (Finsupp.mem_support_iff.mpr hv) (Finsupp.mem_support_iff.mpr hv1)
  ·
    intro v hv
    rcases hv with h1 | h2
    · exact hD₁rat v (Finsupp.mem_support_iff.mpr h1)
    · exact hD₂rat v (Finsupp.mem_support_iff.mpr h2)
  ·
    refine Subtype.ext ?_
    show Pic0.mk _ = (x : Pic0 K F)
    rw [← hD₁mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  ·
    refine Subtype.ext ?_
    show Pic0.mk _ = (y : Pic0 K F)
    rw [← hD₂mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)

include e in

theorem exists_datum_pair (x x' y : Pic0.torsion K F n) :
    ∃ d d' : WeilDatum K F n, d.D₂ = d'.D₂ ∧ d.f₂ = d'.f₂ ∧
      d.classLeft = x ∧ d'.classLeft = x' ∧ d.classRight = y ∧ d'.classRight = y := by
  classical
  obtain ⟨D₂, hD₂mk, hD₂rat, -⟩ := e.move y ∅
  obtain ⟨D₁, hD₁mk, hD₁rat, hD₁avoid⟩ := e.move x (D₂ : Divisor K F).support
  obtain ⟨D₁', hD₁'mk, hD₁'rat, hD₁'avoid⟩ := e.move x' (D₂ : Divisor K F).support
  obtain ⟨f₂, hf₂0, hf₂⟩ := exists_witness y D₂ hD₂mk
  obtain ⟨f₁, hf₁0, hf₁⟩ := exists_witness x D₁ hD₁mk
  obtain ⟨f₁', hf₁'0, hf₁'⟩ := exists_witness x' D₁' hD₁'mk
  have hdisj : ∀ (D : Divisor.degZero (K := K) (F := F)),
      (∀ v ∈ (D : Divisor K F).support, v ∉ (D₂ : Divisor K F).support) →
      ∀ v : Place K F, (D : Divisor K F) v = 0 ∨ (D₂ : Divisor K F) v = 0 := by
    intro D havoid v
    by_cases hv : (D : Divisor K F) v = 0
    · exact Or.inl hv
    · refine Or.inr ?_
      by_contra hv2
      exact havoid v (Finsupp.mem_support_iff.mpr hv) (Finsupp.mem_support_iff.mpr hv2)
  refine ⟨⟨(D₁ : Divisor K F), (D₂ : Divisor K F), f₁, f₂, hf₁0, hf₂0, hf₁, hf₂,
      hdisj D₁ hD₁avoid, ?_⟩,
    ⟨(D₁' : Divisor K F), (D₂ : Divisor K F), f₁', f₂, hf₁'0, hf₂0, hf₁', hf₂,
      hdisj D₁' hD₁'avoid, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases hv with h1 | h2
    · exact hD₁rat v (Finsupp.mem_support_iff.mpr h1)
    · exact hD₂rat v (Finsupp.mem_support_iff.mpr h2)
  · intro v hv
    rcases hv with h1 | h2
    · exact hD₁'rat v (Finsupp.mem_support_iff.mpr h1)
    · exact hD₂rat v (Finsupp.mem_support_iff.mpr h2)
  · refine Subtype.ext ?_
    show Pic0.mk _ = (x : Pic0 K F)
    rw [← hD₁mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  · refine Subtype.ext ?_
    show Pic0.mk _ = (x' : Pic0 K F)
    rw [← hD₁'mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  · refine Subtype.ext ?_
    show Pic0.mk _ = (y : Pic0 K F)
    rw [← hD₂mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  · refine Subtype.ext ?_
    show Pic0.mk _ = (y : Pic0 K F)
    rw [← hD₂mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)

theorem pair_ne_zero (x y : Pic0.torsion K F n) : e.pair x y ≠ 0 := by
  obtain ⟨d, hx, hy⟩ := e.exists_datum x y
  rw [← hx, ← hy, e.compatible d]
  exact d.pairing_ne_zero

theorem pair_add_left (x x' y : Pic0.torsion K F n) :
    e.pair (x + x') y = e.pair x y * e.pair x' y := by
  obtain ⟨d, d', hD₂, hf₂, hx, hx', hy, hy'⟩ := e.exists_datum_pair x x' y
  have h1 := e.compatible (d.addLeft d' hD₂ hf₂)
  rw [WeilDatum.classLeft_addLeft, WeilDatum.classRight_addLeft,
    WeilDatum.addLeft_pairing, hx, hx', hy] at h1
  rw [h1, ← e.compatible d, ← e.compatible d', hx, hx', hy, hy']

theorem pair_mul_pair_swap (x y : Pic0.torsion K F n) :
    e.pair x y * e.pair y x = 1 := by
  obtain ⟨d, hx, hy⟩ := e.exists_datum x y
  have h1 := e.compatible d
  have h2 := e.compatible d.symm
  rw [hx, hy] at h1
  rw [WeilDatum.classLeft_symm, WeilDatum.classRight_symm, hx, hy] at h2
  rw [h1, h2]
  exact d.pairing_mul_symm_pairing

theorem pair_zero_left (y : Pic0.torsion K F n) : e.pair 0 y = 1 := by
  classical
  obtain ⟨D₂, hD₂mk, hD₂rat, -⟩ := e.move y ∅
  obtain ⟨f₂, hf₂0, hf₂⟩ := exists_witness y D₂ hD₂mk

  set d : WeilDatum K F n :=
    ⟨0, (D₂ : Divisor K F), 1, f₂, one_ne_zero, hf₂0,
      fun v => by simp [Place.ord_one],
      hf₂, fun v => Or.inl rfl,
      fun v hv => by
        rcases hv with h1 | h2
        · exact absurd rfl h1
        · exact hD₂rat v (Finsupp.mem_support_iff.mpr h2)⟩ with hd
  have h1 := e.compatible d
  have hclassL : d.classLeft = 0 := by
    have h0 : d.degZeroLeft = (0 : Divisor.degZero (K := K) (F := F)) := Subtype.ext rfl
    refine Subtype.ext ?_
    rw [WeilDatum.coe_classLeft, h0, Pic0.mk_zero]
    simp
  have hclassR : d.classRight = y := by
    refine Subtype.ext ?_
    show Pic0.mk _ = (y : Pic0 K F)
    rw [← hD₂mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  have hpairing : d.pairing = 1 := by
    show Divisor.evalFun (1 : F) (D₂ : Divisor K F) / Divisor.evalFun f₂ (0 : Divisor K F) = 1
    rw [Divisor.evalFun_one, Divisor.evalFun_zero, div_one]
  rw [hclassL, hclassR, hpairing] at h1
  exact h1

theorem pair_zero_right (x : Pic0.torsion K F n) : e.pair x 0 = 1 := by
  have h1 := e.pair_mul_pair_swap x 0
  rw [e.pair_zero_left x, mul_one] at h1
  exact h1

theorem pair_swap_eq_inv (x y : Pic0.torsion K F n) : e.pair y x = (e.pair x y)⁻¹ :=
  eq_inv_of_mul_eq_one_left (e.pair_mul_pair_swap y x)

theorem pair_add_right (x y y' : Pic0.torsion K F n) :
    e.pair x (y + y') = e.pair x y * e.pair x y' := by
  calc e.pair x (y + y') = (e.pair (y + y') x)⁻¹ := e.pair_swap_eq_inv (y + y') x
    _ = (e.pair y x * e.pair y' x)⁻¹ := by rw [e.pair_add_left y y' x]
    _ = (e.pair y x)⁻¹ * (e.pair y' x)⁻¹ := by rw [mul_inv]
    _ = e.pair x y * e.pair x y' := by
        rw [e.pair_swap_eq_inv x y, e.pair_swap_eq_inv x y', inv_inv, inv_inv]

theorem pair_pow_eq_one (hrec : WeilReciprocity K F) (x y : Pic0.torsion K F n) :
    e.pair x y ^ n = 1 := by
  obtain ⟨d, hx, hy⟩ := e.exists_datum x y
  rw [← hx, ← hy, e.compatible d]
  exact d.pairing_pow_eq_one hrec

theorem pair_self_eq_one (hrec : WeilReciprocity K F) (hodd : Odd n)
    (x : Pic0.torsion K F n) : e.pair x x = 1 := by
  have hsq : e.pair x x * e.pair x x = 1 := e.pair_mul_pair_swap x x
  have hpow : e.pair x x ^ n = 1 := e.pair_pow_eq_one hrec x x
  obtain ⟨k, hk⟩ := hodd
  set c : K := e.pair x x with hc
  have hsq' : c ^ 2 = 1 := by rw [pow_two]; exact hsq
  have h2k : c ^ (2 * k) = 1 := by rw [pow_mul, hsq', one_pow]
  have hcn : c ^ n = c := by rw [hk, pow_succ, h2k, one_mul]
  rw [← hcn]
  exact hpow

theorem pair_smul (σ : F ≃ₐ[K] F) (x y : Pic0.torsion K F n) :
    e.pair ⟨σ • (x : Pic0 K F), Pic0.smul_mem_torsion σ x.2⟩
      ⟨σ • (y : Pic0 K F), Pic0.smul_mem_torsion σ y.2⟩ = e.pair x y := by
  obtain ⟨d, hx, hy⟩ := e.exists_datum x y
  have h1 := e.compatible (d.galSmul σ)
  have hL : (d.galSmul σ).classLeft
      = (⟨σ • (x : Pic0 K F), Pic0.smul_mem_torsion σ x.2⟩ : Pic0.torsion K F n) := by
    refine Subtype.ext ?_
    rw [WeilDatum.coe_classLeft_galSmul, hx]
  have hR : (d.galSmul σ).classRight
      = (⟨σ • (y : Pic0 K F), Pic0.smul_mem_torsion σ y.2⟩ : Pic0.torsion K F n) := by
    refine Subtype.ext ?_
    rw [WeilDatum.coe_classRight_galSmul, hy]
  rw [hL, hR, WeilDatum.galSmul_pairing] at h1
  rw [h1, ← e.compatible d, hx, hy]

end DivisorialWeilPairingData

end Carrier

section Bridge

variable {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]

namespace DivisorialWeilPairingData

variable (e : DivisorialWeilPairingData K F n)

def toChar (x : Pic0.torsion K F n) : HomPic0Gm K F n where
  toFun y := e.pair x y
  map_zero_eq_one' := e.pair_zero_right x
  map_add_eq_mul' y y' := e.pair_add_right x y y'

@[simp] theorem toChar_apply (x y : Pic0.torsion K F n) : e.toChar x y = e.pair x y := rfl

def toHom : Pic0.torsion K F n →+ Additive (HomPic0Gm K F n) :=
  AddMonoidHom.mk' (fun x => Additive.ofMul (e.toChar x)) (by
    intro x x'
    have h : e.toChar (x + x') = e.toChar x * e.toChar x' := by
      ext y
      rw [AddChar.mul_apply]
      exact e.pair_add_left x x' y
    show Additive.ofMul (e.toChar (x + x'))
        = Additive.ofMul (e.toChar x) + Additive.ofMul (e.toChar x')
    rw [h, ofMul_mul])

@[simp] theorem toHom_apply_apply (x y : Pic0.torsion K F n) :
    (Additive.toMul (e.toHom x)) y = e.pair x y := rfl

def Perfect : Prop := Function.Bijective e.toHom

def toWeilPairingData (h : e.Perfect) : WeilPairingData K F n where
  toHom := e.toHom
  bijective := h

theorem toWeilPairingData_eval (h : e.Perfect) (x y : Pic0.torsion K F n) :
    (e.toWeilPairingData h).eval x y = e.pair x y := rfl

end DivisorialWeilPairingData

variable (K F) in

def ExistsPerfectDivisorialWeilPairing (n : ℕ) [NeZero n] [HasPrincipalDivisors K F] : Prop :=
  ∃ e : DivisorialWeilPairingData K F n, e.Perfect

theorem nonempty_weilPairingData_of_existsPerfectDivisorialWeilPairing
    (h : ExistsPerfectDivisorialWeilPairing K F n) :
    Nonempty (WeilPairingData K F n) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.toWeilPairingData he⟩

end Bridge

end AlgebraicCurve

/--
info: 'AlgebraicCurve.WeilDatum.classLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.WeilDatum.classLeft

/--
info: 'AlgebraicCurve.WeilDatum.galSmul_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.WeilDatum.galSmul_pairing

/--
info: 'AlgebraicCurve.WeilDatum.pairing_eq_of_addPrincipalLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.WeilDatum.pairing_eq_of_addPrincipalLeft

/--
info: 'AlgebraicCurve.DivisorialWeilPairingData.pair_add_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.DivisorialWeilPairingData.pair_add_left

/--
info: 'AlgebraicCurve.DivisorialWeilPairingData.pair_pow_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.DivisorialWeilPairingData.pair_pow_eq_one

/--
info: 'AlgebraicCurve.DivisorialWeilPairingData.pair_self_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.DivisorialWeilPairingData.pair_self_eq_one

/--
info: 'AlgebraicCurve.DivisorialWeilPairingData.pair_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.DivisorialWeilPairingData.pair_smul

/--
info: 'AlgebraicCurve.DivisorialWeilPairingData.toWeilPairingData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.DivisorialWeilPairingData.toWeilPairingData

/--
info: 'AlgebraicCurve.nonempty_weilPairingData_of_existsPerfectDivisorialWeilPairing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.nonempty_weilPairingData_of_existsPerfectDivisorialWeilPairing


