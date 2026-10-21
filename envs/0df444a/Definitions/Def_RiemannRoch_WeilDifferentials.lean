-- Prove2me | Definitions.Def_RiemannRoch_WeilDifferentials
-- name    : RiemannRoch_WeilDifferentials
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T13:14:23.494981+00:00
-- url     : https://prove2.me/theorems/9aaca127-ffa8-4483-b87a-fda0195fbfdc
-- title:
--   Weil differentials, divisors of differentials and canonical divisors
-- statement:
--   Throughout, $k$ is a field and $K$ is a field together with compatible embeddings $k[X]\subset k(X)\subset K$ such that $K/k(X)$ is a finite separable extension; $K$ is thus an algebraic function field in one variable over $k$, presented together with the transcendental element $x=X\in K$. Assume moreover that $k$ is the full constant field of $K$. Let $\mathcal A_K$ be the adele space, $\mathcal A_K(D)$ its filtration and $\widetilde K$ the principal adeles (files `RiemannRoch_Adeles`, `RiemannRoch_IntrinsicAdeles`), $g$ the genus and $i(D)$ the index of speciality.
--
--   This file introduces, first for chart divisors and then for divisors on intrinsic places:
--
--   1. **Weil differentials.** A Weil differential is a $k$-linear map $\omega:\mathcal A_K\to k$ that vanishes on $\mathcal A_K(D)+\widetilde K$ for some divisor $D$. They form a $K$-vector space $\Omega_K$ under $(x\omega)(\alpha)=\omega(x\alpha)$; $\omega$ is nonzero if it is not the zero map.
--   2. **The spaces $\Omega_K(D)$.** For a divisor $D$,
--   $$\Omega_K(D)=\{\omega:\mathcal A_K\to k\ \text{linear}:\ \omega(\mathcal A_K(D)+\widetilde K)=0\},$$
--   the annihilator of $\mathcal A_K(D)+\widetilde K$; for chart divisors it is finite-dimensional with $\dim_k\Omega_K(D)=i(D)$.
--   3. **Divisor of a differential.** For $\omega\ne0$, the set of divisors $D$ with $\omega(\mathcal A_K(D)+\widetilde K)=0$ has a unique largest element, the divisor $(\omega)$.
--   4. **Canonical divisors.** A divisor $W$ is canonical if $W=(\omega)$ for some nonzero Weil differential $\omega$.
--   5. **Intrinsic versions.** The same notions on intrinsic places, with isomorphisms to the chart versions ($K$-linear for $\Omega_K$, $k$-linear for $\Omega_K(D)$ and the dual of $\mathcal A_K$), together with the intrinsic Riemann–Roch space $\mathcal L(D)=\{f: f=0\text{ or }v_P(f)\ge-D(P)\ \forall P\}$, $\ell(D)$, the defect $\deg D+1-\ell(D)$, the genus (supremum of the defects), $i(D)$, $\dim_k\mathcal A_K/(\mathcal A_K(D)+\widetilde K)$ with its isomorphism to the chart quotient, and the sandwich rank.
--
--   The file also contains the structural lemmas needed for these definitions: $\mathcal A_K/(\mathcal A_K(D)+\widetilde K)$ is finite-dimensional; $D\le D'$ and $\deg D'\le\deg D$ imply $D=D'$; $x\,(\mathcal A_K(D+\operatorname{div}(x))+\widetilde K)\subseteq\mathcal A_K(D)+\widetilde K$; $x\omega=0$ iff $\omega=0$ for $x\ne0$; for a nonzero $\omega$ vanishing on $\mathcal A_K(D_0)+\widetilde K$, the map $f\mapsto f\omega$ is an injective $k$-linear map $\mathcal L(E)\to\Omega_K(D_0-E)$; the vanishing divisors of $\omega$ are closed under $\max$ and have degree at most $2g-1$, whence the existence and uniqueness of $(\omega)$; and the compatibility of the intrinsic and chart constructions.
--
--   Weil differentials provide the canonical divisor $W$ and the duality $\Omega_K(D)\cong\mathcal L(W-D)$ through which the index of speciality becomes $i(D)=\ell(W-D)$, giving the Riemann–Roch theorem $\ell(D)=\deg D+1-g+\ell(W-D)$. In the chain of definition files it imports `RiemannRoch_FilterChain4` and is imported by `RiemannRoch_WeierstrassDedekind`.
--
--   **Formalization Note** The function field is not constructed from $k$: $K$ is an arbitrary field carrying the instances `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, Mathlib's `FunctionField k K` (i.e. $K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`; when constants are needed, also `Algebra k K` with `IsScalarTower k k[X] K`. Weil differentials are the structures `FunctionField.Chart.WeilDifferential k K` and `FunctionField.WeilDifferential k K` (a linear map `toFun` with an existential vanishing divisor); $(\omega)$ is `divOmega` (chosen by `Classical.choose` from the unique-existence statement) and canonical divisors are `IsCanonical`. The intrinsic genus `FunctionField.genus k K` is `(sSup {deg D + 1 - ℓ(D)}).toNat` over intrinsic divisors; its agreement with the chart genus is the separate theorem `FunctionField.genus_eq_genusChart`. The source modules `RiemannRochTheorem/Basic.lean`, `LinearKneser.lean` and `RiemannRochTheorem/Corollaries.lean` are listed among the origins of this file but contribute no declaration to it.
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.5 (Weil differentials $\Omega_F$ and $\Omega_F(A)$, $\dim\Omega_F(A)=i(A)$, the divisor $(\omega)$ of a Weil differential, canonical divisors). Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/WeilDifferential/Basic.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/CoordinateFree/WeilDifferential.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/RiemannRochTheorem/Basic.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/LinearKneser.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/RiemannRochTheorem/Corollaries.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/CoordinateFree/RiemannRoch.lean

import Mathlib
import Definitions.Def_RiemannRoch_FilterChain4

/-
Contains code from riemann-roch-function-fields
(https://github.com/vaca22/riemann-roch-function-fields, commit dbca5bee),
Copyright (c) 2026 Guanghao Li, released under the Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Modified: ported to Lean v4.33.1 / Mathlib 0df444a (module headers converted, some proofs
adapted to this Mathlib, a few names qualified, `picTorsor` omitted; statements unchanged), then
split into prove2.me definitions and theorems, with comments removed.
-/

set_option linter.style.haveILetI false

section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FunctionField.Chart
variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
variable [IsFullConstantField k K]
local instance instDecidableEqRatFuncWeil : DecidableEq k⟮X⟯ := Classical.decEq _
attribute [local instance] adeleFiltAddCommGroup adeleFiltModule
instance instIsScalarTowerAdeleSpace : IsScalarTower k K (AdeleSpace k K) :=
  ⟨fun c x a => Subtype.ext <| funext fun v => by
    change (c • x) * a.val v = c • (x * a.val v)
    rw [Algebra.smul_def, Algebra.smul_def, mul_assoc]⟩
omit [IsFullConstantField k K] in
theorem finite_adeleFilt_sub_quotient {D D' : DivisorA k K} (hle : D ≤ D') :
    Module.Finite k ((adeleFilt k K D') ⧸
      Submodule.comap (adeleFilt k K D').subtype
        (adeleFilt k K D + diagonalSubmodule k K)) := by
  have hE : IsEffective k K (D' - D) := (le_iff_sub_effective k K).mp hle
  have hdiv : D + (D' - D) = D' := by abel
  haveI : Module.Finite k ((adeleFilt k K D') ⧸
      Submodule.comap (adeleFilt k K D').subtype (adeleFilt k K D)) :=
    finiteAdeleFiltDiff_quotient_add_eq k K (M := D) hdiv.symm hE
  exact Module.Finite.equiv (Submodule.quotientQuotientEquivQuotient
    (Submodule.comap (adeleFilt k K D').subtype (adeleFilt k K D))
    (Submodule.comap (adeleFilt k K D').subtype
      (adeleFilt k K D + diagonalSubmodule k K))
    (Submodule.comap_mono (by
      rw [Submodule.add_eq_sup]
      exact le_sup_left)))
instance finiteDimensional_adeleQuotient (D : DivisorA k K) :
    FiniteDimensional k
      ((AdeleSpace k K) ⧸ (adeleFilt k K D + diagonalSubmodule k K)) := by
  obtain ⟨D₁, hD₁⟩ := exists_defect_eq (k := k) (K := K)
  have hle : D ≤ D ⊔ D₁ := le_sup_left
  have hfull : topAdeleSubmodule k K =
      adeleFilt k K (D ⊔ D₁) + diagonalSubmodule k K :=
    adeleSubmodule_top_eq_adeleFilt_add_diagonal (k := k) (K := K)
      (defect_eq_genus_of_ge (k := k) (K := K) le_sup_right hD₁)
  haveI := finite_adeleFilt_sub_quotient (k := k) (K := K) hle
  have hker : Submodule.comap (adeleFilt k K (D ⊔ D₁)).subtype
      (adeleFilt k K D + diagonalSubmodule k K) ≤
      LinearMap.ker (((adeleFilt k K D + diagonalSubmodule k K).mkQ).comp
        (adeleFilt k K (D ⊔ D₁)).subtype) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  refine Module.Finite.of_surjective (Submodule.liftQ _ _ hker) ?_
  intro y
  obtain ⟨x, rfl⟩ :=
    Submodule.mkQ_surjective (adeleFilt k K D + diagonalSubmodule k K) y
  have hx : x ∈ adeleFilt k K (D ⊔ D₁) + diagonalSubmodule k K := by
    have hxtop : x ∈ topAdeleSubmodule k K := Submodule.mem_top
    rwa [hfull] at hxtop
  rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
  refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
  rw [Submodule.liftQ_apply]
  show (adeleFilt k K D + diagonalSubmodule k K).mkQ a =
    (adeleFilt k K D + diagonalSubmodule k K).mkQ (a + b)
  have hb0 : (adeleFilt k K D + diagonalSubmodule k K).mkQ b = 0 := by
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_sup_right hb)
  rw [map_add, hb0, add_zero]
omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
theorem eq_of_le_of_deg_le {D D' : DivisorA k K} (h : D ≤ D')
    (hdeg : deg k K D' ≤ deg k K D) : D = D' := by
  have hE : IsEffective k K (D' - D) := (le_iff_sub_effective k K).mp h
  have hdeg0 : deg k K (D' - D) = 0 := by
    have hge : 0 ≤ deg k K (D' - D) := deg_nonneg k K hE
    rw [deg_sub] at hge ⊢
    omega
  have hzero : D' - D = 0 := eq_zero_of_effective_deg_zero k K hE hdeg0
  exact (sub_eq_zero.mp hzero).symm
structure WeilDifferential where
  toFun : AdeleSpace k K →ₗ[k] k
  vanishes_on : ∃ D : DivisorA k K,
    ∀ α ∈ adeleFilt k K D + diagonalSubmodule k K, toFun α = 0
namespace WeilDifferential
variable {k K}
def IsNonzero (ω : WeilDifferential k K) : Prop := ω.toFun ≠ 0
def differentialSpace (D : DivisorA k K) : Submodule k (AdeleSpace k K →ₗ[k] k) where
  carrier := {φ | ∀ a ∈ adeleFilt k K D + diagonalSubmodule k K, φ a = 0}
  zero_mem' := by simp
  add_mem' {f g} hf hg := by
    intro a ha
    simp [hf a ha, hg a ha]
  smul_mem' c f hf := by
    intro a ha
    simp [hf a ha]
theorem finrank_differentialSpace (D : DivisorA k K) :
    Module.finrank k (differentialSpace D) = indexOfSpecialty k K D := by
  let S := adeleFilt k K D + diagonalSubmodule k K
  have homega : differentialSpace D = S.dualAnnihilator := by
    ext φ
    rw [Submodule.mem_dualAnnihilator]
    change (∀ a ∈ adeleFilt k K D + diagonalSubmodule k K, φ a = 0) ↔ _
    rfl
  rw [homega, ← S.dualQuotEquivDualAnnihilator.finrank_eq, Subspace.dual_finrank_eq]
  exact finrank_adele_quotient k K D
omit [IsFullConstantField k K] in
theorem mul_mem_adeleFilt_add_diagonal (x : Kˣ) (D : DivisorA k K)
    {a : AdeleSpace k K}
    (ha : a ∈ adeleFilt k K (D + principalDivisorA k K (Additive.ofMul x)) +
      diagonalSubmodule k K) :
    (x : K) • a ∈ adeleFilt k K D + diagonalSubmodule k K := by
  rw [Submodule.add_eq_sup] at ha ⊢
  rcases Submodule.mem_sup.mp ha with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
  refine Submodule.mem_sup.mpr ⟨(x : K) • a₁, ?_, (x : K) • a₂, ?_,
    (smul_add (x : K) a₁ a₂).symm⟩
  · intro v
    change placeValuation k K v ((x : K) * a₁.val v) ≤ WithZero.exp (D v)
    rw [map_mul]
    have hxval := placeValuation_eq_exp_neg_principalDivisor k K (Additive.ofMul x) v
    change placeValuation k K v (x : K) =
      WithZero.exp (-(principalDivisorA k K (Additive.ofMul x) v)) at hxval
    rw [hxval]
    have hv := ha₁ v
    rw [Finsupp.add_apply, WithZero.exp_add] at hv
    calc
      WithZero.exp (-(principalDivisorA k K (Additive.ofMul x) v)) *
          placeValuation k K v (a₁.val v) ≤
          WithZero.exp (-(principalDivisorA k K (Additive.ofMul x) v)) *
            (WithZero.exp (D v) *
              WithZero.exp (principalDivisorA k K (Additive.ofMul x) v)) :=
        mul_le_mul_right hv _
      _ = WithZero.exp (D v) := by
        rw [← WithZero.exp_add, ← WithZero.exp_add]
        congr 1
        ring
  · rcases ha₂ with ⟨f, rfl⟩
    exact ⟨(x : K) * f, by ext v; rfl⟩
noncomputable def smulWeil (x : K) (ω : WeilDifferential k K) : WeilDifferential k K := by
  by_cases hx : x = 0
  · exact ⟨0, ⟨0, by simp⟩⟩
  let xu : Kˣ := Units.mk0 x hx
  refine ⟨ω.toFun.comp (mulAdeleLinear k K x), ?_⟩
  obtain ⟨D, hD⟩ := ω.vanishes_on
  refine ⟨D + principalDivisorA k K (Additive.ofMul xu), fun a ha => hD _ ?_⟩
  change x • a ∈ adeleFilt k K D + diagonalSubmodule k K
  simpa only [xu, Units.val_mk0] using
    mul_mem_adeleFilt_add_diagonal (k := k) (K := K) xu D ha
omit [IsFullConstantField k K] in
@[simp]
theorem smulWeil_toFun_apply (x : K) (ω : WeilDifferential k K) (a : AdeleSpace k K) :
    (smulWeil x ω).toFun a = ω.toFun (x • a) := by
  by_cases hx : x = 0
  · simp [smulWeil, hx]
  · simp only [smulWeil, hx, ↓reduceDIte, LinearMap.comp_apply]
    congr 1
instance : Zero (WeilDifferential k K) := ⟨⟨0, ⟨0, by simp⟩⟩⟩
instance : Add (WeilDifferential k K) where
  add ω η := ⟨ω.toFun + η.toFun, by
    obtain ⟨Dω, hω⟩ := ω.vanishes_on
    obtain ⟨Dη, hη⟩ := η.vanishes_on
    refine ⟨Dω ⊓ Dη, fun a ha => ?_⟩
    have hleft : adeleFilt k K (Dω ⊓ Dη) + diagonalSubmodule k K ≤
        adeleFilt k K Dω + diagonalSubmodule k K := by
      simpa only [Submodule.add_eq_sup] using
        sup_le_sup (adeleFilt_mono k K inf_le_left) le_rfl
    have hright : adeleFilt k K (Dω ⊓ Dη) + diagonalSubmodule k K ≤
        adeleFilt k K Dη + diagonalSubmodule k K := by
      simpa only [Submodule.add_eq_sup] using
        sup_le_sup (adeleFilt_mono k K inf_le_right) le_rfl
    simp [hω a (hleft ha), hη a (hright ha)]⟩
omit [IsFullConstantField k K] in
@[ext]
theorem ext {ω η : WeilDifferential k K} (h : ω.toFun = η.toFun) : ω = η := by
  cases ω
  cases η
  cases h
  rfl
instance : Neg (WeilDifferential k K) where
  neg ω := ⟨-ω.toFun, by
    obtain ⟨D, hD⟩ := ω.vanishes_on
    exact ⟨D, fun a ha => by simp [hD a ha]⟩⟩
instance : AddCommGroup (WeilDifferential k K) where
  add_assoc _ _ _ := ext (add_assoc _ _ _)
  zero_add _ := ext (zero_add _)
  add_zero _ := ext (add_zero _)
  add_comm _ _ := ext (add_comm _ _)
  nsmul := nsmulRec
  nsmul_zero _ := ext rfl
  nsmul_succ _ _ := ext rfl
  neg := Neg.neg
  neg_add_cancel ω := ext (neg_add_cancel ω.toFun)
  sub := fun ω η => ω + -η
  sub_eq_add_neg _ _ := rfl
  zsmul := zsmulRec
noncomputable instance : SMul K (WeilDifferential k K) := ⟨smulWeil⟩
noncomputable instance : Module K (WeilDifferential k K) :=
  Module.ofMinimalAxioms
    (fun x ω η => by
      apply ext
      ext a
      change (smulWeil x (ω + η)).toFun a =
        ((smulWeil x ω).toFun + (smulWeil x η).toFun) a
      rw [smulWeil_toFun_apply]
      change (ω.toFun + η.toFun) (x • a) =
        (smulWeil x ω).toFun a + (smulWeil x η).toFun a
      rw [LinearMap.add_apply, smulWeil_toFun_apply, smulWeil_toFun_apply])
    (fun x y ω => by
      apply ext
      ext a
      change (smulWeil (x + y) ω).toFun a =
        ((smulWeil x ω).toFun + (smulWeil y ω).toFun) a
      rw [smulWeil_toFun_apply]
      change ω.toFun ((x + y) • a) =
        (smulWeil x ω).toFun a + (smulWeil y ω).toFun a
      rw [smulWeil_toFun_apply, smulWeil_toFun_apply, add_smul, map_add])
    (fun x y ω => by
      apply ext
      ext a
      change (smulWeil (x * y) ω).toFun a = (smulWeil x (smulWeil y ω)).toFun a
      rw [smulWeil_toFun_apply, smulWeil_toFun_apply, smulWeil_toFun_apply]
      rw [← mul_smul, mul_comm x y])
    (fun ω => by
      apply ext
      ext a
      change (smulWeil 1 ω).toFun a = ω.toFun a
      rw [smulWeil_toFun_apply, one_smul])
omit [IsFullConstantField k K] in
theorem smulWeil_eq_zero_iff (x : K) (hx : x ≠ 0) (ω : WeilDifferential k K) :
    smulWeil x ω = 0 ↔ ω = 0 := by
  constructor
  · intro hxω
    calc ω = (1 : K) • ω := (one_smul K ω).symm
      _ = (x⁻¹ * x) • ω := by rw [inv_mul_cancel₀ hx]
      _ = x⁻¹ • (x • ω) := mul_smul x⁻¹ x ω
      _ = x⁻¹ • (smulWeil x ω) := rfl
      _ = x⁻¹ • (0 : WeilDifferential k K) := by rw [hxω]
      _ = 0 := smul_zero x⁻¹
  · intro hω
    subst hω
    show x • (0 : WeilDifferential k K) = 0
    exact smul_zero x
omit [IsFullConstantField k K] in
theorem differentialSpace_eq_dualAnnihilator (D : DivisorA k K) :
    differentialSpace (k := k) (K := K) D =
      (adeleFilt k K D + diagonalSubmodule k K).dualAnnihilator := by
  ext φ
  rw [Submodule.mem_dualAnnihilator]
  change (∀ a ∈ adeleFilt k K D + diagonalSubmodule k K, φ a = 0) ↔ _
  rfl
instance instFiniteDimensionalDifferentialSpace (D : DivisorA k K) :
    FiniteDimensional k (differentialSpace (k := k) (K := K) D) := by
  rw [differentialSpace_eq_dualAnnihilator D]
  exact Module.Finite.equiv
    (Submodule.dualQuotEquivDualAnnihilator
      (adeleFilt k K D + diagonalSubmodule k K))
def vanishingDivisors (ω : WeilDifferential k K) : Set (DivisorA k K) :=
  {D | ∀ α ∈ adeleFilt k K D + diagonalSubmodule k K, ω.toFun α = 0}
omit [IsFullConstantField k K] in
theorem smulWeil_toFun_mem_differentialSpace (ω : WeilDifferential k K) {D₀ : DivisorA k K}
    (h : D₀ ∈ vanishingDivisors ω) {E : DivisorA k K} (f : RRspace k K E) :
    (smulWeil (f : K) ω).toFun ∈ differentialSpace (k := k) (K := K) (D₀ - E) := by
  have hvan : ∀ α ∈ adeleFilt k K D₀ + diagonalSubmodule k K, ω.toFun α = 0 := h
  show ∀ a ∈ adeleFilt k K (D₀ - E) + diagonalSubmodule k K,
    (smulWeil (f : K) ω).toFun a = 0
  intro a ha
  rw [smulWeil_toFun_apply]
  by_cases hf : (f : K) = 0
  · rw [hf, zero_smul, map_zero]
  · have hmemE : memRRspace k K (D₀ - (D₀ - E)) (f : K) := by
      rw [sub_sub_cancel]
      exact (mem_RRspace_iff k K E (f : K)).mp f.property
    have hdivle : D₀ - E ≤ D₀ +
        principalDivisorA k K (Additive.ofMul (Units.mk0 (f : K) hf)) :=
      le_add_principal_of_memRRspace (k := k) (K := K) (D₀ := D₀ - E) (D₁ := D₀)
        hf hmemE
    have hle : adeleFilt k K (D₀ - E) + diagonalSubmodule k K ≤
        adeleFilt k K (D₀ + principalDivisorA k K
          (Additive.ofMul (Units.mk0 (f : K) hf))) + diagonalSubmodule k K := by
      simpa only [Submodule.add_eq_sup] using
        sup_le_sup (adeleFilt_mono k K hdivle) (le_refl (diagonalSubmodule k K))
    have hsm := mul_mem_adeleFilt_add_diagonal (k := k) (K := K)
      (Units.mk0 (f : K) hf) D₀ (hle ha)
    rw [Units.val_mk0] at hsm
    exact hvan _ hsm
noncomputable def smulIntoOmega (ω : WeilDifferential k K) {D₀ : DivisorA k K}
    (h : D₀ ∈ vanishingDivisors ω) (E : DivisorA k K) :
    RRspace k K E →ₗ[k] differentialSpace (k := k) (K := K) (D₀ - E) where
  toFun f := ⟨(smulWeil (f : K) ω).toFun, smulWeil_toFun_mem_differentialSpace ω h f⟩
  map_add' f g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change (smulWeil ((f : K) + (g : K)) ω).toFun a =
      (smulWeil (f : K) ω).toFun a + (smulWeil (g : K) ω).toFun a
    rw [smulWeil_toFun_apply, smulWeil_toFun_apply, smulWeil_toFun_apply, add_smul,
      map_add]
  map_smul' c f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change (smulWeil (c • (f : K)) ω).toFun a = c • (smulWeil (f : K) ω).toFun a
    rw [smulWeil_toFun_apply, smulWeil_toFun_apply, Algebra.smul_def, mul_smul,
      algebraMap_smul, map_smul]
omit [IsFullConstantField k K] in
@[simp]
theorem smulIntoOmega_coe (ω : WeilDifferential k K) {D₀ : DivisorA k K}
    (h : D₀ ∈ vanishingDivisors ω) (E : DivisorA k K) (f : RRspace k K E) :
    (smulIntoOmega ω h E f : AdeleSpace k K →ₗ[k] k) = (smulWeil (f : K) ω).toFun :=
  rfl
omit [IsFullConstantField k K] in
theorem smulIntoOmega_injective (ω : WeilDifferential k K) {D₀ : DivisorA k K}
    (h : D₀ ∈ vanishingDivisors ω) (E : DivisorA k K) (hω : ω.toFun ≠ 0) :
    Function.Injective (smulIntoOmega ω h E) := by
  intro f g hfg
  by_contra hne
  have hd0 : smulIntoOmega ω h E (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hval : ((f - g : RRspace k K E) : K) ≠ 0 := by
    intro h0
    exact hne (sub_eq_zero.mp (Subtype.ext h0))
  have htoFun : (smulWeil ((f - g : RRspace k K E) : K) ω).toFun = 0 :=
    congrArg Subtype.val hd0
  have hzero : smulWeil ((f - g : RRspace k K E) : K) ω = 0 := ext htoFun
  have hω0 : ω = 0 := (smulWeil_eq_zero_iff _ hval ω).mp hzero
  apply hω
  rw [hω0]
  rfl
omit [IsFullConstantField k K] in
theorem sup_mem_vanishingDivisors {ω : WeilDifferential k K} {D₁ D₂ : DivisorA k K}
    (hD₁ : D₁ ∈ vanishingDivisors ω) (hD₂ : D₂ ∈ vanishingDivisors ω) :
    D₁ ⊔ D₂ ∈ vanishingDivisors ω := by
  intro α hα
  rw [Submodule.add_eq_sup, adeleFilt_sup_eq_add, ← Submodule.add_eq_sup] at hα
  rw [Submodule.add_eq_sup] at hα
  rcases Submodule.mem_sup.mp hα with ⟨a, ha, d, hd, rfl⟩
  rw [Submodule.add_eq_sup] at ha
  rcases Submodule.mem_sup.mp ha with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
  have hsplit : a₁ + a₂ + d = (a₁ + d) + a₂ := by abel
  rw [hsplit, map_add]
  have h1 : ω.toFun (a₁ + d) = 0 := by
    apply hD₁
    rw [Submodule.add_eq_sup]
    exact Submodule.add_mem_sup ha₁ hd
  have h2 : ω.toFun a₂ = 0 := by
    apply hD₂
    rw [Submodule.add_eq_sup]
    exact Submodule.mem_sup_left ha₂
  rw [h1, h2, add_zero]
theorem deg_le_of_mem_vanishingDivisors {ω : WeilDifferential k K} (hω : ω.toFun ≠ 0)
    {D : DivisorA k K} (hD : D ∈ vanishingDivisors ω) :
    deg k K D ≤ 2 * (genus k K : ℤ) - 1 := by
  have hinj : Function.Injective (smulIntoOmega ω hD D) :=
    smulIntoOmega_injective ω hD D hω
  have hle : Module.finrank k (RRspace k K D) ≤
      Module.finrank k (differentialSpace (k := k) (K := K) (D - D)) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have hDD : D - D = (0 : DivisorA k K) := sub_self D
  have hΩ : Module.finrank k (differentialSpace (k := k) (K := K) (D - D)) = genus k K := by
    rw [hDD, finrank_differentialSpace]
    have hidx := indexOfSpecialty_eq (k := k) (K := K) (0 : DivisorA k K)
    rw [ell_zero (k := k) (K := K), deg_zero (k := k) (K := K)] at hidx
    omega
  have hℓg : (ell k K D : ℤ) ≤ (genus k K : ℤ) := by
    have hnat : ell k K D ≤ genus k K := by
      rw [show ell k K D = Module.finrank k (RRspace k K D) from rfl, ← hΩ]
      exact hle
    exact_mod_cast hnat
  have hRR := riemann_ineq (k := k) (K := K) D
  omega
theorem exists_max_vanishingDivisor {ω : WeilDifferential k K} (hω : IsNonzero ω) :
    ∃! W : DivisorA k K, W ∈ vanishingDivisors ω ∧
      ∀ D ∈ vanishingDivisors ω, D ≤ W := by
  have hω' : ω.toFun ≠ 0 := hω
  set P : ℤ → Prop := fun z => ∃ D ∈ vanishingDivisors ω, deg k K D = z with hP
  have hInh : ∃ z, P z := by
    obtain ⟨D₀, hD₀⟩ := ω.vanishes_on
    exact ⟨deg k K D₀, D₀, hD₀, rfl⟩
  have hBdd : ∃ b : ℤ, ∀ z, P z → z ≤ b := by
    refine ⟨2 * (genus k K : ℤ) - 1, ?_⟩
    rintro z ⟨D, hD, rfl⟩
    exact deg_le_of_mem_vanishingDivisors hω' hD
  obtain ⟨ub, ⟨W, hWmem, hWdeg⟩, hubmax⟩ := Int.exists_greatest_of_bdd hBdd hInh
  have hmaxdiv : ∀ D ∈ vanishingDivisors ω, D ≤ W := by
    intro D hD
    have hsup : D ⊔ W ∈ vanishingDivisors ω := sup_mem_vanishingDivisors hD hWmem
    have hdegle : deg k K (D ⊔ W) ≤ ub := hubmax _ ⟨D ⊔ W, hsup, rfl⟩
    have hWle : W ≤ D ⊔ W := le_sup_right
    have hdegW : deg k K (D ⊔ W) ≤ deg k K W := by rw [hWdeg]; exact hdegle
    have heq : W = D ⊔ W := eq_of_le_of_deg_le k K hWle hdegW
    rw [heq]; exact le_sup_left
  refine ⟨W, ⟨hWmem, hmaxdiv⟩, ?_⟩
  rintro W' ⟨hW'mem, hW'max⟩
  exact le_antisymm (hmaxdiv W' hW'mem) (hW'max W hWmem)
noncomputable def divOmega (ω : WeilDifferential k K) (hω : IsNonzero ω) : DivisorA k K :=
  Classical.choose (exists_max_vanishingDivisor (k := k) (K := K) hω)
end WeilDifferential
def IsCanonical (W : DivisorA k K) : Prop :=
  ∃ (ω : WeilDifferential k K) (hω : WeilDifferential.IsNonzero ω),
    WeilDifferential.divOmega ω hω = W
end FunctionField.Chart
end
end
end

section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FunctionField
open Chart
variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]
structure WeilDifferential where
  toFun : AdeleSpace k K →ₗ[k] k
  vanishes_on : ∃ D : Divisor k K,
    ∀ a ∈ adeleFilt k K D + diagonalSubmodule k K, toFun a = 0
namespace WeilDifferential
variable {k K}
def IsNonzero (omega : WeilDifferential k K) : Prop := omega.toFun ≠ 0
def differentialSpace (D : Divisor k K) :
    Submodule k (AdeleSpace k K →ₗ[k] k) where
  carrier := {phi | ∀ a ∈ adeleFilt k K D + diagonalSubmodule k K, phi a = 0}
  zero_mem' := by simp
  add_mem' {phi psi} hphi hpsi := by
    intro a ha
    simp [hphi a ha, hpsi a ha]
  smul_mem' c phi hphi := by
    intro a ha
    simp [hphi a ha]
noncomputable def adeleDualEquivChart :
    (AdeleSpace k K →ₗ[k] k) ≃ₗ[k] (Chart.AdeleSpace k K →ₗ[k] k) :=
  (adeleEquivChart k K).symm.dualMap
omit [IsFullConstantField k K] in
@[simp]
theorem adeleDualEquivChart_apply (phi : AdeleSpace k K →ₗ[k] k)
    (a : Chart.AdeleSpace k K) :
    adeleDualEquivChart (k := k) (K := K) phi a =
      phi ((adeleEquivChart k K).symm a) :=
  rfl
omit [IsFullConstantField k K] in
@[simp]
theorem adeleDualEquivChart_symm_apply (phi : Chart.AdeleSpace k K →ₗ[k] k)
    (a : AdeleSpace k K) :
    (adeleDualEquivChart (k := k) (K := K)).symm phi a =
      phi (adeleEquivChart k K a) :=
  rfl
noncomputable def toChart (omega : WeilDifferential k K) :
    Chart.WeilDifferential k K where
  toFun := adeleDualEquivChart (k := k) (K := K) omega.toFun
  vanishes_on := by
    obtain ⟨D, hD⟩ := omega.vanishes_on
    refine ⟨(divisorEquivChart k K).symm D, fun a ha => ?_⟩
    apply hD ((adeleEquivChart k K).symm a)
    exact (mem_adeleFilt_add_diagonal_equivChart k K D _).mp (by simpa using ha)
noncomputable def ofChart (omega : Chart.WeilDifferential k K) :
    WeilDifferential k K where
  toFun := (adeleDualEquivChart (k := k) (K := K)).symm omega.toFun
  vanishes_on := by
    obtain ⟨D, hD⟩ := omega.vanishes_on
    refine ⟨divisorEquivChart k K D, fun a ha => ?_⟩
    apply hD (adeleEquivChart k K a)
    have hmap := (mem_adeleFilt_add_diagonal_equivChart k K
      (divisorEquivChart k K D) a).mpr ha
    simpa using hmap
omit [IsFullConstantField k K] in
@[ext]
theorem ext {omega eta : WeilDifferential k K} (h : omega.toFun = eta.toFun) :
    omega = eta := by
  cases omega
  cases eta
  cases h
  rfl
instance : Zero (WeilDifferential k K) := ⟨⟨0, ⟨0, by simp⟩⟩⟩
instance : Add (WeilDifferential k K) where
  add omega eta := ⟨omega.toFun + eta.toFun, by
    obtain ⟨Domega, homega⟩ := omega.vanishes_on
    obtain ⟨Deta, heta⟩ := eta.vanishes_on
    refine ⟨Domega ⊓ Deta, fun a ha => ?_⟩
    have hleft : adeleFilt k K (Domega ⊓ Deta) + diagonalSubmodule k K ≤
        adeleFilt k K Domega + diagonalSubmodule k K := by
      simpa only [Submodule.add_eq_sup] using
        sup_le_sup (adeleFilt_mono k K inf_le_left) le_rfl
    have hright : adeleFilt k K (Domega ⊓ Deta) + diagonalSubmodule k K ≤
        adeleFilt k K Deta + diagonalSubmodule k K := by
      simpa only [Submodule.add_eq_sup] using
        sup_le_sup (adeleFilt_mono k K inf_le_right) le_rfl
    simp [homega a (hleft ha), heta a (hright ha)]⟩
instance : Neg (WeilDifferential k K) where
  neg omega := ⟨-omega.toFun, by
    obtain ⟨D, hD⟩ := omega.vanishes_on
    exact ⟨D, fun a ha => by simp [hD a ha]⟩⟩
instance : AddCommGroup (WeilDifferential k K) where
  add_assoc _ _ _ := ext (add_assoc _ _ _)
  zero_add _ := ext (zero_add _)
  add_zero _ := ext (add_zero _)
  add_comm _ _ := ext (add_comm _ _)
  nsmul := nsmulRec
  nsmul_zero _ := ext rfl
  nsmul_succ _ _ := ext rfl
  neg := Neg.neg
  neg_add_cancel omega := ext (neg_add_cancel omega.toFun)
  sub := fun omega eta => omega + -eta
  sub_eq_add_neg _ _ := rfl
  zsmul := zsmulRec
noncomputable def weilDifferentialAddEquivChart :
    WeilDifferential k K ≃+ Chart.WeilDifferential k K where
  toFun := toChart
  invFun := ofChart
  left_inv omega := by
    apply ext
    exact (adeleDualEquivChart (k := k) (K := K)).symm_apply_apply omega.toFun
  right_inv omega := by
    apply Chart.WeilDifferential.ext
    exact (adeleDualEquivChart (k := k) (K := K)).apply_symm_apply omega.toFun
  map_add' omega eta := by
    apply Chart.WeilDifferential.ext
    exact (adeleDualEquivChart (k := k) (K := K)).map_add omega.toFun eta.toFun
noncomputable instance : SMul K (WeilDifferential k K) :=
  ⟨fun x omega =>
    (weilDifferentialAddEquivChart (k := k) (K := K)).symm
      (x • weilDifferentialAddEquivChart (k := k) (K := K) omega)⟩
omit [IsFullConstantField k K] in
@[simp]
theorem weilDifferentialAddEquivChart_smul (x : K) (omega : WeilDifferential k K) :
    weilDifferentialAddEquivChart (k := k) (K := K) (x • omega) =
      x • weilDifferentialAddEquivChart (k := k) (K := K) omega :=
  (weilDifferentialAddEquivChart (k := k) (K := K)).apply_symm_apply _
noncomputable instance : Module K (WeilDifferential k K) :=
  Function.Injective.module K
    (weilDifferentialAddEquivChart (k := k) (K := K)).toAddMonoidHom
    (weilDifferentialAddEquivChart (k := k) (K := K)).injective
    (weilDifferentialAddEquivChart_smul (k := k) (K := K))
noncomputable def weilDifferentialEquivChart :
    WeilDifferential k K ≃ₗ[K] Chart.WeilDifferential k K where
  __ := weilDifferentialAddEquivChart (k := k) (K := K)
  map_smul' := weilDifferentialAddEquivChart_smul (k := k) (K := K)
noncomputable def differentialSpaceEquivChart (D : Divisor k K) :
    differentialSpace (k := k) (K := K) D ≃ₗ[k]
      Chart.WeilDifferential.differentialSpace
        ((divisorEquivChart k K).symm D) where
  toFun phi := ⟨adeleDualEquivChart (k := k) (K := K) phi.1, by
    intro a ha
    apply phi.2 ((adeleEquivChart k K).symm a)
    exact (mem_adeleFilt_add_diagonal_equivChart k K D _).mp (by simpa using ha)⟩
  invFun phi := ⟨(adeleDualEquivChart (k := k) (K := K)).symm phi.1, by
    intro a ha
    apply phi.2 (adeleEquivChart k K a)
    exact (mem_adeleFilt_add_diagonal_equivChart k K D a).mpr ha⟩
  left_inv phi := Subtype.ext
    ((adeleDualEquivChart (k := k) (K := K)).symm_apply_apply phi.1)
  right_inv phi := Subtype.ext
    ((adeleDualEquivChart (k := k) (K := K)).apply_symm_apply phi.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
omit [IsFullConstantField k K] in
theorem isNonzero_toChart (omega : WeilDifferential k K) :
    IsNonzero omega ↔ Chart.WeilDifferential.IsNonzero (toChart omega) := by
  change omega.toFun ≠ 0 ↔
    adeleDualEquivChart (k := k) (K := K) omega.toFun ≠ 0
  exact (adeleDualEquivChart (k := k) (K := K)).map_ne_zero_iff.symm
noncomputable def divOmega (omega : WeilDifferential k K) (homega : IsNonzero omega) :
    Divisor k K :=
  divisorEquivChart k K <|
    Chart.WeilDifferential.divOmega (toChart omega) ((isNonzero_toChart omega).mp homega)
end WeilDifferential
def IsCanonical (W : Divisor k K) : Prop :=
  ∃ (omega : WeilDifferential k K) (homega : WeilDifferential.IsNonzero omega),
    WeilDifferential.divOmega omega homega = W
end FunctionField
end
end
end

section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FunctionField
open Chart
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
def memRRspace (D : Divisor k K) (f : K) : Prop :=
  ∀ v, v.valuation f ≤ WithZero.exp (D v)
namespace memRRspace
variable {k K} {D : Divisor k K}
theorem zero_mem (D : Divisor k K) : memRRspace k K D 0 := fun v => by simp
theorem add_mem {f g : K} (hf : memRRspace k K D f) (hg : memRRspace k K D g) :
    memRRspace k K D (f + g) := fun v =>
  (v.valuation.map_add f g).trans (max_le (hf v) (hg v))
theorem smul_mem (c : k) {f : K} (hf : memRRspace k K D f) :
    memRRspace k K D (c • f) := fun v => by
  by_cases hc : c = 0
  · simp [hc]
  rw [Algebra.smul_def, map_mul, Valuation.IsTrivialOn.eq_one c hc, one_mul]
  exact hf v
end memRRspace
def RRspace (D : Divisor k K) : Submodule k K :=
  { carrier := {f | memRRspace k K D f}
    zero_mem' := memRRspace.zero_mem D
    add_mem' := memRRspace.add_mem
    smul_mem' := memRRspace.smul_mem }
noncomputable def ell (D : Divisor k K) : ℕ :=
  Module.finrank k (RRspace k K D)
noncomputable def defect (D : Divisor k K) : ℤ :=
  D.deg + 1 - ell k K D
noncomputable def genus : ℕ :=
  (sSup {d : ℤ | ∃ D : Divisor k K, defect k K D = d}).toNat
variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]
noncomputable def indexOfSpecialty (D : Divisor k K) : ℕ :=
  (ell k K D - (D.deg + 1 - (genus k K : ℤ))).toNat
noncomputable def finrankAdeleQuotient (D : Divisor k K) : ℕ :=
  Module.finrank k <|
    AdeleSpace k K ⧸ (adeleFilt k K D + diagonalSubmodule k K)
noncomputable def adeleQuotientEquivChart (D : Divisor k K) :
    (AdeleSpace k K ⧸ (adeleFilt k K D + diagonalSubmodule k K)) ≃ₗ[k]
      (Chart.AdeleSpace k K ⧸
        (Chart.adeleFilt k K ((divisorEquivChart k K).symm D) +
          Chart.diagonalSubmodule k K)) :=
  Submodule.Quotient.equiv _ _ (adeleEquivChart k K)
    (map_adeleFilt_add_diagonal_equivChart k K D)
noncomputable def sandwichRank (D E : Divisor k K) (h : D ≤ E) : ℤ := by
  have hchart : (divisorEquivChart k K).symm D ≤
      (divisorEquivChart k K).symm E := by
    intro w
    have hw := h (chartToPlace k K w)
    simpa [divisorEquivChart, Finsupp.domCongr_apply] using hw
  exact Chart.sandwichRank k K ((divisorEquivChart k K).symm D)
    ((divisorEquivChart k K).symm E) hchart
section Canonical
variable {W : Divisor k K} (hW : IsCanonical k K W)
include hW
end Canonical
end FunctionField
end
end
end


