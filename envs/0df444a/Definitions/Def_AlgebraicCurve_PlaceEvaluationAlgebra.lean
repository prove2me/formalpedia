-- Prove2me | Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
-- name    : AlgebraicCurve_PlaceEvaluationAlgebra
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/4bcada18-2902-598a-96cc-8210d0a555b4
-- title:
--   Algebra of evaluation at places and at divisors
-- statement:
--   Throughout, $F$ is a field equipped with a $K$-algebra structure over a field $K$, and $v$ is a `Place K F`: a valuation subring $\mathcal{O}_v \subseteq F$ containing the image of $K$, distinct from $F$ and a principal ideal ring, hence a discrete valuation ring, with $\operatorname{ord}_v$ the associated normalised integer valuation, residue field $\mathcal{O}_v/\mathfrak{m}_v$, degree $\deg v = \dim_K \mathcal{O}_v/\mathfrak m_v$, and $v$ called rational (`Place.IsRational`) when $K \to \mathcal{O}_v/\mathfrak m_v$ is surjective. The evaluation $\mathrm{evalAt}_v(f)$ is the preimage in $K$, via a chosen left inverse of $K \to \mathcal{O}_v/\mathfrak m_v$, of the residue class of $f$ when $f \in \mathcal{O}_v$, and $0$ otherwise; for a divisor $D \in \mathrm{Place}(K,F) \to_{\mathrm{f}} \mathbb{Z}$, $\mathrm{evalFun}(f,D) = \prod_{v \in \operatorname{supp} D} \mathrm{evalAt}_v(f)^{D(v)}$.
--
--   The module collects the arithmetic of these operations. For $f \neq 0$: $\operatorname{ord}_v f \ge 0$ gives $f \in \mathcal{O}_v$; $\operatorname{ord}_v f = 0$ gives that the resulting element of $\mathcal{O}_v$ is a unit, that its residue is nonzero, and (for rational $v$) that $\mathrm{evalAt}_v(f) \neq 0$. For rational $v$, evaluation is multiplicative on $\mathcal{O}_v$, and, in auxiliary form, $\mathrm{evalAt}_v(f^{-1}) = \mathrm{evalAt}_v(f)^{-1}$ and $\mathrm{evalAt}_v(f^n) = \mathrm{evalAt}_v(f)^n$ for $n \in \mathbb{Z}$ when $\operatorname{ord}_v f = 0$. Constants evaluate to themselves, $\mathrm{evalAt}_v(\iota a) = a$, and a rational place has $\deg v = 1$. On the divisor side: $\mathrm{evalFun}(f,D) \neq 0$ if $f$ evaluates nonzero at every place of $\operatorname{supp} D$; $\mathrm{evalFun}(f,D+E) = \mathrm{evalFun}(f,D)\,\mathrm{evalFun}(f,E)$ under nonvanishing on both supports; $\mathrm{evalFun}(fg,D) = \mathrm{evalFun}(f,D)\,\mathrm{evalFun}(g,D)$ when the places of $\operatorname{supp} D$ are rational and $f,g$ lie in their valuation rings; $\operatorname{supp}(nD) \subseteq \operatorname{supp} D$; $\mathrm{evalFun}(f,nD) = \mathrm{evalFun}(f,D)^n$ for $n \in \mathbb{N}$ and for $n \in \mathbb{Z}$; and $\mathrm{evalFun}(f^n,D) = \mathrm{evalFun}(f,D)^n$ when $f \neq 0$ and all places of $\operatorname{supp} D$ are rational with $\operatorname{ord}_v f = 0$.
--
--   **Relation to Mathlib.** The notions of place, divisor and evaluation used here are the project's own; Mathlib supplies the underlying machinery (valuation subrings, discrete valuation rings, height-one spectra, local rings and their residue fields, finitely supported functions).
--
--   **Where it is used.** These evaluation rules are the computational basis for the divisorial Weil pairing on a curve: they feed the Weil reciprocity statement $\mathrm{evalFun}(f, D_g) = \mathrm{evalFun}(g, D_f)$ formulated alongside them, and hence the study of torsion in the degree-zero divisor class group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_PlaceEvaluationAlgebra.lean

import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

theorem mem_toValuationSubring_of_ord_nonneg_alt {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem isUnit_mk_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    IsUnit (⟨f, v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  have huf : (⟨f, v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge⟩ : v.toValuationSubring)
      = (u : v.toValuationSubring) := Subtype.ext hu
  rw [huf]
  exact u.isUnit

theorem residue_ne_zero_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    residue v.toValuationSubring (⟨f, v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge⟩ : v.toValuationSubring)
      ≠ 0 :=
  (residue_ne_zero_iff_isUnit _).mpr (v.isUnit_mk_of_ord_eq_zero hf h)

theorem evalAt_ne_zero_of_ord_eq_zero (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt f ≠ 0 := by
  intro h0
  have hres := v.algebraMap_evalAt hv (v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge)
  rw [h0, map_zero] at hres
  exact v.residue_ne_zero_of_ord_eq_zero hf h hres.symm

theorem evalAt_mul_of_mem (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv (mul_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

private theorem evalAt_inv (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hfi : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hi : v.ord f⁻¹ = 0 := by rw [v.ord_inv, h, neg_zero]
  have hmul := v.evalAt_mul_of_mem hv (v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge) (v.mem_toValuationSubring_of_ord_nonneg_alt hfi hi.ge)
  rw [mul_inv_cancel₀ hf, v.evalAt_one] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

private theorem evalAt_zpow (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) (n : ℤ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  have hpow : ∀ m : ℕ, v.evalAt (f ^ m) = v.evalAt f ^ m := by
    intro m
    induction m with
    | zero => simp [v.evalAt_one]
    | succ m ih =>
      have hm : v.ord (f ^ (m : ℤ)) = 0 := by rw [v.ord_zpow, h, mul_zero]
      rw [pow_succ, v.evalAt_mul_of_mem hv ?_ (v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge), ih, pow_succ]
      have : (f ^ m : F) = f ^ (m : ℤ) := by rw [zpow_natCast]
      rw [this]
      exact v.mem_toValuationSubring_of_ord_nonneg_alt (zpow_ne_zero _ hf) hm.ge
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]
    exact hpow m
  · rw [zpow_negSucc, zpow_negSucc, ← hpow (m + 1)]
    refine v.evalAt_inv hv (pow_ne_zero _ hf) ?_
    have : (f ^ (m + 1) : F) = f ^ ((m + 1 : ℕ) : ℤ) := by rw [zpow_natCast]
    rw [this, v.ord_zpow, h, mul_zero]

theorem evalAt_algebraMap_eq (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have ha : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [ha, ← ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
    v.residueInv_algebraMap]

theorem deg_eq_one_of_isRational {v : Place K F} (hv : v.IsRational) : v.deg = 1 := by
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    ⟨v.algebraMap_residueField_injective, hv⟩
  show Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm

end Place

namespace Divisor

theorem evalFun_ne_zero_of_forall_ne_zero {f : F} {D : Divisor K F}
    (h : ∀ v ∈ D.support, Place.evalAt v f ≠ 0) :
    evalFun f D ≠ 0 := by
  rw [evalFun_def]
  exact Finset.prod_ne_zero_iff.mpr fun v hv => zpow_ne_zero _ (h v hv)

theorem evalFun_add_of_forall_ne_zero (f : F) {D E : Divisor K F}
    (hD : ∀ v ∈ D.support, Place.evalAt v f ≠ 0)
    (hE : ∀ v ∈ E.support, Place.evalAt v f ≠ 0) :
    evalFun f (D + E) = evalFun f D * evalFun f E := by
  classical
  refine Finsupp.prod_add_index (fun v _ => zpow_zero _) (fun v hv b₁ b₂ => ?_)
  refine zpow_add₀ ?_ b₁ b₂
  rcases Finset.mem_union.mp hv with h | h
  · exact hD v h
  · exact hE v h

theorem evalFun_mul_of_forall_mem {f g : F} {D : Divisor K F}
    (hrat : ∀ v ∈ D.support, Place.IsRational v)
    (hf : ∀ v ∈ D.support, f ∈ v.toValuationSubring)
    (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring) :
    evalFun (f * g) D = evalFun f D * evalFun g D := by
  rw [show evalFun (f * g) D = D.prod fun v n => v.evalAt f ^ n * v.evalAt g ^ n from
    Finsupp.prod_congr fun v hv => by
      rw [Place.evalAt_mul_of_mem v (hrat v hv) (hf v hv) (hg v hv), mul_zpow]]
  exact Finsupp.prod_mul

theorem support_smul_subset (n : ℤ) (D : Divisor K F) :
    (n • D).support ⊆ D.support := Finsupp.support_smul

theorem evalFun_natCast_smul_divisor (f : F) (D : Divisor K F) (n : ℕ) :
    evalFun f ((n : ℤ) • D) = evalFun f D ^ n := by
  rw [show evalFun f ((n : ℤ) • D)
        = ∏ v ∈ D.support, v.evalAt f ^ (((n : ℤ) • D) v) from
      Finsupp.prod_of_support_subset _ (support_smul_subset (n : ℤ) D) _
        fun v _ => zpow_zero _,
    evalFun_def, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm ((n : ℤ)) (D v), zpow_mul, zpow_natCast]

theorem evalFun_zsmul_divisor (f : F) (D : Divisor K F) (n : ℤ) :
    evalFun f (n • D) = evalFun f D ^ n := by
  rw [show evalFun f (n • D) = ∏ v ∈ D.support, v.evalAt f ^ ((n • D) v) from
      Finsupp.prod_of_support_subset _ Finsupp.support_smul _ fun v _ => zpow_zero _,
    evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm n (D v), zpow_mul]

theorem evalFun_zpow_left_of_ord_eq_zero {f : F} (hf : f ≠ 0) {D : Divisor K F} (n : ℤ)
    (hrat : ∀ v ∈ D.support, Place.IsRational v)
    (hord : ∀ v ∈ D.support, Place.ord v f = 0) :
    evalFun (f ^ n) D = evalFun f D ^ n := by
  rw [evalFun_def, evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Place.evalAt_zpow v (hrat v hv) hf (hord v hv) n, ← zpow_mul, ← zpow_mul, mul_comm]

end Divisor

end AlgebraicCurve


