-- Prove2me | Definitions.Def_ModularCurve_KwNo6HspecCartierDlogCampaignFrame
-- name    : ModularCurve_KwNo6HspecCartierDlogCampaignFrame
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/43cbe4a9-807e-53b1-92e1-19d2473d7772
-- title:
--   Logarithmic differentials and the submodule of regular differentials
-- statement:
--   The setting is a field extension $F/K$ of fields, thought of as the function field of a curve over $K$, with $\Omega[F\!\mid\!K]$ Mathlib's module of Kähler differentials and with places given by the project structure `Place K F`: a valuation subring $\mathcal{O}_v \subseteq F$ containing the image of $K$, not equal to $F$, and a principal ideal ring (hence a discrete valuation ring), together with the associated normalised integer valuation $\operatorname{ord}_v$ obtained from the adic valuation of its maximal ideal.
--
--   Three facts about $\operatorname{ord}_v$ are recorded: $z \in \mathcal{O}_v$ as soon as $0 \le \operatorname{ord}_v z$, conversely $0 \le \operatorname{ord}_v z$ for $z \in \mathcal{O}_v$, and $\operatorname{ord}_v(\iota(a)) = 0$ for every nonzero $a \in K$, where $\iota$ is the structure map $K \to F$.
--
--   The logarithmic differential is defined by `kw_hwcd_dlog K f` $= f^{-1} \cdot \mathrm{d}f \in \Omega[F\!\mid\!K]$, with $\mathrm{d}$ the universal derivation. It vanishes at $f = 0$ and $f = 1$, satisfies $\operatorname{dlog}(fg) = \operatorname{dlog} f + \operatorname{dlog} g$ and $\operatorname{dlog}(f^n) = n \cdot \operatorname{dlog} f$ for nonzero arguments, and consequently $\operatorname{dlog}(f^{\ell}) = 0$ when $F$ has characteristic $\ell$.
--
--   Under the standing assumptions that $\Omega[F\!\mid\!K]$ is nontrivial and that for every place $v$ the differential $\mathrm{d}\pi_v$ of a chosen uniformiser spans $\Omega[F\!\mid\!K]$ over $F$, each $\omega$ has a well-defined coefficient $c_v(\omega) \in F$ with $\omega = c_v(\omega)\,\mathrm{d}\pi_v$, and $\operatorname{ord}_v^{\mathrm{diff}}(\omega) = \operatorname{ord}_v(c_v(\omega))$. The coefficient is additive in $\omega$, and `kw_hwcd_regularDifferentials K F` is the $K$-submodule of those $\omega$ with $0 \le \operatorname{ord}_v^{\mathrm{diff}}(\omega)$ for all places $v$; membership is by definition this condition. A trivial auxiliary proposition records the ambient axiom use.
--
--   **Relation to Mathlib.** The module of Kähler differentials $\Omega[F\!\mid\!K]$ and its universal derivation `KaehlerDifferential.D` are Mathlib's; `Place`, the order function $\operatorname{ord}_v$, the coefficient with respect to $\mathrm{d}\pi_v$ and its order are the project's own notions. The logarithmic differential $f^{-1}\,\mathrm{d}f$ valued in Kähler differentials, and the submodule cut out by nonnegativity of all differential orders, have no Mathlib counterpart here.
--
--   **Where it is used.** The submodule of regular differentials is the formal stand-in for $H^0(X,\Omega^1)$ of the curve with function field $F/K$, and the dlog calculus together with the characteristic-$\ell$ vanishing $\operatorname{dlog}(f^\ell)=0$ is what the later treatment of the Cartier operator on modular curves in characteristic $\ell$ uses; it serves as the single reference point for the statements about Cartier stability and regularity of logarithmic differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_KwNo6HspecCartierDlogCampaignFrame.lean

import Mathlib
import Definitions.Def_ModularCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open KaehlerDifferential

noncomputable section

namespace AlgebraicCurve

theorem kw_hwcd_axiomAnchor : True :=
  have _h₁ : True = True := propext Iff.rfl
  have _h₂ : ℕ := Classical.choice ⟨0⟩
  have _h₃ : Quot.mk (fun (_ _ : ℕ) => True) 0 = Quot.mk (fun (_ _ : ℕ) => True) 1 :=
    Quot.sound trivial
  trivial

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

theorem kw_hwcd_mem_of_ord_nonneg {z : F} (h : 0 ≤ v.ord z) :
    z ∈ v.toValuationSubring := by
  have _ := kw_hwcd_axiomAnchor
  rcases eq_or_ne z 0 with rfl | hz
  · exact zero_mem _
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hz hπ
    have hn : v.ord z = (((v.ord z).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg h).symm
    rw [hu, hn, zpow_natCast]
    exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 _)

theorem kw_hwcd_ord_nonneg_of_mem {z : F} (hz : z ∈ v.toValuationSubring) :
    0 ≤ v.ord z := by
  have _ := kw_hwcd_axiomAnchor
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [v.ord_zero]
  by_contra hneg
  rw [Int.not_le] at hneg
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hz0 hπ
  have hπF : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero

  set m : ℕ := (-(v.ord z)).toNat with hm
  have hm_pos : 0 < m := by omega
  have hmz : (m : ℤ) = -(v.ord z) := Int.toNat_of_nonneg (by omega)
  have hkey : ((π : F) ^ m) * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) * z
      = 1 := by
    rw [hu]
    have huu : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)
        * (((u : v.toValuationSubring)) : F) = 1 := by
      norm_cast
      simp
    calc ((π : F) ^ m) * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)
          * (((u : v.toValuationSubring) : F) * ((π : F) ^ (v.ord z)))
        = ((((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F)
            * ((u : v.toValuationSubring) : F)) * (((π : F) ^ m) * ((π : F) ^ (v.ord z))) := by
          ring
      _ = ((π : F) ^ (m : ℤ)) * ((π : F) ^ (v.ord z)) := by
          rw [huu, one_mul, zpow_natCast]
      _ = (π : F) ^ ((m : ℤ) + v.ord z) := (zpow_add₀ hπF _ _).symm
      _ = 1 := by rw [hmz]; simp

  have hmem : ((π : v.toValuationSubring) ^ m)
      * ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) * ⟨z, hz⟩ = 1 := by
    apply Subtype.ext
    push_cast
    exact hkey
  have hunit : IsUnit ((π : v.toValuationSubring) ^ m) :=
    IsUnit.of_mul_eq_one _ (by rw [mul_assoc] at hmem; exact hmem)
  exact hπ.not_isUnit ((isUnit_pow_iff hm_pos.ne').mp hunit)

theorem kw_hwcd_ord_algebraMap {a : K} (ha : a ≠ 0) :
    v.ord (algebraMap K F a) = 0 := by
  have _ := kw_hwcd_axiomAnchor
  have hmem : algebraMap K F a ∈ v.toValuationSubring := v.algebraMap_mem' a
  have hmem' : algebraMap K F a⁻¹ ∈ v.toValuationSubring := v.algebraMap_mem' a⁻¹
  have hprod : (⟨_, hmem⟩ * ⟨_, hmem'⟩ : v.toValuationSubring) = 1 := by
    apply Subtype.ext
    show (algebraMap K F a) * (algebraMap K F a⁻¹) = 1
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have hunit : IsUnit (⟨algebraMap K F a, hmem⟩ : v.toValuationSubring) :=
    IsUnit.of_mul_eq_one _ hprod
  simpa using v.ord_coe_unit hunit.unit

end Place

def kw_hwcd_dlog (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (f : F) :
    Ω[F⁄K] :=
  f⁻¹ • KaehlerDifferential.D K F f

@[simp]
theorem kw_hwcd_dlog_zero : kw_hwcd_dlog K (0 : F) = 0 := by
  rw [kw_hwcd_dlog, map_zero, smul_zero]

@[simp]
theorem kw_hwcd_dlog_one : kw_hwcd_dlog K (1 : F) = 0 := by
  rw [kw_hwcd_dlog, Derivation.map_one_eq_zero, smul_zero]

theorem kw_hwcd_dlog_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    kw_hwcd_dlog K (f * g) = kw_hwcd_dlog K f + kw_hwcd_dlog K g := by
  have _ := kw_hwcd_axiomAnchor
  rw [kw_hwcd_dlog, kw_hwcd_dlog, kw_hwcd_dlog, Derivation.leibniz, smul_add,
    smul_smul, smul_smul, mul_inv]
  rw [show f⁻¹ * g⁻¹ * f = g⁻¹ by field_simp,
    show f⁻¹ * g⁻¹ * g = f⁻¹ by field_simp, add_comm]

theorem kw_hwcd_dlog_pow (n : ℕ) {f : F} (hf : f ≠ 0) :
    kw_hwcd_dlog K (f ^ n) = n • kw_hwcd_dlog K f := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, kw_hwcd_dlog_mul (pow_ne_zero k hf) hf, ih, succ_nsmul]

theorem kw_hwcd_dlog_pow_char (ℓ : ℕ) [CharP F ℓ] {f : F} (hf : f ≠ 0) :
    kw_hwcd_dlog K (f ^ ℓ) = 0 := by
  have _ := kw_hwcd_axiomAnchor
  rw [kw_hwcd_dlog_pow ℓ hf, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F ℓ, zero_smul]

section Regular

variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem kw_hwcd_differentialCoeff_add (v : Place K F) (ω ω' : Ω[F⁄K]) :
    v.differentialCoeff (ω + ω')
      = v.differentialCoeff ω + v.differentialCoeff ω' :=
  v.differentialCoeff_unique
    (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

def kw_hwcd_regularDifferentials (K F : Type*) [Field K] [Field F] [Algebra K F]
    [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]] : Submodule K Ω[F⁄K] where
  carrier := {ω | ∀ v : Place K F, 0 ≤ v.ordDifferential ω}
  zero_mem' := by
    intro v
    rw [Place.ordDifferential, v.differentialCoeff_zero, v.ord_zero]
  add_mem' := by
    intro ω ω' hω hω' v
    rw [Place.ordDifferential, kw_hwcd_differentialCoeff_add]
    have h₁ : v.differentialCoeff ω ∈ v.toValuationSubring :=
      Place.kw_hwcd_mem_of_ord_nonneg v (hω v)
    have h₂ : v.differentialCoeff ω' ∈ v.toValuationSubring :=
      Place.kw_hwcd_mem_of_ord_nonneg v (hω' v)
    exact v.kw_hwcd_ord_nonneg_of_mem (add_mem h₁ h₂)
  smul_mem' := by
    intro a ω hω v
    rcases eq_or_ne a 0 with rfl | ha
    · rw [zero_smul, Place.ordDifferential, v.differentialCoeff_zero, v.ord_zero]
    have hsmul : a • ω = (algebraMap K F a) • ω := (algebraMap_smul F a ω).symm
    rw [Place.ordDifferential, hsmul, v.differentialCoeff_smul]
    rcases eq_or_ne (v.differentialCoeff ω) 0 with hc | hc
    · rw [hc, mul_zero, v.ord_zero]
    have hmap : algebraMap K F a ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K F).injective).mpr ha
    rw [v.ord_mul hmap hc, v.kw_hwcd_ord_algebraMap ha, zero_add]
    exact hω v

@[simp]
theorem kw_hwcd_mem_regularDifferentials_iff {ω : Ω[F⁄K]} :
    ω ∈ kw_hwcd_regularDifferentials K F
      ↔ ∀ v : Place K F, 0 ≤ v.ordDifferential ω :=
  Iff.rfl

end Regular

end AlgebraicCurve

end

section Audits

/-- info: 'AlgebraicCurve.kw_hwcd_axiomAnchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.kw_hwcd_axiomAnchor

/-- info: 'AlgebraicCurve.Place.kw_hwcd_mem_of_ord_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.Place.kw_hwcd_mem_of_ord_nonneg

/-- info: 'AlgebraicCurve.Place.kw_hwcd_ord_nonneg_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.Place.kw_hwcd_ord_nonneg_of_mem

/-- info: 'AlgebraicCurve.Place.kw_hwcd_ord_algebraMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.Place.kw_hwcd_ord_algebraMap

/-- info: 'AlgebraicCurve.kw_hwcd_dlog_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.kw_hwcd_dlog_zero

/-- info: 'AlgebraicCurve.kw_hwcd_dlog_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.kw_hwcd_dlog_one

/-- info: 'AlgebraicCurve.kw_hwcd_dlog_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.kw_hwcd_dlog_mul

/-- info: 'AlgebraicCurve.kw_hwcd_dlog_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.kw_hwcd_dlog_pow

/-- info: 'AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff

/-- info: 'AlgebraicCurve.kw_hwcd_dlog_pow_char' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.kw_hwcd_dlog_pow_char

/-- info: 'AlgebraicCurve.kw_hwcd_regularDifferentials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.kw_hwcd_regularDifferentials

/-- info: 'AlgebraicCurve.kw_hwcd_differentialCoeff_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.kw_hwcd_differentialCoeff_add

end Audits


