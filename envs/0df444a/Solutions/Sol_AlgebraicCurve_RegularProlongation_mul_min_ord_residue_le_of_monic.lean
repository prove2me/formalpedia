-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.mul_min_ord_residue_le_of_monic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/76cdbadb-f1ff-502c-a443-1bee850e7ee8

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic

set_option autoImplicit false

noncomputable section

open IsLocalRing Polynomial

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation Place Place.ord_zero"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord ord_zero ord_mul ord_inv ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring"
namespace W9ODivRed
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_neg_of_not_mem {f : F} (hf : f ∉ v.toValuationSubring) : v.ord f < 0 := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ v.toValuationSubring.zero_mem)
  by_contra h
  exact hf (mem_of_ord_nonneg v hf0 (not_lt.mp h))

end Place.W9ODivRed

namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "integers residue_algebraMap algebraMap_mem_iff residue"
namespace W9ODivRed
p2m_open "AlgebraicCurve.RegularProlongation"

section Generic

variable {S E : Type*} [CommSemiring S] [Field E]

theorem eval₂_mem (T : Subring E) (ρ : S →+* E) (hρ : ∀ a, ρ a ∈ T) {y : E} (hy : y ∈ T)
    (q : S[X]) : q.eval₂ ρ y ∈ T := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [eval₂_add]; exact T.add_mem hp hq
  | monomial n a =>
    rw [eval₂_monomial]
    exact T.mul_mem (hρ a) (T.pow_mem hy n)

theorem mul_mem_of_monic (O : ValuationSubring E) (P : E[X]) (hP : P.Monic) (s x : E)
    (hcoeff : ∀ i, P.coeff i * s ^ (P.natDegree - i) ∈ O) (hx : P.eval x = 0) :
    s * x ∈ O := by
  set Q : E[X] := P.scaleRoots s with hQ
  have hQmonic : Q.Monic := (monic_scaleRoots_iff s).mpr hP
  have hQroot : Q.eval (s * x) = 0 := by
    have h := scaleRoots_eval₂_eq_zero (RingHom.id E) (r := x) (s := s) (p := P) hx
    simpa using h
  have hsub : (↑Q.coeffs : Set E) ⊆ O.toSubring := by
    intro c hc
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp (Finset.mem_coe.mp hc)
    rw [hQ, coeff_scaleRoots]
    exact hcoeff n
  set Q' : (O.toSubring)[X] := Q.toSubring O.toSubring hsub with hQ'
  have hQ'monic : Q'.Monic := (monic_toSubring Q O.toSubring hsub).mpr hQmonic
  have hint : IsIntegral O (s * x) := by
    refine ⟨Q', hQ'monic, ?_⟩
    have hmap : Q'.map (algebraMap O E) = Q := map_toSubring Q O.toSubring hsub
    rw [← hmap, eval_map] at hQroot
    exact hQroot
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := E)).mp hint
  rw [← hy]
  exact y.2

end Generic

section Residue

variable {k Fbar : Type*} [Field k] [Field Fbar] [Algebra k Fbar]
variable {S : Type*} [CommRing S] (ρ : S →+* Fbar) (hρ : ∀ w : Place k Fbar, ∀ a, ρ a ∈ w.toValuationSubring)

include hρ in

theorem mul_min_ord_le_ord (y x : Fbar) (m : ℕ) (p : Polynomial (Polynomial S)) (hp : p.Monic)
    (hdeg : ∀ j, (p.coeff j).natDegree ≤ (p.natDegree - j) * m)
    (hroot : p.eval₂ (eval₂RingHom ρ y) x = 0) (w : Place k Fbar) :
    (m : ℤ) * min 0 (w.ord y) ≤ w.ord x := by
  set θ : Polynomial S →+* Fbar := eval₂RingHom ρ y with hθ
  set P : Fbar[X] := p.map θ with hP
  have hPmonic : P.Monic := hp.map θ
  have hPdeg : P.natDegree = p.natDegree := hp.natDegree_map θ
  have hProot : P.eval x = 0 := by rw [hP, eval_map]; exact hroot
  have hPcoeff : ∀ i, P.coeff i = (p.coeff i).eval₂ ρ y := fun i => by
    rw [hP, coeff_map, hθ]; rfl
  set O := w.toValuationSubring with hO
  by_cases hy : y ∈ O
  ·
    have hmin : min 0 (w.ord y) = 0 := min_eq_left (Place.W9ODivRed.ord_nonneg_of_mem w hy)
    rw [hmin, mul_zero]
    have hxO : (1 : Fbar) * x ∈ O := by
      refine mul_mem_of_monic O P hPmonic 1 x (fun i => ?_) hProot
      rw [one_pow, mul_one, hPcoeff]
      exact eval₂_mem O.toSubring ρ (hρ w) hy _
    rw [one_mul] at hxO
    exact Place.W9ODivRed.ord_nonneg_of_mem w hxO
  ·
    have hy0 : y ≠ 0 := fun h => hy (h ▸ O.zero_mem)
    have hordy : w.ord y < 0 := Place.W9ODivRed.ord_neg_of_not_mem w hy
    have hmin : min 0 (w.ord y) = w.ord y := min_eq_right hordy.le
    rw [hmin]
    set g : Fbar := y⁻¹ with hg
    have hgO : g ∈ O := (O.mem_or_inv_mem y).resolve_left hy
    letI : Invertible y := invertibleOfNonzero hy0
    have hinvOf : (⅟y : Fbar) = g := by rw [hg, invOf_eq_inv]

    have hcoeff : ∀ i, P.coeff i * (g ^ m) ^ (P.natDegree - i) ∈ O := by
      intro i
      rw [hPcoeff, hPdeg, ← pow_mul]
      set N := m * (p.natDegree - i) with hN
      have hqN : (p.coeff i).natDegree ≤ N := by
        rw [hN, mul_comm]; exact hdeg i

      have hrefl := eval₂_reflect_mul_pow ρ y N (p.coeff i) hqN
      rw [hinvOf] at hrefl
      have hyN : (y ^ N : Fbar) ≠ 0 := pow_ne_zero _ hy0
      have hkey : (p.coeff i).eval₂ ρ y * g ^ N = (reflect N (p.coeff i)).eval₂ ρ g := by
        rw [← hrefl, mul_assoc, ← mul_pow, hg, mul_inv_cancel₀ hy0, one_pow, mul_one]
      rw [hkey]
      exact eval₂_mem O.toSubring ρ (hρ w) hgO _
    have hxO : g ^ m * x ∈ O := mul_mem_of_monic O P hPmonic (g ^ m) x hcoeff hProot

    rcases eq_or_ne x 0 with rfl | hx0
    · simp only [Place.ord_zero]
      have : (m : ℤ) * w.ord y ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg m) hordy.le
      exact this
    · have h0 := Place.W9ODivRed.ord_nonneg_of_mem w hxO
      have hg0 : g ≠ 0 := inv_ne_zero hy0
      rw [w.ord_mul (pow_ne_zero _ hg0) hx0, ← zpow_natCast, w.ord_zpow, hg, w.ord_inv] at h0
      linarith

end Residue

section Reduction

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def constHom (R : RegularProlongation A F Fbar) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constHom (R : RegularProlongation A F Fbar) (a : A) :
    ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_constHom (R : RegularProlongation A F Fbar) (a : A) :
    R.residue (constHom R a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

theorem subtype_comp_constHom (R : RegularProlongation A F Fbar) :
    R.integers.subtype.comp (constHom R) = (algebraMap L F).comp A.subtype := by
  ext a; rfl

def resConst (A : ValuationSubring L) (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar] :
    A →+* Fbar :=
  (algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A)

theorem residue_comp_constHom (R : RegularProlongation A F Fbar) :
    R.residue.comp (constHom R) = resConst A Fbar := by
  ext a; exact residue_constHom R a

theorem resConst_mem (w : Place (ResidueField A) Fbar) (a : A) :
    resConst A Fbar a ∈ w.toValuationSubring :=
  w.algebraMap_mem' _

theorem eval₂_residue_eq_zero (R : RegularProlongation A F Fbar) (f h : R.integers)
    (p : Polynomial (Polynomial A))
    (hroot : p.eval₂ (eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F)) (h : F) = 0) :
    p.eval₂ (eval₂RingHom (resConst A Fbar) (R.residue f)) (R.residue h) = 0 := by

  set ψ : Polynomial A →+* R.integers := eval₂RingHom (constHom R) f with hψ
  have hcoeψ : R.integers.subtype.comp ψ =
      eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [hψ]
    · simp [hψ]
  have hO : p.eval₂ ψ h = 0 := by
    apply R.integers.subtype_injective

    have := Polynomial.hom_eval₂ p ψ R.integers.subtype h
    rw [map_zero, this, hcoeψ]
    exact hroot

  have hres := congrArg R.residue hO
  rw [map_zero, Polynomial.hom_eval₂] at hres
  have hcomp : R.residue.comp ψ = eval₂RingHom (resConst A Fbar) (R.residue f) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [hψ, residue_constHom, resConst]
    · simp [hψ]
  rw [hcomp] at hres
  exact hres

theorem mul_min_ord_residue_le (R : RegularProlongation A F Fbar) (f h : R.integers) (m : ℕ)
    (p : Polynomial (Polynomial A)) (hp : p.Monic)
    (hdeg : ∀ j, (p.coeff j).natDegree ≤ (p.natDegree - j) * m)
    (hroot : p.eval₂ (eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F)) (h : F) = 0)
    (w : Place (ResidueField A) Fbar) :
    (m : ℤ) * min 0 (w.ord (R.residue f)) ≤ w.ord (R.residue h) :=
  mul_min_ord_le_ord (resConst A Fbar) (resConst_mem) (R.residue f) (R.residue h) m p hp hdeg
    (eval₂_residue_eq_zero R f h p hroot) w

end Reduction

end RegularProlongation.W9ODivRed
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic.AlgebraicCurve.RegularProlongation.W9ODivRed"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic.AlgebraicCurve.RegularProlongation"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic.AlgebraicCurve.RegularProlongation.W9ODivRed P2MW.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic.AlgebraicCurve.RegularProlongation.W9ODivRed P2MW.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic.AlgebraicCurve"

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic.AlgebraicCurve in
theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (f h : R.integers) (m : ℕ)
    (p : Polynomial (Polynomial A)) (hp : p.Monic)
    (hdeg : ∀ j, (p.coeff j).natDegree ≤ (p.natDegree - j) * m)
    (hroot : p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F))
      (h : F) = 0)
    (w : Place (IsLocalRing.ResidueField A) Fbar) :
    (m : ℤ) * min 0 (w.ord (R.residue f)) ≤ w.ord (R.residue h) :=
  RegularProlongation.W9ODivRed.mul_min_ord_residue_le R f h m p hp hdeg hroot w

end S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic (solution)
