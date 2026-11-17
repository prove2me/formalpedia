-- Prove2me | Definitions.Def_N25_CanonicalOpenAlgebraOverRing
-- name    : N25_CanonicalOpenAlgebraOverRing
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:10:54.438823+00:00
-- url     : https://prove2.me/theorems/b7a331e0-f1b5-4a65-bec7-1ff0176c60bb
-- title:
--   Birational equivalence of the canonical and modular-unit opens
-- statement:
--   Over an arbitrary commutative coefficient ring, records the plane relation in its coordinate algebra, defines the normalized forward map to the modular-unit plane open and the explicit inverse map to the canonical open, and packages them as an algebra equivalence. This is the integral birational dictionary that remains available after specialization to the good characteristics.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans
/-! Integral birational equivalence of the literal principal canonical open with the unit-plane open over a coefficient ring. -/

noncomputable section

namespace N25

section Chart

variable (k : Type*) [CommRing k]

open MvPolynomial

theorem canonicalAChart_quadric_overRing :
    canonicalQuadric (canonicalAChartCoordinate25 k 0) (canonicalAChartCoordinate25 k 1)
      (canonicalAChartCoordinate25 k 2) (canonicalAChartCoordinate25 k 3) = 0 := by
  have h : Ideal.Quotient.mk (canonicalAChartIdeal25 k)
      (canonicalQuadric (X 0) (X 1) (X 2) (X 3)) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  simpa only [canonicalQuadric,map_add,map_sub,map_mul,map_pow,map_neg,
    canonicalAChartCoordinate25] using h

theorem canonicalAChart_cubic_overRing :
    canonicalCubic (canonicalAChartCoordinate25 k 0) (canonicalAChartCoordinate25 k 1)
      (canonicalAChartCoordinate25 k 2) (canonicalAChartCoordinate25 k 3) = 0 := by
  have h : Ideal.Quotient.mk (canonicalAChartIdeal25 k)
      (canonicalCubic (X 0) (X 1) (X 2) (X 3)) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  simpa only [canonicalCubic,map_add,map_sub,map_mul,map_pow,map_neg,
    canonicalAChartCoordinate25] using h

theorem canonicalAChart_denominator_overRing :
    canonicalDenominator (canonicalAChartCoordinate25 k 1)
      (canonicalAChartCoordinate25 k 2) (canonicalAChartCoordinate25 k 3) = 1 := by
  have h : Ideal.Quotient.mk (canonicalAChartIdeal25 k)
      (canonicalDenominator (X 1) (X 2) (X 3)-1) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  simpa only [canonicalDenominator,map_add,map_sub,map_one,
    canonicalAChartCoordinate25,sub_eq_zero] using h

end Chart

variable (K : Type*) [CommRing K]

/-- The plane equation vanishes in its literal coordinate ring. -/
theorem unitPlane_relation_overRing : planeRelation (unitPlaneU25C K) (unitPlaneV25C K) = 0 := by
  have h := AdjoinRoot.mk_self (f := (unitPlanePolynomial25C K))
  change AdjoinRoot.mk (unitPlanePolynomial25C K)
    (planeRelation (Polynomial.C Polynomial.X) Polynomial.X) = 0 at h
  have he : AdjoinRoot.mk (unitPlanePolynomial25C K)
      (planeRelation (Polynomial.C Polynomial.X) Polynomial.X) =
      planeRelation (unitPlaneU25C K) (unitPlaneV25C K) := by
    change (AdjoinRoot.mk (unitPlanePolynomial25C K))
      (planeRelation (Polynomial.C Polynomial.X) Polynomial.X) =
      planeRelation ((AdjoinRoot.mk (unitPlanePolynomial25C K)) (Polynomial.C Polynomial.X))
        ((AdjoinRoot.mk (unitPlanePolynomial25C K)) Polynomial.X)
    let m : Polynomial (Polynomial K) →+* (UnitPlaneRing25C K) := AdjoinRoot.mk (unitPlanePolynomial25C K)
    change m (planeRelation (Polynomial.C Polynomial.X) Polynomial.X) =
      planeRelation (m (Polynomial.C Polynomial.X)) (m Polynomial.X)
    simp only [planeRelation,map_add,map_sub,map_mul,map_pow,map_ofNat]
  rw [he] at h
  exact h

/-- The normalized forward formulas define a homomorphism of the actual principal-open rings. -/
theorem exists_canonicalOpen_to_unitPlaneOpen_overRing :
    ∃ f : CanonicalOpenChartRing25 K →ₐ[K] (UnitPlaneOpenRing25C K),
      let l := algebraMap (UnitPlaneRing25C K) (UnitPlaneOpenRing25C K)
      let u := l (unitPlaneU25C K)
      let v := l (unitPlaneV25C K)
      let h := IsLocalization.Away.invSelf (S := (UnitPlaneOpenRing25C K)) (unitPlaneOpenElement25C K)
      ∀ i : Fin 4, f (algebraMap (CanonicalAChartRing25 K) (CanonicalOpenChartRing25 K)
          (canonicalAChartCoordinate25 K i)) =
        (![u,u*h*planeY u v,u*h*planeZ u v,u*h*planeW u v] : Fin 4 → (UnitPlaneOpenRing25C K)) i := by
  let l := algebraMap (UnitPlaneRing25C K) (UnitPlaneOpenRing25C K)
  let u := l (unitPlaneU25C K)
  let v := l (unitPlaneV25C K)
  let h := IsLocalization.Away.invSelf (S := (UnitPlaneOpenRing25C K)) (unitPlaneOpenElement25C K)
  have hi : u*v*planeDenominator u v*h = 1 := by
    simpa only [u,v,l,h,unitPlaneOpenElement25C,planeDenominator,map_mul,map_add,map_pow] using
      (IsLocalization.Away.mul_invSelf (S := (UnitPlaneOpenRing25C K)) (unitPlaneOpenElement25C K))
  have hr : planeRelation u v = 0 := by
    have hh := congrArg l (unitPlane_relation_overRing K)
    simpa only [u,v,planeRelation,map_add,map_sub,map_mul,map_pow,map_ofNat,map_zero] using hh
  have he := plane_normalized_equations u v h hi hr
  dsimp only at he
  rcases he with ⟨hq,hc,ha,hb⟩
  let c : Fin 4 → (UnitPlaneOpenRing25C K) := ![u,u*h*planeY u v,u*h*planeZ u v,u*h*planeW u v]
  let fc : CanonicalAChartRing25 K →ₐ[K] (UnitPlaneOpenRing25C K) :=
    Ideal.Quotient.liftₐ _ (MvPolynomial.aeval c) (by
      intro p hp
      have hh : canonicalAChartIdeal25 K ≤ RingHom.ker (MvPolynomial.aeval c).toRingHom := by
        apply Ideal.span_le.mpr
        intro g hg
        rcases hg with rfl | hg
        · simpa [RingHom.mem_ker,canonicalQuadric,c] using hq
        · rcases hg with rfl | hg
          · simpa [RingHom.mem_ker,canonicalCubic,c] using hc
          · rcases hg with rfl | hg
            · simpa [RingHom.mem_ker,canonicalDenominator,c,sub_eq_zero] using ha
      exact hh hp)
  have hfc : ∀ i : Fin 4, fc (canonicalAChartCoordinate25 K i) = c i := by
    intro i
    change MvPolynomial.aeval c (MvPolynomial.X i) = c i
    exact MvPolynomial.aeval_X c i
  have hu : IsUnit u := isUnit_iff_exists_inv.mpr
    ⟨v*planeDenominator u v*h,by linear_combination hi⟩
  have hd : IsUnit (planeDenominator u v) := isUnit_iff_exists_inv.mpr
    ⟨u*v*h,by linear_combination hi⟩
  have hh : IsUnit h := isUnit_iff_exists_inv.mpr ⟨u*v*planeDenominator u v,by rw [mul_comm,hi]⟩
  have hz : IsUnit (u*h*planeZ u v) := by
    unfold planeZ
    exact (hu.mul hh).mul ((hu.pow 2).mul hd)
  have hb' : IsUnit (canonicalMultiplier u (u*h*planeY u v) (u*h*planeZ u v) (u*h*planeW u v)) := by
    rw [hb]
    exact ((hu.pow 2).mul (hd.pow 2)).mul hh
  have hfunit : IsUnit (fc (canonicalAChartOpenElement25 K)) := by
    have hf : fc (canonicalAChartOpenElement25 K) =
        u*(u*h*planeZ u v)*canonicalMultiplier u (u*h*planeY u v)
          (u*h*planeZ u v) (u*h*planeW u v) := by
      simp [canonicalAChartOpenElement25,canonicalMultiplier,canonicalDenominator,hfc,c]
    rw [hf]
    exact (hu.mul hz).mul hb'
  refine ⟨IsLocalization.Away.liftAlgHom (canonicalAChartOpenElement25 K) hfunit, ?_⟩
  dsimp only
  intro i
  change IsLocalization.Away.lift (canonicalAChartOpenElement25 K) hfunit
    (algebraMap (CanonicalAChartRing25 K) (CanonicalOpenChartRing25 K)
      (canonicalAChartCoordinate25 K i)) = c i
  rw [IsLocalization.Away.lift_eq]
  exact hfc i

/-- The canonical inverse formulas define a homomorphism back to the actual plane open. -/
theorem exists_unitPlaneOpen_to_canonicalOpen_overRing :
    ∃ f : (UnitPlaneOpenRing25C K) →ₐ[K] CanonicalOpenChartRing25 K,
      let l := algebraMap (CanonicalAChartRing25 K) (CanonicalOpenChartRing25 K)
      let x := l (canonicalAChartCoordinate25 K 0)
      let y := l (canonicalAChartCoordinate25 K 1)
      let z := l (canonicalAChartCoordinate25 K 2)
      let w := l (canonicalAChartCoordinate25 K 3)
      let h := IsLocalization.Away.invSelf (S := CanonicalOpenChartRing25 K) (canonicalAChartOpenElement25 K)
      f (algebraMap (UnitPlaneRing25C K) (UnitPlaneOpenRing25C K) (unitPlaneU25C K)) = x ∧
      f (algebraMap (UnitPlaneRing25C K) (UnitPlaneOpenRing25C K) (unitPlaneV25C K)) =
        x^2*(x*canonicalMultiplier x y z w*h) := by
  let l := algebraMap (CanonicalAChartRing25 K) (CanonicalOpenChartRing25 K)
  let x := l (canonicalAChartCoordinate25 K 0)
  let y := l (canonicalAChartCoordinate25 K 1)
  let z := l (canonicalAChartCoordinate25 K 2)
  let w := l (canonicalAChartCoordinate25 K 3)
  let b := canonicalMultiplier x y z w
  let h := IsLocalization.Away.invSelf (S := CanonicalOpenChartRing25 K) (canonicalAChartOpenElement25 K)
  let r := x*b*h
  have hi : x*z*b*h = 1 := by
    simpa only [x,y,z,w,b,l,h,canonicalAChartOpenElement25,canonicalMultiplier,
      canonicalDenominator,map_mul,map_add,map_sub] using
      (IsLocalization.Away.mul_invSelf (S := CanonicalOpenChartRing25 K) (canonicalAChartOpenElement25 K))
  have hq : canonicalQuadric x y z w = 0 := by
    have hh := congrArg l (canonicalAChart_quadric_overRing K)
    simpa only [x,y,z,w,canonicalQuadric,map_add,map_sub,map_mul,map_pow,map_neg,map_zero] using hh
  have hc : canonicalCubic x y z w = 0 := by
    have hh := congrArg l (canonicalAChart_cubic_overRing K)
    simpa only [x,y,z,w,canonicalCubic,map_add,map_sub,map_mul,map_pow,map_zero] using hh
  have ha : canonicalDenominator y z w = 1 := by
    have hh := congrArg l (canonicalAChart_denominator_overRing K)
    simpa only [y,z,w,canonicalDenominator,map_add,map_sub,map_one] using hh
  have hz : z*r = 1 := by dsimp [r]; linear_combination hi
  have hx : x*(z*b*h) = 1 := by linear_combination hi
  have hr := canonical_maps_to_plane_of_inverse x y z w r (z*b*h) ha hz hx hq hc
  let ix : Polynomial K →ₐ[K] CanonicalOpenChartRing25 K := Polynomial.aeval x
  let e : Polynomial (Polynomial K) →+* CanonicalOpenChartRing25 K :=
    Polynomial.eval₂RingHom ix.toRingHom (x^2*r)
  have heC : e (Polynomial.C Polynomial.X) = x := by
    change Polynomial.eval₂ ix.toRingHom (x^2*r) (Polynomial.C Polynomial.X) = x
    rw [Polynomial.eval₂_C]
    exact Polynomial.aeval_X x
  have heX : e Polynomial.X = x^2*r := by
    exact Polynomial.eval₂_X ix.toRingHom (x^2*r)
  have hpoly : (unitPlanePolynomial25C K).eval₂ ix (x^2*r) = 0 := by
    change e (planeRelation (Polynomial.C Polynomial.X) Polynomial.X) = 0
    simpa only [planeRelation,map_add,map_sub,map_mul,map_pow,map_ofNat,heC,heX] using hr
  let fp : (UnitPlaneRing25C K) →ₐ[K] CanonicalOpenChartRing25 K :=
    AdjoinRoot.liftAlgHom (unitPlanePolynomial25C K) ix (x^2*r) hpoly
  have hfu : fp (unitPlaneU25C K) = x := by
    change AdjoinRoot.liftAlgHom (unitPlanePolynomial25C K) ix (x^2*r) hpoly
      (AdjoinRoot.of (unitPlanePolynomial25C K) Polynomial.X) = x
    exact (AdjoinRoot.liftAlgHom_of (unitPlanePolynomial25C K) ix
      (x^2*r) hpoly Polynomial.X).trans (Polynomial.aeval_X x)
  have hfv : fp (unitPlaneV25C K) = x^2*r := by
    exact AdjoinRoot.liftAlgHom_root (unitPlanePolynomial25C K) ix (x^2*r) hpoly
  have hxu : IsUnit x := isUnit_iff_exists_inv.mpr ⟨z*b*h,by linear_combination hi⟩
  have hbu : IsUnit b := isUnit_iff_exists_inv.mpr ⟨x*z*h,by linear_combination hi⟩
  have hhu : IsUnit h := isUnit_iff_exists_inv.mpr ⟨x*z*b,by rw [mul_comm,hi]⟩
  have hru : IsUnit r := (hxu.mul hbu).mul hhu
  have hd : planeDenominator x (x^2*r) = x*r*b := by
    dsimp [b]
    unfold planeDenominator canonicalMultiplier
    rw [ha]
    linear_combination -(x^2+x)*hz
  have hdu : IsUnit (planeDenominator x (x^2*r)) := by
    rw [hd]
    exact (hxu.mul hru).mul hbu
  have hfunit : IsUnit (fp (unitPlaneOpenElement25C K)) := by
    have hf : fp (unitPlaneOpenElement25C K) = x*(x^2*r)*planeDenominator x (x^2*r) := by
      simp [unitPlaneOpenElement25C,planeDenominator,hfu,hfv]
    rw [hf]
    exact (hxu.mul ((hxu.pow 2).mul hru)).mul hdu
  refine ⟨IsLocalization.Away.liftAlgHom (unitPlaneOpenElement25C K) hfunit, ?_⟩
  dsimp only
  constructor
  · change IsLocalization.Away.lift (unitPlaneOpenElement25C K) hfunit
      (algebraMap (UnitPlaneRing25C K) (UnitPlaneOpenRing25C K) (unitPlaneU25C K)) = x
    rw [IsLocalization.Away.lift_eq]
    exact hfu
  · change IsLocalization.Away.lift (unitPlaneOpenElement25C K) hfunit
      (algebraMap (UnitPlaneRing25C K) (UnitPlaneOpenRing25C K) (unitPlaneV25C K)) = x^2*r
    rw [IsLocalization.Away.lift_eq]
    exact hfv

/-- The explicit maps are inverse algebra equivalences of the two literal principal opens. -/
theorem canonicalOpenChart_algEquiv_unitPlaneOpen_overRing :
    ∃ e : CanonicalOpenChartRing25 K ≃ₐ[K] (UnitPlaneOpenRing25C K),
      let l := algebraMap (UnitPlaneRing25C K) (UnitPlaneOpenRing25C K)
      let u := l (unitPlaneU25C K)
      let v := l (unitPlaneV25C K)
      let h := IsLocalization.Away.invSelf (S := (UnitPlaneOpenRing25C K)) (unitPlaneOpenElement25C K)
      ∀ i : Fin 4, e (algebraMap (CanonicalAChartRing25 K) (CanonicalOpenChartRing25 K)
          (canonicalAChartCoordinate25 K i)) =
        (![u,u*h*planeY u v,u*h*planeZ u v,u*h*planeW u v] : Fin 4 → (UnitPlaneOpenRing25C K)) i := by
  obtain ⟨f,hf⟩ := exists_canonicalOpen_to_unitPlaneOpen_overRing K
  obtain ⟨g,hg⟩ := exists_unitPlaneOpen_to_canonicalOpen_overRing K
  dsimp only at hf hg
  let lc := algebraMap (CanonicalAChartRing25 K) (CanonicalOpenChartRing25 K)
  let x := lc (canonicalAChartCoordinate25 K 0)
  let y := lc (canonicalAChartCoordinate25 K 1)
  let z := lc (canonicalAChartCoordinate25 K 2)
  let w := lc (canonicalAChartCoordinate25 K 3)
  let b := canonicalMultiplier x y z w
  let hc := IsLocalization.Away.invSelf (S := CanonicalOpenChartRing25 K) (canonicalAChartOpenElement25 K)
  let r := x*b*hc
  let lp := algebraMap (UnitPlaneRing25C K) (UnitPlaneOpenRing25C K)
  let u := lp (unitPlaneU25C K)
  let v := lp (unitPlaneV25C K)
  let hp := IsLocalization.Away.invSelf (S := (UnitPlaneOpenRing25C K)) (unitPlaneOpenElement25C K)
  have hfx : f x = u := hf 0
  have hfy : f y = u*hp*planeY u v := hf 1
  have hfz : f z = u*hp*planeZ u v := hf 2
  have hfw : f w = u*hp*planeW u v := hf 3
  have hgu : g u = x := hg.1
  have hgv : g v = x^2*r := hg.2
  have hic : x*z*b*hc = 1 := by
    simpa only [x,y,z,w,b,lc,hc,canonicalAChartOpenElement25,canonicalMultiplier,
      canonicalDenominator,map_mul,map_add,map_sub] using
      (IsLocalization.Away.mul_invSelf (S := CanonicalOpenChartRing25 K) (canonicalAChartOpenElement25 K))
  have hip : u*v*planeDenominator u v*hp = 1 := by
    simpa only [u,v,lp,hp,unitPlaneOpenElement25C,planeDenominator,map_mul,map_add,map_pow] using
      (IsLocalization.Away.mul_invSelf (S := (UnitPlaneOpenRing25C K)) (unitPlaneOpenElement25C K))
  have hq : canonicalQuadric x y z w = 0 := by
    have hh := congrArg lc (canonicalAChart_quadric_overRing K)
    simpa only [x,y,z,w,canonicalQuadric,map_add,map_sub,map_mul,map_pow,map_neg,map_zero] using hh
  have hcc : canonicalCubic x y z w = 0 := by
    have hh := congrArg lc (canonicalAChart_cubic_overRing K)
    simpa only [x,y,z,w,canonicalCubic,map_add,map_sub,map_mul,map_pow,map_zero] using hh
  have ha : canonicalDenominator y z w = 1 := by
    have hh := congrArg lc (canonicalAChart_denominator_overRing K)
    simpa only [y,z,w,canonicalDenominator,map_add,map_sub,map_one] using hh
  have hz : z*r = 1 := by dsimp [r]; linear_combination hic
  have hs : x*(x^2*r)*planeDenominator x (x^2*r)*g hp = 1 := by
    have hh := congrArg g hip
    simpa only [planeDenominator,map_mul,map_add,map_pow,map_one,hgu,hgv] using hh
  have hinv := canonical_normalized_inverse x y z w r (g hp) ha hz hq hcc hs
  have hxy : g (f y) = y := by
    rw [hfy]
    simpa only [planeY,map_mul,map_sub,map_add,map_pow,hgu,hgv] using hinv.1
  have hxz : g (f z) = z := by
    rw [hfz]
    simpa only [planeZ,planeDenominator,map_mul,map_add,map_pow,hgu,hgv] using hinv.2.1
  have hxw : g (f w) = w := by
    rw [hfw]
    simpa only [planeW,map_mul,map_add,map_sub,map_pow,hgu,hgv] using hinv.2.2
  have hgf : g.comp f = AlgHom.id K (CanonicalOpenChartRing25 K) := by
    apply IsLocalization.algHom_ext (Submonoid.powers (canonicalAChartOpenElement25 K))
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · change g (f x) = x
      rw [hfx,hgu]
    · exact hxy
    · exact hxz
    · exact hxw
  have hfzr : (u*hp*planeZ u v)*f r = 1 := by
    have hh := congrArg f hz
    simpa only [map_mul,map_one,hfz] using hh
  have hvz : u^2 = v*(u*hp*planeZ u v) := by
    unfold planeZ
    linear_combination -u^2*hip
  have hfgv : f (g v) = v := by
    rw [hgv,map_mul,map_pow,hfx,hvz,mul_assoc,hfzr,mul_one]
  have hfg : f.comp g = AlgHom.id K (UnitPlaneOpenRing25C K) := by
    apply IsLocalization.algHom_ext (Submonoid.powers (unitPlaneOpenElement25C K))
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      change f (g u) = u
      rw [hgu,hfx]
    · exact hfgv
  have hleft : Function.LeftInverse g f := fun a => by
    have hh := AlgHom.congr_fun hgf a
    exact hh
  have hright : Function.RightInverse g f := fun a => by
    have hh := AlgHom.congr_fun hfg a
    exact hh
  exact ⟨AlgEquiv.ofBijective f ⟨hleft.injective,hright.surjective⟩,hf⟩

/-- Integral birational equivalence of the literal principal opens over any coefficient ring. -/
noncomputable def canonicalUnitPlaneOpenAlgEquiv25C :
    CanonicalOpenChartRing25 K ≃ₐ[K] UnitPlaneOpenRing25C K :=
  Classical.choose (canonicalOpenChart_algEquiv_unitPlaneOpen_overRing K)

end N25


