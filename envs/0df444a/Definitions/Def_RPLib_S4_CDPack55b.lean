-- Prove2me | Definitions.Def_RPLib_S4_CDPack55b
-- name    : RPLib_S4_CDPack55b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T16:38:51.113867+00:00
-- url     : https://prove2.me/theorems/1f7dbf0d-b08b-491b-8c82-af1fe4e710bb
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 55b of 71
-- statement:
--   Part 55b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_ThetaSquare_Mult2`: Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)
--   * `Def_RP_ThetaSquare_Curve1`: Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack55

/-!
# Curve-duality library package, part 55b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_ThetaSquare_Mult2`: Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)
* `Def_RP_ThetaSquare_Curve1`: Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_ThetaSquare_Mult2 =====
section

/-!
# Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)

* `avoid_Theta`: a map to `J` with one point off `W` avoids `Θ`;
* `kappa`: the plus-curve chart map `κ = Spec (lawMapPlus) : Spec R2 → X0`, `jMap_transl`, `kappa_kpt`;
* `lawMapPlus_normS`: `κ^* (Nm t) = t · ∏_{i ≠ i0} a_i(t)`;
* `fpull_kappa`, `ord_fpull_kappa`: `κ^* (Nm t)` has order one at a `K`-point `x` when `t` is a uniformizer at
  `ptR2 x` with no zero at the other points `a_i`;
* **`cpull_kappa_eq_one`**: `(τ ∘ κ)^* Θ` has multiplicity exactly one at every `K`-point `x` of the plus-curve
  (`τ = τ_{c_φ⁻¹}`, `φ = ptR2 x`): lower bound by `exists_eta` + `cpull_pos`, upper bound by `cpull_le_ord` with the
  norm `Nm t` (`normS_mem_eta`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB RamanujanPetersson.JacDivisors

universe u

section Mult2

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- A map to `J` with one point off `W` avoids `Θ`. -/
theorem avoid_Theta {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] (f : C ⟶ (Jac K F).left) {y : C}
    (hy : f y ∉ W P0) : Avoid f (Theta P0) := by
  refine ⟨(W P0)ᶜ, (isClosed_W P0).isOpen_compl,
    fun h => hy ((xi_specializes f y).mem_closed (isClosed_W P0) h), fun w hw => ?_⟩
  rw [Theta_apply, if_neg]
  rintro rfl
  exact hw (by rw [← closure_zTheta P0]; exact subset_closure (Set.mem_singleton _))

instance nonempty_top_X0 : Nonempty (⊤ : (X0 K F).Opens) :=
  ⟨⟨Classical.arbitrary (X0 K F), trivial⟩⟩

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

/-- The plus-curve chart map `κ : Spec R2 → X0`. -/
noncomputable def kappa : Spec (.of (R2 c0 a i0)) ⟶ X0 K F :=
  Spec.map (CommRingCat.ofHom (lawMapPlus c0 a i0 : LawRing K F →+* R2 c0 a i0))

theorem jMap_transl (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    (jMap K F (lawMapPlus c0 a i0)).left ≫ (transl (Jac K F) d).left = kappa c0 a i0 ≫ tauX d := by
  rw [tauX, ← Category.assoc]
  rfl

theorem kappa_kpt (x : R2 c0 a i0 →ₐ[K] K) : kappa c0 a i0 (kpt x) = kpt (x.comp (lawMapPlus c0 a i0)) :=
  SpecMap_kpt (lawMapPlus c0 a i0) x

theorem mem_kappa_asIdeal (p : Spec (.of (R2 c0 a i0))) (r : LawRing K F) :
    r ∈ PrimeSpectrum.asIdeal (R := LawRing K F) (kappa c0 a i0 p) ↔
      lawMapPlus c0 a i0 r ∈ PrimeSpectrum.asIdeal (R := R2 c0 a i0) p := Iff.rfl

/-- `κ^* (Nm t) = t · ∏_{i ≠ i0} a_i(t)`. -/
theorem lawMapPlus_normS (t : Rfin K F) :
    lawMapPlus c0 a i0 (awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t)) =
      algebraMap (Rfin K F) (R2 c0 a i0) t *
        algebraMap K (R2 c0 a i0) (∏ i ∈ Finset.univ.erase i0, a i t) := by
  have h1 := AlgHom.congr_fun (lawMapPlus_comp c0 a i0) (normS K (g := genusFK K F) t)
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h1
  rw [h1, show plusR c0 a i0 = plusMap (inclR c0) a i0 from rfl, plusMap_normS, map_mul, map_prod, map_prod]
  congr 1

theorem appTop_kappa (r : LawRing K F) :
    (Scheme.ΓSpecIso (.of (R2 c0 a i0))).inv.hom (lawMapPlus c0 a i0 r) =
      (kappa c0 a i0).appTop.hom ((Scheme.ΓSpecIso (.of (LawRing K F))).inv.hom r) :=
  congrArg (fun f => f.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (lawMapPlus c0 a i0 : LawRing K F →+* R2 c0 a i0)))

/-- Pull-back of a global function of `X0` along `κ`. -/
theorem fpull_kappa [IsDomain (R2 c0 a i0)] (r : LawRing K F) :
    fpull (kappa c0 a i0) ((X0 K F).germToFunctionField ⊤ ((Scheme.ΓSpecIso (.of (LawRing K F))).inv.hom r)) =
      (Spec (.of (R2 c0 a i0))).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (.of (R2 c0 a i0))).inv.hom (lawMapPlus c0 a i0 r)) := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X0 K F)
    (show kappa c0 a i0 (genericPoint (Spec (.of (R2 c0 a i0)))) ∈ (⊤ : (X0 K F).Opens) from trivial),
    fpull_algebraMap, appTop_kappa]
  exact Scheme.Hom.germ_stalkMap_apply (kappa c0 a i0) ⊤ _ trivial _

/-- The constant factor is a unit, so `κ^* (Nm t)` has order one at `x` (`t` a uniformizer at `ptR2 x`). -/
theorem ord_kpt_lawMapPlus [IsDomain (R2 c0 a i0)] (x : R2 c0 a i0 →ₐ[K] K) {t : Rfin K F}
    (ht : ptR2 c0 a i0 x t = 0) (ht2 : t ∉ (ptP (ptR2 c0 a i0 x)).asIdeal ^ 2)
    (hc : ∀ i ∈ Finset.univ.erase i0, a i t ≠ 0) :
    Scheme.ord ((Spec (.of (R2 c0 a i0))).germToFunctionField ⊤ ((Scheme.ΓSpecIso (.of (R2 c0 a i0))).inv.hom
      (lawMapPlus c0 a i0 (awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t))))) (kpt x) = 1 := by
  obtain ⟨hdvr, hsp⟩ := dvr_stalk_R2 c0 a i0 x
  have hu : IsUnit ((Spec (.of (R2 c0 a i0))).presheaf.germ ⊤ (kpt x) trivial
      ((Scheme.ΓSpecIso (.of (R2 c0 a i0))).inv.hom
        (algebraMap K (R2 c0 a i0) (∏ i ∈ Finset.univ.erase i0, a i t)))) := by
    apply IsUnit.map
    apply IsUnit.map
    exact (isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 hc)).map _
  have hspan : Ideal.span {(Spec (.of (R2 c0 a i0))).presheaf.germ ⊤ (kpt x) trivial
      ((Scheme.ΓSpecIso (.of (R2 c0 a i0))).inv.hom
        (lawMapPlus c0 a i0 (awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t))))} =
      maximalIdeal ((Spec (.of (R2 c0 a i0))).presheaf.stalk (kpt x)) := by
    rw [lawMapPlus_normS, map_mul, map_mul, Ideal.span_singleton_mul_right_unit hu]
    exact hsp t ht ht2
  refine ord_germ_eq_one (show kpt x ∈ (⊤ : (Spec (.of (R2 c0 a i0))).Opens) from trivial)
    (coheight_kpt_R2 c0 a i0 x) ?_ hspan
  intro h0
  rw [h0, map_zero, Ideal.span_singleton_eq_bot.2 rfl] at hspan
  exact IsDiscreteValuationRing.not_a_field _ hspan.symm

theorem injective_ΓSpecIso_inv (R : CommRingCat.{u}) : Function.Injective (Scheme.ΓSpecIso R).inv.hom :=
  (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.injective

theorem mem_basicOpen_X0 (r : LawRing K F) (z : X0 K F) :
    z ∈ (X0 K F).basicOpen ((Scheme.ΓSpecIso (.of (LawRing K F))).inv.hom r) ↔
      r ∉ PrimeSpectrum.asIdeal (R := LawRing K F) z :=
  (SetLike.ext_iff.1 (basicOpen_eq_of_affine (R := CommRingCat.of (LawRing K F)) r) z).trans
    (PrimeSpectrum.mem_basicOpen r z)

theorem kappa_generic_mem [IsDomain (R2 c0 a i0)] {r : LawRing K F} (hr : lawMapPlus c0 a i0 r ≠ 0) :
    kappa c0 a i0 (genericPoint (Spec (.of (R2 c0 a i0)))) ∈
      (X0 K F).basicOpen ((Scheme.ΓSpecIso (.of (LawRing K F))).inv.hom r) := by
  rw [mem_basicOpen_X0, mem_kappa_asIdeal, genericPoint_eq_bot_of_affine, PrimeSpectrum.asIdeal_bot, Ideal.mem_bot]
  exact hr

/-- `κ` avoids the divisor of a global function of `X0` whose pull-back is nonzero. -/
theorem avoid_div_kappa [IsDomain (R2 c0 a i0)] {r : LawRing K F} (hr : lawMapPlus c0 a i0 r ≠ 0) :
    Avoid (kappa c0 a i0) (div (X0 K F) ((X0 K F).germToFunctionField ⊤
      ((Scheme.ΓSpecIso (.of (LawRing K F))).inv.hom r))) :=
  ⟨(X0 K F).basicOpen ((Scheme.ΓSpecIso (.of (LawRing K F))).inv.hom r), ((X0 K F).basicOpen _).isOpen,
    kappa_generic_mem c0 a i0 hr, fun _ hw => ord_germ_eq_zero _ hw⟩

theorem mem_ptSet_plus (x : R2 c0 a i0 →ₐ[K] K) :
    ptR2 c0 a i0 x ∈ ptSet ((x.comp (lawMapPlus c0 a i0)).comp (awayι (K := K) (lawPre K F).u0)) := by
  rw [comp_lawMapPlus, ptSet_symPt]
  exact Finset.mem_image.2 ⟨i0, Finset.mem_univ _, Function.update_self _ _ _⟩

theorem not_mem_image_plus (x : R2 c0 a i0 →ₐ[K] K) : ptR2 c0 a i0 x ∉ (Finset.univ.erase i0).image a := by
  intro h
  obtain ⟨i, hi, hia⟩ := Finset.mem_image.1 h
  have h2 : Function.update a i0 (ptR2 c0 a i0 x) i = Function.update a i0 (ptR2 c0 a i0 x) i0 := by
    rw [Function.update_self, Function.update_of_ne (Finset.ne_of_mem_erase hi), hia]
  exact Finset.ne_of_mem_erase hi (injective_update c0 a i0 x h2)

theorem eq_of_mem_ptSet_plus (x : R2 c0 a i0 →ₐ[K] K) {t : Rfin K F}
    (hc : ∀ i ∈ Finset.univ.erase i0, a i t ≠ 0) :
    ∀ ψ ∈ ptSet ((x.comp (lawMapPlus c0 a i0)).comp (awayι (K := K) (lawPre K F).u0)), ψ t = 0 →
      ψ = ptR2 c0 a i0 x := by
  intro ψ hψ hψt
  rw [comp_lawMapPlus, ptSet_symPt] at hψ
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hψ
  by_cases hi : i = i0
  · rw [hi, Function.update_self]
  · rw [Function.update_of_ne hi] at hψt
    exact absurd hψt (hc i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩))

variable (hg : 0 < genusFK K F) (c : (Rfin K F →ₐ[K] K) → (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F))
  (hc : ∀ φ, ((Multiplicative.toAdd (jacPicEquiv K F (c φ)) : Pic0K K F) : PicK K F) =
    clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F)

set_option maxHeartbeats 1000000 in
include hg hc in
/-- Upper bound: the multiplicity is at most the order of `κ^* (Nm t)`, which is one. -/
theorem cpull_kappa_le_one [IsDomain (R2 c0 a i0)] (x : R2 c0 a i0 →ₐ[K] K)
    (hA' : Avoid (kappa c0 a i0) (JacDivisors.pullback (tauX (c (ptR2 c0 a i0 x))⁻¹) (Theta P0))) :
    cpull (kappa c0 a i0) (JacDivisors.pullback (tauX (c (ptR2 c0 a i0 x))⁻¹) (Theta P0)) (kpt x) ≤ 1 := by
  obtain ⟨t, ht, ht2, htS⟩ := exists_unif (ptR2 c0 a i0 x) ((Finset.univ.erase i0).image a)
    (not_mem_image_plus c0 a i0 x)
  have hcst : ∀ i ∈ Finset.univ.erase i0, a i t ≠ 0 := fun i hi => htS _ (Finset.mem_image_of_mem a hi)
  have hord := ord_kpt_lawMapPlus c0 a i0 x ht ht2 hcst
  have hLN0 : lawMapPlus c0 a i0 (awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t)) ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero, Scheme.ord_zero] at hord
    exact zero_ne_one hord
  have hs0 : (Scheme.ΓSpecIso (.of (LawRing K F))).inv.hom
      (awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t)) ≠ 0 := fun h =>
    hLN0 (by rw [injective_ΓSpecIso_inv _ (h.trans (map_zero _).symm), map_zero])
  have hg0 : (X0 K F).germToFunctionField ⊤ ((Scheme.ΓSpecIso (.of (LawRing K F))).inv.hom
      (awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t))) ≠ 0 := fun h =>
    hs0 (Scheme.germToFunctionField_injective (X0 K F) ⊤ (h.trans (map_zero _).symm))
  have hle := cpull_le_ord (kappa c0 a i0) (pullback_mem_weilDivisors _ (Theta P0)) hA' hg0
    (avoid_div_kappa c0 a i0 hLN0) (kpt x) (fun z _ hz1 => by
      rw [pullback_tauX_apply P0 hg, div_apply]
      split_ifs with hz
      · have hN := normS_mem_eta P0 hg c hc (ptR2 c0 a i0 x) (fun h0 => ht2 (by rw [h0]; exact Submodule.zero_mem _)) ht
          (x.comp (lawMapPlus c0 a i0)) (mem_ptSet_plus c0 a i0 x) (eq_of_mem_ptSet_plus c0 a i0 x hcst) hz
        have hzr : z ∉ (X0 K F).basicOpen ((Scheme.ΓSpecIso (.of (LawRing K F))).inv.hom
            (awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t))) := by
          rw [mem_basicOpen_X0, not_not]
          exact hN
        have := ord_germ_pos (show z ∈ (⊤ : (X0 K F).Opens) from trivial) hz1 hs0 hzr
        omega
      · exact ord_germ_nonneg _ trivial)
  rwa [fpull_kappa, hord] at hle

include hg hc in
/-- Lower bound: `κ (kpt x)` lies on the translate of `W`. -/
theorem one_le_cpull_kappa [IsDomain (R2 c0 a i0)] (x : R2 c0 a i0 →ₐ[K] K)
    (hA' : Avoid (kappa c0 a i0) (JacDivisors.pullback (tauX (c (ptR2 c0 a i0 x))⁻¹) (Theta P0))) :
    1 ≤ cpull (kappa c0 a i0) (JacDivisors.pullback (tauX (c (ptR2 c0 a i0 x))⁻¹) (Theta P0)) (kpt x) := by
  have hy : tauX (c (ptR2 c0 a i0 x))⁻¹ (kappa c0 a i0 (kpt x)) ∈ W P0 := by
    rw [kappa_kpt, tauX_apply]
    exact mem_transl_W P0 c hc _ _ (mem_ptSet_plus c0 a i0 x)
  obtain ⟨z₀, hz₀, hsp⟩ := exists_eta P0 _ hy
  have hpos := cpull_pos (kappa c0 a i0) (pullback_mem_weilDivisors _ (Theta P0)) hA'
    (coheight_kpt_R2 c0 a i0 x)
    (fun z _ _ => by rw [pullback_tauX_apply P0 hg]; split_ifs <;> norm_num) hsp
    (by rw [pullback_tauX_apply P0 hg, if_pos hz₀]; norm_num)
  omega

include hg hc in
/-- **Multiplicity one along the plus-curve** (F6b): at every `K`-point `x` of `Spec R2`, the pull-back of `Θ`
along `τ_{c_φ⁻¹} ∘ κ` (`φ = ptR2 x`) has multiplicity exactly one. -/
theorem cpull_kappa_eq_one [IsDomain (R2 c0 a i0)] (x : R2 c0 a i0 →ₐ[K] K)
    (hA : Avoid (kappa c0 a i0 ≫ tauX (c (ptR2 c0 a i0 x))⁻¹) (Theta P0)) :
    cpull (kappa c0 a i0 ≫ tauX (c (ptR2 c0 a i0 x))⁻¹) (Theta P0) (kpt x) = 1 := by
  have hD := theta_mem_weilDivisors P0 hg
  rw [cpull_comp _ _ hD hA]
  have hA' := avoid_pullback _ _ hD hA
  exact le_antisymm (cpull_kappa_le_one P0 c0 a i0 hg c hc x hA') (one_le_cpull_kappa P0 c0 a i0 hg c hc x hA')

end Mult2

end RamanujanPetersson.ThetaSquare

end

-- ===== S4.Def_RP_ThetaSquare_Curve1 =====
section

/-!
# Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)

* `fe P0 e = AJ ≫ transl e : X1 → J` (`p ↦ AJ(p) · e`), `feX` its underlying scheme map, `comp_fe`, `mem_W_fe`;
* **`Dc P0 e := cpull (feX P0 e) Θ`**, a cycle on the curve `X1`; `Dc_nonneg`, `Dc_eq_zero` (support in `f_e⁻¹ W`);
* `plusX` is an open immersion (`ι2`), and `plusX ≫ f_{cE · d} = τ_d ∘ κ` (`plusX_fe`);
* **`Dc_plusX_eq_one`**: `D_e` has multiplicity exactly one at the point `plusX (kpt x)` when `e = cE · c_φ⁻¹`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB RamanujanPetersson.JacDivisors

universe u

section Curve1

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

instance isLocallyNoetherian_X1 : IsLocallyNoetherian (X1 K F) := by
  haveI : LocallyOfFiniteType (toSpecK K (algebraMap K[X] F X) 1) := inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (toSpecK K (algebraMap K[X] F X) 1)

variable (P0 : Place K F)

/-- The translated Abel-Jacobi map `f_e : X1 → J`, `p ↦ AJ(p) · e`. -/
noncomputable def fe (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : X1O K F ⟶ Jac K F :=
  ajO P0 ≫ transl (Jac K F) e

/-- The underlying map of schemes of `f_e`. -/
noncomputable def feX (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : X1 K F ⟶ (Jac K F).left :=
  (fe P0 e).left

theorem comp_fe (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    q ≫ fe P0 e = (q ≫ ajO P0) * e := by
  rw [fe, ← Category.assoc, comp_transl, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem feX_kpt (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    feX P0 e (q.left (IsLocalRing.closedPoint K)) = (q ≫ fe P0 e).left (IsLocalRing.closedPoint K) :=
  rfl

/-- `f_e (q) ∈ W` in terms of classes (Riemann's theorem). -/
theorem mem_W_fe (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    feX P0 e (q.left (IsLocalRing.closedPoint K)) ∈ W P0 ↔
      ∃ t : Fin (n0 K F) → Place K F, jacPicEquiv K F ((q ≫ ajO P0) * e) =
        Multiplicative.ofAdd (∑ i, ajCls K F P0 (t i)) := by
  rw [feX_kpt, mem_W_iff, comp_fe]

/-- **The curve cycle** `D_e := f_e^* Θ` on `X1`. -/
noncomputable def Dc (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : AlgebraicCycle (X1 K F) ℤ :=
  cpull (feX P0 e) (Theta P0)

theorem theta_eq_zero_of_not_mem {w : (Jac K F).left} (hw : w ∉ W P0) : Theta P0 w = 0 := by
  rw [Theta_apply, if_neg]
  rintro rfl
  exact hw (by rw [← closure_zTheta P0]; exact subset_closure (Set.mem_singleton _))

variable (hg : 0 < genusFK K F)

include hg in
theorem Dc_nonneg (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (y : X1 K F) : 0 ≤ Dc P0 e y := by
  by_cases hA : Avoid (feX P0 e) (Theta P0)
  · exact cpull_nonneg _ (theta_mem_weilDivisors P0 hg) hA y (fun z _ _ => Theta_nonneg P0 z)
  · rw [Dc, cpull, dif_neg (fun h => hA h.2)]
    exact le_refl _

include hg in
/-- **Support**: `D_e` vanishes off `f_e⁻¹ W`. -/
theorem Dc_eq_zero (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {y : X1 K F} (hy : feX P0 e y ∉ W P0) :
    Dc P0 e y = 0 := by
  by_cases hA : Avoid (feX P0 e) (Theta P0)
  · exact cpull_eq_zero_of _ (theta_mem_weilDivisors P0 hg) hA (isClosed_W P0).isOpen_compl hy
      (fun w hw => theta_eq_zero_of_not_mem P0 hw)
  · rw [Dc, cpull, dif_neg (fun h => hA h.2)]
    rfl

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

/-- The plus-curve chart `Spec R2 → X1` as a map of schemes. -/
noncomputable def ι2 : Spec (.of (R2 c0 a i0)) ⟶ X1 K F := (plusX c0 a i0).left

instance isOpenImmersion_ι2 : IsOpenImmersion (ι2 (F := F) c0 a i0) := by
  have h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (awayι (K := K) (plusH c0 a i0) : R1 F c0 →+* R2 c0 a i0))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of (R1 F c0)) (plusH c0 a i0)
  have h2 := isOpenImmersion_bc_R1 (K := K) (F := F) c0
  have h3 : IsIso (Spec.map (CommRingCat.ofHom
      ((sym1Equiv (k := K) (B := Bc F c0)).toAlgHom : SymRing K (Bc F c0) 1 →+* Bc F c0))) :=
    inferInstanceAs (IsIso (Spec.map (RingEquiv.toCommRingCatIso
      (sym1Equiv (k := K) (B := Bc F c0)).toRingEquiv).hom))
  have e4 : Spec.map (CommRingCat.ofHom (symToR2 c0 a i0 : SymRing K (Bc F c0) 1 →+* R2 c0 a i0)) =
      Spec.map (CommRingCat.ofHom (awayι (K := K) (plusH c0 a i0) : R1 F c0 →+* R2 c0 a i0)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Bc F c0) (R1 F c0))) ≫
          Spec.map (CommRingCat.ofHom
            ((sym1Equiv (k := K) (B := Bc F c0)).toAlgHom : SymRing K (Bc F c0) 1 →+* Bc F c0)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have h4 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (symToR2 c0 a i0 : SymRing K (Bc F c0) 1 →+* R2 c0 a i0))) := by
    rw [e4]
    infer_instance
  haveI : IsOpenImmersion (ιO K F (op (idx0 c0))).left := isOpenImmersion_ιX1 (K := K) (F := F) (op (idx0 c0))
  have e : ι2 (F := F) c0 a i0 =
      Spec.map (CommRingCat.ofHom (symToR2 c0 a i0 : SymRing K (Bc F c0) 1 →+* R2 c0 a i0)) ≫
        (ιO K F (op (idx0 c0))).left := rfl
  rw [e]
  infer_instance

/-- `plusX ≫ f_{cE · d} = jMap (lawMapPlus) ≫ transl d` (over `Spec K`). -/
theorem plusX_fe_over (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    plusX c0 a i0 ≫ fe P0 (cE a i0 P0 * d) = jMap K F (lawMapPlus c0 a i0) ≫ transl (Jac K F) d := by
  rw [fe, ← transl_comp_transl, ← plus_eq c0 a i0 P0]
  simp only [← Category.assoc]
  congr 1
  rw [comp_transl, mul_comm]

/-- **The plus-curve is the translated Abel-Jacobi map**: `ι2 ≫ f_{cE · d} = κ ≫ τ_d`. -/
theorem plusX_fe (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    ι2 c0 a i0 ≫ feX P0 (cE a i0 P0 * d) = kappa c0 a i0 ≫ tauX d := by
  have h := congrArg (fun f => f.left) (plusX_fe_over P0 c0 a i0 d)
  simp only [Over.comp_left] at h
  exact h.trans (jMap_transl c0 a i0 d)

variable (c : (Rfin K F →ₐ[K] K) → (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F))
  (hc : ∀ φ, ((Multiplicative.toAdd (jacPicEquiv K F (c φ)) : Pic0K K F) : PicK K F) =
    clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F)

include hg hc in
/-- **Multiplicity one on the curve** (T4c): `D_e` is `1` at the plus-curve point `ι2 (kpt x)` when
`e = cE · c_φ⁻¹` (`φ = ptR2 x`) and `f_e` avoids `Θ`. -/
theorem Dc_plusX_eq_one (x : R2 c0 a i0 →ₐ[K] K)
    (hA : Avoid (feX P0 (cE a i0 P0 * (c (ptR2 c0 a i0 x))⁻¹)) (Theta P0)) :
    Dc P0 (cE a i0 P0 * (c (ptR2 c0 a i0 x))⁻¹) (ι2 c0 a i0 (kpt x)) = 1 := by
  haveI := isDomain_R2 c0 a i0 x
  haveI : Nonempty (Spec (.of (R2 c0 a i0))) := ⟨kpt x⟩
  haveI := isDominant_openImm (ι2 (F := F) c0 a i0)
  have hD := theta_mem_weilDivisors P0 hg
  rw [Dc, ← cpull_comp_openImm (ι2 c0 a i0) _ hD hA, plusX_fe]
  have hA2 := avoid_comp_left (ι2 c0 a i0) _ hA
  rw [plusX_fe] at hA2
  exact cpull_kappa_eq_one P0 c0 a i0 hg c hc x hA2

end Curve1

end RamanujanPetersson.ThetaSquare

end


