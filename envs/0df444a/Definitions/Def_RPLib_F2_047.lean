-- Prove2me | Definitions.Def_RPLib_F2_047
-- name    : RPLib_F2_047
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T19:17:52.929952+00:00
-- url     : https://prove2.me/theorems/56ab8988-1ad2-4a82-aadb-2ccfa83babf7
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 047 of 70
-- statement:
--   File 047 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_ThetaSquare_Mult2`: Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)
--   * `S4.Def_RP_ThetaSquare_Curve2`: Unit S4-ThetaSquare, file Curve2: the support of `D_e` on `K`-points (T4c, part 2; Riemann-Roch only)
--   * `S4.Def_RP_ThetaSquare_Curve4`: Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))
--   * `S4.Def_RP_ThetaSquare_Curve6`: Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)
--   * `S4.Def_RP_ThetaSquare_Curve8`: Unit S4-ThetaSquare, file Curve8: points of `X1^g` (T4c (D), nonemptiness, part 1)
--   * `S4.Def_RP_ThetaSquare_Curve9`: Unit S4-ThetaSquare, file Curve9: the good open set is nonempty and dense (T4c (D), nonemptiness, part 2)
--   * `S4.Def_RP_ThetaCube_CubeZ`: S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`
--   * `S4.Def_RP_ThetaCube_Maps`: S4-ThetaCube, file Maps (D-B4, part 3): the map `Φ3 : X1^n ⟶ J^3` and its lines
--   * `S4.Def_RP_ThetaCube_Tr`: S4-ThetaCube, file Tr (D-C1, part 2): trace functions on `J` and their values on the chart
--   * `S4.Def_RP_ThetaCube_TrPP`: S4-ThetaCube, file TrPP (D-C1, part 4): the block trace identity on `X1^n`
--   * `S4.Def_RP_ThetaCube_GrA`: S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
--   * `S4.Def_RP_JacFrob_JJ`: S4-JacFrob, part JJ: instances on `J` and `J ⊗ J` over an algebraically closed field
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_044
import Definitions.Def_RPLib_F2_081

/-!
# Ramanujan-Petersson curve library (flat edition), file 047 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_ThetaSquare_Mult2`: Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)
* `S4.Def_RP_ThetaSquare_Curve2`: Unit S4-ThetaSquare, file Curve2: the support of `D_e` on `K`-points (T4c, part 2; Riemann-Roch only)
* `S4.Def_RP_ThetaSquare_Curve4`: Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))
* `S4.Def_RP_ThetaSquare_Curve6`: Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)
* `S4.Def_RP_ThetaSquare_Curve8`: Unit S4-ThetaSquare, file Curve8: points of `X1^g` (T4c (D), nonemptiness, part 1)
* `S4.Def_RP_ThetaSquare_Curve9`: Unit S4-ThetaSquare, file Curve9: the good open set is nonempty and dense (T4c (D), nonemptiness, part 2)
* `S4.Def_RP_ThetaCube_CubeZ`: S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`
* `S4.Def_RP_ThetaCube_Maps`: S4-ThetaCube, file Maps (D-B4, part 3): the map `Φ3 : X1^n ⟶ J^3` and its lines
* `S4.Def_RP_ThetaCube_Tr`: S4-ThetaCube, file Tr (D-C1, part 2): trace functions on `J` and their values on the chart
* `S4.Def_RP_ThetaCube_TrPP`: S4-ThetaCube, file TrPP (D-C1, part 4): the block trace identity on `X1^n`
* `S4.Def_RP_ThetaCube_GrA`: S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
* `S4.Def_RP_JacFrob_JJ`: S4-JacFrob, part JJ: instances on `J` and `J ⊗ J` over an algebraically closed field
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

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

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

end Mult2

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve2 =====
section

/-!
# Unit S4-ThetaSquare, file Curve2: the support of `D_e` on `K`-points (T4c, part 2; Riemann-Roch only)

Let `G ≥ 0` have degree `g` and `ℓ(G) = 1`, let `W0` be canonical, and let the class of `e ∈ J(K)` be
`[W0 - G] - (g - 2)[P0]`. Then (Milne III.6.7, support part):

* `one_le_ell_iff`: `ℓ(D) ≥ 1` iff the class of `D` contains an effective divisor;
* **`eff_iff_mem_supp`**: `W0 - G + [v]` is equivalent to an effective divisor iff `v ∈ supp G`
  (Riemann-Roch in degree `g - 1` and uniqueness of the effective divisor in the class of `G`);
* `ell_eq_one_of_mem`: for `v ∈ supp G` that effective divisor `E_v` is unique;
* `exists_sum_ajCls_iff`: the Riemann condition of `mem_W_fe` in divisor form;
* **`mem_W_fe_iff`**: `f_e(q) ∈ W` iff `q ∈ supp G`, for every `K`-point `q` of `X1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve2

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- The Riemann condition of `mem_W_fe` in divisor form: for `ε = [W0 - G] - (g-2)[P0]`,
`[v] - [P0] + ε` is a sum of `g - 1` points minus `(g-1)[P0]` iff `W0 - G + [v]` is equivalent to an effective divisor. -/
theorem exists_sum_ajCls_iff (hg : 0 < genusFK K F) (P0 : Place K F) {W0 G : Places.Divisor K F}
    (hW : IsCanonicalFK K F W0) (hd : G.deg = genusFK K F) (ε : Pic0K K F)
    (hε : (ε : PicK K F) = clsK K F (W0 - G) - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1))
    (v : Place K F) :
    (∃ t : Fin (n0 K F) → Place K F, ajCls K F P0 v + ε = ∑ i, ajCls K F P0 (t i)) ↔
      ∃ E : Places.Divisor K F, 0 ≤ E ∧ clsK K F E = clsK K F (W0 - G + Finsupp.single v 1) := by
  have hn : ((n0 K F : ℕ) : ℤ) = genusFK K F - 1 := by
    rw [n0]
    omega
  set c := clsK K F (Finsupp.single P0 1) with hcdef
  have hsum : ∀ t : Fin (n0 K F) → Place K F,
      ((∑ i, ajCls K F P0 (t i) : Pic0K K F) : PicK K F) =
        clsK K F (∑ i, Finsupp.single (t i) (1 : ℤ)) - ((genusFK K F : ℤ) - 1) • c := by
    intro t
    rw [AddSubmonoidClass.coe_finsetSum, clsK_sum]
    show ∑ i, (clsK K F (Finsupp.single (t i) 1) - c) = _
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← hn, natCast_zsmul]
  have hc1 : ((genusFK K F : ℤ) - 1) • c = ((genusFK K F : ℤ) - 2) • c + c := by
    rw [show (genusFK K F : ℤ) - 1 = ((genusFK K F : ℤ) - 2) + 1 by ring, add_zsmul, one_zsmul]
  have hlhs : ((ajCls K F P0 v + ε : Pic0K K F) : PicK K F) =
      clsK K F (W0 - G + Finsupp.single v 1) - ((genusFK K F : ℤ) - 1) • c := by
    rw [AddSubgroup.coe_add, coe_ajCls, hε, clsK_add (K := K) (F := F), hc1]
    generalize ((genusFK K F : ℤ) - 2) • c = y
    abel
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨∑ i, Finsupp.single (t i) (1 : ℤ),
      Finset.sum_nonneg fun i _ => Finsupp.single_nonneg.2 zero_le_one, ?_⟩
    have h := congrArg Subtype.val ht
    rw [hlhs, hsum] at h
    exact (sub_left_inj.1 h).symm
  · rintro ⟨E, hE, hc⟩
    have hdeg : E.deg = ((n0 K F : ℕ) : ℤ) := by
      have h := congrArg (degPicK K F) hc
      rw [degPicK_clsK, degPicK_clsK, PlacesK.Divisor.deg_add, PlacesK.Divisor.deg_sub, hd,
        degFK_canonical (constField_eq_bot' (K := K) (F := F)) hW, deg_single_one] at h
      rw [h, hn]
      ring
    obtain ⟨t, ht⟩ := exists_sum_single_of_nonneg (n0 K F) hE hdeg
    refine ⟨t, Subtype.ext ?_⟩
    rw [hlhs, hsum, ← ht, hc]

section Geom

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

end Geom

end Curve2

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve4 =====
section

/-!
# Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))

* `exists_of_Zdiv_pos`: a place in the support of `Zdiv S` is a point of `S`;
* `exists_mem_X0`: if `ℓ(W0 - G + 2[v]) = 1` and that class contains the reduced divisor `Zdiv S`, then `v ∈ S`;
* `exists_R2pt`: a point `φ` of an `X0` point with `φ(x - c0) ≠ 0` is `ptR2 x` for a `K`-point `x` of a plus chart;
* `Zdiv_image_eq`, `eq_cE`: class bookkeeping (`e = cE · c_φ⁻¹`);
* **`Dc_eq_one`**: for `e` of class `[W0 - G] - (g-2)[P0]` and `q` with `1 ≤ G (kPl q)`, `D_e` is `1` at `q`
  (hypotheses: `ℓ(W0 - G + 2[kPl q]) = 1`, an `X0` point in that class, `f_e` avoids `Θ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve4

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

set_option maxSynthPendingDepth 1 in
theorem yR_u0_ne_zero (yR : LawRing K F →ₐ[K] K) :
    (yR.comp (awayι (K := K) (lawPre K F).u0)) (lawPre K F).u0 ≠ 0 :=
  ((IsLocalization.Away.algebraMap_isUnit (lawPre K F).u0).map yR).ne_zero

open Classical

/-- A point `φ` of an `X0` point `yR` with `φ(x - c0) ≠ 0` is `ptR2 x` for a `K`-point `x` of a plus chart
`R2 c0 t i0`, where `t` enumerates the points of `yR` and `t i0 = φ`. -/
theorem exists_R2pt (c0 : K) (yR : LawRing K F →ₐ[K] K) {φ : Rfin K F →ₐ[K] K}
    (hφ : φ ∈ ptSet (yR.comp (awayι (K := K) (lawPre K F).u0))) (hxc : φ (xcR F c0) ≠ 0) :
    ∃ t : Fin (genusFK K F) → (Rfin K F →ₐ[K] K), ∃ i0 : Fin (genusFK K F), ∃ x : R2 c0 t i0 →ₐ[K] K,
      ptR2 c0 t i0 x = φ ∧ Finset.univ.image t = ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)) ∧
      Function.Injective t ∧ t i0 = φ := by
  obtain ⟨t, ht, hmem⟩ := exists_enum (ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)))
    (card_lawPt (K := K) (F := F) yR)
  obtain ⟨i0, hi0⟩ := (hmem φ).1 hφ
  have him : Finset.univ.image t = ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)) := Finset.ext fun ψ => by
    rw [Finset.mem_image, hmem ψ]
    simp
  have hlt : Function.Injective (liftTuple (yR.comp (awayι (K := K) (lawPre K F).u0))) := by
    have hc := card_lawPt (K := K) (F := F) yR
    unfold ptSet at hc
    have h2 : (Finset.univ.image (liftTuple (yR.comp (awayι (K := K) (lawPre K F).u0)))).card =
        (Finset.univ : Finset (Fin (genusFK K F))).card := by
      rw [hc, Finset.card_univ, Fintype.card_fin]
    intro i j hij
    exact Finset.card_image_iff.1 h2 (Finset.mem_coe.2 (Finset.mem_univ i)) (Finset.mem_coe.2 (Finset.mem_univ j)) hij
  have hsym : symPt t = yR.comp (awayι (K := K) (lawPre K F).u0) := by
    rw [symPt_eq_of_image_eq ht hlt him, symPt_liftTuple]
  haveI : IsScalarTower K (Rfin K F) (R1 F c0) :=
    IsScalarTower.of_algebraMap_eq fun k => ((inclR c0).commutes k).symm
  obtain ⟨φ1, hφ1⟩ : ∃ φ1 : R1 F c0 →ₐ[K] K, φ1.comp (inclR c0) = φ :=
    ⟨IsLocalization.Away.liftAlgHom (xcR F c0) (f := φ) (isUnit_iff_ne_zero.2 hxc), AlgHom.ext fun w => by
      rw [AlgHom.comp_apply, IsLocalization.Away.liftAlgHom_apply, ← algebraMap_rfin_R1, IsLocalization.Away.lift_eq]
      rfl⟩
  have hu : IsUnit (φ1 (plusH c0 t i0)) := by
    have h := congrArg (fun z : SymRing K (Rfin K F) (genusFK K F) →ₐ[K] K => z (lawPre K F).u0)
      (comp_plusMap (inclR c0) t i0 φ1)
    simp only [AlgHom.comp_apply] at h
    rw [hφ1, ← hi0, Function.update_eq_self, hsym] at h
    unfold plusH plusR
    rw [h]
    exact isUnit_iff_ne_zero.2 (yR_u0_ne_zero yR)
  obtain ⟨x, hx⟩ : ∃ x : R2 c0 t i0 →ₐ[K] K, x.comp (awayι (K := K) (plusH c0 t i0)) = φ1 :=
    ⟨IsLocalization.Away.liftAlgHom (plusH c0 t i0) (f := φ1) hu, AlgHom.ext fun w => by
      rw [AlgHom.comp_apply, awayι_apply, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
      rfl⟩
  refine ⟨t, i0, x, ?_, him, ht, hi0⟩
  show (x.comp (awayι (K := K) (plusH c0 t i0))).comp (inclR c0) = φ
  rw [hx, hφ1]

section Geom

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

end Geom

end Curve4

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve6 =====
section

/-!
# Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)

* `ell_two_eq_one`: for `G ≥ 0` reduced of degree `g` with `ℓ(G) = 1`, `ℓ(W0 - G + 2[v]) = 1` for every place `v`;
* `exists_cK`, `exists_c2`: the constant `K`-points of classes `[W0] - (g-2)[P0] - [Θ]` and `g[P0] - [Θ]`;
* `exists_kJ`: a `K`-point of `J` whose closed point lies in `jX0 (X0)` is `kJ yR`;
* `avoid_of_not_mem`: `e ∉ W` makes `f_e` avoid `Θ`;
* **`isGoodFor_of`**: if `e ∉ W`, `c_K e⁻¹ ∈ jX0 (X0)`, and `AJ(q)² e c_2 ∈ jX0 (X0)` whenever `f_e (q) ∈ W`, then
  `e` is good for some `G` (`IsGoodFor P0 W0 e G`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve6

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem ajCls_self (P0 : Place K F) : ajCls K F P0 P0 = 0 :=
  Subtype.ext ((coe_ajCls P0 P0).trans (sub_self _))

/-- A `K`-point of `J` whose closed point lies in the chart `jX0 (X0)` is `kJ yR`. -/
theorem exists_kJ (x : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hx : x.left (IsLocalRing.closedPoint K) ∈ Set.range (jX0 K F)) :
    ∃ yR : LawRing K F →ₐ[K] K, kJ yR = x := by
  obtain ⟨z, hz⟩ := hx
  have hcl : IsClosed ({x.left (IsLocalRing.closedPoint K)} : Set (Jac K F).left) :=
    (pointEquivClosedPoint (Jac K F).hom ⟨x.left, Over.w x⟩).2
  have hpre : (jX0 K F) ⁻¹' {x.left (IsLocalRing.closedPoint K)} = {z} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hz]
    exact (jX0 K F).isOpenEmbedding.injective.eq_iff
  have hz' : IsClosed ({z} : Set (X0 K F)) := by
    rw [← hpre]
    exact hcl.preimage (jX0 K F).continuous
  obtain ⟨yR, hy⟩ := JacLaw.exists_kpt (K := K) (A := LawRing K F) z hz'
  refine ⟨yR, ?_⟩
  apply Over.OverMorphism.ext
  refine ext_of_apply_closedPoint_eq (Jac K F).hom (Over.w _) (Over.w _) ?_
  rw [pt_kJ, hy]
  exact hz

end Curve6

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve8 =====
section

/-!
# Unit S4-ThetaSquare, file Curve8: points of `X1^g` (T4c (D), nonemptiness, part 1)

* `exists_pt_coord`: a `K`-point of `X1^n` with prescribed coordinates;
* `coe_sum_ajCls`, `deg_sum_single`: classes and degrees of `Σ [t_i]`;
* `exists_c3`: the constant `c_3` of class `[W0] - (g-2)[P0] - g[P0]`;
* `eM c3 : X1^g ⟶ J`, `p ↦ c_3 Φ_g(p)⁻¹`, of class `[W0 - Σ [p_i]] - (g-2)[P0]` (`cls_eM`), surjective on
  `K`-points (`eM_surj`);
* `ell_eq_one_of_not_mem`: `ℓ(G) = 1` when the class `[W0 - G] - (g-2)[P0]` is off `W`;
* `exists_t_swap`: the Riemann-Roch step for the chart condition at a coordinate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve8

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem coe_sum_ajCls (P0 : Place K F) {n : ℕ} (t : Fin n → Place K F) :
    ((∑ i, ajCls K F P0 (t i) : Pic0K K F) : PicK K F) =
      clsK K F (∑ i, Finsupp.single (t i) 1) - (n : ℤ) • clsK K F (Finsupp.single P0 1) := by
  rw [AddSubmonoidClass.coe_finsetSum, clsK_sum]
  simp only [coe_ajCls]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, natCast_zsmul]

end Curve8

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve9 =====
section

/-!
# Unit S4-ThetaSquare, file Curve9: the good open set is nonempty and dense (T4c (D), nonemptiness, part 2)

On `X1^g` (irreducible) the three open conditions on `p`, with `e := e_M(p) = c_3 Φ_g(p)⁻¹`:
* `Ua`: `c_K e⁻¹ ∈ jX0 (X0)`; `Ub`: `e ∉ W`; `Uj j`: `AJ(p_j)² e c_2 ∈ jX0 (X0)` (each nonempty);
* `mem_Ogood_of_U`: a `K`-point `p` in all of them gives `e ∈ Ogood` (`f_e (q) ∈ W` forces `q = p_j` for some `j`);
* **`exists_kpt_Ogood`**, **`nonempty_Ogood`**, **`dense_Ogood`**: `Ogood P0 cK c2` has a `K`-point and is dense in `J`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve9

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (cK c2 c3 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)

theorem exists_y0 : Nonempty (LawRing K F →ₐ[K] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (LawRing K F)
  obtain ⟨y0, -⟩ := JacLaw.exists_kpt (K := K) (A := LawRing K F)
    ((⟨m, hm.isPrime⟩ : PrimeSpectrum (LawRing K F)) : X0 K F)
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm)
  exact ⟨y0⟩

end Curve9

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaCube_CubeZ =====
section

/-!
# S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`

* instances on `J ⊗ J` and `P := J ⊗ (J ⊗ J)`: integral, locally Noetherian, factorial stalks;
* `q1 q2 q3 : P ⟶ J` (projections), `cubeMap α β ga = lift α (lift β ga)`;
* `cubeZ P0 x0`: the seven-term combination of `(m_S ≫ τ_{x0})^* Θ` on `P`;
* **`cpull_cubeZ`**: `(α, β, ga)^* cubeZ = cubeC (φ ↦ (φ ≫ τ_{x0})^* Θ) α β ga` (seven `Avoid` hypotheses);
* `cpull_cubeZ_hom`: the same for homomorphisms, when `x0 ∉ W`;
* **`cubeC_mem_numKer`**: if a positive multiple of `cubeZ P0 x0` is principal on `P`, the cube relation holds
  numerically for `c φ := (φ ≫ τ_{x0})^* Θ` and all homomorphisms `α β ga`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section General

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

end General

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

instance isIntegral_J2 : IsIntegral (Jac K F ⊗ Jac K F).left :=
  IntersectA.isIntegral_pullback (Jac K F).hom (Jac K F).hom

instance isIntegral_J3 : IsIntegral (Jac K F ⊗ (Jac K F ⊗ Jac K F)).left :=
  IntersectA.isIntegral_pullback (Jac K F).hom (Jac K F ⊗ Jac K F).hom

instance smooth_J2 : Smooth (Jac K F ⊗ Jac K F).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

instance smooth_J3 : Smooth (Jac K F ⊗ (Jac K F ⊗ Jac K F)).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

instance isLocallyNoetherian_J3 : IsLocallyNoetherian (Jac K F ⊗ (Jac K F ⊗ Jac K F)).left :=
  LocallyOfFiniteType.isLocallyNoetherian (Jac K F ⊗ (Jac K F ⊗ Jac K F)).hom

instance ufd_J3 (y : (Jac K F ⊗ (Jac K F ⊗ Jac K F)).left) :
    UniqueFactorizationMonoid ((Jac K F ⊗ (Jac K F ⊗ Jac K F)).left.presheaf.stalk y) :=
  uniqueFactorizationMonoid_stalk_of_smooth (Jac K F ⊗ (Jac K F ⊗ Jac K F)).hom y

variable (K F) in
/-- First projection `J^3 ⟶ J`. -/
noncomputable def q1 : Jac K F ⊗ (Jac K F ⊗ Jac K F) ⟶ Jac K F := fst _ _

variable (K F) in
/-- Second projection `J^3 ⟶ J`. -/
noncomputable def q2 : Jac K F ⊗ (Jac K F ⊗ Jac K F) ⟶ Jac K F := snd _ _ ≫ fst _ _

variable (K F) in
/-- Third projection `J^3 ⟶ J`. -/
noncomputable def q3 : Jac K F ⊗ (Jac K F ⊗ Jac K F) ⟶ Jac K F := snd _ _ ≫ snd _ _

/-- The map `(α, β, ga) : J ⟶ J^3`. -/
noncomputable def cubeMap (α β ga : Jac K F ⟶ Jac K F) : Jac K F ⟶ Jac K F ⊗ (Jac K F ⊗ Jac K F) :=
  lift α (lift β ga)

lemma cubeMap_q1 (α β ga : Jac K F ⟶ Jac K F) : cubeMap α β ga ≫ q1 K F = α := lift_fst _ _

lemma cubeMap_q2 (α β ga : Jac K F ⟶ Jac K F) : cubeMap α β ga ≫ q2 K F = β := by
  rw [q2, ← Category.assoc, cubeMap, lift_snd, lift_fst]

lemma cubeMap_q3 (α β ga : Jac K F ⟶ Jac K F) : cubeMap α β ga ≫ q3 K F = ga := by
  rw [q3, ← Category.assoc, cubeMap, lift_snd, lift_snd]

variable (P0 : Place K F)

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Maps =====
section

/-!
# S4-ThetaCube, file Maps (D-B4, part 3): the map `Φ3 : X1^n ⟶ J^3` and its lines
* `cpull_pbTh_X1`, **`cpull_cubeZ_X1`**: the cube divisor pulled back along any `f : X1 ⟶ J^3`;
* `comp_finprod`: composition distributes over finite products in the hom-group;
* `psiS P0 n β S := Π_{k : β k ∈ S} pr_k ≫ aj` (blocks given by `β : Fin n → Fin 3`), `psiS_mul`;
* `Phi3 P0 n β := (psiS {0}, psiS {1}, psiS {2})`, `Phi3_q1`, `Phi3_q2`, `Phi3_q3`;
* **`line_psiS_transl`**: along the `i0`-th line through `p`, `psiS S ≫ τ_{x0}` is `f_e` (if `β i0 ∈ S`) or the
  constant `e`, for `e = (p ≫ psiE S i0) * x0`;
* `cpull_const_Theta`: a constant map off `W` pulls `Θ` back to `0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Maps

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

lemma toUnit_comp_apply_J (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (x : (X1O K F).left) :
    (toUnit (X1O K F) ≫ e).left x = pt (Jac K F) e :=
  congrArg (fun y => e.left y) (Subsingleton.elim (α := Spec (.of K)) _ _)

end Maps

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Tr =====
section

/-!
# S4-ThetaCube, file Tr (D-C1, part 2): trace functions on `J` and their values on the chart
* `invFF_algebraMap`, `fpull_invFF`: along an open immersion `ι`, `(ffMap ι)⁻¹ H` is regular at `ι (ℓ η)` when `H` is
  regular at `ℓ η`, and `fpull (ℓ ≫ ι) ((ffMap ι)⁻¹ H) = fpull ℓ H`;
* `gff a`: a global function of `Spec R` as a rational function; `kff c := gff c` (constants on `Spec K`);
  `fpull_SpecMap_gff`: `Spec φ^* (gff a) = gff (φ a)` (and regularity);
* `trX0 f := gff (tr f)` on the chart `X0`, `trJ d f := (ffMap τ_d)⁻¹ (trX0 f) ∈ K(J)` (`f ∈ Rfin`);
* `kJ_transl_left`, **`trJ_val`**: at `kJ yR ≫ t_d`, `trJ d f` is regular with value `kff (yR (tr f))`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open Polynomial

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory Topology RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place Rfin)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.JacComplete RamanujanPetersson.IsogDegA
open RamanujanPetersson.JacDivisors

universe u

section OpenImm

variable {P U C : Scheme.{u}} [IsIntegral P] [IsIntegral U] [IsIntegral C] (ι : U ⟶ C) [IsOpenImmersion ι]
  [IsDominant ι]

end OpenImm

section SpecVal

variable {R : Type u} [CommRing R] [IsDomain R]

end SpecVal

section Trace

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- `trX0 f = Σ_l f(P_l)` as a (global) function on the chart `X0`. -/
noncomputable def trX0 (f : Rfin K F) : (X0 K F).functionField :=
  gff (R := LawRing K F) (awayι (K := K) (lawPre K F).u0 (traceS K f))

/-- The trace function `trJ d f := (τ_d^*)⁻¹ (trX0 f) ∈ K(J)`. -/
noncomputable def trJ (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (f : Rfin K F) : (Jac K F).left.functionField :=
  (inv (ffMap (tauX d))).hom (trX0 K F f)

theorem kJ_transl_left (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (yR : LawRing K F →ₐ[K] K) :
    (kJ yR ≫ transl (Jac K F) d).left = Spec.map (CommRingCat.ofHom (yR : LawRing K F →+* K)) ≫ tauX d := by
  change Spec.map (CommRingCat.ofHom (yR : LawRing K F →+* K)) ≫
    (Spec.map (CommRingCat.ofHom (RingHom.id (LawRing K F))) ≫ jX0 K F) ≫ (transl (Jac K F) d).left = _
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  rfl

/-- **Value of `trJ` on the translated chart.** -/
theorem trJ_val_of (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (yR : LawRing K F →ₐ[K] K) (f : Rfin K F)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hp : p.left = Spec.map (CommRingCat.ofHom (yR : LawRing K F →+* K)) ≫ tauX d) :
    RegAt (p.left (genericPoint _)) (trJ d f) ∧
      fpull p.left (trJ d f) = kff (yR (awayι (K := K) (lawPre K F).u0 (traceS K f))) := by
  rw [hp]
  obtain ⟨h1, h2⟩ := fpull_SpecMap_gff (yR : LawRing K F →+* K) (awayι (K := K) (lawPre K F).u0 (traceS K f))
  obtain ⟨h3, h4⟩ := fpull_invFF (tauX d) (Spec.map (CommRingCat.ofHom (yR : LawRing K F →+* K))) h1
  exact ⟨h3, h4.trans h2⟩

end Trace

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_TrPP =====
section

/-!
# S4-ThetaCube, file TrPP (D-C1, part 4): the block trace identity on `X1^n`
* `blk n β S := {k | β k ∈ S}` (the coordinates multiplied in `psiS P0 n β S`);
* `trace_val`: at a `K`-point `yR` of the chart, `yR (tr f) = Σ_{ψ ∈ ptSet yR} ψ f`;
* `trPP_val`: at a `K`-point `p` of `X1^n` such that `p ≫ ψ_S` lies on the translated chart at `yR` and the block points
  `p ≫ pr_k` (`k ∈ blk`) are the distinct points of `yR`, both sides of the identity are regular with equal values;
* **`trPP`**: if this holds on a nonempty open, `ψ_S^* (trJ d f) = Σ_{k ∈ blk} pr_k^* (phiX f)` in `K(X1^n)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR RamanujanPetersson.JacLaw
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section TrPP

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

open Classical in
/-- The trace at a `K`-point of the chart is the sum over its points. -/
theorem trace_val (yR : LawRing K F →ₐ[K] K) (f : Places.Rfin K F) :
    yR (awayι (K := K) (lawPre K F).u0 (traceS K f)) =
      ∑ ψ ∈ ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)), ψ f := by
  have hc := card_lawPt (K := K) (F := F) yR
  have hinj : Set.InjOn (liftTuple (yR.comp (awayι (K := K) (lawPre K F).u0)))
      ((Finset.univ : Finset (Fin (genusFK K F))) : Set (Fin (genusFK K F))) := by
    apply Finset.injOn_of_card_image_eq
    rw [Finset.card_fin]
    exact hc
  have h1 := symPt_traceS (liftTuple (yR.comp (awayι (K := K) (lawPre K F).u0))) f
  rw [symPt_liftTuple] at h1
  rw [ptSet, Finset.sum_image hinj]
  exact h1

end TrPP

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_GrA =====
section

/-!
# S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
* `fpull_eq_ffMap`, `fpull_comp_dom`: along dominant maps `fpull` is the field map `ffMap`;
* `surjective_hom_of_nonempty`, `surjective_fst_left`, `surjective_snd_left`; `surjective_prj`, `isDominant_prj`;
* `qb b` (the three projections `J^3 ⟶ J`), `isDominant_qb`, `Phi3_qb`;
* **`ffMap_Phi3_fpull`**: `Φ3^# (q_b^# G) = ψ_{b}^# G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Dom

variable {C P Y : Scheme.{u}} [IsIntegral C] [IsIntegral P] [IsIntegral Y]

end Dom

section GrA

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- The three projections `J^3 ⟶ J`. -/
noncomputable def qb : Fin 3 → (Jac K F ⊗ (Jac K F ⊗ Jac K F) ⟶ Jac K F) := ![q1 K F, q2 K F, q3 K F]

theorem surjective_qb (b : Fin 3) : Surjective (qb K F b).left := by
  fin_cases b
  · exact surjective_fst_left _ _
  · show Surjective ((snd (Jac K F) (Jac K F ⊗ Jac K F)).left ≫ (fst (Jac K F) (Jac K F)).left)
    have := surjective_snd_left (Jac K F) (Jac K F ⊗ Jac K F)
    have := surjective_fst_left (Jac K F) (Jac K F)
    infer_instance
  · show Surjective ((snd (Jac K F) (Jac K F ⊗ Jac K F)).left ≫ (snd (Jac K F) (Jac K F)).left)
    have := surjective_snd_left (Jac K F) (Jac K F ⊗ Jac K F)
    have := surjective_snd_left (Jac K F) (Jac K F)
    infer_instance

instance isDominant_qb (b : Fin 3) : IsDominant (qb K F b).left := by
  have := surjective_qb (K := K) (F := F) b
  infer_instance

variable (P0 : Place K F)

end GrA

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_JacFrob_JJ =====
section

/-!
# S4-JacFrob, part JJ: instances on `J` and `J ⊗ J` over an algebraically closed field

* `isIntegral_JacL : IsIntegral (Jac K F).left`;
* `isIntegral_JacJac : IsIntegral (Jac K F ⊗ Jac K F).left` (S4-IntersectA `isIntegral_pullback`);
* `isReduced_JacJac`, `lft_JacJac`, `smooth_JacJac`: what `extJ` (with `V = J`) and `eq_of_kpt_eq`
  (on `J ⊗ J`) ask for.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory RamanujanPetersson.JacComplete

universe u

section JJ

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

instance isIntegral_JacL : IsIntegral (Jac K F).left := isIntegral_of_irreducibleSpace_of_isReduced _

instance isIntegral_JacJac : IsIntegral (Jac K F ⊗ Jac K F).left :=
  IntersectA.isIntegral_pullback (Jac K F).hom (Jac K F).hom

end JJ

end RamanujanPetersson.JacFrob


end


