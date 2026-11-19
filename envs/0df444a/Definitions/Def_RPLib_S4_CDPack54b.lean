-- Prove2me | Definitions.Def_RPLib_S4_CDPack54b
-- name    : RPLib_S4_CDPack54b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T15:52:15.148193+00:00
-- url     : https://prove2.me/theorems/3eddd9ad-451c-493c-b94b-f6c54fff0b1d
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 54b of 71
-- statement:
--   Part 54b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_ThetaSquare_Pts`: Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`
--   * `Def_RP_ThetaSquare_Codim`: Unit S4-ThetaSquare, file Codim: `Θ` is a prime Weil divisor (`coheight (zTheta P0) = 1`)
--   * `Def_RP_JacFrob_JJ`: S4-JacFrob, part JJ: instances on `J` and `J ⊗ J` over an algebraically closed field
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack54
import Definitions.Def_RPLib_S4_CDPack46
import Definitions.Def_RPLib_S4_CDPack25

/-!
# Curve-duality library package, part 54b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_ThetaSquare_Pts`: Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`
* `Def_RP_ThetaSquare_Codim`: Unit S4-ThetaSquare, file Codim: `Θ` is a prime Weil divisor (`coheight (zTheta P0) = 1`)
* `Def_RP_JacFrob_JJ`: S4-JacFrob, part JJ: instances on `J` and `J ⊗ J` over an algebraically closed field
-/

set_option autoImplicit false

-- ===== S4.Def_RP_ThetaSquare_Pts =====
section

/-!
# Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`

Input for `coheight (zTheta P0) ≤ 1` (file `Codim`, Krull on the chart `X0`):
* `kJ yR`: the `K`-point of `J` at the closed point `yR` of `X0`; `pt_kJ` (it is `jX0 (kpt yR)`) and `cls_kJ`
  (its class is `[Zdiv A] - [Θ]`, `A` the `g` points of `yR`); `deg_thetaK : deg [Θ] = g`;
* `exists_cJ`: the `K`-point `c_φ` with class `[φ] + (g-1)[P0] - [Θ]`;
* `mem_W_of_cls`: a class `[Zdiv S] - (g-1)[P0]` with `#S = g-1` lies on `W`;
* `mem_transl_W`: if `φ` is one of the points of `yR`, then `jX0 (kpt yR) - c_φ ∈ W`;
* `finite_zeros`: a nonzero `u ∈ Rfin` has finitely many zeros.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB

universe u

section Pts

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- The `K`-point of `J` at the closed point `yR` of the chart `X0`. -/
noncomputable def kJ (yR : LawRing K F →ₐ[K] K) : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F :=
  kptO yR ≫ jMap K F (AlgHom.id K (LawRing K F))

theorem pt_kJ (yR : LawRing K F →ₐ[K] K) : (kJ yR).left (IsLocalRing.closedPoint K) = jX0 K F (kpt yR) := by
  show jX0 K F (Spec.map (CommRingCat.ofHom ((AlgHom.id K (LawRing K F)) : LawRing K F →+* LawRing K F))
    (Spec.map (CommRingCat.ofHom (yR : LawRing K F →+* K)) (IsLocalRing.closedPoint K))) = _
  rw [SpecMap_closedPoint, SpecMap_kpt, AlgHom.comp_id]

theorem cls_kJ (yR : LawRing K F →ₐ[K] K) :
    ((Multiplicative.toAdd (jacPicEquiv K F (kJ yR)) : Pic0K K F) : PicK K F) =
      clsK K F (Zdiv (ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)))) - thetaK K F := by
  rw [kJ, jacPicEquiv_jMap, AlgHom.comp_id, psiJ, psiS_kpt]
  rfl

theorem deg_thetaK : degPicK K F (thetaK K F) = genusFK K F := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (LawRing K F)
  obtain ⟨y0, -⟩ := JacLaw.exists_kpt (K := K) (A := LawRing K F) ((⟨m, hm.isPrime⟩ : PrimeSpectrum (LawRing K F)) : X0 K F)
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm)
  have h0 := (mem_Pic0K K F).1 (Multiplicative.toAdd (jacPicEquiv K F (kJ y0))).2
  rw [cls_kJ, map_sub, degPicK_clsK, deg_Zdiv, card_lawPt] at h0
  omega

/-- The `K`-point `c_φ` with class `[φ] + (g-1)[P0] - [Θ]`. -/
theorem exists_cJ (hg : 0 < genusFK K F) (φ : Rfin K F →ₐ[K] K) :
    ∃ c : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, ((Multiplicative.toAdd (jacPicEquiv K F c) : Pic0K K F) : PicK K F) =
      clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F := by
  have hm : clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) -
      thetaK K F ∈ Pic0K K F := by
    rw [mem_Pic0K, map_sub, map_add, map_nsmul, degPicK_clsK, degPicK_clsK, deg_single_one, deg_single_one,
      deg_thetaK, nsmul_eq_mul, _root_.mul_one]
    simp only [n0]
    omega
  exact ⟨(jacPicEquiv K F).symm (Multiplicative.ofAdd ⟨_, hm⟩), by rw [MulEquiv.apply_symm_apply]; rfl⟩

/-- A class `[Zdiv S] - (g-1)[P0]` with `#S = g - 1` lies on `W`. -/
theorem mem_W_of_cls (x : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (S : Finset (Rfin K F →ₐ[K] K))
    (hS : S.card = n0 K F)
    (h : ((Multiplicative.toAdd (jacPicEquiv K F x) : Pic0K K F) : PicK K F) =
      clsK K F (Zdiv S) - n0 K F • clsK K F (Finsupp.single P0 1)) :
    x.left (IsLocalRing.closedPoint K) ∈ W P0 := by
  let e : Fin (n0 K F) ≃ S := (finCongr hS.symm).trans S.equivFin.symm
  refine (mem_W_iff P0 x).2 ⟨fun i => Sum.inl (ptP (e i).1), ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rw [toAdd_ofAdd, h, AddSubmonoidClass.coe_finsetSum]
  simp only [coe_ajCls]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Zdiv, clsK_sum, ← Finset.sum_coe_sort S]
  exact (e.sum_comp (fun z : S => clsK K F (Finsupp.single (Sum.inl (ptP z.1) : Place K F) (1 : ℤ)))).symm

/-- If `φ` is one of the `g` points of `yR`, then `jX0 (kpt yR) - c_φ ∈ W`. -/
theorem mem_transl_W (c : (Rfin K F →ₐ[K] K) → (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F))
    (hc : ∀ φ, ((Multiplicative.toAdd (jacPicEquiv K F (c φ)) : Pic0K K F) : PicK K F) =
      clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (yR : LawRing K F →ₐ[K] K) (φ : Rfin K F →ₐ[K] K)
    (hφ : φ ∈ ptSet (yR.comp (awayι (K := K) (lawPre K F).u0))) :
    (transl (Jac K F) (c φ)⁻¹).left (jX0 K F (kpt yR)) ∈ W P0 := by
  rw [← pt_kJ]
  change (transl (Jac K F) (c φ)⁻¹).left (pt (Jac K F) (kJ yR)) ∈ W P0
  rw [transl_pt]
  have hcard : ((ptSet (yR.comp (awayι (K := K) (lawPre K F).u0))).erase φ).card = n0 K F := by
    rw [Finset.card_erase_of_mem hφ, card_lawPt]
  apply mem_W_of_cls P0 _ _ hcard
  have hZ : Zdiv (ptSet (yR.comp (awayι (K := K) (lawPre K F).u0))) =
      Zdiv ((ptSet (yR.comp (awayι (K := K) (lawPre K F).u0))).erase φ) +
        Finsupp.single (Sum.inl (ptP φ)) 1 := by
    conv_lhs => rw [← Finset.insert_erase hφ]
    exact Zdiv_insert (Finset.notMem_erase φ _)
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, AddSubgroup.coe_add, AddSubgroup.coe_neg, cls_kJ, hc, hZ,
    clsK_add]
  abel

/-- A nonzero `u ∈ Rfin` has finitely many zeros. -/
theorem finite_zeros {u : Rfin K F} (hu : u ≠ 0) : {φ : Rfin K F →ₐ[K] K | φ u = 0}.Finite := by
  have hI : Ideal.span {u} ≠ (0 : Ideal (Rfin K F)) := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine ((Ideal.finite_factors hI).preimage ptP_injective.injOn).subset fun φ hφ => ?_
  show (ptP φ).asIdeal ∣ Ideal.span {u}
  rw [Ideal.dvd_span_singleton]
  exact mem_ptP.2 hφ

end Pts

end RamanujanPetersson.ThetaSquare

end

-- ===== S4.Def_RP_ThetaSquare_Codim =====
section

/-!
# Unit S4-ThetaSquare, file Codim: `Θ` is a prime Weil divisor (`coheight (zTheta P0) = 1`)

`coheight_zTheta_le_one` (Krull on the chart `X0 = Spec LawRing`): pick a chart point `y0`, one of its points `φ0`
and `u = x - x(φ0) ∈ Rfin` (nonzero: `exists_pool`), `N = Nm(u) ∈ LawRing`; a minimal prime `q` of `(N)` has height
`≤ 1` (Krull's principal ideal theorem). Every closed point `A'` of `V(N)` contains a zero `φ` of `u`, so
`jX0 A' - c_φ ∈ W` (`mem_transl_W`); `V(N)` is closed in the Jacobson `X0` and the finite union of the translates
`W + c_φ` is closed, so `jX0 q` lies in one of them, whence `coheight zTheta ≤ coheight (jX0 q) = ht q ≤ 1`.
`theta_mem_weilDivisors`: with `one_le_coheight_zTheta`, `Θ ∈ weilDivisors J`.
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

section Codim

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- The value of `Nm(u)` at a chart point is `∏_l φ_l(u)`. -/
theorem eval_normS (u : Rfin K F) (yR : LawRing K F →ₐ[K] K) :
    yR (awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) u)) =
      ∏ l, liftTuple (yR.comp (awayι (K := K) (lawPre K F).u0)) l u := by
  show (yR.comp (awayι (K := K) (lawPre K F).u0)) (normS K u) = _
  conv_lhs => rw [← symPt_liftTuple (yR.comp (awayι (K := K) (lawPre K F).u0))]
  exact symPt_normS _ u

set_option maxHeartbeats 1000000 in
/-- **`Θ` has codimension `≤ 1`** (Krull's principal ideal theorem on the chart `X0`). -/
theorem coheight_zTheta_le_one (hg : 0 < genusFK K F) : Order.coheight (zTheta P0) ≤ 1 := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (LawRing K F)
  obtain ⟨y0, -⟩ := JacLaw.exists_kpt (K := K) (A := LawRing K F)
    ((⟨m, hm.isPrime⟩ : PrimeSpectrum (LawRing K F)) : X0 K F)
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm)
  obtain ⟨φ0, hφ0⟩ : (ptSet (y0.comp (awayι (K := K) (lawPre K F).u0))).Nonempty :=
    Finset.card_pos.1 (by rw [card_lawPt]; exact hg)
  set u : Rfin K F := xB K F - algebraMap K (Rfin K F) (φ0 (xB K F)) with hu_def
  have hφ0u : φ0 u = 0 := by
    rw [hu_def, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hu : u ≠ 0 := by
    intro h0
    obtain ⟨T, hT, hTb⟩ := JacComplete.exists_pool (K := K) (F := F) (X - C (φ0 (xB K F)))
      (X_sub_C_ne_zero _) 1
    obtain ⟨ψ, hψ⟩ : T.Nonempty := Finset.card_pos.1 (by omega)
    apply hTb ψ hψ
    have h1 : ψ u = 0 := by rw [h0, map_zero]
    rw [hu_def, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at h1
    rw [eval_sub, eval_X, eval_C]
    exact h1
  set N : LawRing K F := awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) u) with hN_def
  have hN : ∀ yR : LawRing K F →ₐ[K] K, yR N = 0 →
      ∃ φ ∈ ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)), φ u = 0 := by
    intro yR h
    rw [hN_def, eval_normS] at h
    obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.1 h
    exact ⟨_, (mem_ptSet _ _).2 ⟨l, rfl⟩, hl⟩
  have hy0N : y0 N = 0 := by
    obtain ⟨l, hl⟩ := (mem_ptSet _ _).1 hφ0
    rw [hN_def, eval_normS]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by rw [hl]; exact hφ0u)
  -- the minimal prime `q` of `(N)` (Krull: height `≤ 1`)
  have hNk : Ideal.span {N} ≤ RingHom.ker (y0 : LawRing K F →+* K) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (RingHom.mem_ker).2 hy0N
  haveI : (RingHom.ker (y0 : LawRing K F →+* K)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hqmin, -⟩ := Ideal.exists_minimalPrimes_le hNk
  haveI : IsNoetherianRing (LawRing K F) := Algebra.FiniteType.isNoetherianRing K _
  have hq1 : q.height ≤ 1 := by
    have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset (s := ({N} : Finset (LawRing K F))) (p := q)
      (by rw [Finset.coe_singleton]; exact hqmin)
    rwa [Finset.card_singleton, Nat.cast_one] at h1
  let xq : X0 K F := ((⟨q, hqmin.1.1⟩ : PrimeSpectrum (LawRing K F)) : X0 K F)
  -- the finite union of translates `W + c_φ`, `φ(u) = 0`, is closed and contains `jX0 (V(N))`
  choose c hc using exists_cJ P0 hg
  let Sset : Set (Jac K F).left :=
    ⋃ φ ∈ {φ : Rfin K F →ₐ[K] K | φ u = 0}, (transl (Jac K F) (c φ)⁻¹).left ⁻¹' W P0
  have hS : IsClosed Sset := (finite_zeros hu).isClosed_biUnion fun φ _ =>
    (isClosed_W P0).preimage (transl (Jac K F) (c φ)⁻¹).left.continuous
  haveI hJ : JacobsonSpace (X0 K F) := LocallyOfFiniteType.jacobsonSpace (jX0 K F ≫ (Jac K F).hom)
  haveI : JacobsonSpace (PrimeSpectrum ↑(CommRingCat.of (LawRing K F))) := hJ
  have hV : IsClosed (PrimeSpectrum.zeroLocus ({N} : Set (LawRing K F)) : Set (X0 K F)) :=
    PrimeSpectrum.isClosed_zeroLocus _
  have hsub : (PrimeSpectrum.zeroLocus ({N} : Set (LawRing K F)) : Set (X0 K F)) ⊆ jX0 K F ⁻¹' Sset := by
    rw [← closure_inter_closedPoints hV]
    refine closure_minimal ?_ (hS.preimage (jX0 K F).continuous)
    rintro p ⟨hpN, hpc⟩
    obtain ⟨yR, rfl⟩ := JacLaw.exists_kpt (K := K) (A := LawRing K F) p hpc
    have hyN : yR N = 0 := by
      have h1 : N ∈ PrimeSpectrum.asIdeal (R := LawRing K F) (kpt yR) :=
        (PrimeSpectrum.mem_zeroLocus _ _).1 hpN (Set.mem_singleton N)
      rwa [kpt_asIdeal, RingHom.mem_ker] at h1
    obtain ⟨φ, hφ, hφu⟩ := hN yR hyN
    exact Set.mem_biUnion (x := φ) hφu (mem_transl_W P0 c hc yR φ hφ)
  have hxq : jX0 K F xq ∈ Sset := hsub ((PrimeSpectrum.mem_zeroLocus _ _).2
    (Set.singleton_subset_iff.2 (hqmin.1.2 (Ideal.subset_span rfl))))
  obtain ⟨φ, -, hφW⟩ := Set.mem_iUnion₂.1 hxq
  -- coheight
  have hspec : (transl (Jac K F) (c φ)⁻¹).left (jX0 K F xq) ≤ zTheta P0 := by
    have h2 : (transl (Jac K F) (c φ)⁻¹).left (jX0 K F xq) ∈ closure {zTheta P0} := by
      rw [closure_zTheta P0]; exact hφW
    exact specializes_iff_mem_closure.2 h2
  haveI := isIso_translL (Jac K F) (c φ)⁻¹
  calc Order.coheight (zTheta P0)
      ≤ Order.coheight ((transl (Jac K F) (c φ)⁻¹).left (jX0 K F xq)) := Order.coheight_anti hspec
    _ = Order.coheight (jX0 K F xq) := (transl (Jac K F) (c φ)⁻¹).left.isOpenEmbedding.coheight_eq
    _ = Order.coheight xq := (jX0 K F).isOpenEmbedding.coheight_eq
    _ = q.height := (idealHeight_eq_coheight (.of (LawRing K F)) xq).symm
    _ ≤ 1 := hq1

/-- **`Θ` is a prime Weil divisor** of `J` (for `g ≥ 1`). -/
theorem coheight_zTheta (hg : 0 < genusFK K F) : Order.coheight (zTheta P0) = 1 :=
  le_antisymm (coheight_zTheta_le_one P0 hg) (one_le_coheight_zTheta P0 hg)

theorem theta_mem_weilDivisors (hg : 0 < genusFK K F) : Theta P0 ∈ weilDivisors (Jac K F).left := by
  intro z hz
  rw [Theta_apply] at hz
  split_ifs at hz with h
  · rw [h]; exact coheight_zTheta P0 hg
  · exact absurd rfl hz

end Codim

end RamanujanPetersson.ThetaSquare

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

instance isReduced_JacJac : IsReduced (Jac K F ⊗ Jac K F).left := inferInstance

instance lft_JacJac : LocallyOfFiniteType (Jac K F ⊗ Jac K F).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

instance smooth_JacJac : Smooth (Jac K F ⊗ Jac K F).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

example : Smooth (Jac K F).hom := inferInstance

end JJ

end RamanujanPetersson.JacFrob

end


