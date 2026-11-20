-- Prove2me | Definitions.Def_RPLib_F2_059
-- name    : RPLib_F2_059
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T21:21:02.925034+00:00
-- url     : https://prove2.me/theorems/e833d907-59af-4012-8dd8-2e9d429e38e8
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 059 of 70
-- statement:
--   File 059 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_ThetaSquare_Pts`: Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`
--   * `S4.Def_RP_ThetaSquare_Codim`: Unit S4-ThetaSquare, file Codim: `Θ` is a prime Weil divisor (`coheight (zTheta P0) = 1`)
--   * `S4.Def_RP_ThetaSquare_Sep`: Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)
--   * `S4.Def_RP_ThetaSquare_ThetaX0`: Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`
--   * `S4.Def_RP_ThetaSquare_PlusX`: Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map
--   * `S4.Def_RP_ThetaSquare_Mult2`: Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)
--   * `S4.Def_RP_ThetaSquare_Curve1`: Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)
--   * `S4.Def_RP_ThetaSquare_Curve2`: Unit S4-ThetaSquare, file Curve2: the support of `D_e` on `K`-points (T4c, part 2; Riemann-Roch only)
--   * `S4.Def_RP_ThetaSquare_Curve3`: Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)
--   * `S4.Def_RP_ThetaSquare_Curve5`: Unit S4-ThetaSquare, file Curve5: the pull-back `D_e` as a divisor, and the curve-level square (T4c (C), T5)
--   * `S4.Def_RP_ThetaSquare_Curve6`: Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)
--   * `S4.Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
--   * `S4.Def_RP_ThetaSquare_Curve8`: Unit S4-ThetaSquare, file Curve8: points of `X1^g` (T4c (D), nonemptiness, part 1)
--   * `S4.Def_RP_ThetaSquare_Curve9`: Unit S4-ThetaSquare, file Curve9: the good open set is nonempty and dense (T4c (D), nonemptiness, part 2)
--   * `S4.Def_RP_ThetaCube_Deg`: S4-ThetaCube, T8a: the inputs `hD` and `hproj` of DegPoly for the theta divisor
--   * `S4.Def_RP_ThetaCube_Cover`: S4-ThetaCube, file Cover (D-A, rest): the line test on `X1^n`
--   * `S4.Def_RP_ThetaCube_CubeZ`: S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`
--   * `S4.Def_RP_ThetaCube_Sym`: S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_058

/-!
# Ramanujan-Petersson curve library (flat edition), file 059 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_ThetaSquare_Pts`: Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`
* `S4.Def_RP_ThetaSquare_Codim`: Unit S4-ThetaSquare, file Codim: `Θ` is a prime Weil divisor (`coheight (zTheta P0) = 1`)
* `S4.Def_RP_ThetaSquare_Sep`: Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)
* `S4.Def_RP_ThetaSquare_ThetaX0`: Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`
* `S4.Def_RP_ThetaSquare_PlusX`: Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map
* `S4.Def_RP_ThetaSquare_Mult2`: Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)
* `S4.Def_RP_ThetaSquare_Curve1`: Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)
* `S4.Def_RP_ThetaSquare_Curve2`: Unit S4-ThetaSquare, file Curve2: the support of `D_e` on `K`-points (T4c, part 2; Riemann-Roch only)
* `S4.Def_RP_ThetaSquare_Curve3`: Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)
* `S4.Def_RP_ThetaSquare_Curve5`: Unit S4-ThetaSquare, file Curve5: the pull-back `D_e` as a divisor, and the curve-level square (T4c (C), T5)
* `S4.Def_RP_ThetaSquare_Curve6`: Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)
* `S4.Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
* `S4.Def_RP_ThetaSquare_Curve8`: Unit S4-ThetaSquare, file Curve8: points of `X1^g` (T4c (D), nonemptiness, part 1)
* `S4.Def_RP_ThetaSquare_Curve9`: Unit S4-ThetaSquare, file Curve9: the good open set is nonempty and dense (T4c (D), nonemptiness, part 2)
* `S4.Def_RP_ThetaCube_Deg`: S4-ThetaCube, T8a: the inputs `hD` and `hproj` of DegPoly for the theta divisor
* `S4.Def_RP_ThetaCube_Cover`: S4-ThetaCube, file Cover (D-A, rest): the line test on `X1^n`
* `S4.Def_RP_ThetaCube_CubeZ`: S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`
* `S4.Def_RP_ThetaCube_Sym`: S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`
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

-- ===== S4.Def_RP_ThetaSquare_Sep =====
section

/-!
# Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)

* **`eq_one_of_stab`**: a `K`-point `c` of `J` with `W(K) · c ⊆ W` is `1` (Riemann's theorem `mem_W_iff` and the
  divisor form `mem_PrincK_of_stab`);
* `hsep_W`: translates of `W` separate `K`-points: for `b ≠ b'` some `a` has `b a ∈ W`, `b' a ∉ W`;
* `support_effI_Theta`: the support of the ideal sheaf `effI Θ` is `W`; `support_effI_Theta_ne_top`;
* **`hsep_Theta`**: the `hsep` hypothesis of `inum_pos` for `D = Θ`.
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
open RamanujanPetersson.IntersectC

universe u

section Sep

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **Translates of `W` separate `K`-points.** -/
theorem hsep_W (hg : 0 < genusFK K F) (b b' : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (hbb : b ≠ b') :
    ∃ a, pt (Jac K F) (b * a) ∈ W P0 ∧ pt (Jac K F) (b' * a) ∉ W P0 := by
  by_contra hne
  push Not at hne
  apply hbb
  have h1 := eq_one_of_stab P0 hg (b⁻¹ * b') fun w hw => by
    have hw' : b * (b⁻¹ * w) = w := by rw [← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]
    have h2 := hne (b⁻¹ * w) (by rw [hw']; exact hw)
    have heq : b' * (b⁻¹ * w) = w * (b⁻¹ * b') := (jacPicEquiv K F).injective (by
      simp only [map_mul, map_inv]
      ac_rfl)
    rw [← heq]
    exact h2
  rw [_root_.inv_mul_eq_one] at h1
  exact h1

/-- The support of the ideal sheaf of `Θ` is `W`. -/
theorem support_effI_Theta : ((effI (Theta P0)).support : Set (Jac K F).left) = W P0 := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, hxz⟩ := mem_support_effI (Theta P0) (finite_support_Theta P0) hx
    rw [Theta_apply] at hz
    split_ifs at hz with h
    · rw [← closure_zTheta P0, ← h]
      exact hxz
    · exact absurd hz (lt_irrefl 0)
  · intro hx
    have hz := mem_support_effI_of_pos (Theta P0) (finite_support_Theta P0) (z := zTheta P0)
      (by rw [Theta_apply, if_pos rfl]; exact one_pos)
    rw [← closure_zTheta P0] at hx
    exact closure_minimal (Set.singleton_subset_iff.2 hz) (effI (Theta P0)).support.isClosed hx

/-- **The `hsep` input of `IntersectC.inum_pos` for `D = Θ`.** -/
theorem hsep_Theta (hg : 0 < genusFK K F) :
    ∀ b b' : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, b ≠ b' → ∃ a,
      pt (Jac K F) (b * a) ∈ ((effI (Theta P0)).support : Set (Jac K F).left) ∧
        pt (Jac K F) (b' * a) ∉ ((effI (Theta P0)).support : Set (Jac K F).left) := by
  rw [support_effI_Theta]
  exact hsep_W P0 hg

end Sep

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_ThetaX0 =====
section

/-!
# Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`

* `pullback_openImm`: the pull-back of a Weil divisor along an open immersion is its restriction;
* `tauX d`, an open immersion, dominant; `pullback_tauX_apply`: `τ_d^* Θ` is the indicator of `τ_d⁻¹ (zTheta)`;
* `exists_eta`: if `τ_d y ∈ W`, then `zTheta = τ_d η'` for some `η' ⤳ y`;
* `exists_sep`: finitely many `K`-points of `Rfin` off a finite set `S` are common zeros of an `s` that has no zero on `S`;
* `normS_mem_eta` (the upper-bound input of the plus-curve trick): if `φ(t) = 0` and some chart point `A` contains `φ`
  but no other zero of `t`, then `Nm(t)` vanishes at the point `η'` with `τ_{c_φ⁻¹} η' = zTheta`. Proof: a minimal prime
  `q ⊆ m_A` of `(Nm t)` has height `≤ 1` (Krull); every closed point of `V(Nm t)` contains a zero of `t`, so it lies on
  `τ⁻¹ W` (if that zero is `φ`, `mem_transl_W`) or on `V(Nm s)` (`s` vanishing at the other zeros, none on `A`); by
  Jacobson `q ∈ τ⁻¹ W`, and `coheight zTheta = 1` forces `τ q = zTheta`.
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

section General

open CategoryTheory AlgebraicGeometry

variable {U C : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [IsIntegral C] [IsLocallyNoetherian C]
  [∀ y : C, UniqueFactorizationMonoid (C.presheaf.stalk y)] (ι : U ⟶ C) [IsOpenImmersion ι] [IsDominant ι]

end General

section ThetaX0

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- If `τ_d y ∈ W`, the generic point `zTheta` is `τ_d η'` for a generization `η'` of `y`. -/
theorem exists_eta (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {y : X0 K F} (hy : tauX d y ∈ W P0) :
    ∃ z : X0 K F, tauX d z = zTheta P0 ∧ z ⤳ y := by
  have h1 : zTheta P0 ⤳ tauX d y := specializes_iff_mem_closure.2 (by rw [closure_zTheta P0]; exact hy)
  obtain ⟨z, hz⟩ : zTheta P0 ∈ Set.range (tauX d) :=
    h1.mem_open (tauX d).isOpenEmbedding.isOpen_range ⟨y, rfl⟩
  refine ⟨z, hz, ?_⟩
  rw [← (tauX d).isOpenEmbedding.toIsEmbedding.toIsInducing.specializes_iff, hz]
  exact h1

end ThetaX0

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_PlusX =====
section

/-!
# Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map

`plusX c0 a i0 : Spec R2 ⟶ X1` (through the chart `{c0}`) and the constant `cE a i0 P0` (class `[E] + [P0] - [Θ]`)
satisfy **`plus_eq`**: `(const cE) * (plusX ≫ AJ_{P0}) = jMap lawMapPlus` (`Spec R2 → X0 → J`).
Also `exists_eq_kptO` (every `K`-point of `Spec R` is `kptO x`) and `finiteType_R1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.JacComplete RamanujanPetersson.RR
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

universe u

section KptO

variable {K : Type u} [Field K]

end KptO

section PlusX

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (c0 : K)

variable [IsAlgClosed K]

variable (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F)) (P0 : Place K F)

theorem kptO_plus (x : R2 c0 a i0 →ₐ[K] K) :
    kptO x ≫ ((toUnit (specO K (R2 c0 a i0)) ≫ cE a i0 P0) * (plusX c0 a i0 ≫ ajO P0)) =
      kptO x ≫ jMap K F (lawMapPlus c0 a i0) := by
  rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (kptO x ≫ toUnit (specO K (R2 c0 a i0))) (𝟙 _),
    Category.id_comp, kptO_plusX_ajO]
  apply (jacPicEquiv K F).injective
  rw [map_mul, cE, ajK, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
  apply Subtype.ext
  rw [AddSubgroup.coe_add, jacPicEquiv_jMap K F (lawMapPlus c0 a i0) x, psiJ_lawMapPlus]
  show clsK K F (plusE a i0) + clsK K F (Finsupp.single P0 1) - thetaK K F +
    (clsK K F (Finsupp.single (Sum.inl (ptP (ptR2 c0 a i0 x))) 1) - clsK K F (Finsupp.single P0 1)) = _
  abel

/-- **The plus-curve is a translate of the Abel-Jacobi map**: `cE · (plusX ≫ AJ) = Spec R2 → X0 → J`. -/
theorem plus_eq : (toUnit (specO K (R2 c0 a i0)) ≫ cE a i0 P0) * (plusX c0 a i0 ≫ ajO P0) =
    jMap K F (lawMapPlus c0 a i0) := by
  refine (lawChunk K F).hom_ext_kpt (by show IsReduced (Spec (.of (R2 c0 a i0))); infer_instance)
    (by show LocallyOfFiniteType (sR K (R2 c0 a i0)); infer_instance) _ _ fun p => ?_
  obtain ⟨x, rfl⟩ := exists_eq_kptO p
  exact congrArg (lawChunk K F).kval (kptO_plus c0 a i0 P0 x)

end PlusX

end RamanujanPetersson.ThetaSquare


end

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

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

variable (hg : 0 < genusFK K F) (c : (Rfin K F →ₐ[K] K) → (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F))
  (hc : ∀ φ, ((Multiplicative.toAdd (jacPicEquiv K F (c φ)) : Pic0K K F) : PicK K F) =
    clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F)

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

variable (P0 : Place K F)

/-- `f_e (q) ∈ W` in terms of classes (Riemann's theorem). -/
theorem mem_W_fe (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    feX P0 e (q.left (IsLocalRing.closedPoint K)) ∈ W P0 ↔
      ∃ t : Fin (n0 K F) → Place K F, jacPicEquiv K F ((q ≫ ajO P0) * e) =
        Multiplicative.ofAdd (∑ i, ajCls K F P0 (t i)) := by
  rw [feX_kpt, mem_W_iff, comp_fe]

theorem theta_eq_zero_of_not_mem {w : (Jac K F).left} (hw : w ∉ W P0) : Theta P0 w = 0 := by
  rw [Theta_apply, if_neg]
  rintro rfl
  exact hw (by rw [← closure_zTheta P0]; exact subset_closure (Set.mem_singleton _))

variable (hg : 0 < genusFK K F)

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

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

end Curve1

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

section Geom

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Support of `D_e` on `K`-points, set form** (Milne III.6.7): if the class of `e` is `[W0 - G] - (g-2)[P0]`
with `G ≥ 0`, `deg G = g`, `ℓ(G) = 1`, then `f_e(q) ∈ W` iff `q ∈ supp G`. -/
theorem mem_W_fe_iff (hg : 0 < genusFK K F) (P0 : Place K F) {W0 G : Places.Divisor K F}
    (hW : IsCanonicalFK K F W0) (hG : 0 ≤ G) (hd : G.deg = genusFK K F) (h1 : ellFK K F G = 1)
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (he : ((Multiplicative.toAdd (jacPicEquiv K F e) : Pic0K K F) : PicK K F) =
      clsK K F (W0 - G) - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1))
    (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    feX P0 e (q.left (IsLocalRing.closedPoint K)) ∈ W P0 ↔ 1 ≤ G (kPl q) := by
  rw [mem_W_fe, ← eff_iff_mem_supp hW hG hd h1 (kPl q), ← exists_sum_ajCls_iff hg P0 hW hd _ he (kPl q)]
  refine exists_congr fun t => ?_
  rw [_root_.map_mul, jacPicEquiv_ajO, ← ofAdd_toAdd (jacPicEquiv K F e), ← ofAdd_add]
  exact Multiplicative.ofAdd.injective.eq_iff

end Geom

end Curve2

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve3 =====
section

/-!
# Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)

* `div_pow_of_div`, `le_ell_single`: if `div f = [Q'] - [Q]` with `Q ≠ Q'` then `ℓ(n[Q]) ≥ n + 1` for all `n`;
* **`eq_of_clsK_single`** (Abel for one point, `g ≥ 1`): `[Q] ~ [Q'] ⇒ Q = Q'`; `ajK_injective`;
* `kPl_kptO_plusX`: the place of the plus-curve point at `x` is `ptR2 x`; `kPl_chart`: the place of a chart point;
* **`exists_chart0`**: every `K`-point `q` of `X1` lies in a chart `{c0}`, at a point centered at `kPl q`;
  `xcR_ne_of_isCenter`: then `x - c0` does not vanish at that place;
* **`eq_iota2`**: if `ptR2 x` is the place of `q` (chart `{c0}` from `exists_chart0`), then `q = ι2 (kpt x)`.
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

section Abel

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

end Abel

section Geom

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **The plus chart through a `K`-point**: if `ptR2 x` is the place of `q` and `q` sits in the chart `{c0}`
(`exists_chart0`), then `q = ι2 (kpt x)`. -/
theorem eq_iota2 {q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F} {c0 : K} {ψ0 : SymRing K (Bc F c0) 1 →ₐ[K] K}
    (hc : IsCenter (kPl q) (ψ0.comp diag1))
    (hq : q.left (IsLocalRing.closedPoint K) = colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (op (idx0 c0))
        (kpt (A := SymRing K (Bc F c0) 1) ψ0))
    (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F)) (x : R2 c0 a i0 →ₐ[K] K)
    (hx : (Sum.inl (ptP (ptR2 c0 a i0 x)) : Place K F) = kPl q) :
    q.left (IsLocalRing.closedPoint K) = ι2 c0 a i0 (kpt x) := by
  have h2 : IsCenter (kPl q) ((x.comp (symToR2 c0 a i0)).comp diag1) := by
    rw [symToR2_diag1, ← hx]
    exact isCenter_R1 c0 (x.comp (awayι (K := K) (plusH c0 a i0)))
  have heq : ψ0.comp diag1 = (x.comp (symToR2 c0 a i0)).comp diag1 :=
    eq_of_zero_imp fun b hb => (h2.2 b).1 ((hc.2 b).2 hb)
  have heq' : ψ0 = x.comp (symToR2 c0 a i0) := by
    refine AlgHom.ext fun s => ?_
    have h5 := congrArg (fun φ => φ (undiag1 s)) heq
    simpa only [AlgHom.comp_apply, diag1_undiag1] using h5
  rw [hq, heq', ← SpecMap_kpt]
  rfl

end Geom

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve5 =====
section

/-!
# Unit S4-ThetaSquare, file Curve5: the pull-back `D_e` as a divisor, and the curve-level square (T4c (C), T5)

* `IsGoodFor P0 W0 e G`: the hypotheses under which `D_e = AJ^*(Θ translated by e)` is the reduced divisor `G`
  (`G ≥ 0` reduced of degree `g` with `ℓ(G) = 1`, the class of `e` is `[W0 - G] - (g-2)[P0]`, `f_e` avoids `Θ`, and for
  each `v ∈ G` the class `W0 - G + 2[v]` has `ℓ = 1` and contains the divisor of an `X0` point);
* **`Dc_kpt_eq`**: then `D_e (q) = G (kPl q)` at every `K`-point `q` of `X1`; `Dc_generic`: `D_e (η) = 0`;
* `sub_mem_PrincK`: `e1 e2 = e3 e4` forces `G1 + G2 - G3 - G4 ∈ PrincK`;
* **`square_curve`** (the curve-level theorem of the square): for good `e1, e2, e3, e4` with `e1 e2 = e3 e4`, the cycle
  `D_{e1} + D_{e2} - D_{e3} - D_{e4}` on `X1` is the principal divisor `G1 + G2 - G3 - G4` (on `K`-points, and `0` at `η`).
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

section Curve5

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **`e` is good for `G`**: the hypotheses under which `D_e` is the reduced divisor `G`. -/
structure IsGoodFor (P0 : Place K F) (W0 : Places.Divisor K F) (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (G : Places.Divisor K F) : Prop where
  nonneg : 0 ≤ G
  deg : G.deg = genusFK K F
  ell : ellFK K F G = 1
  red : ∀ v, G v ≤ 1
  cls : ((Multiplicative.toAdd (jacPicEquiv K F e) : Pic0K K F) : PicK K F) =
    clsK K F (W0 - G) - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1)
  avoid : Avoid (feX P0 e) (Theta P0)
  ptX0 : ∀ v, 1 ≤ G v → ellFK K F (W0 - G + Finsupp.single v 2) = 1 ∧
    ∃ yR : LawRing K F →ₐ[K] K, clsK K F (Zdiv (ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)))) =
      clsK K F (W0 - G + Finsupp.single v 2)

end Curve5

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

/-- Every place is the place of a `K`-point of `X1`. -/
theorem exists_kPl_eq (hg : 0 < genusFK K F) (P0 v : Place K F) :
    ∃ q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F, kPl q = v := by
  obtain ⟨q, hq⟩ := exists_kX1 P0 v
  exact ⟨q, ajK_injective hg P0 ((kPl_spec P0 q).symm.trans hq)⟩

/-- `e ∉ W` makes `f_e` avoid `Θ` (`f_e (P0) = e`). -/
theorem avoid_of_not_mem (P0 : Place K F) {e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F}
    (ha : e.left (IsLocalRing.closedPoint K) ∉ W P0) : Avoid (feX P0 e) (Theta P0) := by
  obtain ⟨q0, hq0⟩ := exists_kX1 P0 P0
  refine avoid_Theta P0 (feX P0 e) (y := q0.left (IsLocalRing.closedPoint K)) ?_
  rw [feX_kpt, comp_fe, hq0, ajK_self, _root_.one_mul]
  exact ha

/-- **Goodness from classes**: `G ≥ 0` reduced of degree `g`, `[e] = [W0 - G] - (g-2)[P0]`, `e ∉ W`, and
`AJ(q)² e c_2 ∈ jX0 (X0)` whenever `f_e (q) ∈ W`. -/
theorem isGoodFor_of_cls (hg : 0 < genusFK K F) (P0 : Place K F) {W0 G : Places.Divisor K F}
    (hW : IsCanonicalFK K F W0) {c2 e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F}
    (hc2 : ((Multiplicative.toAdd (jacPicEquiv K F c2) : Pic0K K F) : PicK K F) =
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (hG0 : 0 ≤ G) (hd : G.deg = genusFK K F) (hred : ∀ v, G v ≤ 1)
    (he : ((Multiplicative.toAdd (jacPicEquiv K F e) : Pic0K K F) : PicK K F) =
      clsK K F (W0 - G) - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1))
    (ha : e.left (IsLocalRing.closedPoint K) ∉ W P0)
    (hc : ∀ q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F, feX P0 e (q.left (IsLocalRing.closedPoint K)) ∈ W P0 →
      ((q ≫ ajO P0) * (q ≫ ajO P0) * e * c2).left (IsLocalRing.closedPoint K) ∈ Set.range (jX0 K F)) :
    IsGoodFor P0 W0 e G := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have h1 : ellFK K F G = 1 := by
    have hrr := riemannRochFK' hk hW G
    rw [hd] at hrr
    have h0 : ellFK K F (W0 - G) = 0 := by
      by_contra hne
      obtain ⟨E, hE, hcE⟩ := (one_le_ell_iff (W0 - G)).1 (by omega)
      have hex : ∃ E' : Places.Divisor K F, 0 ≤ E' ∧
          clsK K F E' = clsK K F (W0 - G + Finsupp.single P0 1) :=
        ⟨E + Finsupp.single P0 1, add_nonneg hE (Finsupp.single_nonneg.2 zero_le_one), by
          rw [clsK_add (K := K) (F := F), hcE, ← clsK_add (K := K) (F := F)]⟩
      obtain ⟨t, ht⟩ := (exists_sum_ajCls_iff hg P0 hW hd _ he P0).2 hex
      rw [ajCls_self, zero_add] at ht
      exact ha ((mem_W_iff P0 e).2 ⟨t, by rw [← ht, ofAdd_toAdd]⟩)
    omega
  refine ⟨hG0, hd, h1, hred, he, avoid_of_not_mem P0 ha,
    fun v hv => ⟨ell_two_eq_one hW hG0 hd h1 hred v, ?_⟩⟩
  obtain ⟨q, rfl⟩ := exists_kPl_eq hg P0 v
  obtain ⟨yR, hyR⟩ := exists_kJ _ (hc q ((mem_W_fe_iff hg P0 hW hG0 hd h1 e he q).2 hv))
  refine ⟨yR, ?_⟩
  have h := cls_kJ yR
  rw [hyR] at h
  simp only [_root_.map_mul, toAdd_mul, AddSubgroup.coe_add] at h
  rw [jacPicEquiv_ajO, toAdd_ofAdd, coe_ajCls, he, hc2, sub_zsmul] at h
  have h2 : (Finsupp.single (kPl q) (2 : ℤ) : Places.Divisor K F) =
      Finsupp.single (kPl q) 1 + Finsupp.single (kPl q) 1 := by
    rw [← Finsupp.single_add]
    norm_num
  rw [h2, clsK_add (K := K) (F := F), clsK_add (K := K) (F := F)]
  calc clsK K F (Zdiv (ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)))) =
      (clsK K F (Zdiv (ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)))) - thetaK K F) + thetaK K F := by abel
    _ = _ := by rw [← h]; abel

/-- **`K`-point reduction** (T4c (D)): for constants `c_K`, `c_2` of classes `[W0] - (g-2)[P0] - [Θ]` and
`g[P0] - [Θ]`, a `K`-point `e ∉ W` with `c_K e⁻¹ ∈ jX0 (X0)` and `AJ(q)² e c_2 ∈ jX0 (X0)` whenever
`f_e (q) ∈ W` is good for `G := Zdiv` of the `X0` point of `c_K e⁻¹`. -/
theorem isGoodFor_of (hg : 0 < genusFK K F) (P0 : Place K F) {W0 : Places.Divisor K F}
    (hW : IsCanonicalFK K F W0) {cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F}
    (hcK : ((Multiplicative.toAdd (jacPicEquiv K F cK) : Pic0K K F) : PicK K F) =
        clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (hc2 : ((Multiplicative.toAdd (jacPicEquiv K F c2) : Pic0K K F) : PicK K F) =
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (ha : e.left (IsLocalRing.closedPoint K) ∉ W P0)
    (hb : (cK * e⁻¹).left (IsLocalRing.closedPoint K) ∈ Set.range (jX0 K F))
    (hc : ∀ q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F, feX P0 e (q.left (IsLocalRing.closedPoint K)) ∈ W P0 →
      ((q ≫ ajO P0) * (q ≫ ajO P0) * e * c2).left (IsLocalRing.closedPoint K) ∈ Set.range (jX0 K F)) :
    ∃ G, IsGoodFor P0 W0 e G := by
  obtain ⟨yR, hyR⟩ := exists_kJ _ hb
  refine ⟨Zdiv (ptSet (yR.comp (awayι (K := K) (lawPre K F).u0))),
    isGoodFor_of_cls hg P0 hW hc2 (Zdiv_nonneg _) ?_ (Zdiv_le_one _) ?_ ha hc⟩
  · rw [deg_Zdiv, card_lawPt]
  · have h := cls_kJ yR
    rw [hyR] at h
    simp only [_root_.map_mul, map_inv, toAdd_mul, toAdd_inv, AddSubgroup.coe_add, AddSubgroup.coe_neg] at h
    rw [hcK] at h
    rw [clsK_sub]
    calc ((Multiplicative.toAdd (jacPicEquiv K F e) : Pic0K K F) : PicK K F) =
        (clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) - thetaK K F) -
          (clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) - thetaK K F +
            -((Multiplicative.toAdd (jacPicEquiv K F e) : Pic0K K F) : PicK K F)) := by abel
      _ = _ := by rw [h]; abel

end Curve6

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve7 =====
section

/-!
# Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)

* `kapM cK : J ⟶ J`, `e ↦ c_K e⁻¹`; `mu1 P0 : J × X1 ⟶ J`, `(e, q) ↦ AJ(q) e`; `mu2 P0 c2`, `(e, q) ↦ AJ(q)² e c_2`;
* `Bad P0 c2 := mu1⁻¹ W ∩ mu2⁻¹ (J \ jX0 (X0))`, closed in `J × X1`;
* **`Ogood P0 cK c2 := Wᶜ ∩ kapM⁻¹ (jX0 (X0)) ∩ (pr_J Bad)ᶜ`**, open (`isOpen_Ogood`: `pr_J` is closed, `X1` proper);
* **`isGoodFor_of_mem`**: every `K`-point of `Ogood` is good;
* `not_mem_image_Bad`, `mem_Ogood_of`: the converse criterion (all `K`-points `(e, q)` off `Bad`).
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

section Curve7

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)

theorem isClosed_Bad : IsClosed (Bad P0 c2) :=
  ((isClosed_W P0).preimage (mu1 P0).left.continuous).inter
    (isOpen_range_jX0.isClosed_compl.preimage (mu2 P0 c2).left.continuous)

theorem isOpen_Ogood : IsOpen (Ogood P0 cK c2) :=
  ((isClosed_W P0).isOpen_compl.inter (isOpen_range_jX0.preimage (kapM cK).left.continuous)).inter
    ((fst (Jac K F) (X1O K F)).left.isClosedMap _ (isClosed_Bad P0 c2)).isOpen_compl

/-- **Every `K`-point of `Ogood` is good.** -/
theorem isGoodFor_of_mem (hg : 0 < genusFK K F) {W0 : Places.Divisor K F} (hW : IsCanonicalFK K F W0)
    {cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F}
    (hcK : ((Multiplicative.toAdd (jacPicEquiv K F cK) : Pic0K K F) : PicK K F) =
        clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (hc2 : ((Multiplicative.toAdd (jacPicEquiv K F c2) : Pic0K K F) : PicK K F) =
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (he : e.left (IsLocalRing.closedPoint K) ∈ Ogood P0 cK c2) :
    ∃ G, IsGoodFor P0 W0 e G := by
  obtain ⟨⟨ha, hb⟩, hc⟩ := he
  refine isGoodFor_of hg P0 hW hcK hc2 e ha (by rw [pt_comp_kapM]; exact hb) fun q hq => ?_
  by_contra hn
  apply hc
  refine ⟨(lift e q).left (IsLocalRing.closedPoint K), ⟨?_, ?_⟩, ?_⟩
  · show (lift e q ≫ mu1 P0).left (IsLocalRing.closedPoint K) ∈ W P0
    rw [comp_mu1]
    exact hq
  · show (lift e q ≫ mu2 P0 c2).left (IsLocalRing.closedPoint K) ∉ Set.range (jX0 K F)
    rw [comp_mu2]
    exact hn
  · show (lift e q ≫ fst (Jac K F) (X1O K F)).left (IsLocalRing.closedPoint K) = _
    rw [lift_fst]

/-- If no `K`-point `(e, q)` is bad, the closed point `e` is off `pr_J Bad`
(a closed point of the fibre over `e` is a `K`-point). -/
theorem not_mem_image_Bad (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (h : ∀ q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F, (lift e q).left (IsLocalRing.closedPoint K) ∉ Bad P0 c2) :
    e.left (IsLocalRing.closedPoint K) ∉ (fst (Jac K F) (X1O K F)).left '' Bad P0 c2 := by
  rintro ⟨z, hz, hze⟩
  have hcl : IsClosed ({e.left (IsLocalRing.closedPoint K)} : Set (Jac K F).left) :=
    (pointEquivClosedPoint (Jac K F).hom ⟨e.left, Over.w e⟩).2
  haveI : LocallyOfFiniteType (Jac K F ⊗ X1O K F).hom := by
    show LocallyOfFiniteType (pullback.fst (Jac K F).hom (toSpecK K (algebraMap K[X] F X) 1) ≫ (Jac K F).hom)
    infer_instance
  haveI : JacobsonSpace (Jac K F ⊗ X1O K F).left := LocallyOfFiniteType.jacobsonSpace (Jac K F ⊗ X1O K F).hom
  obtain ⟨z', ⟨hz'B, hz'e⟩, hz'c⟩ := nonempty_inter_closedPoints
    (Z := Bad P0 c2 ∩ (fst (Jac K F) (X1O K F)).left ⁻¹' {e.left (IsLocalRing.closedPoint K)}) ⟨z, hz, hze⟩
    ((isClosed_Bad P0 c2).inter (hcl.preimage (fst (Jac K F) (X1O K F)).left.continuous)).isLocallyClosed
  let p : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F ⊗ X1O K F :=
    Over.homMk (pointOfClosedPoint (Jac K F ⊗ X1O K F).hom z' hz'c) (pointOfClosedPoint_comp _ _ _)
  have hp : p.left (IsLocalRing.closedPoint K) = z' :=
    pointOfClosedPoint_apply (Jac K F ⊗ X1O K F).hom z' hz'c _
  have hpe : p ≫ fst (Jac K F) (X1O K F) = e := by
    apply Over.OverMorphism.ext
    refine ext_of_apply_closedPoint_eq (Jac K F).hom (Over.w _) (Over.w _) ?_
    show (fst (Jac K F) (X1O K F)).left (p.left (IsLocalRing.closedPoint K)) = _
    rw [hp]
    exact hz'e
  apply h (p ≫ snd (Jac K F) (X1O K F))
  rw [← hpe, lift_comp_fst_snd, hp]
  exact hz'B

/-- **Criterion for `Ogood`**: `e ∉ W`, `c_K e⁻¹ ∈ jX0 (X0)`, and `AJ(q)² e c_2 ∈ jX0 (X0)` whenever `f_e (q) ∈ W`. -/
theorem mem_Ogood_of (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (ha : e.left (IsLocalRing.closedPoint K) ∉ W P0)
    (hb : (cK * e⁻¹).left (IsLocalRing.closedPoint K) ∈ Set.range (jX0 K F))
    (hc : ∀ q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F, feX P0 e (q.left (IsLocalRing.closedPoint K)) ∈ W P0 →
      ((q ≫ ajO P0) * (q ≫ ajO P0) * e * c2).left (IsLocalRing.closedPoint K) ∈ Set.range (jX0 K F)) :
    e.left (IsLocalRing.closedPoint K) ∈ Ogood P0 cK c2 := by
  refine ⟨⟨ha, by
    show (kapM cK).left (e.left (IsLocalRing.closedPoint K)) ∈ Set.range (jX0 K F)
    rw [← pt_comp_kapM]; exact hb⟩, not_mem_image_Bad P0 c2 e fun q ⟨h1, h2⟩ => h2 ?_⟩
  have h1' : (lift e q ≫ mu1 P0).left (IsLocalRing.closedPoint K) ∈ W P0 := h1
  rw [comp_mu1] at h1'
  show (lift e q ≫ mu2 P0 c2).left (IsLocalRing.closedPoint K) ∈ Set.range (jX0 K F)
  rw [comp_mu2]
  exact hc q h1'

end Curve7

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

/-- A `K`-point of `X1^n` with prescribed coordinates. -/
theorem exists_pt_coord (hg : 0 < genusFK K F) (P0 : Place K F) :
    ∀ (n : ℕ) (t : Fin n → Place K F), ∃ p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n,
      ∀ i, kPl (p ≫ prj K F n i) = t i
  | 0, _ => ⟨𝟙 _, fun i => i.elim0⟩
  | n + 1, t => by
    obtain ⟨p, hp⟩ := exists_pt_coord hg P0 n (fun i => t (Fin.castSucc i))
    obtain ⟨q, hq⟩ := exists_kPl_eq hg P0 (t (Fin.last n))
    refine ⟨lift p q, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · show kPl (lift p q ≫ (Fin.lastCases (snd (PP K F n) (X1O K F))
        (fun j => fst (PP K F n) (X1O K F) ≫ prj K F n j) (Fin.last n) : PP K F n ⊗ X1O K F ⟶ X1O K F)) = _
      rw [Fin.lastCases_last, lift_snd, hq]
    · show kPl (lift p q ≫ (Fin.lastCases (snd (PP K F n) (X1O K F))
        (fun j => fst (PP K F n) (X1O K F) ≫ prj K F n j) (Fin.castSucc j) : PP K F n ⊗ X1O K F ⟶ X1O K F)) = _
      rw [Fin.lastCases_castSucc, lift_fst_assoc, hp]

/-- `ℓ(G) = 1` when `deg G = g` and the class `[W0 - G] - (g-2)[P0]` of `e` is off `W`. -/
theorem ell_eq_one_of_not_mem (hg : 0 < genusFK K F) (P0 : Place K F) {W0 G : Places.Divisor K F}
    (hW : IsCanonicalFK K F W0) (hd : G.deg = genusFK K F) {e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F}
    (he : ((Multiplicative.toAdd (jacPicEquiv K F e) : Pic0K K F) : PicK K F) =
      clsK K F (W0 - G) - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1))
    (ha : e.left (IsLocalRing.closedPoint K) ∉ W P0) : ellFK K F G = 1 := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have hrr := riemannRochFK' hk hW G
  rw [hd] at hrr
  have h0 : ellFK K F (W0 - G) = 0 := by
    by_contra hne
    obtain ⟨E, hE, hcE⟩ := (one_le_ell_iff (W0 - G)).1 (by omega)
    have hex : ∃ E' : Places.Divisor K F, 0 ≤ E' ∧
        clsK K F E' = clsK K F (W0 - G + Finsupp.single P0 1) :=
      ⟨E + Finsupp.single P0 1, add_nonneg hE (Finsupp.single_nonneg.2 zero_le_one), by
        rw [clsK_add (K := K) (F := F), hcE, ← clsK_add (K := K) (F := F)]⟩
    obtain ⟨t, ht⟩ := (exists_sum_ajCls_iff hg P0 hW hd _ he P0).2 hex
    rw [ajCls_self, zero_add] at ht
    exact ha ((mem_W_iff P0 e).2 ⟨t, by rw [← ht, ofAdd_toAdd]⟩)
  omega

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

theorem nonempty_Ub (hg : 0 < genusFK K F) : (Ub P0 c3).Nonempty := by
  obtain ⟨x, hx⟩ := exists_not_mem_W P0 hg
  obtain ⟨p, hp⟩ := eM_surj P0 c3 x
  refine ⟨p.left (IsLocalRing.closedPoint K), ?_⟩
  show (p ≫ eM P0 c3).left (IsLocalRing.closedPoint K) ∉ W P0
  rw [hp]
  exact hx

theorem nonempty_Uj (hg : 0 < genusFK K F) {W0 : Places.Divisor K F} (hW : IsCanonicalFK K F W0)
    {c2 c3 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F}
    (hc2 : ((Multiplicative.toAdd (jacPicEquiv K F c2) : Pic0K K F) : PicK K F) =
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (hc3 : ((Multiplicative.toAdd (jacPicEquiv K F c3) : Pic0K K F) : PicK K F) =
        clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) -
          (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1))
    (j : Fin (genusFK K F)) : (Uj P0 c2 c3 j).Nonempty := by
  obtain ⟨y0⟩ := exists_y0 (K := K) (F := F)
  obtain ⟨s, hs⟩ := exists_sum_single_of_nonneg (genusFK K F)
    (Zdiv_nonneg (ptSet (y0.comp (awayι (K := K) (lawPre K F).u0)))) (by rw [deg_Zdiv, card_lawPt])
  obtain ⟨t, htj, hts⟩ := exists_t_swap hW s j
  obtain ⟨p, hp⟩ := exists_pt_coord hg P0 (genusFK K F) t
  have hv : p ≫ (lift (eM P0 c3) (prj K F (genusFK K F) j) ≫ mu2 P0 c2) = kJ y0 := by
    rw [← Category.assoc, comp_lift, comp_mu2]
    apply (jacPicEquiv K F).injective
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [cls_kJ]
    simp only [_root_.map_mul, toAdd_mul, AddSubgroup.coe_add]
    rw [jacPicEquiv_ajO, toAdd_ofAdd, coe_ajCls, cls_eM P0 hc3, hc2]
    simp only [hp]
    rw [htj, hs, ← hts, sub_zsmul]
    have h2 : (Finsupp.single (s j) (2 : ℤ) : Places.Divisor K F) =
        Finsupp.single (s j) 1 + Finsupp.single (s j) 1 := by
      rw [← Finsupp.single_add]
      norm_num
    rw [h2, clsK_add (K := K) (F := F), clsK_add (K := K) (F := F)]
    abel
  refine ⟨p.left (IsLocalRing.closedPoint K), ?_⟩
  show (p ≫ (lift (eM P0 c3) (prj K F (genusFK K F) j) ≫ mu2 P0 c2)).left (IsLocalRing.closedPoint K) ∈
    Set.range (jX0 K F)
  rw [hv, pt_kJ]
  exact ⟨_, rfl⟩

/-- A `K`-point of `X1^g` in `Ua ∩ Ub ∩ ⋂ Uj` gives a point `e_M(p)` of `Ogood`. -/
theorem mem_Ogood_of_U (hg : 0 < genusFK K F) {W0 : Places.Divisor K F} (hW : IsCanonicalFK K F W0)
    {c3 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F}
    (hc3 : ((Multiplicative.toAdd (jacPicEquiv K F c3) : Pic0K K F) : PicK K F) =
        clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) -
          (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1))
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F (genusFK K F))
    (ha : p.left (IsLocalRing.closedPoint K) ∈ Ua P0 cK c3) (hb : p.left (IsLocalRing.closedPoint K) ∈ Ub P0 c3)
    (hc : ∀ j, p.left (IsLocalRing.closedPoint K) ∈ Uj P0 c2 c3 j) :
    (p ≫ eM P0 c3).left (IsLocalRing.closedPoint K) ∈ Ogood P0 cK c2 := by
  have he := cls_eM P0 hc3 p
  have hD0 : (0 : Places.Divisor K F) ≤ ∑ i, Finsupp.single (kPl (p ≫ prj K F (genusFK K F) i)) 1 :=
    Finset.sum_nonneg fun i _ => Finsupp.single_nonneg.2 zero_le_one
  have hd : (∑ i, Finsupp.single (kPl (p ≫ prj K F (genusFK K F) i)) (1 : ℤ) : Places.Divisor K F).deg =
      genusFK K F := deg_sum_single _
  have hb' : (p ≫ eM P0 c3).left (IsLocalRing.closedPoint K) ∉ W P0 := hb
  have h1 := ell_eq_one_of_not_mem hg P0 hW hd he hb'
  refine mem_Ogood_of P0 cK c2 _ hb' ?_ fun q hq => ?_
  · rw [pt_comp_kapM]
    exact ha
  · have hv := (mem_W_fe_iff hg P0 hW hD0 hd h1 _ he q).1 hq
    obtain ⟨j, hj⟩ : ∃ j, kPl (p ≫ prj K F (genusFK K F) j) = kPl q := by
      by_contra hne
      simp only [not_exists] at hne
      have h0 : (∑ i, Finsupp.single (kPl (p ≫ prj K F (genusFK K F) i)) (1 : ℤ) : Places.Divisor K F)
          (kPl q) = 0 := by
        rw [Finsupp.finsetSum_apply]
        exact Finset.sum_eq_zero fun i _ => by rw [Finsupp.single_apply, if_neg (hne i)]
      omega
    have hq' : q ≫ ajO P0 = (p ≫ prj K F (genusFK K F) j) ≫ ajO P0 := by
      rw [kPl_spec P0 q, kPl_spec P0 (p ≫ prj K F (genusFK K F) j), hj]
    rw [hq', ← comp_mu2 P0 c2 (p ≫ eM P0 c3) (p ≫ prj K F (genusFK K F) j), ← comp_lift, Category.assoc]
    exact hc j

/-- **`Ogood` has a `K`-point** (for any `c_K` and a `c_2` of class `g[P0] - [Θ]`). -/
theorem exists_kpt_Ogood (hg : 0 < genusFK K F) {W0 : Places.Divisor K F} (hW : IsCanonicalFK K F W0)
    {c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F}
    (hc2 : ((Multiplicative.toAdd (jacPicEquiv K F c2) : Pic0K K F) : PicK K F) =
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) - thetaK K F) :
    ∃ e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, e.left (IsLocalRing.closedPoint K) ∈ Ogood P0 cK c2 := by
  obtain ⟨c3, hc3⟩ := exists_c3 P0 hW
  have hUo : IsOpen ((Ua P0 cK c3 ∩ Ub P0 c3) ∩ ⋂ j, Uj P0 c2 c3 j) :=
    ((isOpen_Ua P0 cK c3).inter (isOpen_Ub P0 c3)).inter (isOpen_iInter_of_finite fun j => isOpen_Uj P0 c2 c3 j)
  have hU : ((Ua P0 cK c3 ∩ Ub P0 c3) ∩ ⋂ j, Uj P0 c2 c3 j).Nonempty :=
    nonempty_preirreducible_inter ((isOpen_Ua P0 cK c3).inter (isOpen_Ub P0 c3))
      (isOpen_iInter_of_finite fun j => isOpen_Uj P0 c2 c3 j)
      (nonempty_preirreducible_inter (isOpen_Ua P0 cK c3) (isOpen_Ub P0 c3) (nonempty_Ua P0 cK c3)
        (nonempty_Ub P0 c3 hg))
      (nonempty_iInter_of_open _ (fun j => isOpen_Uj P0 c2 c3 j) fun j => nonempty_Uj P0 hg hW hc2 hc3 j)
  haveI : JacobsonSpace (PP K F (genusFK K F)).left :=
    LocallyOfFiniteType.jacobsonSpace (PP K F (genusFK K F)).hom
  obtain ⟨z, hzU, hzc⟩ := nonempty_inter_closedPoints hU hUo.isLocallyClosed
  let p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F (genusFK K F) :=
    Over.homMk (pointOfClosedPoint (PP K F (genusFK K F)).hom z hzc) (pointOfClosedPoint_comp _ _ _)
  have hp : p.left (IsLocalRing.closedPoint K) = z :=
    pointOfClosedPoint_apply (PP K F (genusFK K F)).hom z hzc _
  rw [← hp] at hzU
  obtain ⟨⟨ha, hb⟩, hc⟩ := hzU
  exact ⟨_, mem_Ogood_of_U P0 cK c2 hg hW hc3 p ha hb (Set.mem_iInter.1 hc)⟩

end Curve9

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaCube_Deg =====
section

/-!
# S4-ThetaCube, T8a: the inputs `hD` and `hproj` of DegPoly for the theta divisor

* `polyEnd_one`: `1(π) = 𝟙`.
* `exists_avoid`, `cTh P0 hg φ := (φ ≫ τ_b)^* Θ` for a translate `b` whose image avoids `Θ`.
* `iform_cTh`: `(cTh φ)^g = deg φ · (Θ^g)`.
* `formTh g hdim`: the intersection form as a multilinear map (`DegPoly.formOfAdd` of `iform`).
* `hD_Th`, `hproj_Th`: the hypotheses `hD` and `hproj` of `DegPoly.degreeDataOfQuad` for
  `c G := cTh (polyEnd π G)` and `deg G := degree (polyEnd π G).left`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Poly

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

end Poly

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- Every endomorphism has a translate whose generic image avoids `Θ`. -/
lemma exists_avoid (hg : 0 < genusFK K F) (φ : Jac K F ⟶ Jac K F) [IsMonHom φ] :
    ∃ b : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, Avoid (φ ≫ transl (Jac K F) b).left (Theta P0) := by
  obtain ⟨x, hx⟩ := exists_not_mem_W P0 hg
  refine ⟨x, avoid_Theta P0 _ (y := pt (Jac K F) 1) ?_⟩
  rw [← pt_comp, ← Category.assoc, MonObj.one_comp, pt_comp, transl_pt, _root_.one_mul]
  exact hx

/-- The pulled-back theta divisor `(φ ≫ τ_b)^* Θ`, for a chosen translate `b` avoiding `Θ`. -/
noncomputable def cTh (hg : 0 < genusFK K F) (φ : Jac K F ⟶ Jac K F) [IsMonHom φ] :
    AlgebraicCycle (Jac K F).left ℤ :=
  cpull (φ ≫ transl (Jac K F) (exists_avoid P0 hg φ).choose).left (Theta P0)

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Cover =====
section

/-!
# S4-ThetaCube, file Cover (D-A, rest): the line test on `X1^n`

* `coheight_kpt_X1`: `K`-points of `X1` have codimension one (singleton chart, `Sym¹` regular of dimension one);
* **`eq_zero_of_lines`**: let `E` be a Weil divisor on `X1^n` (factorial stalks) and, for each direction `i`, `B i`
  a proper closed subset, saturated for the `i`-th lines, such that for every `K`-point `p ∉ B i` the `i`-th line
  through `p` avoids `E` and pulls `E` back to `0` at the parameter of `p`. Then `E = 0`.
  Proof: a point `y` of codimension one off some `B i` is handled by the curve test (`eq_zero_of_tests`) with the
  `i`-th lines through the closed points of `(B i)ᶜ`. If `y ∈ ⋂ B i`, then `Y = closure {y}` is a component of every
  `B i`; off the other components every line through a point of `Y` stays in `Y`, so `Y = X1^n` by `reach`, and `y`
  would be the generic point.
* `eq_zero_of_lines'`: the same with `ℓ^* E = 0` as a cycle.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Cover

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable {n : ℕ} [∀ y : (PP K F n).left, UniqueFactorizationMonoid ((PP K F n).left.presheaf.stalk y)]

/-- **The line test on `X1^n`.** -/
theorem eq_zero_of_lines {E : AlgebraicCycle (PP K F n).left ℤ} (hE : E ∈ weilDivisors (PP K F n).left)
    (B : Fin n → Set (PP K F n).left) (hB : ∀ i, IsClosed (B i)) (hBne : ∀ i, B i ≠ Set.univ)
    (hsat : ∀ i (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n), p.left (IsLocalRing.closedPoint K) ∈ B i →
      Set.range (line K F n i p).left ⊆ B i)
    (htest : ∀ i (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n), p.left (IsLocalRing.closedPoint K) ∉ B i →
      Avoid (line K F n i p).left E ∧
        cpull (line K F n i p).left E ((p ≫ prj K F n i).left (IsLocalRing.closedPoint K)) = 0) :
    E = 0 := by
  haveI : JacobsonSpace (PP K F n).left := LocallyOfFiniteType.jacobsonSpace (PP K F n).hom
  haveI : CompactSpace (PP K F n).left := QuasiCompact.compactSpace_of_compactSpace (PP K F n).hom
  haveI : IsNoetherian (PP K F n).left := {}
  have hval : ∀ i (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n),
      (line K F n i p).left ((p ≫ prj K F n i).left (IsLocalRing.closedPoint K)) =
        p.left (IsLocalRing.closedPoint K) := fun i p =>
    congrArg (fun φ => φ.left (IsLocalRing.closedPoint K)) (line_val n i p)
  refine eq_zero_of_tests (C := X1 K F) hE fun y hy => ?_
  by_cases hyB : ∃ i, y ∉ B i
  · obtain ⟨i, hi⟩ := hyB
    refine ⟨(B i)ᶜ, (hB i).isOpen_compl, hi, fun z hz hzc => ?_⟩
    obtain ⟨p, rfl⟩ := exists_kpt_of_closed (K := K) (F := F) n hzc
    obtain ⟨hA, h0⟩ := htest i p hz
    exact ⟨(line K F n i p).left, (p ≫ prj K F n i).left (IsLocalRing.closedPoint K), hval i p,
      coheight_kpt_X1 _, hA, h0⟩
  exfalso
  push Not at hyB
  set Y : Set (PP K F n).left := closure {y} with hYdef
  have hYB : ∀ i, Y ⊆ B i := fun i => closure_minimal (Set.singleton_subset_iff.mpr (hyB i)) (hB i)
  have hR : ∀ i, ∃ R : Set (PP K F n).left, IsClosed R ∧ y ∉ R ∧ B i ⊆ Y ∪ R := by
    intro i
    obtain ⟨T, hT, hST⟩ := NoetherianSpace.exists_finset_irreducible (⟨B i, hB i⟩ : Closeds (PP K F n).left)
    have hCB : ∀ C ∈ T, (C : Set (PP K F n).left) ⊆ B i := fun C hCT x hx => by
      have h : C ≤ T.sup id := Finset.le_sup (f := id) hCT
      rw [← hST] at h
      exact SetLike.coe_subset_coe.mpr h hx
    refine ⟨⋃ C ∈ {C | C ∈ T ∧ (C : Set (PP K F n).left) ≠ Y}, (C : Set (PP K F n).left), ?_, ?_, ?_⟩
    · exact (T.finite_toSet.subset fun C hC => hC.1).isClosed_biUnion fun C _ => C.isClosed
    · rw [Set.mem_iUnion₂]
      rintro ⟨C, ⟨hCT, hCY⟩, hyC⟩
      have hgen := (hT ⟨C, hCT⟩).isGenericPoint_genericPoint C.isClosed
      have ht := IntersectC.eq_of_coheight_one (hB i) (hBne i) hy (hCB C hCT hgen.mem) (hgen.specializes hyC)
      apply hCY
      rw [hYdef, ← ht]
      exact hgen.def.symm
    · intro z hz
      have hzT : z ∈ ((T.sup id : Closeds (PP K F n).left) : Set (PP K F n).left) := by rw [← hST]; exact hz
      rw [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂] at hzT
      obtain ⟨C, hCT, hzC⟩ := hzT
      by_cases hCY : (C : Set (PP K F n).left) = Y
      · exact Or.inl (hCY ▸ hzC)
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨C, ⟨hCT, hCY⟩, hzC⟩)
  choose R hRc hyR hBR using hR
  have hUo : IsOpen (⋂ i, (R i)ᶜ) := isOpen_iInter_of_finite fun i => (hRc i).isOpen_compl
  have hyU : y ∈ ⋂ i, (R i)ᶜ := Set.mem_iInter.mpr fun i => hyR i
  have hlines : LinesIn K F n Y (⋂ i, (R i)ᶜ) := by
    rintro p ⟨hpY, hpU⟩ i
    have hirr : IsIrreducible (Set.range (line K F n i p).left) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ (line K F n i p).left.continuous.continuousOn
    have hsub : Set.range (line K F n i p).left ⊆ Y ∪ R i := (hsat i p (hYB i hpY)).trans (hBR i)
    rcases isPreirreducible_iff_isClosed_union_isClosed.mp hirr.isPreirreducible Y (R i) isClosed_closure
      (hRc i) hsub with h | h
    · exact h
    · exact absurd (h ⟨_, hval i p⟩) (Set.mem_iInter.mp hpU i)
  have hYU := reach (K := K) (F := F) n Y (⋂ i, (R i)ᶜ) isClosed_closure isIrreducible_singleton.closure hUo
    ⟨y, subset_closure rfl, hyU⟩ hlines
  have hmax : IsMax y := fun b _ => specializes_iff_mem_closure.mpr (Set.eq_univ_iff_forall.mp hYU b)
  rw [Order.coheight_eq_zero.mpr hmax] at hy
  exact zero_ne_one hy

end Cover

end RamanujanPetersson.ThetaCube


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

variable (P0 : Place K F)

/-- `(m ≫ τ_{x0})^* Θ` on `J^3`, for a dominant `m ≫ τ_{x0}`. -/
noncomputable def pbTh (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (m : Jac K F ⊗ (Jac K F ⊗ Jac K F) ⟶ Jac K F)
    [IsDominant (m ≫ transl (Jac K F) x0).left] : AlgebraicCycle (Jac K F ⊗ (Jac K F ⊗ Jac K F)).left ℤ :=
  JacDivisors.pullback (m ≫ transl (Jac K F) x0).left (Theta P0)

/-- The cube divisor `Σ_S ± m_S^* Θ_{x0}` on `J^3`. -/
noncomputable def cubeZ (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    AlgebraicCycle (Jac K F ⊗ (Jac K F ⊗ Jac K F)).left ℤ :=
  pbTh P0 x0 (q1 K F * q2 K F * q3 K F) - pbTh P0 x0 (q1 K F * q2 K F) - pbTh P0 x0 (q1 K F * q3 K F) -
    pbTh P0 x0 (q2 K F * q3 K F) + pbTh P0 x0 (q1 K F) + pbTh P0 x0 (q2 K F) + pbTh P0 x0 (q3 K F)

lemma pbTh_mem (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (m : Jac K F ⊗ (Jac K F ⊗ Jac K F) ⟶ Jac K F)
    [IsDominant (m ≫ transl (Jac K F) x0).left] :
    pbTh P0 x0 m ∈ weilDivisors (Jac K F ⊗ (Jac K F ⊗ Jac K F)).left :=
  pullback_mem_weilDivisors _ _

lemma cubeZ_mem (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    cubeZ P0 x0 ∈ weilDivisors (Jac K F ⊗ (Jac K F ⊗ Jac K F)).left := by
  exact (weilDivisors _).add_mem ((weilDivisors _).add_mem ((weilDivisors _).add_mem ((weilDivisors _).sub_mem
    ((weilDivisors _).sub_mem ((weilDivisors _).sub_mem (pbTh_mem P0 x0 _) (pbTh_mem P0 x0 _))
      (pbTh_mem P0 x0 _)) (pbTh_mem P0 x0 _)) (pbTh_mem P0 x0 _)) (pbTh_mem P0 x0 _)) (pbTh_mem P0 x0 _)

/-- A map sending the unit to the unit avoids `Θ` after translating by `x0 ∉ W`. -/
lemma avoid_of_one_comp (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (hx0 : pt (Jac K F) x0 ∉ W P0)
    (φ : Jac K F ⟶ Jac K F) (h : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) ≫ φ = 1) :
    Avoid (φ ≫ transl (Jac K F) x0).left (Theta P0) := by
  refine avoid_Theta P0 _ (y := pt (Jac K F) 1) ?_
  rw [← pt_comp, ← Category.assoc, h, pt_comp, transl_pt, _root_.one_mul]
  exact hx0

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Sym =====
section

/-!
# S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`

* `algebraMap_generic`, **`cpull_eq_pullback`**: for a dominant map, `cpull` is `JacDivisors.pullback`;
* `negJ = (𝟙 J)⁻¹` (the inverse map), `comp_negJ : φ ≫ negJ = φ⁻¹`;
* `DTh P0 x0 := τ_{x0}^* Θ + (negJ ≫ τ_{x0})^* Θ`: Weil (`DTh_mem`), effective (`DTh_nonneg`);
* `avoid_DTh`: every homomorphism avoids `DTh P0 x0` when `x0 ∉ W`;
* **`cpull_DTh`**: `φ^* D' = (φ ≫ τ_{x0})^* Θ + (φ⁻¹ ≫ τ_{x0})^* Θ`;
* **`cpull_inv_DTh`**: `(φ⁻¹)^* D' = φ^* D'` (exact symmetry).
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
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (φ : C ⟶ Y) [IsDominant φ]

end General

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- The symmetric divisor `D' = τ_{x0}^* Θ + (negJ ≫ τ_{x0})^* Θ`. -/
noncomputable def DTh (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : AlgebraicCycle (Jac K F).left ℤ :=
  JacDivisors.pullback (transl (Jac K F) x0).left (Theta P0) +
    JacDivisors.pullback (negJ K F ≫ transl (Jac K F) x0).left (Theta P0)

lemma DTh_mem (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : DTh P0 x0 ∈ weilDivisors (Jac K F).left :=
  (weilDivisors _).add_mem (pullback_mem_weilDivisors _ _) (pullback_mem_weilDivisors _ _)

lemma avoid_negJ_transl (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (hx0 : pt (Jac K F) x0 ∉ W P0) :
    Avoid (negJ K F ≫ transl (Jac K F) x0).left (Theta P0) :=
  avoid_of_one_comp P0 x0 hx0 _ (by rw [negJ, ← GrpObj.inv_eq_inv]; exact GrpObj.one_inv)

end Theta

end RamanujanPetersson.ThetaCube


end


