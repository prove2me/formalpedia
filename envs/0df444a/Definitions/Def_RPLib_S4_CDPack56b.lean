-- Prove2me | Definitions.Def_RPLib_S4_CDPack56b
-- name    : RPLib_S4_CDPack56b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T19:04:50.857206+00:00
-- url     : https://prove2.me/theorems/babc24a2-0b18-425d-a7a7-4ace5cf40475
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 56b of 71
-- statement:
--   Part 56b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_ThetaSquare_Curve4`: Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))
--   * `Def_RP_ThetaSquare_Curve5`: Unit S4-ThetaSquare, file Curve5: the pull-back `D_e` as a divisor, and the curve-level square (T4c (C), T5)
--   * `Def_RP_ThetaSquare_Curve6`: Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)
--   * `Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack56

/-!
# Curve-duality library package, part 56b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_ThetaSquare_Curve4`: Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))
* `Def_RP_ThetaSquare_Curve5`: Unit S4-ThetaSquare, file Curve5: the pull-back `D_e` as a divisor, and the curve-level square (T4c (C), T5)
* `Def_RP_ThetaSquare_Curve6`: Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)
* `Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
-/

set_option autoImplicit false

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

theorem exists_of_Zdiv_pos {S : Finset (Rfin K F →ₐ[K] K)} {v : Place K F} (h : 1 ≤ Zdiv S v) :
    ∃ φ ∈ S, v = Sum.inl (ptP φ) := by
  rcases v with P | P
  · obtain ⟨φ, rfl⟩ := exists_ptP P
    rw [Zdiv_inl_ptP] at h
    by_cases hφ : φ ∈ S
    · exact ⟨φ, hφ, rfl⟩
    · rw [if_neg hφ] at h
      omega
  · rw [Zdiv_inr] at h
    omega

/-- If `ℓ(W0 - G + 2[v]) = 1` (`v ∈ G`) and that class contains `Zdiv S`, then `v` is a point of `S`. -/
theorem exists_mem_X0 {W0 G : Places.Divisor K F} (hW : IsCanonicalFK K F W0) (hG : 0 ≤ G)
    (hd : G.deg = genusFK K F) (h1 : ellFK K F G = 1) {v : Place K F} (hv : 1 ≤ G v)
    (h2 : ellFK K F (W0 - G + Finsupp.single v 2) = 1) (S : Finset (Rfin K F →ₐ[K] K))
    (hy : clsK K F (Zdiv S) = clsK K F (W0 - G + Finsupp.single v 2)) :
    ∃ φ ∈ S, v = Sum.inl (ptP φ) := by
  obtain ⟨E, hE0, hEc⟩ := (eff_iff_mem_supp hW hG hd h1 v).2 hv
  obtain ⟨f0, -, -, huniq⟩ := exists_eq_of_ell_one h2
  have e2 : W0 - G + Finsupp.single v 1 + Finsupp.single v 1 = W0 - G + Finsupp.single v 2 := by
    rw [add_assoc, ← Finsupp.single_add]
    norm_num
  have hE1 : 0 ≤ E + Finsupp.single v 1 := add_nonneg hE0 (Finsupp.single_nonneg.2 zero_le_one)
  have hc1 : clsK K F (E + Finsupp.single v 1) = clsK K F (W0 - G + Finsupp.single v 2) := by
    rw [clsK_add, hEc, ← clsK_add, e2]
  have hZ := (huniq _ (Zdiv_nonneg S) hy).trans (huniq _ hE1 hc1).symm
  have hEv := Finsupp.le_def.1 hE0 v
  have hpos : 1 ≤ Zdiv S v := by
    rw [hZ, Finsupp.add_apply, Finsupp.single_eq_same]
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hEv
    omega
  exact exists_of_Zdiv_pos hpos

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

theorem Zdiv_image_eq (t : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (ht : Function.Injective t)
    (i0 : Fin (genusFK K F)) :
    Zdiv (Finset.univ.image t) = Finsupp.single (Sum.inl (ptP (t i0))) 1 + plusE t i0 := by
  rw [Zdiv, Finset.sum_image (fun i _ j _ h => ht h), ← Finset.add_sum_erase _ _ (Finset.mem_univ i0), plusE]

section Geom

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Class bookkeeping**: `e = cE · c_φ⁻¹` for `φ = t i0`. -/
theorem eq_cE (hg : 0 < genusFK K F) (P0 : Place K F) {W0 G : Places.Divisor K F}
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (he : ((Multiplicative.toAdd (jacPicEquiv K F e) : Pic0K K F) : PicK K F) =
      clsK K F (W0 - G) - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1))
    (t : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (ht : Function.Injective t) (i0 : Fin (genusFK K F))
    (hy : clsK K F (Zdiv (Finset.univ.image t)) =
      clsK K F (W0 - G + Finsupp.single (Sum.inl (ptP (t i0))) 2))
    (c : (Rfin K F →ₐ[K] K) → (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F))
    (hc : ∀ φ, ((Multiplicative.toAdd (jacPicEquiv K F (c φ)) : Pic0K K F) : PicK K F) =
      clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F) :
    e = cE t i0 P0 * (c (t i0))⁻¹ := by
  apply (jacPicEquiv K F).injective
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rw [he, _root_.map_mul, map_inv, toAdd_mul, toAdd_inv, AddSubgroup.coe_add, AddSubgroup.coe_neg, hc, cE,
    MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hE : clsK K F (plusE t i0) =
      clsK K F (W0 - G + Finsupp.single (Sum.inl (ptP (t i0))) 2) -
        clsK K F (Finsupp.single (Sum.inl (ptP (t i0))) 1) := by
    rw [← hy, Zdiv_image_eq t ht i0, clsK_add]
    abel
  have h2v : clsK K F (W0 - G + Finsupp.single (Sum.inl (ptP (t i0)) : Place K F) 2) =
      clsK K F (W0 - G) + clsK K F (Finsupp.single (Sum.inl (ptP (t i0))) 1) +
        clsK K F (Finsupp.single (Sum.inl (ptP (t i0))) 1) := by
    rw [← clsK_add, ← clsK_add, add_assoc, ← Finsupp.single_add]
    norm_num
  have hn0 : ((n0 K F : ℕ) : ℤ) = (genusFK K F : ℤ) - 1 := by
    simp only [n0]
    omega
  show _ = clsK K F (plusE t i0) + clsK K F (Finsupp.single P0 1) - thetaK K F +
    -(clsK K F (Finsupp.single (Sum.inl (ptP (t i0))) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F)
  rw [hE, h2v, ← natCast_zsmul, hn0]
  module

/-- **Multiplicity one at the points of `G`** (T4c step (B)): for `e` of class `[W0 - G] - (g-2)[P0]`
(`G ≥ 0`, `deg G = g`, `ℓ(G) = 1`) avoiding `Θ`, and a `K`-point `q` of `X1` with `1 ≤ G (kPl q)` such that
`ℓ(W0 - G + 2[kPl q]) = 1` and that class contains the divisor of an `X0` point, `D_e` is `1` at `q`. -/
theorem Dc_eq_one (hg : 0 < genusFK K F) (P0 : Place K F) {W0 G : Places.Divisor K F}
    (hW : IsCanonicalFK K F W0) (hG : 0 ≤ G) (hd : G.deg = genusFK K F) (h1 : ellFK K F G = 1)
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (he : ((Multiplicative.toAdd (jacPicEquiv K F e) : Pic0K K F) : PicK K F) =
      clsK K F (W0 - G) - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1))
    (hA : Avoid (feX P0 e) (Theta P0))
    (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) (hv : 1 ≤ G (kPl q))
    (h2 : ellFK K F (W0 - G + Finsupp.single (kPl q) 2) = 1)
    (yR : LawRing K F →ₐ[K] K)
    (hy : clsK K F (Zdiv (ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)))) =
      clsK K F (W0 - G + Finsupp.single (kPl q) 2)) :
    Dc P0 e (q.left (IsLocalRing.closedPoint K)) = 1 := by
  obtain ⟨c0, ψ0, hcen, hq⟩ := exists_chart0 hg q
  obtain ⟨φ, hφA, hvφ⟩ := exists_mem_X0 hW hG hd h1 hv h2 _ hy
  have hcen' : IsCenter (Sum.inl (ptP φ) : Place K F) (ψ0.comp diag1) := hvφ ▸ hcen
  have hxc : φ (xcR F c0) ≠ 0 := xcR_ne_of_isCenter c0 hcen'
  obtain ⟨t, i0, x, hx, him, ht, hti⟩ := exists_R2pt c0 yR hφA hxc
  choose c hc using fun ψ => exists_cJ P0 hg ψ
  have hq2 := eq_iota2 hcen hq t i0 x (by rw [hx, hvφ])
  have hy' : clsK K F (Zdiv (Finset.univ.image t)) =
      clsK K F (W0 - G + Finsupp.single (Sum.inl (ptP (t i0))) 2) := by
    rw [him, hti, ← hvφ]
    exact hy
  have heq : e = cE t i0 P0 * (c (ptR2 c0 t i0 x))⁻¹ := by
    rw [hx, ← hti]
    exact eq_cE hg P0 e he t ht i0 hy' c hc
  rw [hq2, heq]
  rw [heq] at hA
  exact Dc_plusX_eq_one P0 hg c0 t i0 c hc x hA

end Geom

end Curve4

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

/-- **`D_e` on `K`-points** (Milne III.6.7 at the closed points): `D_e (q) = G (kPl q)`. -/
theorem Dc_kpt_eq (hg : 0 < genusFK K F) (P0 : Place K F) {W0 G : Places.Divisor K F}
    (hW : IsCanonicalFK K F W0) {e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F} (h : IsGoodFor P0 W0 e G)
    (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    Dc P0 e (q.left (IsLocalRing.closedPoint K)) = G (kPl q) := by
  by_cases hv : 1 ≤ G (kPl q)
  · obtain ⟨h2, yR, hy⟩ := h.ptX0 _ hv
    rw [Dc_eq_one hg P0 hW h.nonneg h.deg h.ell e h.cls h.avoid q hv h2 yR hy]
    have := h.red (kPl q)
    omega
  · have h0 : G (kPl q) = 0 := by
      have := Finsupp.le_def.1 h.nonneg (kPl q)
      simp only [Finsupp.coe_zero, Pi.zero_apply] at this
      omega
    rw [h0]
    exact Dc_eq_zero P0 hg e fun hm => hv ((mem_W_fe_iff hg P0 hW h.nonneg h.deg h.ell e h.cls q).1 hm)

/-- `D_e` vanishes at the generic point of `X1`. -/
theorem Dc_generic (hg : 0 < genusFK K F) (P0 : Place K F) {e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F}
    (hA : Avoid (feX P0 e) (Theta P0)) : Dc P0 e (genericPoint (X1 K F)) = 0 := by
  obtain ⟨V, hV, hηV, h0⟩ := hA
  exact cpull_eq_zero_of _ (theta_mem_weilDivisors P0 hg) ⟨V, hV, hηV, h0⟩ hV hηV h0

/-- `e1 e2 = e3 e4` forces `G1 + G2 - G3 - G4` to be principal. -/
theorem sub_mem_PrincK (P0 : Place K F) {W0 G1 G2 G3 G4 : Places.Divisor K F}
    {e1 e2 e3 e4 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F}
    (h1 : IsGoodFor P0 W0 e1 G1) (h2 : IsGoodFor P0 W0 e2 G2) (h3 : IsGoodFor P0 W0 e3 G3)
    (h4 : IsGoodFor P0 W0 e4 G4) (h : e1 * e2 = e3 * e4) : G1 + G2 - G3 - G4 ∈ PrincK K F := by
  have h' := congrArg (fun z => ((Multiplicative.toAdd (jacPicEquiv K F z) : Pic0K K F) : PicK K F)) h
  simp only [_root_.map_mul, toAdd_mul, AddSubgroup.coe_add] at h'
  rw [h1.cls, h2.cls, h3.cls, h4.cls, clsK_sub, clsK_sub, clsK_sub, clsK_sub] at h'
  have h0 : clsK K F (G1 + G2 - G3 - G4) = 0 := by
    rw [clsK_sub, clsK_sub, clsK_add]
    calc clsK K F G1 + clsK K F G2 - clsK K F G3 - clsK K F G4 =
        -((clsK K F W0 - clsK K F G1 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) +
            (clsK K F W0 - clsK K F G2 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1))) -
          (clsK K F W0 - clsK K F G3 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) +
            (clsK K F W0 - clsK K F G4 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1)))) := by abel
      _ = 0 := by rw [h', sub_self, neg_zero]
  exact (QuotientAddGroup.eq_zero_iff _).1 h0

/-- **The curve-level theorem of the square** (T5): for good `e1, e2, e3, e4` with `e1 e2 = e3 e4`, the cycle
`D_{e1} + D_{e2} - D_{e3} - D_{e4}` on `X1` is the principal divisor `G1 + G2 - G3 - G4` at every `K`-point,
and vanishes at the generic point. -/
theorem square_curve (hg : 0 < genusFK K F) (P0 : Place K F) {W0 G1 G2 G3 G4 : Places.Divisor K F}
    (hW : IsCanonicalFK K F W0) {e1 e2 e3 e4 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F}
    (h1 : IsGoodFor P0 W0 e1 G1) (h2 : IsGoodFor P0 W0 e2 G2) (h3 : IsGoodFor P0 W0 e3 G3)
    (h4 : IsGoodFor P0 W0 e4 G4) (h : e1 * e2 = e3 * e4) :
    G1 + G2 - G3 - G4 ∈ PrincK K F ∧
      (∀ q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F,
        (Dc P0 e1 + Dc P0 e2 - Dc P0 e3 - Dc P0 e4) (q.left (IsLocalRing.closedPoint K)) =
          (G1 + G2 - G3 - G4) (kPl q)) ∧
      (Dc P0 e1 + Dc P0 e2 - Dc P0 e3 - Dc P0 e4) (genericPoint (X1 K F)) = 0 := by
  refine ⟨sub_mem_PrincK P0 h1 h2 h3 h4 h, fun q => ?_, ?_⟩
  · simp only [Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_sub, Pi.add_apply,
      Pi.sub_apply, Finsupp.coe_add, Finsupp.coe_sub]
    rw [Dc_kpt_eq hg P0 hW h1, Dc_kpt_eq hg P0 hW h2, Dc_kpt_eq hg P0 hW h3, Dc_kpt_eq hg P0 hW h4]
  · simp only [Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_sub, Pi.add_apply,
      Pi.sub_apply]
    rw [Dc_generic hg P0 h1.avoid, Dc_generic hg P0 h2.avoid, Dc_generic hg P0 h3.avoid, Dc_generic hg P0 h4.avoid]
    simp

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

theorem ajCls_self (P0 : Place K F) : ajCls K F P0 P0 = 0 :=
  Subtype.ext ((coe_ajCls P0 P0).trans (sub_self _))

theorem ajK_self (P0 : Place K F) : ajK K F P0 P0 = 1 := by
  rw [ajK, ajCls_self, ofAdd_zero, map_one]

/-- Every place is the place of a `K`-point of `X1`. -/
theorem exists_kPl_eq (hg : 0 < genusFK K F) (P0 v : Place K F) :
    ∃ q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F, kPl q = v := by
  obtain ⟨q, hq⟩ := exists_kX1 P0 v
  exact ⟨q, ajK_injective hg P0 ((kPl_spec P0 q).symm.trans hq)⟩

theorem Zdiv_le_one (S : Finset (Rfin K F →ₐ[K] K)) (v : Place K F) : Zdiv S v ≤ 1 := by
  rcases v with P | P
  · obtain ⟨φ, rfl⟩ := exists_ptP P
    rw [Zdiv_inl_ptP]
    split_ifs <;> omega
  · rw [Zdiv_inr]
    omega

/-- For `G ≥ 0` reduced of degree `g` with `ℓ(G) = 1`: `ℓ(W0 - G + 2[v]) = 1` for every `v`. -/
theorem ell_two_eq_one {W0 G : Places.Divisor K F} (hW : IsCanonicalFK K F W0) (hG : 0 ≤ G)
    (hd : G.deg = genusFK K F) (h1 : ellFK K F G = 1) (hred : ∀ v, G v ≤ 1) (v : Place K F) :
    ellFK K F (W0 - G + Finsupp.single v 2) = 1 := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have hrr := riemannRochFK' hk hW (W0 - G + Finsupp.single v 2)
  rw [show W0 - (W0 - G + Finsupp.single v 2) = G - Finsupp.single v 2 by abel,
    PlacesK.Divisor.deg_add, PlacesK.Divisor.deg_sub, hd, degFK_canonical hk hW, deg_single'] at hrr
  have h0 : ellFK K F (G - Finsupp.single v 2) = 0 := by
    by_contra hne
    obtain ⟨E, hE, hc⟩ := (one_le_ell_iff (G - Finsupp.single v 2)).1 (by omega)
    obtain ⟨f0, -, -, huniq⟩ := exists_eq_of_ell_one h1
    have hc' : clsK K F (E + Finsupp.single v 2) = clsK K F G := by
      rw [clsK_add (K := K) (F := F), hc, ← clsK_add (K := K) (F := F), sub_add_cancel]
    have hEG : E + Finsupp.single v 2 = G :=
      (huniq _ (add_nonneg hE (Finsupp.single_nonneg.2 zero_le_two)) hc').trans (huniq G hG rfl).symm
    have h2 := hred v
    rw [← hEG, Finsupp.add_apply, Finsupp.single_eq_same] at h2
    have := Finsupp.le_def.1 hE v
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  omega

/-- A `K`-point of `J` with a given degree-`0` class. -/
theorem exists_pt_cls (X : PicK K F) (hX : degPicK K F X = 0) :
    ∃ c : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F,
      ((Multiplicative.toAdd (jacPicEquiv K F c) : Pic0K K F) : PicK K F) = X :=
  ⟨(jacPicEquiv K F).symm (Multiplicative.ofAdd ⟨X, (mem_Pic0K K F).2 hX⟩), by
    rw [MulEquiv.apply_symm_apply]; rfl⟩

/-- The constant `c_K` of class `[W0] - (g-2)[P0] - [Θ]`. -/
theorem exists_cK (P0 : Place K F) {W0 : Places.Divisor K F} (hW : IsCanonicalFK K F W0) :
    ∃ c : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F,
      ((Multiplicative.toAdd (jacPicEquiv K F c) : Pic0K K F) : PicK K F) =
        clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) - thetaK K F := by
  apply exists_pt_cls
  rw [map_sub, map_sub, map_zsmul, degPicK_clsK, degPicK_clsK, deg_single_one, deg_thetaK,
    degFK_canonical (constField_eq_bot' (K := K) (F := F)) hW, smul_eq_mul]
  ring

/-- The constant `c_2` of class `g[P0] - [Θ]`. -/
theorem exists_c2 (P0 : Place K F) :
    ∃ c : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F,
      ((Multiplicative.toAdd (jacPicEquiv K F c) : Pic0K K F) : PicK K F) =
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) - thetaK K F := by
  apply exists_pt_cls
  rw [map_sub, map_zsmul, degPicK_clsK, deg_single_one, deg_thetaK, smul_eq_mul]
  ring

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

/-- `κ : J ⟶ J`, `e ↦ c_K e⁻¹`. -/
noncomputable def kapM : Jac K F ⟶ Jac K F := toUnit (Jac K F) ≫ cK * (𝟙 (Jac K F))⁻¹

/-- `μ1 : J × X1 ⟶ J`, `(e, q) ↦ AJ(q) e`. -/
noncomputable def mu1 : Jac K F ⊗ X1O K F ⟶ Jac K F :=
  (snd (Jac K F) (X1O K F) ≫ ajO P0) * fst (Jac K F) (X1O K F)

/-- `μ2 : J × X1 ⟶ J`, `(e, q) ↦ AJ(q)² e c_2`. -/
noncomputable def mu2 : Jac K F ⊗ X1O K F ⟶ Jac K F :=
  (snd (Jac K F) (X1O K F) ≫ ajO P0) * (snd (Jac K F) (X1O K F) ≫ ajO P0) * fst (Jac K F) (X1O K F) *
    (toUnit _ ≫ c2)

theorem comp_kapM (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : e ≫ kapM cK = cK * e⁻¹ := by
  rw [kapM, MonObj.comp_mul, ← Category.assoc, toUnit_unique (e ≫ toUnit _) (𝟙 _), Category.id_comp,
    GrpObj.comp_inv, Category.comp_id]

theorem comp_mu1 (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    lift e q ≫ mu1 P0 = q ≫ fe P0 e := by
  rw [mu1, MonObj.comp_mul, lift_snd_assoc, lift_fst, comp_fe]

theorem comp_mu2 (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    lift e q ≫ mu2 P0 c2 = (q ≫ ajO P0) * (q ≫ ajO P0) * e * c2 := by
  rw [mu2, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, lift_snd_assoc, lift_fst, ← Category.assoc,
    toUnit_unique (lift e q ≫ toUnit _) (𝟙 _), Category.id_comp]

theorem isOpen_range_jX0 : IsOpen (Set.range (jX0 K F)) := (jX0 K F).isOpenEmbedding.isOpen_range

/-- The bad pairs `(e, q)`: `AJ(q) e ∈ W` but `AJ(q)² e c_2 ∉ jX0 (X0)`. -/
def Bad : Set (Jac K F ⊗ X1O K F).left :=
  (mu1 P0).left ⁻¹' W P0 ∩ (mu2 P0 c2).left ⁻¹' (Set.range (jX0 K F))ᶜ

theorem isClosed_Bad : IsClosed (Bad P0 c2) :=
  ((isClosed_W P0).preimage (mu1 P0).left.continuous).inter
    (isOpen_range_jX0.isClosed_compl.preimage (mu2 P0 c2).left.continuous)

instance universallyClosed_fstJ : UniversallyClosed (fst (Jac K F) (X1O K F)).left := by
  show UniversallyClosed (pullback.fst (Jac K F).hom (toSpecK K (algebraMap K[X] F X) 1))
  infer_instance

/-- **The open set of good points**: `Wᶜ ∩ κ⁻¹ (jX0 (X0)) ∩ (pr_J Bad)ᶜ`. -/
def Ogood : Set (Jac K F).left :=
  (W P0)ᶜ ∩ (kapM cK).left ⁻¹' Set.range (jX0 K F) ∩ ((fst (Jac K F) (X1O K F)).left '' Bad P0 c2)ᶜ

theorem isOpen_Ogood : IsOpen (Ogood P0 cK c2) :=
  ((isClosed_W P0).isOpen_compl.inter (isOpen_range_jX0.preimage (kapM cK).left.continuous)).inter
    ((fst (Jac K F) (X1O K F)).left.isClosedMap _ (isClosed_Bad P0 c2)).isOpen_compl

theorem pt_comp_kapM (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    (cK * e⁻¹).left (IsLocalRing.closedPoint K) = (kapM cK).left (e.left (IsLocalRing.closedPoint K)) := by
  rw [← comp_kapM]
  rfl

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


