-- Prove2me | Definitions.Def_RPLib_F2_056
-- name    : RPLib_F2_056
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T20:42:39.006646+00:00
-- url     : https://prove2.me/theorems/a7f622cf-744a-4d15-9a5f-e58acb978775
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 056 of 70
-- statement:
--   File 056 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacComplete_AJGlue`: The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces
--   * `S4.Def_RP_JacComplete_AJGlue2`: The Jacobian (unit S4-JacComplete), part `AJGlue2`: the Abel-Jacobi map on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`
--   * `S4.Def_RP_JacComplete_AJCo`: The Jacobian (unit S4-JacComplete), part `AJCo`: the Abel-Jacobi map on the curve `X1 = Sym¹ X`
--   * `S4.Def_RP_ThetaSquare_Pts`: Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`
--   * `S4.Def_RP_ThetaSquare_PlusX`: Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map
--   * `S4.Def_RP_ThetaSquare_Curve3`: Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)
--   * `S4.Def_RP_ThetaSquare_Curve4`: Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))
--   * `S4.Def_RP_ThetaSquare_Curve6`: Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)
--   * `S4.Def_RP_ThetaSquare_Curve8`: Unit S4-ThetaSquare, file Curve8: points of `X1^g` (T4c (D), nonemptiness, part 1)
--   * `S4.Def_RP_JacFrob_Val`: S4-JacFrob, part Val: values of `mor φ hφ` on the `K`-points of `J` coming from `D(φ u0)`
--   * `S4.Def_RP_JacFrob_Val2`: S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`
--   * `S4.Def_RP_JacFrob_Val3`: S4-JacFrob, part Val3: `π_J := π_J⁰ · (translation by cPt)` and `[a ≫ π_J] = σ_*[a]` over `D(u0) ∩ D(Φ u0)`
--   * `S4.Def_RP_JacFrob_Hom`: S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects
--   * `S4.Def_RP_JacFrob_All`: S4-JacFrob, part All: `[a ≫ π_J] = σ_*[a]` for every `K`-point; `π_J` is the arithmetic Frobenius on `Pic(X-bar)`
--   * `S4.Def_RP_JacFrob_PolyG`: S4-JacFrob, part PolyG: `ℤ[π] → End(J)` on points, generically
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_055

/-!
# Ramanujan-Petersson curve library (flat edition), file 056 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacComplete_AJGlue`: The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces
* `S4.Def_RP_JacComplete_AJGlue2`: The Jacobian (unit S4-JacComplete), part `AJGlue2`: the Abel-Jacobi map on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`
* `S4.Def_RP_JacComplete_AJCo`: The Jacobian (unit S4-JacComplete), part `AJCo`: the Abel-Jacobi map on the curve `X1 = Sym¹ X`
* `S4.Def_RP_ThetaSquare_Pts`: Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`
* `S4.Def_RP_ThetaSquare_PlusX`: Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map
* `S4.Def_RP_ThetaSquare_Curve3`: Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)
* `S4.Def_RP_ThetaSquare_Curve4`: Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))
* `S4.Def_RP_ThetaSquare_Curve6`: Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)
* `S4.Def_RP_ThetaSquare_Curve8`: Unit S4-ThetaSquare, file Curve8: points of `X1^g` (T4c (D), nonemptiness, part 1)
* `S4.Def_RP_JacFrob_Val`: S4-JacFrob, part Val: values of `mor φ hφ` on the `K`-points of `J` coming from `D(φ u0)`
* `S4.Def_RP_JacFrob_Val2`: S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`
* `S4.Def_RP_JacFrob_Val3`: S4-JacFrob, part Val3: `π_J := π_J⁰ · (translation by cPt)` and `[a ≫ π_J] = σ_*[a]` over `D(u0) ∩ D(Φ u0)`
* `S4.Def_RP_JacFrob_Hom`: S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects
* `S4.Def_RP_JacFrob_All`: S4-JacFrob, part All: `[a ≫ π_J] = σ_*[a]` for every `K`-point; `π_J` is the arithmetic Frobenius on `Pic(X-bar)`
* `S4.Def_RP_JacFrob_PolyG`: S4-JacFrob, part PolyG: `ℤ[π] → End(J)` on points, generically
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_AJGlue =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces

`B' = Rfin (SynF K F c0)`.
* `locallyOfFiniteType_sR`; the piece index `PIdx K F c0` and the open immersions `pj c0 i : Spec LocR → Spec B'`.
* `pj_kpt` (closed points), `pj_cov` (the pieces cover the closed points), `pj_over`.
The glued map `ajChart` is in part `AJGlue2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- the instance diamonds on the nested localizations need nested synthPending (diagnostics, session 20)
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Glue

open Classical
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K]

variable [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K)

theorem pj_over (i : PIdx K F c0) :
    (ajPiece P0 c0 i.2.1 i.2.2).left ≫ (Jac K F).hom = pj c0 i ≫ sR K (Rfin K (SynF K F c0)) :=
  (ajPiece_over P0 c0 i.2.1 i.2.2).trans (pieceIn_over c0 i.2.1 i.2.2).symm

end Glue

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJGlue2 =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGlue2`: the Abel-Jacobi map on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`

* `pj_comp`: the pieces agree at closed points over the same point of `Spec B'`.
* **`ajChart P0 c0 : Spec B' ⟶ J`** glued (`JacChunk.glueY`) from the pieces; `ajChart_over`
  (its value `ajChart_kpt` moved to AJCo, session 22, to keep this file under the 150 user-s cap).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- the instance diamonds on the nested localizations need nested synthPending (diagnostics, session 20)
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Glue

open Classical
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K]

variable [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K)

set_option maxHeartbeats 800000 in
/-- The pieces agree at closed points over the same point of `Spec B'`. -/
theorem pj_comp (i i' : PIdx K F c0) (p : Spec (.of (LocR c0 i.2.1 i.2.2)))
    (p' : Spec (.of (LocR c0 i'.2.1 i'.2.2)))
    (hp : IsClosed ({p} : Set (Spec (.of (LocR c0 i.2.1 i.2.2)))))
    (hp' : IsClosed ({p'} : Set (Spec (.of (LocR c0 i'.2.1 i'.2.2)))))
    (e : pj c0 i p = pj c0 i' p') :
    (ajPiece P0 c0 i.2.1 i.2.2).left p = (ajPiece P0 c0 i'.2.1 i'.2.2).left p' := by
  obtain ⟨x, rfl⟩ := exists_kpt (K := K) (A := LocR c0 i.2.1 i.2.2) p hp
  obtain ⟨x', rfl⟩ := exists_kpt (K := K) (A := LocR c0 i'.2.1 i'.2.2) p' hp'
  have h1 := pj_kpt c0 i x
  have h2 := pj_kpt c0 i' x'
  have h : x.comp (pieceIn c0 i.2.1 i.2.2) = x'.comp (pieceIn c0 i'.2.1 i'.2.2) :=
    kpt_injective (K := K) (A := Rfin K (SynF K F c0)) (h1.symm.trans (e.trans h2))
  rw [ajPiece_kpt, ajPiece_kpt]
  unfold plP
  rw [h]

/-- **The Abel-Jacobi map on the chart** `Spec B'` (`B' = Rfin (SynF K F c0)`), glued from the pieces. -/
noncomputable def ajChart : Spec (.of (Rfin K (SynF K F c0))) ⟶ (Jac K F).left :=
  JacChunk.glueY (sR K (Rfin K (SynF K F c0))) (Jac K F).hom
    (fun i : PIdx K F c0 => Spec (.of (LocR c0 i.2.1 i.2.2))) (pj c0)
    (fun i => (ajPiece P0 c0 i.2.1 i.2.2).left) (pj_cov c0) (pj_over P0 c0) (pj_comp P0 c0)

theorem ajChart_over : ajChart P0 c0 ≫ (Jac K F).hom = sR K (Rfin K (SynF K F c0)) :=
  JacChunk.glueY_over _ _ _ _ _ _ _ _

end Glue

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJCo =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJCo`: the Abel-Jacobi map on the curve `X1 = Sym¹ X`

`X1 K F = SymX K x 1` (`x = algebraMap K[X] F X`): the charts `Spec Sym¹ B_A` glued (JacSymB).
* `diag1 : B →ₐ Sym¹ B` (the single tensor factor) and its naturality `symMap_diag1`;
* `isReduced_X1`; `plA A θ`, the center of a `K`-point `θ` of `B_A` (`isCenter_plA`, `plA_restrict`);
* `chartAJ P0 A : chart A ⟶ J` (`Rfin (SynF c) ≅ B_{c} ⊆ B_A → Sym¹ B_A`, then `ajChart P0 c`), value `chartAJ_kpt`;
* **`ajX1 P0 : X1 K F ⟶ J`** glued (`JacChunk.glueY`); `ajX1_over`, **`ajX1_apply`**: the value at the closed
  point `colimit.ι A (kpt ψ)` is `ajPt P0 (plA A (ψ.comp diag1))` (class `[Q] - [P0]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- the instance diamonds on the nested localizations need nested synthPending (diagnostics, session 20)
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Diag

variable {k : Type*} [CommRing k] {B : Type*} [CommRing B] [Algebra k B]

end Diag

section AJ1

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **Value of the chart AJ map at a closed point** `kpt Q`: the point of `J` of class `[Q] - [P0]`. -/
theorem ajChart_kpt (c0 : K) (Q : Rfin K (SynF K F c0) →ₐ[K] K) :
    ajChart P0 c0 (kpt (A := Rfin K (SynF K F c0)) Q) = ajPt K F P0 (plC c0 Q) := by
  obtain ⟨r, D, c, x, rfl⟩ := exists_piece_through (F := F) c0 Q
  rw [← pj_kpt c0 ⟨r, D, c⟩ x]
  exact (JacChunk.glueY_apply _ _ _ _ _ _ _ _ (⟨r, D, c⟩ : PIdx K F c0) _).trans (ajPiece_kpt P0 c0 D c x)

/-- The AJ map on the chart `A` of `X1`. -/
noncomputable def chartAJ (A : (ChartIdx K)ᵒᵖ) : cht K F A ⟶ (Jac K F).left :=
  Spec.map (CommRingCat.ofHom (R := Rfin K (SynF K F A.unop.2.choose))
      (S := SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) (cPt K F A.unop : _ →+* _)) ≫
    ajChart P0 A.unop.2.choose

theorem chartAJ_over (A : (ChartIdx K)ᵒᵖ) :
    chartAJ P0 A ≫ (Jac K F).hom =
      colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A ≫ toSpecK K (algebraMap K[X] F X) 1 := by
  rw [ι_toSpecK, chartAJ]
  refine (Category.assoc _ _ _).trans ?_
  rw [ajChart_over]
  exact SpecMap_sR (cPt K F A.unop)

theorem chartAJ_kpt (A : (ChartIdx K)ᵒᵖ) (ψ : SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1 →ₐ[K] K) :
    chartAJ P0 A (kpt (A := SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) ψ) =
      ajPt K F P0 (plA A.unop (ψ.comp diag1)) := by
  have key : ψ.comp (cPt K F A.unop) =
      ptSyn A.unop.2.choose ((ψ.comp diag1).comp
        (Subalgebra.inclusion (chartRing_mono _ (Finset.singleton_subset_iff.2 A.unop.2.choose_spec)))) := by
    simp only [cPt, ptSyn, AlgHom.comp_assoc]
  rw [chartAJ, Scheme.Hom.comp_apply, SpecMap_kpt (A := Rfin K (SynF K F A.unop.2.choose))
      (B := SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) (cPt K F A.unop) ψ,
    ajChart_kpt, key]
  rfl

end AJ1

end RamanujanPetersson.JacComplete


end

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

end Pts

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

theorem mem_Pic0K_cE :
    clsK K F (plusE a i0) + clsK K F (Finsupp.single P0 1) - thetaK K F ∈ Pic0K K F := by
  rw [mem_Pic0K, map_sub, map_add, deg_thetaK, degPicK_clsK, degPicK_clsK, deg_plusE, deg_single_one]
  ring

/-- The constant `cE` with class `[E] + [P0] - [Θ]`. -/
noncomputable def cE : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F :=
  (jacPicEquiv K F).symm (Multiplicative.ofAdd ⟨_, mem_Pic0K_cE a i0 P0⟩)

end PlusX

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

theorem ajK_injective (hg : 0 < genusFK K F) (P0 : Place K F) : Function.Injective (ajK K F P0) := by
  intro Q Q' h
  have h1 : ajCls K F P0 Q = ajCls K F P0 Q' :=
    Multiplicative.ofAdd.injective ((jacPicEquiv K F).symm.injective h)
  have h2 : ((ajCls K F P0 Q : Pic0K K F) : PicK K F) = ajCls K F P0 Q' := by rw [h1]
  rw [coe_ajCls, coe_ajCls] at h2
  exact eq_of_clsK_single hg (sub_left_inj.1 h2)

end Geom

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

open Classical

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

/-- The constant `c_3` of class `[W0] - (g-2)[P0] - g[P0]`. -/
theorem exists_c3 (P0 : Place K F) {W0 : Places.Divisor K F} (hW : IsCanonicalFK K F W0) :
    ∃ c : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F,
      ((Multiplicative.toAdd (jacPicEquiv K F c) : Pic0K K F) : PicK K F) =
        clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) -
          (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) := by
  apply exists_pt_cls
  simp only [map_sub, map_zsmul, degPicK_clsK, deg_single_one,
    degFK_canonical (constField_eq_bot' (K := K) (F := F)) hW, smul_eq_mul]
  ring

end Curve8

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_JacFrob_Val =====
section

/-!
# S4-JacFrob, part Val: values of `mor φ hφ` on the `K`-points of `J` coming from `D(φ u0)`

Generic (JacComplete context `K F : Type u`, `[IsAlgClosed K]`):
* `kptEquiv_of_jX0`, `jacPicEquiv_of_jX0`: a `K`-point `a` of `J` with closed point `jX0 x` (`x` closed in `X0`) has value
  `lamB x` in `H` and class `psiJ x` in `Pic⁰`;
* `eJ_kpt`, `mor_kpt`: `mor φ hφ` sends `jX0 (kpt (z ∘ ι))` to `jX0 (kpt (z ∘ rho φ))` for `z : S_g[1/u0][1/φ u0] →ₐ[K] K`;
* `jacPicEquiv_mor`: the class of `a ≫ mor φ hφ` is `psiJ (kpt (z ∘ rho φ))`;
* `zOf`, `zOf_comp`: every `y` with `y (φ u0) ≠ 0` factors through `S_g[1/u0][1/φ u0]`;
* `comp_rho_S`: on `S_g`, `z ∘ rho φ` is `(z ∘ ι) ∘ φ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Val

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem jacPicEquiv_of_jX0 (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (x : X0 K F) (hx : IsClosed ({x} : Set (X0 K F)))
    (ha : a.left (IsLocalRing.closedPoint K) = jX0 K F x) :
    ((Multiplicative.toAdd (jacPicEquiv K F a) : Pic0K K F) : PicK K F) = psiJ K F x := by
  rw [jacPicEquiv_apply, kptEquiv_of_jX0 a x hx ha]
  exact jacPic0_lamB (K := K) (F := F) x hx

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

end Val

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Val2 =====
section

/-!
# S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`

Generic:
* `ptOf_comp_xMap`, `symPt_comp_symMap`, `ptSet_comp_symMap`: the support of `y ∘ symMap f` is `(supp y) ∘ f`;
* `thetaK`, `psiJ_kpt`: `psiJ (kpt y) = [Z(y|S_g)] - [Θ]`; `cls_of_kpt`, `cls_mor`, `cls_mor_hom`: classes of `a` and `a ≫ mor φ hφ`.

For `J = J_{F-bar}` over `k-bar`:
* `PhiR_eq_pow`: `Φ b = (σ⁻¹ b)^q` on `Rfin`; `ptP_comp_PhiR`: the place of `χ ∘ Φ` is `σ_*` of the place of `χ`;
* `comp_PhiR_injective`, `Zdiv_image_PhiR`, `Zdiv_ptSet_PhiS`: `Z(y ∘ Φ_S) = σ_* Z(y)`;
* `cTheta = σ_*[Θ] - [Θ] ∈ Pic⁰`; **`jacPicEquiv_piJ0`**: `[a ≫ π_J⁰] = σ_*[a] + cTheta`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory IsDedekindDomain
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR
open RamanujanPetersson.PicDescent

universe u

section SymPt

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {B' : Type*} [CommRing B'] [Algebra k B']
  {g : ℕ}

end SymPt

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

/-- The class of a `K`-point over `D(u0) ∩ D(φ u0)`: `[Z(y_S)] - [Θ]` with `y_S = z ∘ ι ∘ ι` on `S_g`. -/
theorem cls_of_kpt (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (z : BRing φ →ₐ[K] K)
    (ha : a.left (IsLocalRing.closedPoint K) =
      jX0 K F (kpt (z.comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ))))) :
    ((Multiplicative.toAdd (jacPicEquiv K F a) : Pic0K K F) : PicK K F) =
      clsK K F (Zdiv (ptSet ((z.comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ))).comp
        (IsScalarTower.toAlgHom K (SymRing K (Places.Rfin K F) (genusFK K F)) (LawRing K F))))) - thetaK K F :=
  (jacPicEquiv_of_jX0 a _ (JacLaw.isClosed_kpt _) ha).trans (psiJ_kpt _)

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

end Spec

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Val3 =====
section

/-!
# S4-JacFrob, part Val3: `π_J := π_J⁰ · (translation by cPt)` and `[a ≫ π_J] = σ_*[a]` over `D(u0) ∩ D(Φ u0)`

Generic: `cls_mul` (classes of products of `K`-points add), `comp_mul_toUnit` (`a ≫ (ψ * (toUnit ≫ c)) = (a ≫ ψ) * c`).
For `J = J_{F-bar}`: `cPt` (the point of class `-cTheta`), `cls_cPt`, **`piJ`**, **`jacPicEquiv_piJ`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem cls_mul (a b : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    ((Multiplicative.toAdd (jacPicEquiv K F (a * b)) : Pic0K K F) : PicK K F) =
      ((Multiplicative.toAdd (jacPicEquiv K F a) : Pic0K K F) : PicK K F) +
        ((Multiplicative.toAdd (jacPicEquiv K F b) : Pic0K K F) : PicK K F) := by
  rw [map_mul, toAdd_mul, AddSubgroup.coe_add]

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

set_option synthInstance.maxHeartbeats 100000 in
/-- The `K`-point of `J` with class `-cTheta`. -/
noncomputable def cPt : 𝟙_ (Over (Spec (.of (kbar Fq Ω)))) ⟶ Jac (kbar Fq Ω) (Fbar Fq F Ω) :=
  (jacPicEquiv _ _).symm
    (Multiplicative.ofAdd (-(⟨cTheta Fq F Ω hk, cTheta_mem_Pic0K Fq F Ω hk⟩ : Pic0K (kbar Fq Ω) (Fbar Fq F Ω))))

set_option synthInstance.maxHeartbeats 100000 in
theorem cls_cPt :
    ((Multiplicative.toAdd (jacPicEquiv _ _ (cPt Fq F Ω hk)) : Pic0K _ _) : PicK (kbar Fq Ω) (Fbar Fq F Ω)) =
      -cTheta Fq F Ω hk := by
  rw [cPt, MulEquiv.apply_symm_apply, toAdd_ofAdd, AddSubgroup.coe_neg]

end Spec

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Hom =====
section

/-!
# S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects

Generic (JacComplete context): `ptW` (a `K`-point of `J` inside `jX0(D(φ u0))` comes from a `K`-point of
`S_g[1/u0][1/φ u0]`), `UJ W` (the dense open `fst⁻¹W ∩ snd⁻¹W ∩ μ⁻¹W` of `J × J`), and `isMonHom_of_cls`:
a map `ψ : J ⟶ J` acting on the classes of the `K`-points over a dense open `W` through an additive map `s`
is a homomorphism of group objects. For `J = J_{F-bar}`: **`isMonHom_piJ`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (ψ : Jac K F ⟶ Jac K F) (s : PicK K F ≃+ PicK K F) (W : (Jac K F).left.Opens)

theorem mul_comp_of_cls
    (hψ : ∀ a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, a.left (IsLocalRing.closedPoint K) ∈ W →
      ((Multiplicative.toAdd (jacPicEquiv K F (a ≫ ψ)) : Pic0K K F) : PicK K F) =
        s ((Multiplicative.toAdd (jacPicEquiv K F a) : Pic0K K F) : PicK K F))
    (b₁ b₂ : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (h₁ : b₁.left (IsLocalRing.closedPoint K) ∈ W)
    (h₂ : b₂.left (IsLocalRing.closedPoint K) ∈ W) (h₁₂ : (b₁ * b₂).left (IsLocalRing.closedPoint K) ∈ W) :
    (b₁ * b₂) ≫ ψ = (b₁ ≫ ψ) * (b₂ ≫ ψ) := by
  apply (jacPicEquiv K F).injective
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rw [hψ _ h₁₂, cls_mul, cls_mul, map_add, hψ _ h₁, hψ _ h₂]

theorem comp_mu_comp
    (hψ : ∀ a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, a.left (IsLocalRing.closedPoint K) ∈ W →
      ((Multiplicative.toAdd (jacPicEquiv K F (a ≫ ψ)) : Pic0K K F) : PicK K F) =
        s ((Multiplicative.toAdd (jacPicEquiv K F a) : Pic0K K F) : PicK K F))
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F ⊗ Jac K F)
    (h₁ : (p ≫ fst _ _).left (IsLocalRing.closedPoint K) ∈ W)
    (h₂ : (p ≫ snd _ _).left (IsLocalRing.closedPoint K) ∈ W)
    (h₃ : (p ≫ μ).left (IsLocalRing.closedPoint K) ∈ W) :
    p ≫ μ ≫ ψ = p ≫ (ψ ⊗ₘ ψ) ≫ μ := by
  have e : p ≫ μ = (p ≫ fst _ _) * (p ≫ snd _ _) := by rw [MonObj.mul_eq_mul, MonObj.comp_mul]
  rw [← Category.assoc, e, mul_comp_of_cls ψ s W hψ _ _ h₁ h₂ (by rw [← e]; exact h₃),
    MonObj.mul_eq_mul (M := Jac K F), MonObj.comp_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
  simp only [Category.assoc]

theorem mul_hom_of_cls (hW : Dense (W : Set (Jac K F).left))
    (hψ : ∀ a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, a.left (IsLocalRing.closedPoint K) ∈ W →
      ((Multiplicative.toAdd (jacPicEquiv K F (a ≫ ψ)) : Pic0K K F) : PicK K F) =
        s ((Multiplicative.toAdd (jacPicEquiv K F a) : Pic0K K F) : PicK K F)) :
    μ ≫ ψ = (ψ ⊗ₘ ψ) ≫ μ := by
  apply eq_of_kpt_eq (V := Jac K F ⊗ Jac K F) (dense_UJ W hW)
  intro u
  have hp : (u ≫ ιU _ (UJ K F W)).left (IsLocalRing.closedPoint K) ∈ UJ K F W := by
    rw [comp_left_cp]
    exact (u.left (IsLocalRing.closedPoint K)).2
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hp
  have := comp_mu_comp ψ s W hψ (u ≫ ιU _ (UJ K F W)) (by rw [comp_left_cp]; exact h₁)
    (by rw [comp_left_cp]; exact h₂) (by rw [comp_left_cp]; exact h₃)
  simpa only [Category.assoc] using this

/-- **A map `J ⟶ J` acting on the classes of the `K`-points over a dense open through `s` is a homomorphism.** -/
theorem isMonHom_of_cls (hW : Dense (W : Set (Jac K F).left))
    (hψ : ∀ a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, a.left (IsLocalRing.closedPoint K) ∈ W →
      ((Multiplicative.toAdd (jacPicEquiv K F (a ≫ ψ)) : Pic0K K F) : PicK K F) =
        s ((Multiplicative.toAdd (jacPicEquiv K F a) : Pic0K K F) : PicK K F)) :
    IsMonHom ψ where
  one_hom := one_hom_of_mul_hom ψ (mul_hom_of_cls ψ s W hW hψ)
  mul_hom := mul_hom_of_cls ψ s W hW hψ

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

end Spec

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_All =====
section

/-!
# S4-JacFrob, part All: `[a ≫ π_J] = σ_*[a]` for every `K`-point; `π_J` is the arithmetic Frobenius on `Pic(X-bar)`

Generic: `exists_kpt_mem` (every nonempty open of `J` contains a `K`-point), `invMul a` (`x ↦ x⁻¹ * a`),
`cls_all` (a homomorphism acting through `s` on the classes of the `K`-points over a dense open does so everywhere).
For `J = J_{F-bar}`: **`jacPicEquiv_piJ_all`**, **`piBar_jacPicEquiv_piJ`** (review R4, through `Ψ : PicBar ≃+ PicK`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **Values on all points**: a homomorphism `ψ : J ⟶ J` acting through `s` on the classes of the `K`-points
over a dense open `W` does so on all `K`-points. -/
theorem cls_all (ψ : Jac K F ⟶ Jac K F) [IsMonHom ψ] (s : PicK K F ≃+ PicK K F) (W : (Jac K F).left.Opens)
    (hW : Dense (W : Set (Jac K F).left))
    (hψ : ∀ a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, a.left (IsLocalRing.closedPoint K) ∈ W →
      ((Multiplicative.toAdd (jacPicEquiv K F (a ≫ ψ)) : Pic0K K F) : PicK K F) =
        s ((Multiplicative.toAdd (jacPicEquiv K F a) : Pic0K K F) : PicK K F))
    (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    ((Multiplicative.toAdd (jacPicEquiv K F (a ≫ ψ)) : Pic0K K F) : PicK K F) =
      s ((Multiplicative.toAdd (jacPicEquiv K F a) : Pic0K K F) : PicK K F) := by
  have : Nonempty (Jac K F).left := ⟨(η[Jac K F]).left (IsLocalRing.closedPoint K)⟩
  obtain ⟨c, hc⟩ := exists_kpt_mem W hW.nonempty
  have h2 : (((invMul a).left ⁻¹ᵁ W : (Jac K F).left.Opens) : Set (Jac K F).left).Nonempty := by
    refine ⟨(a * c⁻¹).left (IsLocalRing.closedPoint K), ?_⟩
    show (invMul a).left ((a * c⁻¹).left (IsLocalRing.closedPoint K)) ∈ W
    rw [← comp_left_cp, comp_invMul, _root_.mul_inv_rev, _root_.inv_inv, _root_.mul_assoc,
      _root_.inv_mul_cancel, _root_.mul_one]
    exact hc
  obtain ⟨y, hy2, hy1⟩ := hW.inter_open_nonempty _ ((invMul a).left ⁻¹ᵁ W).isOpen h2
  obtain ⟨b, hb1, hb2⟩ := exists_kpt_mem (W ⊓ (invMul a).left ⁻¹ᵁ W) ⟨y, hy1, hy2⟩
  have hb2' : (b⁻¹ * a).left (IsLocalRing.closedPoint K) ∈ W := by
    rw [← comp_invMul, comp_left_cp]
    exact hb2
  have ha : a = b * (b⁻¹ * a) := (_root_.mul_inv_cancel_left b a).symm
  rw [ha, MonObj.mul_comp, cls_mul, cls_mul, map_add, hψ _ hb1, hψ _ hb2']

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

end Spec

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_PolyG =====
section

/-!
# S4-JacFrob, part PolyG: `ℤ[π] → End(J)` on points, generically

For a map `ψ : J ⟶ J` whose action on the classes of the `K`-points is `πM` (through an additive map `t`
from `Pic⁰`): `cls_piter`, **`cls_polyEnd`** (`F(ψ)` acts as `aeval πM F`), `hom_ext_kpt` (maps `J ⟶ J` agreeing
on `K`-points are equal), `polyEnd_X`, **`polyEnd_mul_of_cls`** (`F G ↦ (FG)(ψ) = G(ψ) ≫ F(ψ)`: the ring map
`ℤ[π] → End(J)`), `polyEnd_eq_one_iff`, **`kerPtsEquiv`** (`Ker F(ψ)(K) ≃ ker (aeval πM F)`),
**`degree_polyEnd_eq_card_ker`** (`deg F(ψ) = #ker (aeval πM F)` when `dψ = 1`, `p ∤ F(0)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable {M : Type*} [AddCommGroup M]

theorem cls0_mul (a b : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    Multiplicative.toAdd (jacPicEquiv K F (a * b)) =
      Multiplicative.toAdd (jacPicEquiv K F a) + Multiplicative.toAdd (jacPicEquiv K F b) := by
  rw [map_mul, toAdd_mul]

theorem cls0_zpow (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (n : ℤ) :
    Multiplicative.toAdd (jacPicEquiv K F (a ^ n)) = n • Multiplicative.toAdd (jacPicEquiv K F a) := by
  rw [map_zpow, toAdd_zpow]

/-- Values of `ψ^∘n` on points. -/
theorem cls_piter (ψ : Jac K F ⟶ Jac K F) (t : Pic0K K F →+ M) (πM : Module.End ℤ M)
    (hψ : ∀ a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F,
      t (Multiplicative.toAdd (jacPicEquiv K F (a ≫ ψ))) = πM (t (Multiplicative.toAdd (jacPicEquiv K F a))))
    (n : ℕ) (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    t (Multiplicative.toAdd (jacPicEquiv K F (a ≫ IsogDegB.piter ψ n))) =
      (πM ^ n) (t (Multiplicative.toAdd (jacPicEquiv K F a))) := by
  induction n generalizing a with
  | zero =>
    show t (Multiplicative.toAdd (jacPicEquiv K F (a ≫ 𝟙 _))) = _
    rw [Category.comp_id, pow_zero, Module.End.one_apply]
  | succ n ih =>
    show t (Multiplicative.toAdd (jacPicEquiv K F (a ≫ ψ ≫ IsogDegB.piter ψ n))) = _
    rw [← Category.assoc, ih, hψ, pow_succ, Module.End.mul_apply]

/-- **Values of `F(ψ)` on points**: `F(ψ)` acts as `aeval πM F`. -/
theorem cls_polyEnd (ψ : Jac K F ⟶ Jac K F) (t : Pic0K K F →+ M) (πM : Module.End ℤ M)
    (hψ : ∀ a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F,
      t (Multiplicative.toAdd (jacPicEquiv K F (a ≫ ψ))) = πM (t (Multiplicative.toAdd (jacPicEquiv K F a))))
    (P : ℤ[X]) (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    t (Multiplicative.toAdd (jacPicEquiv K F (a ≫ IsogDegB.polyEnd ψ P))) =
      aeval πM P (t (Multiplicative.toAdd (jacPicEquiv K F a))) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [IsogDegB.polyEnd_add, MonObj.comp_mul, cls0_mul, map_add, hP, hQ, map_add, LinearMap.add_apply]
  | monomial n c =>
    rw [IsogDegB.polyEnd_monomial, GrpObj.comp_zpow, cls0_zpow, map_zsmul, cls_piter ψ t πM hψ n a,
      aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]

/-- **The ring map `ℤ[π] → End(J)`** (multiplicativity; additivity is `IsogDegB.polyEnd_add`). -/
theorem polyEnd_mul_of_cls (ψ : Jac K F ⟶ Jac K F) (e : Pic0K K F ≃+ M) (πM : Module.End ℤ M)
    (hψ : ∀ a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F,
      e (Multiplicative.toAdd (jacPicEquiv K F (a ≫ ψ))) = πM (e (Multiplicative.toAdd (jacPicEquiv K F a))))
    (P Q : ℤ[X]) : IsogDegB.polyEnd ψ (P * Q) = IsogDegB.polyEnd ψ Q ≫ IsogDegB.polyEnd ψ P := by
  have h : ∀ (R : ℤ[X]) (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F),
      e (Multiplicative.toAdd (jacPicEquiv K F (a ≫ IsogDegB.polyEnd ψ R))) =
        aeval πM R (e (Multiplicative.toAdd (jacPicEquiv K F a))) :=
    cls_polyEnd ψ e.toAddMonoidHom πM hψ
  refine hom_ext_kpt _ _ fun a => (jacPicEquiv K F).injective (Multiplicative.toAdd.injective (e.injective ?_))
  rw [← Category.assoc, h, h, h, map_mul, Module.End.mul_apply]

theorem polyEnd_eq_one_iff (ψ : Jac K F ⟶ Jac K F) (e : Pic0K K F ≃+ M) (πM : Module.End ℤ M)
    (hψ : ∀ a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F,
      e (Multiplicative.toAdd (jacPicEquiv K F (a ≫ ψ))) = πM (e (Multiplicative.toAdd (jacPicEquiv K F a))))
    (P : ℤ[X]) (c : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    c ≫ IsogDegB.polyEnd ψ P = 1 ↔ aeval πM P (e (Multiplicative.toAdd (jacPicEquiv K F c))) = 0 := by
  have h : e (Multiplicative.toAdd (jacPicEquiv K F (c ≫ IsogDegB.polyEnd ψ P))) =
      aeval πM P (e (Multiplicative.toAdd (jacPicEquiv K F c))) :=
    cls_polyEnd ψ e.toAddMonoidHom πM hψ P c
  rw [← h]
  constructor
  · intro h1
    rw [h1, map_one, toAdd_one, map_zero]
  · intro h1
    apply (jacPicEquiv K F).injective
    apply Multiplicative.toAdd.injective
    apply e.injective
    rw [h1, map_one, toAdd_one, map_zero]

/-- **`Ker F(ψ)(K) ≃ ker (aeval πM F)`.** -/
noncomputable def kerPtsEquiv (ψ : Jac K F ⟶ Jac K F) [IsMonHom ψ] (e : Pic0K K F ≃+ M) (πM : Module.End ℤ M)
    (hψ : ∀ a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F,
      e (Multiplicative.toAdd (jacPicEquiv K F (a ≫ ψ))) = πM (e (Multiplicative.toAdd (jacPicEquiv K F a))))
    (P : ℤ[X]) : IsogDegA.kerPts (Jac K F) (IsogDegB.polyEnd ψ P) ≃ LinearMap.ker (aeval πM P) :=
  ((jacPicEquiv K F).toEquiv.trans (Multiplicative.toAdd.trans e.toEquiv)).subtypeEquiv fun c => by
    rw [LinearMap.mem_ker]
    exact polyEnd_eq_one_iff ψ e πM hψ P c

end Gen

end RamanujanPetersson.JacFrob


end


