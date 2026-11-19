-- Prove2me | Definitions.Def_RPLib_S4_CDPack43
-- name    : RPLib_S4_CDPack43
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T15:24:16.495312+00:00
-- url     : https://prove2.me/theorems/7a5dd091-e9a6-4d31-8255-17183affdea0
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 43 of 71
-- statement:
--   Part 43 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_AJCo`: The Jacobian (unit S4-JacComplete), part `AJCo`: the Abel-Jacobi map on the curve `X1 = Sym¹ X`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack41d
import Definitions.Def_RPLib_S4_CDPack39
import Definitions.Def_RPLib_S4_CDPack42
import Definitions.Def_RPLib_S4_CDPack42b

/-!
# Curve-duality library package, part 43 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_AJCo`: The Jacobian (unit S4-JacComplete), part `AJCo`: the Abel-Jacobi map on the curve `X1 = Sym¹ X`
-/

set_option autoImplicit false

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

/-- `B → Sym¹ B`: the single tensor factor (every element of `X¹` is `S_1`-invariant). -/
noncomputable def diag1 : B →ₐ[k] SymRing k B 1 :=
  (inc (k := k) (B := B) (g := 1) 0).codRestrict (SymRing k B 1) (fun b => by
    rw [mem_symRing]
    intro σ
    rw [Subsingleton.elim σ 1, one_smul])

theorem diag1_coe (b : B) : (diag1 (k := k) b : XPow k B 1) = inc 0 b := rfl

theorem symMap_diag1 {B' : Type*} [CommRing B'] [Algebra k B'] (f : B →ₐ[k] B') :
    (symMap (g := 1) f).comp diag1 = diag1.comp f :=
  AlgHom.ext fun b => Subtype.ext (by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, symMap_coe, diag1_coe, diag1_coe, ← AlgHom.comp_apply, xMap_inc,
      AlgHom.comp_apply])

end Diag

section AJ1

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

instance fact_transcendental_xF : Fact (Transcendental K (algebraMap K[X] F X)) := ⟨transcendental_xF K F⟩

instance finiteType_chartIdx (A : ChartIdx K) : Algebra.FiniteType K (chartRing (algebraMap K[X] F X) A.1) :=
  finiteType_chartRing (transcendental_xF K F) A.2

variable (K F) in
/-- The curve `X1 = Sym¹ X`. -/
noncomputable abbrev X1 : Scheme.{u} := SymX K (algebraMap K[X] F X) 1

variable (K F) in
/-- The chart `A` of `X1`, `Spec Sym¹ B_A`. -/
noncomputable abbrev cht (A : (ChartIdx K)ᵒᵖ) : Scheme.{u} :=
  Spec (.of (SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1))

instance isReduced_cht (A : (ChartIdx K)ᵒᵖ) : IsReduced (cht K F A) := by
  show IsReduced (Spec (CommRingCat.of (SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1)))
  infer_instance

instance isReduced_X1 : IsReduced (X1 K F) := by
  have : ∀ t : X1 K F, _root_.IsReduced ((X1 K F).presheaf.stalk t) := fun t => by
    obtain ⟨A, z, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (symDiagram K (algebraMap K[X] F X) 1) t
    have e := (asIso ((colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A).stalkMap z)).commRingCatIsoToRingEquiv
    have : IsReduced ((symDiagram K (algebraMap K[X] F X) 1).obj A) := isReduced_cht (K := K) (F := F) A
    exact isReduced_of_injective e.toRingHom e.injective
  exact isReduced_of_isReduced_stalk (X1 K F)

/-- The center of a `K`-point `θ` of `B_A` (the chart-`{c}` center for the chosen `c ∈ A`). -/
noncomputable def plA (A : ChartIdx K) (θ : chartRing (algebraMap K[X] F X) A.1 →ₐ[K] K) : Place K F :=
  plc A.2.choose (θ.comp (Subalgebra.inclusion (chartRing_mono _ (Finset.singleton_subset_iff.2 A.2.choose_spec))))

theorem isCenter_plA (A : ChartIdx K) (θ : chartRing (algebraMap K[X] F X) A.1 →ₐ[K] K) :
    IsCenter (plA A θ) θ :=
  isCenter_plc_of_mem A.2.choose_spec θ

theorem plA_eq_of_isCenter (A : ChartIdx K) {θ : chartRing (algebraMap K[X] F X) A.1 →ₐ[K] K} {R : Place K F}
    (hR : IsCenter R θ) : plA A θ = R :=
  isCenter_unique A.2.choose_spec (isCenter_plA A θ) hR

/-- The center does not depend on the chart. -/
theorem plA_restrict {A A' : ChartIdx K} (h : A.1 ⊆ A'.1) (θ : chartRing (algebraMap K[X] F X) A'.1 →ₐ[K] K) :
    plA A (θ.comp (Subalgebra.inclusion (chartRing_mono _ h))) = plA A' θ :=
  (plA_eq_of_isCenter A' (isCenter_extend h A.2.choose_spec θ (isCenter_plA A _))).symm

variable (K F) in
/-- `Rfin (SynF c) ≅ B_{c} ⊆ B_A → Sym¹ B_A` for the chosen `c ∈ A`. -/
noncomputable def cPt (A : ChartIdx K) :
    Rfin K (SynF K F A.2.choose) →ₐ[K] SymRing K (chartRing (algebraMap K[X] F X) A.1) 1 :=
  diag1.comp ((Subalgebra.inclusion (chartRing_mono _ (Finset.singleton_subset_iff.2 A.2.choose_spec))).comp
    (rfinG A.2.choose).symm.toAlgHom)

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

theorem cht_cov (t : X1 K F) (_ : IsClosed ({t} : Set (X1 K F))) :
    ∃ A : (ChartIdx K)ᵒᵖ, ∃ p : cht K F A, colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A p = t :=
  Scheme.IsLocallyDirected.ι_jointly_surjective (symDiagram K (algebraMap K[X] F X) 1) t

set_option maxHeartbeats 800000 in
/-- The chart maps agree at closed points with the same image in `X1`. -/
theorem chartAJ_comp (A A' : (ChartIdx K)ᵒᵖ) (p : cht K F A) (p' : cht K F A')
    (hp : IsClosed ({p} : Set (cht K F A))) (_ : IsClosed ({p'} : Set (cht K F A')))
    (e : colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A p =
      colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A' p') :
    chartAJ P0 A p = chartAJ P0 A' p' := by
  obtain ⟨A'', fi, fj, z, rfl, rfl⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff (symDiagram K (algebraMap K[X] F X) 1)).1 e
  have hz : IsClosed ({z} : Set ((symDiagram K (algebraMap K[X] F X) 1).obj A'')) := by
    have hinj := ((symDiagram K (algebraMap K[X] F X) 1).map fi).isOpenEmbedding.injective
    have h := hp.preimage ((symDiagram K (algebraMap K[X] F X) 1).map fi).isOpenEmbedding.continuous
    have e2 : (⇑((symDiagram K (algebraMap K[X] F X) 1).map fi)) ⁻¹'
        {((symDiagram K (algebraMap K[X] F X) 1).map fi) z} = {z} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact hinj.eq_iff
    exact (congrArg IsClosed e2).mp h
  obtain ⟨ψ, rfl⟩ := exists_kpt (K := K) (A := SymRing K (chartRing (algebraMap K[X] F X) A''.unop.1) 1) z hz
  have key : ∀ {B0 : (ChartIdx K)ᵒᵖ} (f : A'' ⟶ B0),
      (symDiagram K (algebraMap K[X] F X) 1).map f
          (kpt (A := SymRing K (chartRing (algebraMap K[X] F X) A''.unop.1) 1) ψ) =
        kpt (A := SymRing K (chartRing (algebraMap K[X] F X) B0.unop.1) 1)
          (ψ.comp (chartMap (algebraMap K[X] F X) 1 (leOfHom f.unop))) := fun {B0} f => by
    rw [symDiagram_map]
    exact SpecMap_kpt (A := SymRing K (chartRing (algebraMap K[X] F X) B0.unop.1) 1)
      (B := SymRing K (chartRing (algebraMap K[X] F X) A''.unop.1) 1)
      (chartMap (algebraMap K[X] F X) 1 (leOfHom f.unop)) ψ
  have key2 : ∀ {B0 : (ChartIdx K)ᵒᵖ} (f : A'' ⟶ B0),
      (ψ.comp (chartMap (algebraMap K[X] F X) 1 (leOfHom f.unop))).comp diag1 =
        (ψ.comp diag1).comp (Subalgebra.inclusion (chartRing_mono _ (leOfHom f.unop))) := fun f => by
    rw [AlgHom.comp_assoc, chartMap, symMap_diag1, AlgHom.comp_assoc]
  rw [key fi, key fj, chartAJ_kpt, chartAJ_kpt, key2 fi, key2 fj, plA_restrict (leOfHom fi.unop),
    plA_restrict (leOfHom fj.unop)]

instance isOpenImmersion_ιX1 (A : (ChartIdx K)ᵒᵖ) :
    IsOpenImmersion (X := cht K F A) (Y := X1 K F) (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A) :=
  JacSym.isOpenImmersion_ι K (algebraMap K[X] F X) 1 A

/-- **The Abel-Jacobi map on the curve** `X1 = Sym¹ X` (base point `P0`), glued from the charts. -/
noncomputable def ajX1 : X1 K F ⟶ (Jac K F).left :=
  JacChunk.glueY (toSpecK K (algebraMap K[X] F X) 1) (Jac K F).hom (cht K F)
    (colimit.ι (symDiagram K (algebraMap K[X] F X) 1)) (chartAJ P0) cht_cov (chartAJ_over P0)
    (chartAJ_comp P0)

theorem ajX1_over : ajX1 P0 ≫ (Jac K F).hom = toSpecK K (algebraMap K[X] F X) 1 :=
  JacChunk.glueY_over _ _ _ _ _ _ _ _

/-- **Value of the AJ map** at the closed point `colimit.ι A (kpt ψ)` of `X1`: the point of class `[Q] - [P0]`,
`Q = plA A (ψ.comp diag1)`. -/
theorem ajX1_apply (A : (ChartIdx K)ᵒᵖ) (ψ : SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1 →ₐ[K] K) :
    ajX1 P0 (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A
        (kpt (A := SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) ψ)) =
      ajPt K F P0 (plA A.unop (ψ.comp diag1)) :=
  (JacChunk.glueY_apply _ _ _ _ _ _ _ _ A _).trans (chartAJ_kpt P0 A ψ)

end AJ1

end RamanujanPetersson.JacComplete

end


