-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotIsUnitNatCastOfIsLocalHom
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotIsUnitNatCastOfIsLocalHom
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:09:13.924821+00:00
-- url     : https://prove2.me/theorems/b48347bb-a14b-4156-a8db-d643772b3cad
-- title:
--   Not Is Unit Nat Cast Of Is Local Hom
-- statement:
--   Definitions and structural lemmas for Not Is Unit Nat Cast Of Is Local Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OriginChartMultiplication_constantCoeff_mulSeries
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OriginChartMultiplication_mulSeries_succ
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OriginChartMultiplication_mulSeries_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TorsionCompare
theorem mulF_mapF {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ} (F : FGLaw T d)
    (n : ℕ) : mulF (F.mapF f) n = fun i => MvPowerSeries.map f (mulSeries F n i) := by
  induction n with
  | zero => funext i; simp [mulF, mulSeries_zero]
  | succ n ih =>
    funext i
    have h : ∀ q : Fin 2 × Fin d, MvPowerSeries.constantCoeff
        ((![mulSeries F n, pt T d 0] : Fin 2 → Pt T 1 d) q.1 q.2) = 0 := by
      rintro ⟨a, j⟩
      fin_cases a
      · exact constantCoeff_mulSeries F n j
      · simp [pt]
    rw [mulSeries_succ]
    show ev ![mulF (F.mapF f) n, pt O d 0] (MvPowerSeries.map f (F.F i)) =
      MvPowerSeries.map f (ev ![mulSeries F n, pt T d 0] (F.F i))
    unfold ev
    rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero h), ih]
    congr 1
    funext q
    obtain ⟨a, j⟩ := q
    fin_cases a
    · rfl
    · simp [pt]
theorem span_mulF_eq_torsionIdeal {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ}
    (F : FGLaw T d) (n : ℕ) :
    Ideal.span (Set.range (mulF (F.mapF f) n)) = torsionIdeal f F n := by
  rw [mulF_mapF]; rfl
def quotEquiv {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ}
    (F : FGLaw T d) (n : ℕ) : QF (F.mapF f) n ≃ₐ[O] TorsionRing f F n :=
  Ideal.quotientEquivAlgOfEq O (span_mulF_eq_torsionIdeal f F n)
section Jets
variable {R : Type} [CommRing R]
theorem algOverHom_comp {A B C : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [CommRing C] [Algebra R C] (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) :
    algOverHom (ψ.comp φ) = algOverHom ψ ≫ algOverHom φ := by
  ext1
  simp only [algOverHom, Over.homMk_left, Over.comp_left, spMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl
theorem algOverHom_id {A : Type} [CommRing A] [Algebra R A] :
    algOverHom (AlgHom.id R A) = 𝟙 _ := by
  ext1
  simp only [algOverHom, Over.homMk_left, Over.id_left, spMap]
  exact Spec.map_id _
theorem jet_ext {κ S : Type} [CommRing S] [Algebra R S] {m : ℕ} {φ ψ : JetR R κ m →ₐ[R] S}
    (h : ∀ j, φ (zR m j) = ψ (zR m j)) : φ = ψ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h
def jetRename {κ κ' : Type} (e : κ → κ') (m : ℕ) : JetR R κ m →ₐ[R] JetR R κ' m :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun q => zR m (e q))
    (aeval_kill m _ _ (fun q => Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self (e q))))
      (jet_aug_pow κ' m))
theorem jetRename_zR {κ κ' : Type} (e : κ → κ') (m : ℕ) (j : κ) :
    jetRename (R := R) e m (zR m j) = zR m (e j) := by
  exact MvPolynomial.aeval_X _ _
theorem jetRename_comp_of_inverse {κ κ' : Type} (e : κ → κ') (e' : κ' → κ)
    (h : ∀ j, e' (e j) = j) (m : ℕ) :
    (jetRename (R := R) e' m).comp (jetRename e m) = AlgHom.id R _ :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jetRename_zR, jetRename_zR, h]; rfl
end Jets
section Charts
variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]
def renameChart {G : Over (Sp R)} {σ σ' : Type} (e : σ → σ')
    (x : ∀ m : ℕ, algOver R (JetR R σ m) ⟶ G) : ∀ m : ℕ, algOver R (JetR R σ' m) ⟶ G :=
  fun m => algOverHom (jetRename e m) ≫ x m
theorem renameChart_renameChart {G : Over (Sp R)} {σ σ' : Type} (e : σ → σ') (e' : σ' → σ)
    (h : ∀ j, e' (e j) = j) (x : ∀ m : ℕ, algOver R (JetR R σ m) ⟶ G) :
    renameChart e' (renameChart e x) = x := by
  funext m
  unfold renameChart
  rw [← Category.assoc, ← algOverHom_comp, jetRename_comp_of_inverse e e' h, algOverHom_id,
    Category.id_comp]
def UniversalJets {σ : Type} (x : ∀ m : ℕ, algOver R (JetR R σ m) ⟶ G) : Prop :=
  (∀ m, algOverHom (jetTruncR R σ m) ≫ x (m + 1) = x m) ∧
  (∀ m, algOverHom (jetZeroR R σ m) ≫ x m = toUnit _ ≫ η[G]) ∧
  (∀ (κ : Type) (m : ℕ) (y : algOver R (JetR R κ m) ⟶ G),
    algOverHom (jetZeroR R κ m) ≫ y = toUnit _ ≫ η[G] →
    ∃! ψ : JetR R σ m →ₐ[R] JetR R κ m,
      (∀ j, jetZeroR R κ m (ψ (zR m j)) = 0) ∧ y = algOverHom ψ ≫ x m)
variable {d : ℕ}
def toOne (j : Fin d) : Fin 1 × Fin d := (0, j)
theorem toOne_snd (q : Fin 1 × Fin d) : toOne q.2 = q :=
  Prod.ext (Subsingleton.elim _ _) rfl
def chartEquiv (G : Over (Sp R)) (d : ℕ) :
    (∀ m : ℕ, algOver R (JetR R (Fin 1 × Fin d) m) ⟶ G) ≃
      (∀ m : ℕ, algOver R (JetR R (Fin d) m) ⟶ G) where
  toFun := renameChart Prod.snd
  invFun := renameChart toOne
  left_inv := renameChart_renameChart Prod.snd toOne toOne_snd
  right_inv := renameChart_renameChart toOne Prod.snd fun _ => rfl
end Charts
end GlobalTheory.TorsionCompare


