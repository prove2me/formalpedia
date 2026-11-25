-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T14:24:47.60466+00:00
-- url     : https://prove2.me/theorems/06c76771-737a-573a-831c-d19730838538
-- title:
--   Exists Pt J
-- statement:
--   Definitions and structural lemmas for Exists Pt J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsPtJ.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIsUnivChartOfIsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_cc_pt
import Theorems.Thm_GlobalTheory_FormalLog_evHom_apply
import Theorems.Thm_GlobalTheory_FormalLog_ev_X
import Theorems.Thm_GlobalTheory_FormalLog_pt_apply
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChartJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
section Points
variable {k : Type} [CommRing k] {d : ℕ}
variable (k d) in

def Q (n : ℕ) : AddSubgroup (Pt k n d) where
  carrier := {p | ∀ i, constantCoeff (p i) = 0}
  add_mem' := fun ha hb i => by rw [Pi.add_apply, map_add, ha i, hb i, add_zero]
  zero_mem' := fun _ => map_zero _
  neg_mem' := fun ha i => by rw [Pi.neg_apply, map_neg, ha i, neg_zero]
variable {n l : ℕ}
def gen (j : Fin n) : Q k d n := ⟨pt k d j, cc_pt j⟩
theorem czQ (b : Fin n → Q k d l) : CZ (fun j => (b j).1) := fun j i => (b j).2 i
def sb (b : Fin n → Q k d l) : PS k n d →+* PS k l d := evHom (czQ b)
theorem sb_apply (b : Fin n → Q k d l) (f : PS k n d) : sb b f = ev (fun j => (b j).1) f := evHom_apply (czQ b) f
def sq (b : Fin n → Q k d l) : Q k d n →+ Q k d l where
  toFun p := ⟨fun i => sb b (p.1 i), fun i =>
    (congrArg constantCoeff (sb_apply b _)).trans (constantCoeff_ev (czQ b) (p.2 i))⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)
@[simp] theorem sq_gen (b : Fin n → Q k d l) (j : Fin n) : sq b (gen j) = b j := by
  apply Subtype.ext
  funext i
  show sb b (pt k d j i) = (b j).1 i
  rw [sb_apply, pt_apply, ev_X (czQ b)]
def ac (A : Q k d 1) (u : Q k d n) : Q k d n := sq ![u] A
def op (F : Q k d 2) (u v : Q k d n) : Q k d n := sq ![u, v] F
end Points
variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]
def pj (m : ℕ) (f : MvPowerSeries σ R) : JetR R σ m := Ideal.Quotient.mk _ (truncTotal (m + 1) f)
theorem aug_pj (m : ℕ) (f : MvPowerSeries σ R) : jetAug R σ m (pj m f) = constantCoeff f := by
  show (MvPolynomial.aeval fun _ => (0 : R)) (truncTotal (m + 1) f) = constantCoeff f
  simp [MvPowerSeries.constantCoeff_truncTotal_eq_ite]
def jS {κ : Type} (m : ℕ) (a : κ → MvPowerSeries τ R) (ha : ∀ s, constantCoeff (a s) = 0) : JetR R κ m →ₐ[R] JetR R τ m :=
  jetLift R (RingHom.ker (jetAug R τ m)) (ker_jetAug_pow τ m) (fun s => pj m (a s)) fun s => (aug_pj m _).trans (ha s)
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}
def jP (m : ℕ) (p : Q R d n) : JetR R (Fin d) m →ₐ[R] JetR R (Fin n × Fin d) m := jS m p.1 p.2
def ptJ (m : ℕ) (p : Q R d n) : sp (R₀ := R) (JetR R (Fin n × Fin d) m) ⟶ G := spMap (jP m p) ≫ x m
def jQ (m : ℕ) (b : Fin n → Q R d l) : JetR R (Fin n × Fin d) m →ₐ[R] JetR R (Fin l × Fin d) m :=
  jS m (fun s => (b s.1).1 s.2) fun s => (b s.1).2 s.2
variable {x} (hx : IsUnivChart G d x)
include hx
end GlobalTheory.ChartJet


