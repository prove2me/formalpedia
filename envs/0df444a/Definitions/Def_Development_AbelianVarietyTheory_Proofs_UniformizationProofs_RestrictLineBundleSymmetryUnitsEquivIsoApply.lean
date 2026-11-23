-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RestrictLineBundleSymmetryUnitsEquivIsoApply
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RestrictLineBundleSymmetryUnitsEquivIsoApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:58.637561+00:00
-- url     : https://prove2.me/theorems/c4529cb2-d801-4bab-8ff6-bdde72448462
-- title:
--   Restrict Line Bundle Symmetry Units Equiv Iso Apply
-- statement:
--   Definitions and structural lemmas for Restrict Line Bundle Symmetry Units Equiv Iso Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RestrictLineBundleSymmetryUnitsEquivIsoApply.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.BoxCompare
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.LB
open GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum (PowerDatum IsNormSymm)
section Units
variable {X Y : Scheme.{0}}
lemma res_self {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)ˣ) : res h x = x := by
  ext
  change (X.presheaf.map (𝟙 (Opposite.op U))).hom (x : Γ(X, U)) = _
  rw [X.presheaf.map_id]
  rfl
lemma gen_ext {L : LB X} {s t : LB.Gen L} (h : ∀ i, s.s i = t.s i) : s = t := by
  cases s; cases t
  congr 1
  exact funext h
lemma res_gen_congr {L : LB X} (s : LB.Gen L) {i j : L.ι} (e : i = j) {W : X.Opens}
    (h : W ≤ L.U i) (h' : W ≤ L.U j) : res h (s.s i) = res h' (s.s j) := by
  subst e
  rfl
end Units
section TwoForms
variable {X T : Scheme.{0}} (L : LB X) (f : X ⟶ X)
abbrev SymGen := LB.Gen (LB.LinComb L (K := Fin 2) ![f, 𝟙 X] ![1, -1])
lemma le_two {W : X.Opens} (j : Fin 2 → L.ι) :
    W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] j ↔ W ≤ f ⁻¹ᵁ L.U (j 0) ∧ W ≤ L.U (j 1) := by
  refine ⟨fun h => ⟨h.trans (wchart_le L _ j 0), h.trans (wchart_le L _ j 1)⟩,
    fun h y hy => Set.mem_iInter.2 fun k => ?_⟩
  fin_cases k
  · exact h.1 hy
  · exact h.2 hy
lemma le_one {W : T.Opens} (e : T ⟶ X) (a : PUnit.{1} → L.ι) :
    W ≤ wchart L (fun _ : PUnit.{1} => e) a ↔ W ≤ e ⁻¹ᵁ L.U (a ⟨⟩) :=
  ⟨fun h => h.trans (wchart_le L _ a ⟨⟩), fun h _ hy => Set.mem_iInter.2 fun _ => h hy⟩
lemma toIso_le (p : (PUnit.{1} → L.ι) × L.ι) :
    wchart L (fun _ : PUnit.{1} => f) p.1 ⊓ L.U p.2 ≤
      wchart L (K := Fin 2) ![f, 𝟙 X] ![p.1 ⟨⟩, p.2] :=
  (le_two L f _).2 ⟨(le_one L f _).1 inf_le_left, inf_le_right⟩
lemma ofIso_le (j : Fin 2 → L.ι) :
    wchart L (K := Fin 2) ![f, 𝟙 X] j ≤
      wchart L (fun _ : PUnit.{1} => f) (fun _ => j 0) ⊓ L.U (j 1) :=
  le_inf ((le_one L f _).2 ((le_two L f j).1 le_rfl).1) ((le_two L f j).1 le_rfl).2
def symEquiv : SymGen L f ≃ LB.Iso L (L.pull f) where
  toFun sy := ⟨fun p => res (toIso_le L f p) (ts sy ![p.1 ⟨⟩, p.2])⟩
  invFun w := ⟨fun j => res (ofIso_le L f j) (w.s (fun _ => j 0, j 1))⟩
  left_inv sy := gen_ext fun j => by
    refine (res_res _ _ _).trans ((res_gen_congr sy ?_ _ le_rfl).trans (res_self _ _))
    funext k
    fin_cases k <;> rfl
  right_inv w := gen_ext fun p => (res_res _ _ _).trans (res_self _ _)
def SymCompat (sy : SymGen L f) : Prop :=
  ∀ (a b a' b' : L.ι) (W : X.Opens) (h₁ : W ≤ f ⁻¹ᵁ (L.U a ⊓ L.U a')) (h₂ : W ≤ L.U b ⊓ L.U b')
    (h₃ : W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] ![a, b])
    (h₄ : W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] ![a', b']),
    res h₃ (ts sy ![a, b]) =
      res h₁ (pullU f _ (L.g a a')) * (res h₂ (L.g b b'))⁻¹ * res h₄ (ts sy ![a', b'])
end TwoForms
section Norm
variable {X T : Scheme.{0}} (L : LB X) (f : X ⟶ X) (e : T ⟶ X)
def DiagOne (sy : SymGen L f) : Prop :=
  ∀ (a : L.ι) (W : T.Opens) (h : W ≤ e ⁻¹ᵁ wchart L (K := Fin 2) ![f, 𝟙 X] ![a, a]),
    res h (pullU e _ (ts sy ![a, a])) = 1
def FixesRig (sy : SymGen L f) (r : LB.Gen (L.pull e)) : Prop :=
  ∀ (a b : L.ι) (W : T.Opens) (ha : W ≤ wchart L (fun _ : PUnit.{1} => e) (fun _ => a))
    (hb : W ≤ wchart L (fun _ : PUnit.{1} => e) (fun _ => b))
    (h : W ≤ e ⁻¹ᵁ wchart L (K := Fin 2) ![f, 𝟙 X] ![a, b]),
    res ha (ts r (fun _ => a)) = res h (pullU e _ (ts sy ![a, b])) * res hb (ts r (fun _ => b))
end Norm
section GroupNorm
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
def IsCanonSym (L : LB G.left) (sy : SymGen L (ι[G]).left) : Prop :=
  sy.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ sy (eSec G)) (LB.oneGen L)
end GroupNorm
section Pow
variable {S : Scheme.{0}}
def powEquiv (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) :
    Out.IsPowGrp G' G j ≃ PowerDatum j G' G where
  toFun p := ⟨p.pr, p.hom, fun T => ⟨fun x y h => p.lim.hom_ext fun i => congrFun h i.as,
    fun z => ⟨p.lim.lift (Fan.mk T z), funext fun i => p.lim.fac (Fan.mk T z) ⟨i⟩⟩⟩⟩
  invFun P := ⟨P.pr, P.isMonHom, mkFanLimit _ (fun s => ((P.bij s.pt).2 s.proj).choose)
    (fun s i => congrFun ((P.bij s.pt).2 s.proj).choose_spec i)
    (fun s _ hm => (P.bij s.pt).1
      ((funext hm).trans ((P.bij s.pt).2 s.proj).choose_spec.symm))⟩
  left_inv p := by
    cases p
    dsimp only
    congr 1
    exact Subsingleton.elim _ _
  right_inv _ := rfl
abbrev GrpWithMaps (G : Over S) (n : ℕ) := Σ H : Over S, GrpObj H × (Fin n → (H ⟶ G))
def powStep (G : Over S) [GrpObj G] {n : ℕ} (x : GrpWithMaps G n) : GrpWithMaps G (n + 1) :=
  ⟨G ⊗ x.1, letI := x.2.1; inferInstance,
    fun i => Fin.cases (fst G x.1) (fun k => snd G x.1 ≫ x.2.2 k) i⟩
variable {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
variable [IsCommMonObj G'] [IsCommMonObj G]
end Pow
section Clauses
variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] {j : ℕ}
end Clauses
def WellFormedSt : Prop :=
  ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (j : ℕ) (p : Out.IsPowGrp G' G j) (L : RigLB G),
    (Out.boxLB L.L p.pr).IsLB ∧ (Out.boxRig p L.L L.rig).IsGen
def BoxSymRigSt : Prop :=
  ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (j : ℕ) (p : Out.IsPowGrp G' G j) (L : RigLB G) (sy : SymGen L.L (ι[G]).left),
    IsCanonSym L.L sy → IsCanonSym (Out.boxLB L.L p.pr) (Out.boxSym p L.L sy)
end GlobalTheory.BoxCompare


