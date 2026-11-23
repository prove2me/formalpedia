-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
-- name    : Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:34.520422+00:00
-- url     : https://prove2.me/theorems/ced5adb2-19eb-4274-bec8-914aa7b60e1e
-- title:
--   Power Group Datum
-- statement:
--   Definitions and structural lemmas for Power Group Datum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/PowerGroupDatum.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}}
structure PowerDatum (j : ℕ) (G' G : Over S) [GrpObj G'] [GrpObj G] where

  pr : Fin j → (G' ⟶ G)

  isMonHom : ∀ i, IsMonHom (pr i)

  bij : ∀ T : Over S, Function.Bijective (fun (x : T ⟶ G') (i : Fin j) => x ≫ pr i)
attribute [instance] PowerDatum.isMonHom
section Power
variable (G : Over S)
def powObj (j : ℕ) : Over S :=
  Nat.rec (𝟙_ (Over S)) (fun _ H => G ⊗ H) j
def powPr (j : ℕ) : Fin j → (powObj G j ⟶ G) :=
  Nat.rec (motive := fun j => Fin j → (powObj G j ⟶ G)) (fun i => i.elim0)
    (fun j q i => Fin.cases (fst G (powObj G j)) (fun k => snd G (powObj G j) ≫ q k) i) j
variable [GrpObj G]
@[reducible] def powGrp (j : ℕ) : GrpObj (powObj G j) :=
  Nat.rec (motive := fun j => GrpObj (powObj G j)) (inferInstanceAs (GrpObj (𝟙_ (Over S))))
    (fun j h => letI := h; inferInstanceAs (GrpObj (G ⊗ powObj G j))) j
instance (j : ℕ) : GrpObj (powObj G j) := powGrp G j
instance powComm [IsCommMonObj G] (j : ℕ) : IsCommMonObj (powObj G j) := by
  induction j with
  | zero => exact inferInstanceAs (IsCommMonObj (𝟙_ (Over S)))
  | succ j ih => exact inferInstanceAs (IsCommMonObj (G ⊗ powObj G j))
lemma powPr_isMonHom : (j : ℕ) → (i : Fin j) → IsMonHom (powPr G j i)
  | 0 => fun i => i.elim0
  | j + 1 => fun i => by
    refine Fin.cases ?_ (fun k => ?_) i
    · exact inferInstanceAs (IsMonHom (fst G (powObj G j)))
    · have := powPr_isMonHom j k
      exact inferInstanceAs (IsMonHom (snd G (powObj G j) ≫ powPr G j k))
omit [GrpObj G] in
lemma powPr_bij (T : Over S) : (j : ℕ) →
    Function.Bijective (fun (x : T ⟶ powObj G j) (i : Fin j) => x ≫ powPr G j i)
  | 0 => ⟨fun x y _ => toUnit_unique (X := T) x y,
      fun _ => ⟨toUnit T, funext fun i => i.elim0⟩⟩
  | j + 1 => by
    obtain ⟨hi, hs⟩ := powPr_bij T j
    refine ⟨fun x y h => ?_, fun z => ?_⟩
    · refine CartesianMonoidalCategory.hom_ext (X := G) (Y := powObj G j) x y (congrFun h 0) (hi ?_)
      funext k
      exact (Category.assoc _ _ _).trans ((congrFun h k.succ).trans (Category.assoc _ _ _).symm)
    · obtain ⟨y, hy⟩ := hs (fun k => z k.succ)
      refine ⟨lift (z 0) y, funext fun i => Fin.cases ?_ (fun k => ?_) i⟩
      · exact lift_fst _ _
      · exact (lift_snd_assoc (z 0) y (powPr G j k)).trans (congrFun hy k)
def powDatum (j : ℕ) : PowerDatum j (powObj G j) G :=
  ⟨powPr G j, powPr_isMonHom G j, fun T => powPr_bij G T j⟩
end Power
section Symm
variable {G : Over S} [GrpObj G]
lemma eSec_inv : eSec G ≫ (GrpObj.inv (X := G)).left = 𝟙 _ ≫ eSec G := by
  rw [Category.id_comp, eSec, ← Over.comp_left]
  congr 1
  simp
variable [IsCommMonObj G]
def IsNormSymm (L : RigLB G) (w : LB.Iso L.L (L.L.pull (GrpObj.inv (X := G)).left)) : Prop :=
  w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec G) (fun _ => 1)) L.rig
      (rigPullOf (GrpObj.inv (X := G)).left (𝟙 _) eSec_inv L.L L.rig)
def RespectsCube (L : LB G.left) (w : LB.Iso L (L.pull (GrpObj.inv (X := G)).left))
    (t : LB.Gen (Theta G L)) : Prop :=
  LB.Gen.Maps (LB.linCombIso w (thφ G (x3 G)) thε) t
    ((CubeMap.ofHom (GrpObj.inv (X := G))).thetaPull L t)
example (L : RigLB G) : L.IsSymmetric ↔ ∃ w, IsNormSymm L w :=
  ⟨fun ⟨_, w, h⟩ => ⟨w, h⟩, fun ⟨w, h⟩ => ⟨eSec_inv, w, h⟩⟩
end Symm
namespace PowerDatum
variable {j : ℕ} {G' G : Over S} [GrpObj G'] [GrpObj G] (P : PowerDatum j G' G)
def box (L : LB G.left) : LB G'.left :=
  LB.LinComb L (K := Fin j) (fun i => (P.pr i).left) (fun _ => 1)
lemma eSec_pr (i : Fin j) : eSec G' ≫ (P.pr i).left = eSec G := by
  rw [eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
lemma inv_pr (i : Fin j) : (GrpObj.inv (X := G')).left ≫ (P.pr i).left =
    (P.pr i).left ≫ (GrpObj.inv (X := G)).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  simp
lemma rig_le (L : LB G.left) (a : PUnit.{1} → Fin j → L.ι) (i : Fin j) :
    LB.wchart (P.box L) (fun _ : PUnit.{1} => eSec G') a ≤
      LB.wchart L (fun _ : PUnit.{1} => eSec G) (fun _ => a ⟨⟩ i) := by
  intro y hy
  have h1 : (eSec G').base y ∈ LB.wchart L (fun i => (P.pr i).left) (a ⟨⟩) :=
    Set.mem_iInter.1 hy ⟨⟩
  have h2 : (P.pr i).left.base ((eSec G').base y) ∈ L.U (a ⟨⟩ i) := Set.mem_iInter.1 h1 i
  refine Set.mem_iInter.2 fun _ => ?_
  change (eSec G).base y ∈ (L.U (a ⟨⟩ i) : Set _)
  rw [← P.eSec_pr i]
  exact h2
def boxRig (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) :
    LB.Gen ((P.box L).pull (eSec G')) where
  s := fun a => ∏ i, res (P.rig_le L a i) (r.s (fun _ => a ⟨⟩ i))
lemma symm_le (L : LB G.left) (p : (PUnit.{1} → Fin j → L.ι) × (Fin j → L.ι)) (i : Fin j) :
    LB.wchart (P.box L) (fun _ : PUnit.{1} => (GrpObj.inv (X := G')).left) p.1 ⊓
        LB.wchart L (fun i => (P.pr i).left) p.2 ≤
      (P.pr i).left ⁻¹ᵁ (LB.wchart L (fun _ : PUnit.{1} => (GrpObj.inv (X := G)).left)
        (fun _ => p.1 ⟨⟩ i) ⊓ L.U (p.2 i)) := by
  intro y hy
  have h1 : (GrpObj.inv (X := G')).left.base y ∈ LB.wchart L (fun i => (P.pr i).left) (p.1 ⟨⟩) :=
    Set.mem_iInter.1 hy.1 ⟨⟩
  have h2 : (P.pr i).left.base ((GrpObj.inv (X := G')).left.base y) ∈ L.U (p.1 ⟨⟩ i) :=
    Set.mem_iInter.1 h1 i
  refine ⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.1 hy.2 i⟩
  change ((P.pr i).left ≫ (GrpObj.inv (X := G)).left).base y ∈ (L.U (p.1 ⟨⟩ i) : Set _)
  rw [← P.inv_pr i]
  exact h2
def boxSymm (L : LB G.left) (w : LB.Iso L (L.pull (GrpObj.inv (X := G)).left)) :
    LB.Iso (P.box L) ((P.box L).pull (GrpObj.inv (X := G')).left) where
  s := fun p => ∏ i, res (P.symm_le L p i)
    (pullU (P.pr i).left _ (w.s (fun _ => p.1 ⟨⟩ i, p.2 i)))
variable [IsCommMonObj G'] [IsCommMonObj G]
lemma theta_le (L : LB G.left) (a : thK.{0} → Fin j → L.ι) (i : Fin j) :
    LB.wchart (P.box L) (thφ G' (x3 G')) a ≤
      (P.pr i ⊗ₘ P.pr i ⊗ₘ P.pr i).left ⁻¹ᵁ LB.wchart L (thφ G (x3 G)) (fun I => a I i) := by
  intro y hy
  refine Set.mem_iInter.2 fun I => ?_
  have h1 : (thφ G' (x3 G') I).base y ∈ LB.wchart L (fun i => (P.pr i).left) (a I) :=
    Set.mem_iInter.1 hy I
  have h2 : (P.pr i).left.base ((thφ G' (x3 G') I).base y) ∈ L.U (a I i) := Set.mem_iInter.1 h1 i
  change ((CubeMap.ofHom (P.pr i)).F3 ≫ (psum G (x3 G) I.down).left).base y ∈
    (L.U (a I i) : Set _)
  rw [← (CubeMap.ofHom (P.pr i)).psum_comm I.down]
  exact h2
def boxTheta (L : LB G.left) (t : LB.Gen (Theta G L)) : LB.Gen (Theta G' (P.box L)) where
  s := fun a => ∏ i, res (P.theta_le L a i)
    (pullU (P.pr i ⊗ₘ P.pr i ⊗ₘ P.pr i).left _ (t.s (fun I => a I i)))
def boxRigLB (L : RigLB G) (hL : (P.box L.L).IsLB) (hr : (P.boxRig L.L L.rig).IsGen) :
    RigLB G' :=
  ⟨P.box L.L, P.boxRig L.L L.rig, hL, hr⟩
end PowerDatum
def BoxRigidifiedSt : Prop :=
  ∀ {S : Scheme.{0}} {j : ℕ} {G' G : Over S} [GrpObj G'] [GrpObj G] (P : PowerDatum j G' G)
    (L : RigLB G), (P.box L.L).IsLB ∧ (P.boxRig L.L L.rig).IsGen
def BoxCubicalSt : Prop :=
  ∀ {S : Scheme.{0}} {j : ℕ} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (P : PowerDatum j G' G) (L : RigLB G) (c : CubicalStr G L),
    ∃ (hL : (P.box L.L).IsLB) (hr : (P.boxRig L.L L.rig).IsGen)
      (c' : CubicalStr G' (P.boxRigLB L hL hr)), c'.t = P.boxTheta L.L c.t
def BoxNormSymmSt : Prop :=
  ∀ {S : Scheme.{0}} {j : ℕ} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (P : PowerDatum j G' G) (L : RigLB G)
    (w : LB.Iso L.L (L.L.pull (GrpObj.inv (X := G)).left)), IsNormSymm L w →
    ∃ (hL : (P.box L.L).IsLB) (hr : (P.boxRig L.L L.rig).IsGen),
      IsNormSymm (P.boxRigLB L hL hr) (P.boxSymm L.L w)
def BoxRespectsCubeSt : Prop :=
  ∀ {S : Scheme.{0}} {j : ℕ} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (P : PowerDatum j G' G) (L : LB G.left)
    (w : LB.Iso L (L.pull (GrpObj.inv (X := G)).left)) (t : LB.Gen (Theta G L)),
    RespectsCube L w t → RespectsCube (P.box L) (P.boxSymm L w) (P.boxTheta L t)
def BoxCubicalSymmetricSt : Prop :=
  BoxRigidifiedSt ∧ BoxCubicalSt ∧ BoxNormSymmSt ∧ BoxRespectsCubeSt
example (G : Over S) [GrpObj G] : PowerDatum 1 G G :=
  ⟨fun _ => 𝟙 G, fun _ => inferInstance, fun _ =>
    ⟨fun x y h => by simpa using congrFun h 0,
      fun z => ⟨z 0, funext fun i => by rw [Subsingleton.elim i 0]; simp⟩⟩⟩
end GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum


