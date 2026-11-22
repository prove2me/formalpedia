-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:41.366893+00:00
-- url     : https://prove2.me/theorems/dcd0a624-c126-40b1-a583-21d233ff7fe5
-- title:
--   Cubical Pull Base Change St
-- statement:
--   Definitions and structural lemmas for Cubical Pull Base Change St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/CubicalStructures/CubicalPullBaseChangeSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
namespace LB
variable {X Y : Scheme.{u}}
def linCombIso {L M : LB X} {K : Type u} [Fintype K] (w : Iso L M) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : Iso (LinComb L φ ε) (LinComb M φ ε) where
  s := fun p => ∏ k, (res (le_inf (inf_le_left.trans (wchart_le M φ p.1 k))
      (inf_le_right.trans (wchart_le L φ p.2 k)) :
        wchart M φ p.1 ⊓ wchart L φ p.2 ≤ φ k ⁻¹ᵁ (M.U (p.1 k) ⊓ L.U (p.2 k)))
      (pullU (φ k) _ (w.s (p.1 k, p.2 k)))) ^ (ε k)
def Gen.Maps {A B : LB X} (w : Iso A B) (a : Gen A) (b : Gen B) : Prop :=
  ∀ p : B.ι × A.ι, res (inf_le_left : B.U p.1 ⊓ A.U p.2 ≤ B.U p.1) (b.s p.1) =
    @id (Γ(X, B.U p.1 ⊓ A.U p.2)ˣ) (w.s p) * res (inf_le_right : B.U p.1 ⊓ A.U p.2 ≤ A.U p.2) (a.s p.2)
end LB
section Group
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
structure CubeMap {S S' : Scheme.{u}} (G' : Over S') (G : Over S) [GrpObj G'] [IsCommMonObj G']
    [GrpObj G] [IsCommMonObj G] where
  F : G'.left ⟶ G.left
  F3 : (G3 G').left ⟶ (G3 G).left
  e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left
  e_comm : eSec G' ≫ F = e ≫ eSec G
  psum_comm : ∀ I : Finset (Fin 3), (psum G' (x3 G') I).left ≫ F = F3 ≫ (psum G (x3 G) I).left
variable {S S' : Scheme.{u}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G']
  [GrpObj G] [IsCommMonObj G]
lemma rigPull_le (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left)
    (j : PUnit.{u+1} → PUnit.{u+1} → L.ι) :
    LB.wchart (L.pull F) (fun _ : PUnit.{u+1} => eSec G') j ≤
      e ⁻¹ᵁ LB.wchart L (fun _ : PUnit.{u+1} => eSec G) (fun _ => j ⟨⟩ ⟨⟩) := by
  intro x hx
  have h0 : (eSec G').base x ∈ (L.pull F).U (j ⟨⟩) := Set.mem_iInter.1 hx ⟨⟩
  have h1 : x ∈ (eSec G' ≫ F) ⁻¹ᵁ L.U (j ⟨⟩ ⟨⟩) := Set.mem_iInter.1 h0 ⟨⟩
  rw [he] at h1
  exact Set.mem_iInter.2 fun _ => h1
def rigPullOf (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) :
    LB.Gen ((L.pull F).pull (eSec G')) where
  s := fun j => res (rigPull_le F e he L j) (pullU e _ (r.s (fun _ => j ⟨⟩ ⟨⟩)))
namespace CubeMap
lemma theta_le (m : CubeMap G' G) (L : LB G.left) (j : thK.{u} → PUnit.{u+1} → L.ι) :
    LB.wchart (L.pull m.F) (thφ G' (x3 G')) j ≤
      m.F3 ⁻¹ᵁ LB.wchart L (thφ G (x3 G)) (fun I => j I ⟨⟩) := by
  intro x hx
  refine Set.mem_iInter.2 fun I => ?_
  have h0 : (thφ G' (x3 G') I).base x ∈ (L.pull m.F).U (j I) := Set.mem_iInter.1 hx I
  have h1 : x ∈ ((psum G' (x3 G') I.down).left ≫ m.F) ⁻¹ᵁ L.U (j I ⟨⟩) :=
    Set.mem_iInter.1 h0 ⟨⟩
  rw [m.psum_comm I.down] at h1
  exact h1
def rigPull (m : CubeMap G' G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) :
    LB.Gen ((L.pull m.F).pull (eSec G')) :=
  rigPullOf m.F m.e m.e_comm L r
def thetaPull (m : CubeMap G' G) (L : LB G.left) (t : LB.Gen (Theta G L)) :
    LB.Gen (Theta G' (L.pull m.F)) where
  s := fun j => res (m.theta_le L j) (pullU m.F3 _ (t.s (fun I => j I ⟨⟩)))
def rigLB (m : CubeMap G' G) (L : RigLB G) (hL : (L.L.pull m.F).IsLB)
    (hr : (m.rigPull L.L L.rig).IsGen) : RigLB G' :=
  ⟨L.L.pull m.F, m.rigPull L.L L.rig, hL, hr⟩
def IsPullCubical (m : CubeMap G' G) {L' : RigLB G'} (c' : CubicalStr G' L') {L : RigLB G}
    (c : CubicalStr G L) : Prop :=
  ∃ w : LB.Iso L'.L (L.L.pull m.F), w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{u+1}) (fun _ => eSec G') (fun _ => 1)) L'.rig
      (m.rigPull L.L L.rig) ∧
    LB.Gen.Maps (LB.linCombIso w (thφ G' (x3 G')) thε) c'.t (m.thetaPull L.L c.t)
end CubeMap
def RigLB.IsSymmetric (L : RigLB G) : Prop :=
  ∃ he : eSec G ≫ (GrpObj.inv (X := G)).left = 𝟙 _ ≫ eSec G,
  ∃ w : LB.Iso L.L (L.L.pull (GrpObj.inv (X := G)).left), w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{u+1}) (fun _ => eSec G) (fun _ => 1)) L.rig
      (rigPullOf (GrpObj.inv (X := G)).left (𝟙 _) he L.L L.rig)
section OfHom
variable {T G'' G₀ : Over S} [GrpObj G''] [IsCommMonObj G''] [GrpObj G₀] [IsCommMonObj G₀]
lemma foldr_padd_comp (f : G'' ⟶ G₀) [IsMonHom f] {n : ℕ} (x : Fin n → (T ⟶ G''))
    (l : List (Fin n)) :
    l.foldr (fun k acc => padd G'' (x k) acc) (pzero G'' T) ≫ f =
      l.foldr (fun k acc => padd G₀ (x k ≫ f) acc) (pzero G₀ T) := by
  induction l with
  | nil => simp only [List.foldr_nil, pzero, Category.assoc, IsMonHom.one_hom]
  | cons k l ih =>
    simp only [List.foldr_cons]
    rw [← ih]
    simp only [padd, Category.assoc, IsMonHom.mul_hom,
      CartesianMonoidalCategory.lift_map_assoc]
lemma foldr_padd_pre {T' : Over S} (h : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G₀))
    (l : List (Fin n)) :
    l.foldr (fun k acc => padd G₀ (h ≫ x k) acc) (pzero G₀ T') =
      h ≫ l.foldr (fun k acc => padd G₀ (x k) acc) (pzero G₀ T) := by
  induction l with
  | nil =>
    simp only [List.foldr_nil, pzero]
    rw [← Category.assoc, CartesianMonoidalCategory.comp_toUnit]
  | cons k l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    simp only [padd, CartesianMonoidalCategory.comp_lift_assoc]
lemma cubeProj_comp_map (f : G'' ⟶ G₀) (k : Fin 3) :
    x3 G'' k ≫ f = (f ⊗ₘ f ⊗ₘ f) ≫ x3 G₀ k := by
  fin_cases k <;>
    simp [x3, CartesianMonoidalCategory.tensorHom_fst, CartesianMonoidalCategory.tensorHom_snd,
      CartesianMonoidalCategory.tensorHom_fst_assoc, CartesianMonoidalCategory.tensorHom_snd_assoc]
def CubeMap.ofHom (f : G'' ⟶ G₀) [IsMonHom f] : CubeMap G'' G₀ where
  F := f.left
  F3 := (f ⊗ₘ f ⊗ₘ f).left
  e := 𝟙 _
  e_comm := by
    rw [Category.id_comp, eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  psum_comm := fun I => by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp only [psum]
    rw [foldr_padd_comp, ← foldr_padd_pre]
    have hx : (fun k acc => padd G₀ (x3 G'' k ≫ f) acc) =
        (fun k acc => padd G₀ ((f ⊗ₘ f ⊗ₘ f) ≫ x3 G₀ k) acc) := by
      funext k acc; rw [cubeProj_comp_map]
    rw [hx]
end OfHom
def PullIsLBSt : Prop :=
  ∀ {X Y : Scheme.{u}} (L : LB X) (F : Y ⟶ X), L.IsLB → (L.pull F).IsLB
def RigPullIsGenSt : Prop :=
  ∀ {S S' : Scheme.{u}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))),
    L.IsLB → r.IsGen → (rigPullOf F e he L r).IsGen
def ThetaPullIsGenSt : Prop :=
  ∀ {S S' : Scheme.{u}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L : LB G.left) (t : LB.Gen (Theta G L)),
    L.IsLB → t.IsGen → (m.thetaPull L t).IsGen
def LinCombIsoIsGenSt : Prop :=
  ∀ {X Y : Scheme.{u}} {L M : LB X} {K : Type u} [Fintype K] (w : LB.Iso L M)
    (φ : K → (Y ⟶ X)) (ε : K → ℤ), L.IsLB → M.IsLB → w.IsGen → (LB.linCombIso w φ ε).IsGen
def CubicalPullOfHomSt : Prop :=
  ∀ {S : Scheme.{u}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (f : G' ⟶ G) [IsMonHom f] (L : RigLB G) (c : CubicalStr G L),
    ∃ (hL : (L.L.pull f.left).IsLB) (hr : ((CubeMap.ofHom f).rigPull L.L L.rig).IsGen)
      (c' : CubicalStr G' ((CubeMap.ofHom f).rigLB L hL hr)),
      c'.t = (CubeMap.ofHom f).thetaPull L.L c.t
open scoped CategoryTheory.Obj in

def CubicalPullBaseChangeSt : Prop :=
  ∀ {S S' : Scheme.{u}} (p : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    [IsCommMonObj ((Over.pullback p).obj G)],
    (∃ m : CubeMap ((Over.pullback p).obj G) G, m.F = pullback.fst G.hom p ∧ m.e = p) ∧
    ∀ (m : CubeMap ((Over.pullback p).obj G) G), m.F = pullback.fst G.hom p → m.e = p →
      ∀ (L : RigLB G) (c : CubicalStr G L),
      ∃ (hL : (L.L.pull m.F).IsLB) (hr : (m.rigPull L.L L.rig).IsGen)
        (c' : CubicalStr _ (m.rigLB L hL hr)), c'.t = m.thetaPull L.L c.t
def SymmPullOfHomSt : Prop :=
  ∀ {S : Scheme.{u}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (f : G' ⟶ G) [IsMonHom f] (L : RigLB G) (hL : (L.L.pull f.left).IsLB)
    (hr : ((CubeMap.ofHom f).rigPull L.L L.rig).IsGen),
    L.IsSymmetric → ((CubeMap.ofHom f).rigLB L hL hr).IsSymmetric
def IsPullCubicalUniqueSt : Prop :=
  ∀ {S S' : Scheme.{u}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) {L : RigLB G} (c : CubicalStr G L)
    {L₁ L₂ : RigLB G'} (c₁ : CubicalStr G' L₁) (c₂ : CubicalStr G' L₂),
    m.IsPullCubical c₁ c → m.IsPullCubical c₂ c →
    ∃ w : LB.Iso L₁.L L₂.L, w.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit.{u+1}) (fun _ => eSec G') (fun _ => 1)) L₁.rig
        L₂.rig ∧
      LB.Gen.Maps (LB.linCombIso w (thφ G' (x3 G')) thε) c₁.t c₂.t
end Group
end
end ReciprocityTheory.ChartRestriction.G.Semi


