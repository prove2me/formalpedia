-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:09.525935+00:00
-- url     : https://prove2.me/theorems/ec88a5cd-9810-4b1b-93ee-e77b19447fad
-- title:
--   Deg Prod
-- statement:
--   Definitions and structural lemmas for Deg Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/DegProd.lean

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
namespace GeneratorPullback
variable {X X' Y Y' : Scheme.{0}} (L : LB X)
lemma pullAlong_le {K : Type} [Fintype K] (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X))
    (ψ : K → (Y' ⟶ X')) (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (jj : K → (L.pull F).ι) :
    LB.wchart (L.pull F) ψ jj ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => jj k ⟨⟩) := by
  intro y hy
  show h.base y ∈ (⋂ k, (φ k).base ⁻¹' (L.U (jj k ⟨⟩) : Set X))
  refine Set.mem_iInter.2 fun k => ?_
  have h1 : (ψ k).base y ∈ LB.wchart L (fun _ : PUnit => F) (jj k) := Set.mem_iInter.1 hy k
  have h2 : F.base ((ψ k).base y) ∈ L.U (jj k ⟨⟩) := Set.mem_iInter.1 h1 ⟨⟩
  change (h ≫ φ k).base y ∈ (L.U (jj k ⟨⟩) : Set X)
  rw [← hψ k]
  exact h2
def pullAlong {K : Type} [Fintype K] (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K → (Y' ⟶ X')) (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε)) :
    LB.Gen (LB.LinComb (L.pull F) ψ ε) where
  s := fun jj => res (pullAlong_le L F h φ ψ hψ jj) (pullU h _ (t.s (fun k => jj k ⟨⟩)))
lemma box_le {J K : Type} [Fintype J] [Fintype K] (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X'))
    (jj : K → (LB.LinComb L F (fun _ => 1)).ι) (i : J) :
    LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj ≤
      LB.wchart (L.pull (F i)) φ (fun k _ => jj k i) := by
  intro y hy
  refine Set.mem_iInter.2 fun k => ?_
  have h1 : (φ k).base y ∈ LB.wchart L F (jj k) := Set.mem_iInter.1 hy k
  have h2 : (F i).base ((φ k).base y) ∈ L.U (jj k i) := Set.mem_iInter.1 h1 i
  show (φ k).base y ∈ (⋂ _u : PUnit, (F i).base ⁻¹' (L.U (jj k i) : Set X))
  exact Set.mem_iInter.2 fun _ => h2
def boxGen {J K : Type} [Fintype J] [Fintype K] (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X'))
    (ε : K → ℤ) (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) :
    LB.Gen (LB.LinComb (LB.LinComb L F (fun _ => 1)) φ ε) where
  s := fun jj => ∏ i, res (box_le L F φ jj i) ((t i).s (fun k _ => jj k i))
end GeneratorPullback
section Pow
variable {S : Scheme.{0}}
def powObj (G : Over S) : ℕ → Over S
  | 0 => 𝟙_ (Over S)
  | n + 1 => G ⊗ powObj G n
instance powObj.grp (G : Over S) [GrpObj G] : ∀ n, GrpObj (powObj G n)
  | 0 => inferInstanceAs (GrpObj (𝟙_ (Over S)))
  | n + 1 => by
    haveI := powObj.grp G n
    exact inferInstanceAs (GrpObj (G ⊗ powObj G n))
instance powObj.comm (G : Over S) [GrpObj G] [IsCommMonObj G] : ∀ n, IsCommMonObj (powObj G n)
  | 0 => inferInstanceAs (IsCommMonObj (𝟙_ (Over S)))
  | n + 1 => by
    haveI := powObj.comm G n
    exact inferInstanceAs (IsCommMonObj (G ⊗ powObj G n))
def powPr (G : Over S) : ∀ {n : ℕ}, Fin n → (powObj G n ⟶ G)
  | _ + 1, ⟨0, _⟩ => fst _ _
  | n + 1, ⟨i + 1, h⟩ => snd _ _ ≫ powPr G (n := n) ⟨i, Nat.lt_of_succ_lt_succ h⟩
instance powPr.isMonHom (G : Over S) [GrpObj G] : ∀ {n : ℕ} (i : Fin n), IsMonHom (powPr G i)
  | _ + 1, ⟨0, _⟩ => inferInstanceAs (IsMonHom (fst _ _))
  | n + 1, ⟨i + 1, h⟩ => by
    haveI := powPr.isMonHom G (n := n) ⟨i, Nat.lt_of_succ_lt_succ h⟩
    exact inferInstanceAs (IsMonHom (snd _ _ ≫ powPr G (n := n) ⟨i, Nat.lt_of_succ_lt_succ h⟩))
def powIsLimit (G : Over S) : ∀ n : ℕ, IsLimit (Fan.mk (powObj G n) (powPr G (n := n)))
  | 0 => mkFanLimit _ (fun s => toUnit s.pt) (fun _ i => i.elim0) (fun _ _ _ => toUnit_unique _ _)
  | n + 1 =>
    mkFanLimit _
      (fun s => lift (s.proj 0) ((powIsLimit G n).lift (Fan.mk s.pt (fun i => s.proj i.succ))))
      (fun s i => by
        refine Fin.cases ?_ (fun i => ?_) i
        · exact lift_fst _ _
        · exact (lift_snd_assoc _ _ _).trans
            ((powIsLimit G n).fac (Fan.mk s.pt fun i => s.proj i.succ) ⟨i⟩))
      (fun s m hm => by
        apply CartesianMonoidalCategory.hom_ext
        · have h0 : m ≫ powPr G 0 = s.proj 0 := hm 0
          exact h0.trans (lift_fst _ _).symm
        · refine Eq.trans ?_ (lift_snd _ _).symm
          apply (powIsLimit G n).hom_ext
          rintro ⟨i⟩
          have hi : m ≫ snd _ _ ≫ powPr G i = s.proj i.succ := hm i.succ
          exact ((Category.assoc _ _ _).trans hi).trans
            ((powIsLimit G n).fac (Fan.mk s.pt fun i => s.proj i.succ) ⟨i⟩).symm)
structure IsPowGrp (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) where
  pr : Fin j → (G' ⟶ G)
  hom : ∀ i, IsMonHom (pr i)
  lim : IsLimit (Fan.mk G' pr)
def powIsPowGrp (G : Over S) [GrpObj G] (n : ℕ) : IsPowGrp (powObj G n) G n :=
  ⟨powPr G, fun i => inferInstance, powIsLimit G n⟩
abbrev boxLB {G' G : Over S} {j : ℕ} (L : LB G.left) (pr : Fin j → (G' ⟶ G)) : LB G'.left :=
  LB.LinComb L (K := Fin j) (fun i => (pr i).left) (fun _ => 1)
variable {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] {j : ℕ}
def boxRig (p : IsPowGrp G' G j) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) :
    LB.Gen ((boxLB L p.pr).pull (eSec G')) :=
  GeneratorPullback.boxGen L (fun i => (p.pr i).left) (fun _ => eSec G') (fun _ => 1)
    (fun i => letI := p.hom i; (CubeMap.ofHom (p.pr i)).rigPull L r)
def boxCub (p : IsPowGrp G' G j) (L : LB G.left) (t : LB.Gen (Theta G L)) :
    LB.Gen (Theta G' (boxLB L p.pr)) :=
  GeneratorPullback.boxGen L (fun i => (p.pr i).left) (thφ G' (x3 G')) thε
    (fun i => letI := p.hom i; (CubeMap.ofHom (p.pr i)).thetaPull L t)
theorem inv_pr (p : IsPowGrp G' G j) (i : Fin j) (k : Fin 2) :
    (![(ι[G']).left, 𝟙 G'.left] : Fin 2 → (G'.left ⟶ G'.left)) k ≫ (p.pr i).left =
      (p.pr i).left ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k := by
  have := p.hom i
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]
  · simp
def boxSym (p : IsPowGrp G' G j) (L : LB G.left)
    (sy : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) :
    LB.Gen (LB.LinComb (boxLB L p.pr) (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1]) :=
  GeneratorPullback.boxGen L (fun i => (p.pr i).left) _ _
    (fun i => GeneratorPullback.pullAlong L (p.pr i).left (p.pr i).left _ _ _ (inv_pr p i) sy)
def BoxIsLBSt : Prop :=
  ∀ (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left),
    L.IsLB → (boxLB L p.pr).IsLB
def BoxRigIsGenSt : Prop :=
  ∀ (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ)
    (p : IsPowGrp G' G j) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))),
    L.IsLB → r.IsGen → (boxRig p L r).IsGen
def BoxCubicalSt : Prop :=
  ∀ (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ)
    (p : IsPowGrp G' G j) (L : RigLB G) (c : CubicalStr G L) (hL : (boxLB L.L p.pr).IsLB)
    (hr : (boxRig p L.L L.rig).IsGen),
    ∃ c' : CubicalStr G' ⟨boxLB L.L p.pr, boxRig p L.L L.rig, hL, hr⟩, c'.t = boxCub p L.L c.t
def BoxSymSt : Prop :=
  ∀ (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ)
    (p : IsPowGrp G' G j) (L : LB G.left)
    (sy : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])),
    L.IsLB → sy.IsGen →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ sy (eSec G)) (LB.oneGen L) →
    (boxSym p L sy).IsGen ∧
      LB.Gen.Corr (boxLB L p.pr) _ _ _ _ (LB.pullGen (boxLB L p.pr) _ _ (boxSym p L sy) (eSec G'))
        (LB.oneGen (boxLB L p.pr))
end Pow
end ReciprocityTheory.ChartRestriction.G.Out


