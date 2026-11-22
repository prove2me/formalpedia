-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:27:43.539642+00:00
-- url     : https://prove2.me/theorems/f3a4577b-09c0-44bb-9293-b3fca4c3cab8
-- title:
--   Cube Symmetric Swap First
-- statement:
--   Definitions and structural lemmas for Cube Symmetric Swap First, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/CubicalStructures/CubeSymmetricSwapFirst.lean

import Mathlib
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
def res {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) : Γ(X, U)ˣ →* Γ(X, V)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom
def pullU {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) : Γ(X, U)ˣ →* Γ(Y, f ⁻¹ᵁ U)ˣ :=
  Units.map (f.app U).hom
structure LB (X : Scheme.{u}) where
  ι : Type u
  U : ι → X.Opens
  g : ∀ i j, Γ(X, U i ⊓ U j)ˣ
structure LB.IsLB {X : Scheme.{u}} (L : LB X) : Prop where
  cover : ⨆ i, L.U i = ⊤
  g_self : ∀ i, res (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) (L.g i i) = 1
  cocycle : ∀ i j k,
    res (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j) (L.g i j) *
    res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k) (L.g j k) =
    res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k) (L.g i k)
namespace LB
variable {X Y Z : Scheme.{u}}
structure Gen (L : LB X) where
  s : ∀ i, Γ(X, L.U i)ˣ
def Gen.IsGen {L : LB X} (t : Gen L) : Prop :=
  ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (t.s i) =
    L.g i j * res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (t.s j)
structure Sec (L : LB X) where
  f : ∀ i, Γ(X, L.U i)
  compat : ∀ i j, (X.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op).hom (f i) =
    (L.g i j : Γ(X, L.U i ⊓ L.U j)) *
      (X.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op).hom (f j)
def div (M L : LB X) : LB X where
  ι := M.ι × L.ι
  U := fun p => M.U p.1 ⊓ L.U p.2
  g := fun p q =>
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ≤ M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
    (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ≤ L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹
abbrev Iso (L M : LB X) := Gen (div M L)
def wchart (L : LB X) {K : Type u} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι) : Y.Opens :=
  ⟨⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X),
    isOpen_iInter_of_finite fun k => (L.U (j k)).isOpen.preimage (φ k).base.hom.continuous⟩
lemma wchart_le (L : LB X) {K : Type u} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι) (k : K) :
    wchart L φ j ≤ φ k ⁻¹ᵁ L.U (j k) :=
  fun _ hy => Set.mem_iInter.1 hy k
def LinComb (L : LB X) {K : Type u} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) : LB Y where
  ι := K → L.ι
  U := wchart L φ
  g := fun j j' => ∏ k, (res (le_inf (inf_le_left.trans (wchart_le L φ j k))
      (inf_le_right.trans (wchart_le L φ j' k)) :
        wchart L φ j ⊓ wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
      (pullU (φ k) _ (L.g (j k) (j' k)))) ^ (ε k)
abbrev pull (L : LB X) (f : Y ⟶ X) : LB Y := LinComb L (K := PUnit) (fun _ => f) (fun _ => 1)
variable (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']
def pullGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : Gen (LinComb L φ ε)) (h : Z ⟶ Y) :
    Gen (LinComb L (fun k => h ≫ φ k) ε) where
  s := fun j => res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
    wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ wchart L φ j)
    (pullU h _ (c.s j))
def mulGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : Gen (LinComb L φ ε)) (t' : Gen (LinComb L φ' ε')) :
    Gen (LinComb L (K := K ⊕ K') (Sum.elim φ φ') (Sum.elim ε ε')) where
  s := fun j => res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)) :
      wchart L (Sum.elim φ φ') j ≤ wchart L φ (j ∘ Sum.inl)) (t.s _) *
    res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)) :
      wchart L (Sum.elim φ φ') j ≤ wchart L φ' (j ∘ Sum.inr)) (t'.s _)
def invGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : Gen (LinComb L φ ε)) :
    Gen (LinComb L φ (fun k => - ε k)) where
  s := fun j => (t.s j)⁻¹
def Coh (φ : K → (Y ⟶ X)) (j : K → L.ι) : Prop :=
  ∀ k₁ k₂, φ k₁ = φ k₂ → j k₁ = j k₂
open scoped Classical in

def SameSum (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) : Prop :=
  ∀ ψ : Y ⟶ X, (∑ k, if φ k = ψ then ε k else 0) = ∑ k', if φ' k' = ψ then ε' k' else 0
def Gen.Corr (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : Gen (LinComb L φ ε)) (t' : Gen (LinComb L φ' ε')) : Prop :=
  ∀ (j : K → L.ι) (j' : K' → L.ι), Coh L φ j → Coh L φ' j' →
    (∀ k k', φ k = φ' k' → j k = j' k') →
    res (inf_le_left : wchart L φ j ⊓ wchart L φ' j' ≤ wchart L φ j) (t.s j) =
    res (inf_le_right : wchart L φ j ⊓ wchart L φ' j' ≤ wchart L φ' j') (t'.s j')
def oneGen : Gen (LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s := fun _ => 1
end LB
section Group
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G]
def padd {T : Over S} (a b : T ⟶ G) : T ⟶ G := lift a b ≫ μ[G]
def pzero (T : Over S) : T ⟶ G := toUnit T ≫ η[G]
def psum {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) : T ⟶ G :=
  ((List.finRange n).filter (· ∈ I)).foldr (fun k acc => padd G (x k) acc) (pzero G T)
abbrev G2 : Over S := G ⊗ G
abbrev G3 : Over S := G ⊗ G ⊗ G
abbrev G4 : Over S := G ⊗ G ⊗ G ⊗ G
def x2 : Fin 2 → (G2 G ⟶ G) := ![fst G G, snd G G]
def x3 : Fin 3 → (G3 G ⟶ G) := ![fst _ _, snd _ _ ≫ fst _ _, snd _ _ ≫ snd _ _]
def x4 : Fin 4 → (G4 G ⟶ G) :=
  ![fst _ _, snd _ _ ≫ fst _ _, snd _ _ ≫ snd _ _ ≫ fst _ _, snd _ _ ≫ snd _ _ ≫ snd _ _]
def eSec : (𝟙_ (Over S)).left ⟶ G.left := η[G].left
structure RigLB where
  L : LB G.left
  rig : LB.Gen (L.pull (eSec G))
  isLB : L.IsLB
  rigGen : rig.IsGen
def cubeLB {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (L : LB G.left) : LB T.left :=
  LB.LinComb L (K := ULift.{u} (Finset (Fin n))) (fun I => (psum G x I.down).left)
    (fun I => (-1) ^ (n - I.down.card))
def abelian₂ (L : LB G.left) : LB (G2 G).left := cubeLB G (x2 G) L
def Theta (L : LB G.left) : LB (G3 G).left := cubeLB G (x3 G) L
def thK := ULift.{u} (Finset (Fin 3))
instance : Fintype (thK) := inferInstanceAs (Fintype (ULift (Finset (Fin 3))))
def thφ {T : Over S} (x : Fin 3 → (T ⟶ G)) : thK → (T.left ⟶ G.left) := fun I => (psum G x I.down).left
def thε : thK → ℤ := fun I => (-1) ^ (3 - I.down.card)
def faceMap (i : Fin 3) : G2 G ⟶ G3 G :=
  ![lift (pzero G _) (lift (x2 G 0) (x2 G 1)), lift (x2 G 0) (lift (pzero G _) (x2 G 1)),
    lift (x2 G 0) (lift (x2 G 1) (pzero G _))] i
structure CubicalStr (L : RigLB G) where
  t : LB.Gen (Theta G L.L)
  isGen : t.IsGen
  face : ∀ i : Fin 3,
    LB.Gen.Corr L.L _ _ (Y := (G2 G).left) _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε t (faceMap G i).left)
      (LB.oneGen L.L)
  cubeSymmetric_swap_first : LB.Gen.Corr L.L _ _ _ _ t
    (LB.pullGen L.L (thφ G (x3 G)) thε t (lift (x3 G 1) (lift (x3 G 0) (x3 G 2))).left)
  cubeSymmetric_swap_last : LB.Gen.Corr L.L _ _ _ _ t
    (LB.pullGen L.L (thφ G (x3 G)) thε t (lift (x3 G 0) (lift (x3 G 2) (x3 G 1))).left)
  cocycle : LB.Gen.Corr L.L _ _ _ _
    (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε t
        (lift (padd G (x4 G 0) (x4 G 1)) (lift (x4 G 2) (x4 G 3))).left)
      (LB.pullGen L.L (thφ G (x3 G)) thε t (lift (x4 G 0) (lift (x4 G 1) (x4 G 3))).left))
    (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε t
        (lift (x4 G 0) (lift (padd G (x4 G 1) (x4 G 2)) (x4 G 3))).left)
      (LB.pullGen L.L (thφ G (x3 G)) thε t (lift (x4 G 1) (lift (x4 G 2) (x4 G 3))).left))
end Group
end
end ReciprocityTheory.ChartRestriction.G.Semi


