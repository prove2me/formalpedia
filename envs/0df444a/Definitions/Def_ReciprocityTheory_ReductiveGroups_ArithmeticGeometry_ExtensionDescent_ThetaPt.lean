-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:24.866364+00:00
-- url     : https://prove2.me/theorems/4321ed5c-dc2f-4da0-8d13-4723f2892a1b
-- title:
--   Theta Pt
-- statement:
--   Definitions and structural lemmas for Theta Pt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ThetaPt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver
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
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
def negT (T : Over S) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A ≫ (GrpObj.inv : A ⟶ A))
def negLB (L : LB A.left) (k : ℤ) (T : Over S) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k]
def powφ {T : Over S} (x : T ⟶ A) (n : ℕ) : Fin n × Fin 2 → ((T ⊗ A).left ⟶ A.left) :=
  fun p => (translT A (x ^ (p.1 : ℕ))).left ≫ (![(snd T A).left, (translPt A x).left] p.2)
def powε (k : ℤ) (n : ℕ) : Fin n × Fin 2 → ℤ := fun p => ![k, -k] p.2
def powGen (L : LB A.left) (k : ℤ) {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) :
    LB.Gen (LB.LinComb L (powφ A θ.pt n) (powε k n)) where
  s := fun j => ∏ j₀ : Fin n,
    res ((fun _ hy => Set.mem_iInter.2 fun b => Set.mem_iInter.1 hy (j₀, b)) :
        LB.wchart L (powφ A θ.pt n) j ≤
          LB.wchart L (fun b => (translT A (θ.pt ^ (j₀ : ℕ))).left ≫
            (![(snd T A).left, (translPt A θ.pt).left] b)) (fun b => j (j₀, b)))
      ((LB.pullGen L _ _ θ.φ (translT A (θ.pt ^ (j₀ : ℕ))).left).s (fun b => j (j₀, b)))
def symGen (L : LB A.left) (k : ℤ) {T : Over S} (θ : ThetaGrp A L k T)
    (nu : LB.Gen (negLB A L k T)) :=
  LB.mulGen L _ _ _ _
    (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ θ.φ (translT A θ.pt⁻¹).left) nu)
    (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ θ.φ (negT A T).left)
      (LB.invGen L _ _ (LB.pullGen L _ _ nu (translT A θ.pt⁻¹).left)))
structure SymLift (L : LB A.left) (k : ℤ) (n : ℕ) {T : Over S} (x : T ⟶ A)
    (θ : ThetaGrp A L k T) : Prop where

  pt_eq : θ.pt = x

  pow_eq : LB.Gen.Corr L _ _ _ _ (powGen A L k θ n) (LB.oneGen L)

  sym : ∃ nu : LB.Gen (negLB A L k T), nu.IsGen ∧ LB.Gen.Corr L _ _ _ _ (symGen A L k θ nu) (LB.oneGen L)
def LPow (L : LB A.left) (a : ℤ) (T : Over S) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 1) (fun _ => (snd T A).left) (fun _ => a)
def liftFun {T : Over S} (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤)) : Γ((T ⊗ A).left, W) :=
  ((T ⊗ A).left.presheaf.map (homOfLE le_top).op).hom ((fst T A).left.appTop.hom r)
theorem chart_le_zero (L : LB A.left) {T : Over S} (m : T ⊗ A ⟶ A) (j : Fin 2 → L.ι) :
    LB.wchart L ![(snd T A).left, m.left] j ≤ LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0) :=
  fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
theorem chart_le_pull (L : LB A.left) {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A)
    (hm : ψ ≫ snd T A = m) (j : Fin 2 → L.ι) :
    LB.wchart L ![(snd T A).left, m.left] j ≤
      ψ.left ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1) := by
  intro y hy
  have h1 : m.left.base y ∈ (L.U (j 1) : Set A.left) := Set.mem_iInter.1 hy 1
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  rw [← e] at h1
  exact Set.mem_iInter.2 fun _ => h1
def IsTwistPull (L : LB A.left) {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A)
    (hm : ψ ≫ snd T A = m) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b]))
    (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)) : Prop :=
  ∀ j : Fin 2 → L.ι,
    ((T ⊗ A).left.presheaf.map (homOfLE (chart_le_zero A L m j)).op).hom (s'.f (fun _ => j 0)) =
      (show Γ((T ⊗ A).left, LB.wchart L ![(snd T A).left, m.left] j) from (α.s j).val) *
        ((T ⊗ A).left.presheaf.map (homOfLE (chart_le_pull A L ψ m hm j)).op).hom
          ((ψ.left.app _).hom (s.f (fun _ => j 1)))
def IsActOf (L : LB A.left) (k : ℤ) {T : Over S} (θ : ThetaGrp A L k T) (s s' : LB.Sec (LPow A L k T)) : Prop :=
  IsTwistPull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) k k θ.φ s s'
def IsGenSec (L : LB A.left) (a : ℤ) {T : Over S} (th : LB.Sec (LPow A L a T)) : Prop :=
  ∀ s : LB.Sec (LPow A L a T), ∃ r : Γ(T.left, ⊤), ∀ j, s.f j = liftFun A _ r * th.f j
def ptSecT {T : Over S} (z : T ⟶ A) : T ⟶ T ⊗ A := lift (𝟙 T) z
theorem val_le (L : LB A.left) {T : Over S} (z : T ⟶ A) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => z.left) j ≤
      (ptSecT A z).left ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => (snd T A).left) j := by
  intro y hy
  have h1 : z.left.base y ∈ (L.U (j 0) : Set A.left) := Set.mem_iInter.1 hy 0
  have e : (ptSecT A z).left ≫ (snd T A).left = z.left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  rw [← e] at h1
  exact Set.mem_iInter.2 fun i => by
    rw [Subsingleton.elim i 0]; exact h1
def IsValueAt (L : LB A.left) (a : ℤ) {T : Over S} (s : LB.Sec (LPow A L a T)) (z : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)))
    (v : Γ(T.left, ⊤)) : Prop :=
  ∀ j : Fin 1 → L.ι,
    (T.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (s.f j)) =
      (T.left.presheaf.map (homOfLE le_top).op).hom v * (show Γ(T.left, LB.wchart L (fun _ : Fin 1 => z.left) j) from (τ.s j).val)
def mulT (T : Over S) (k : ℕ) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A ^ k)
def IsThetaPtOver (P : PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (v : I → Γ(T.left, ⊤)) : Prop :=
  ∃ (th : LB.Sec (LPow P.A P.L 1 T)) (s1 : LB.Sec (LPow P.A P.L ((k : ℤ) ^ 2) T))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![(k : ℤ) ^ 2, -1]))
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left)
      (fun _ => (k : ℤ) ^ 2)))
    (U : I → ThetaGrp P.A P.L ((k : ℤ) ^ 2) T) (s2 : I → LB.Sec (LPow P.A P.L ((k : ℤ) ^ 2) T))
    (w : I → Γ(T.left, ⊤)) (u : Γ(T.left, ⊤)ˣ),
    IsGenSec P.A P.L 1 th ∧ α.IsGen ∧ τ.IsGen ∧
    IsTwistPull P.A P.L (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _) ((k : ℤ) ^ 2) 1 α th s1 ∧
    (∀ i, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) (U i)) ∧
    (∀ i, IsActOf P.A P.L ((k : ℤ) ^ 2) (U i) s1 (s2 i)) ∧
    (∀ i, IsValueAt P.A P.L ((k : ℤ) ^ 2) (s2 i) 1 τ (w i)) ∧
    ∀ i, v i = (u : Γ(T.left, ⊤)) * w i
def IsThetaPt (P : PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (v : I → Γ(T.left, ⊤)) : Prop :=
  Odd k ∧ IsUnit (k : Γ(T.left, ⊤)) ∧ ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
    IsThetaPtOver P k (fun i => overResι V ≫ x i) (fun i => V.ι.appTop.hom (v i))
def IsVVGen (P : PolAV S) (N m : ℕ) {T : Over S} (t : LB.Sec (LPow P.A P.L N T)) : Prop :=
  ∃ (th : LB.Sec (LPow P.A P.L 1 T)) (s1 : LB.Sec (LPow P.A P.L N T))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]))
    (U : ThetaGrp P.A P.L N T),
    α.IsGen ∧ IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) N 1 α th s1 ∧
    IsActOf P.A P.L N U s1 t
def InVVOver (P : PolAV S) (N m : ℕ) {T : Over S} (s : LB.Sec (LPow P.A P.L N T)) : Prop :=
  ∃ (n : ℕ) (r : Fin n → Γ(T.left, ⊤)) (t : Fin n → LB.Sec (LPow P.A P.L N T)),
    (∀ l, IsVVGen P N m (t l)) ∧ ∀ j, s.f j = ∑ l, liftFun P.A _ (r l) * (t l).f j
theorem chart_le_res (L : LB A.left) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A)
    (a : ℤ) (j : Fin 1 → L.ι) :
    (LPow A L a T').U j ≤ h.left ⁻¹ᵁ (LPow A L a T).U j := by
  intro y hy
  have h1 : (snd T' A).left.base y ∈ (L.U (j 0) : Set A.left) := Set.mem_iInter.1 hy 0
  have e : h.left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, hh]
  rw [← e] at h1
  exact Set.mem_iInter.2 fun i => by
    rw [Subsingleton.elim i 0]; exact h1
def IsPullSec (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A)
    (hh : h ≫ snd T A = snd T' A) (s : LB.Sec (LPow A L a T)) (s' : LB.Sec (LPow A L a T')) : Prop :=
  ∀ j, s'.f j = ((T' ⊗ A).left.presheaf.map (homOfLE (chart_le_res A L h hh a j)).op).hom
    ((h.left.app _).hom (s.f j))
def InVV (P : PolAV S) (N m : ℕ) {T : Over S} (s : LB.Sec (LPow P.A P.L N T)) : Prop :=
  ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ sV : LB.Sec (LPow P.A P.L N (overRes V)),
    IsPullSec P.A P.L N (overResι V ▷ P.A) (whiskerRight_snd _ _) s sV ∧ InVVOver P N m sV
def InVVw (P : PolAV S) (N m : ℕ) {T : Over S} {I : Type} (h : I → (T ⟶ P.A))
    (χ : I → Γ(T.left, ⊤)ˣ) (s : LB.Sec (LPow P.A P.L N T)) : Prop :=
  Odd N ∧ IsUnit (N : Γ(T.left, ⊤)) ∧ InVV P N m s ∧
    ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ sV : LB.Sec (LPow P.A P.L N (overRes V)),
      IsPullSec P.A P.L N (overResι V ▷ P.A) (whiskerRight_snd _ _) s sV ∧
      ∀ (i : I) (U : ThetaGrp P.A P.L N (overRes V)) (s' : LB.Sec (LPow P.A P.L N (overRes V))),
        SymLift P.A P.L N N (overResι V ≫ h i) U → IsActOf P.A P.L N U sV s' →
          ∀ j, s'.f j = liftFun P.A _ (unitRes V (χ i) : Γ((overRes V).left, ⊤)) * sV.f j
def IsEvT (P : PolAV S) (N : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (τ : ∀ i, LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (x i).left) (fun _ => (N : ℤ))))
    (s : LB.Sec (LPow P.A P.L N T)) (w : I → Γ(T.left, ⊤)) : Prop :=
  ∀ i, IsValueAt P.A P.L N s (x i) (τ i) (w i)
end ReciprocityTheory.ChartRestriction.G.Out


