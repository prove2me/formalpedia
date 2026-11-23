-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
-- name    : Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:23.787495+00:00
-- url     : https://prove2.me/theorems/e3106756-1801-4d08-91ed-67c57da7af04
-- title:
--   Conv Gr Of
-- statement:
--   Definitions and structural lemmas for Conv Gr Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/EisensteinSeries/SiegelEisensteinContinuation/ConvGrOf.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
namespace PositivityTheory.RgEis
structure Ad (E R : Type) [Field E] [CommRing R] where
  i : E →+* R
  σ : R →+* R
  O : Subring R
  W : Type
  φ : W → (R →+* ℂ)
  lg : Rˣ → ℝ
  χ : Rˣ →* Circle
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
def stab (R : Type) [CommRing R] (s : Set ι) : Subgroup (GL ι R) where
  carrier := {g | ∀ r ∉ s, ∀ c ∈ s, (g : Matrix ι ι R) r c = 0 ∧ ((g⁻¹ : GL ι R) : Matrix ι ι R) r c = 0}
  one_mem' := fun r hr c hc => by
    have : r ≠ c := fun h => hr (h ▸ hc)
    simp [Matrix.one_apply_ne this]
  mul_mem' := fun {a b} ha hb r hr c hc => by
    have key : ∀ x y : Matrix ι ι R, (∀ r ∉ s, ∀ c ∈ s, x r c = 0) → (∀ r ∉ s, ∀ c ∈ s, y r c = 0) → (x * y) r c = 0 :=
      fun x y hx hy => by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun m _ => ?_
        by_cases hm : m ∈ s
        · rw [hx r hr m hm, zero_mul]
        · rw [hy m hm c hc, mul_zero]
    refine ⟨key _ _ (fun r hr c hc => (ha r hr c hc).1) fun r hr c hc => (hb r hr c hc).1, ?_⟩
    rw [_root_.mul_inv_rev]
    exact key _ _ (fun r hr c hc => (hb r hr c hc).2) fun r hr c hc => (ha r hr c hc).2
  inv_mem' := fun {a} ha r hr c hc => ⟨(ha r hr c hc).2, by rw [inv_inv]; exact (ha r hr c hc).1⟩
open Classical in

def bdet (s : Set ι) (g : GL ι R) : Rˣ :=
  if h : IsUnit ((g : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det then h.unit else 1
open Classical in

def ext {G : Type} [Group G] (K P : Subgroup G) (f : G → ℝ) (g : G) : ℝ :=
  if h : ∃ k : K, g * (k : G)⁻¹ ∈ P then f (g * (h.choose : G)⁻¹) else 0
namespace Ad
variable (A : Ad E R)
def ratGL (ι : Type) [Fintype ι] [DecidableEq ι] : Subgroup (GL ι R) := (Matrix.GeneralLinearGroup.map (n := ι) A.i).range
def kGL (ι : Type) [Fintype ι] [DecidableEq ι] : Subgroup (GL ι R) where
  carrier := {k | (∀ r c, (k : Matrix ι ι R) r c ∈ A.O ∧ ((k⁻¹ : GL ι R) : Matrix ι ι R) r c ∈ A.O) ∧
    ∀ w, (k : Matrix ι ι R).map (A.φ w) ∈ Matrix.unitaryGroup ι ℂ}
  one_mem' := ⟨fun r c => by
      by_cases h : r = c
      · subst h; simp [A.O.one_mem]
      · simp [Matrix.one_apply_ne h, A.O.zero_mem],
    fun w => by rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]; exact one_mem _⟩
  mul_mem' := fun {a b} ha hb => ⟨fun r c => ⟨by
      rw [Units.val_mul, Matrix.mul_apply]; exact A.O.sum_mem fun m _ => A.O.mul_mem (ha.1 r m).1 (hb.1 m c).1, by
      rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact A.O.sum_mem fun m _ => A.O.mul_mem (hb.1 r m).2 (ha.1 m c).2⟩,
    fun w => by rw [Units.val_mul, Matrix.map_mul]; exact mul_mem (ha.2 w) (hb.2 w)⟩
  inv_mem' := fun {a} ha => ⟨fun r c => ⟨(ha.1 r c).2, by rw [inv_inv]; exact (ha.1 r c).1⟩, fun w => by
    have h : (a : Matrix ι ι R).map (A.φ w) * ((a⁻¹ : GL ι R) : Matrix ι ι R).map (A.φ w) = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := Matrix.mem_unitaryGroup_iff'.1 (ha.2 w)
    have e : ((a⁻¹ : GL ι R) : Matrix ι ι R).map (A.φ w) = star ((a : Matrix ι ι R).map (A.φ w)) := by
      rw [← Matrix.one_mul (((a⁻¹ : GL ι R) : Matrix ι ι R).map (A.φ w)), ← h2, Matrix.mul_assoc, h, Matrix.mul_one]
    rw [e]; exact Unitary.star_mem (ha.2 w)⟩
def htGL (s : Set ι) : GL ι R → ℝ := ext (A.kGL ι) (stab R s) fun p => A.lg (bdet s p)
def cGL (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι R) : ℂ := A.χ (Matrix.GeneralLinearGroup.det g)
def J (R : Type) [CommRing R] (ε : ℤˣ) (ι : Type) [DecidableEq ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks 0 1 (((ε : ℤ) : R) • 1) 0
def uSub (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι] : Subgroup (GL (ι ⊕ ι) R) where
  carrier := {g | (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * J R ε ι * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ = J R ε ι}
  one_mem' := by simp [Matrix.map_one _ (map_zero A.σ) (map_one A.σ)]
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.transpose_mul, Matrix.map_mul] at *
    calc _ = (b : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * ((a : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * J R ε ι * (a : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ) * (b : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, hb]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at *
    have h1 : ((a⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * (a : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    have h2 : (a : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ * ((a⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    calc _ = ((a⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * ((a : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * J R ε ι * (a : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ) *
          ((a⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ := by rw [ha]
      _ = (((a⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * (a : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ) * J R ε ι *
          ((a : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ * ((a⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
abbrev U (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι] : Type := A.uSub ε ι
variable (ε : ℤˣ)
def uΓ (ι : Type) [Fintype ι] [DecidableEq ι] : Subgroup (A.U ε ι) := (A.ratGL (ι ⊕ ι)).subgroupOf _
def uK (ι : Type) [Fintype ι] [DecidableEq ι] : Subgroup (A.U ε ι) := (A.kGL (ι ⊕ ι)).subgroupOf _
def uQ (s : Set ι) : Subgroup (A.U ε ι) := (stab R (Sum.inl '' s)).subgroupOf _
def uH (s : Set ι) : A.U ε ι → ℝ := ext (A.uK ε ι) (A.uQ ε s) fun p => A.lg (bdet (Sum.inl '' s) p.1)
def uC (ι : Type) [Fintype ι] [DecidableEq ι] (g : A.U ε ι) : ℂ := A.χ (bdet (Sum.inl '' (Set.univ : Set ι)) g.1)
variable [TopologicalSpace R]
structure GoodL : Prop where
  iinj : Function.Injective A.i
  lgmul : ∀ x y, A.lg (x * y) = A.lg x + A.lg y
  lgcont : Continuous A.lg
  lgi : ∀ x : Eˣ, A.lg (Units.map A.i.toMonoidHom x) = 0
  χcont : Continuous A.χ
  χi : ∀ x : Eˣ, A.χ (Units.map A.i.toMonoidHom x) = 1
  kcpt : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], IsCompact (A.kGL ι : Set (GL ι R))
  iwa : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : Set ι), Iwa (stab R s) (A.kGL ι)
structure Good : Prop extends A.GoodL where
  σσ : ∀ x, A.σ (A.σ x) = x
  σcont : Continuous A.σ
  σO : ∀ x ∈ A.O, A.σ x ∈ A.O
  σφ : ∀ w x, A.φ w (A.σ x) = conj (A.φ w x)
  σi : ∀ x, ∃ y, A.σ (A.i x) = A.i y
  χσ : ∀ x, A.χ (Units.map A.σ.toMonoidHom x) = (A.χ x)⁻¹
def MirGL : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (i₀ i₁ : ι), 2 ≤ Fintype.card ι →
    (AllRep (A.kGL ι) fun ρ => HasFirst (A.ratGL ι) (A.kGL ι) ⊤ (stab R {i₀}) (stab R {i₁}ᶜ) 1 (A.htGL {i₀})
      (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g)
      (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) ρ) ∧
    (AllRep (A.kGL ι) fun ρ => HasWall (A.ratGL ι) (A.kGL ι) (stab R {i₁}ᶜ) (stab R {i₀}) 1
      (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) (A.htGL {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) ρ) ∧
    AllRep (A.kGL ι) fun ρ => HasLast (A.ratGL ι) (A.kGL ι) ⊤ (stab R {i₀}) (stab R {i₁}ᶜ) 1 (A.htGL {i₀})
      (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g)
      (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) (A.htGL Set.univ)
      (Fintype.card ι) ρ
def ConvGr : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : Set ι), ∃ R₀ : ℝ, ∀ x : ℝ, R₀ < x →
    Conv (A.ratGL ι) (stab R s) fun g => x * A.htGL s g
def Sg (ι : Type) [Fintype ι] [DecidableEq ι] : Prop :=
  Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι) → AllRep (A.uK ε ι) fun ρ =>
    HasWall (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε Set.univ) (A.uH ε Set.univ)
      (fun g => (Fintype.card ι : ℝ) * A.uH ε Set.univ g) ρ
end Ad
def ForAd (Q : ∀ {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R], Ad E R → Prop) : Prop :=
  ∀ (E R : Type) [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] (A : Ad E R), A.Good → Q A
def ForAdL (Q : ∀ {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R], Ad E R → Prop) : Prop :=
  ∀ (E R : Type) [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] (A : Ad E R), A.GoodL → Q A
def GrpTop : Prop := ForAd fun {_} {R} _ _ _ _ A => ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ε : ℤˣ),
  T2Space (GL ι R) ∧ LocallyCompactSpace (GL ι R) ∧ SecondCountableTopology (GL ι R) ∧ T2Space (A.U ε ι) ∧
  LocallyCompactSpace (A.U ε ι) ∧ SecondCountableTopology (A.U ε ι) ∧ IsCompact (A.uK ε ι : Set (A.U ε ι))
def BdetLaw : Prop := ForAdL fun {_} {R} _ _ _ _ A => ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : Set ι),
  IsClosed (stab R s : Set (GL ι R)) ∧ (∀ p ∈ stab R s, ∀ q ∈ stab R s, bdet s (p * q) = bdet s p * bdet s q) ∧
  ContinuousOn (bdet s) (stab R s : Set (GL ι R)) ∧
  (∀ p ∈ stab R s, p ∈ A.ratGL ι → ∃ x, bdet s p = Units.map A.i.toMonoidHom x) ∧
  (∀ p ∈ stab R s, p ∈ A.kGL ι → A.lg (bdet s p) = 0) ∧
  ∀ g : GL ι R, bdet (Set.univ : Set ι) g = Matrix.GeneralLinearGroup.det g
def ExtLaw : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (Γ K P : Subgroup G) (f : G → ℝ),
    IsCompact (K : Set G) → IsClosed (P : Set G) → Iwa P K → (∀ p ∈ P, ∀ q ∈ P, f (p * q) = f p + f q) → ContinuousOn f P →
    (∀ p ∈ P, p ∈ K → f p = 0) → (∀ p ∈ P, p ∈ Γ → f p = 0) →
    IsHt Γ K P (ext K P f) ∧ ∀ p ∈ P, ∀ k ∈ K, ext K P f (p * k) = f p
def LeviS : Prop := ForAd fun {_} {R} _ _ _ _ A => ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ε : ℤˣ),
  Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι) →
  ∃ (π : A.uQ ε (Set.univ : Set ι) →* GL ι R) (j : GL ι R →* A.uQ ε (Set.univ : Set ι)),
    IsLevi (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε Set.univ) (A.ratGL ι) (A.kGL ι) π j 1 ∧
    (∀ s : Set ι, IsPull (A.uQ ε Set.univ) (A.uQ ε s ⊓ A.uQ ε Set.univ) (stab R s) π 1 (A.uC ε ι) (A.cGL ι)) ∧
    (∀ s : Set ι, Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι)) ∧
    ∀ s : Set ι, PullHt (A.uK ε ι) (A.uQ ε Set.univ) π (A.uH ε s) (A.htGL s)
open Classical in

def LeviQ : Prop := ForAd fun {_} {_} _ _ _ _ A => ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ε : ℤˣ) (s : Set ι),
  Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι) →
  ∃ (π : A.uQ ε s →* A.U ε (sᶜ : Set ι)) (j : A.U ε (sᶜ : Set ι) →* A.uQ ε s) (c₀ : A.U ε ι → ℂ),
    IsLevi (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε s) (A.uΓ ε _) (A.uK ε _) π j c₀ ∧
    IsPull (A.uQ ε s) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uQ ε Set.univ) π c₀ (A.uC ε ι) (A.uC ε _) ∧
    Iwa (A.uQ ε (Set.univ : Set (sᶜ : Set ι))) (A.uK ε _) ∧
    PullHt (A.uK ε ι) (A.uQ ε s) π (fun g => A.uH ε Set.univ g - A.uH ε s g) (A.uH ε Set.univ)
def ParLaw : Prop := ForAd fun {_} {R} _ _ _ _ A => ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ε : ℤˣ) (s : Set ι),
  (IsPar (A.ratGL ι) (A.kGL ι) (stab R s) 1 ∧ IsPar (A.ratGL ι) (A.kGL ι) (stab R s) (A.cGL ι) ∧
    IsCh (A.ratGL ι) ⊤ (A.cGL ι) ∧ IsHt (A.ratGL ι) (A.kGL ι) (stab R s) (A.htGL s) ∧ stab R (Set.univ : Set ι) = ⊤) ∧
  (Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι) →
    IsPar (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uC ε ι) ∧
    IsHt (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε s) (A.uH ε s) ∧ ∀ g, A.uH ε s g = A.htGL (Sum.inl '' s) g.1)
def ConvGrOf : Prop := ForAd fun {_} {_} _ _ _ _ A => A.MirGL → A.ConvGr
def ConvU : Prop := ForAd fun {_} {_} _ _ _ _ A => A.ConvGr → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ε : ℤˣ) (s : Set ι),
  Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι) → ∃ R₀ : ℝ,
    (∀ y : ℝ, R₀ < y → Conv (A.uΓ ε ι) (A.uQ ε Set.univ) fun g => y * A.uH ε Set.univ g) ∧
    ∀ x y : ℝ, R₀ < x → R₀ < y →
      Conv (A.uΓ ε ι) (A.uQ ε s ⊓ A.uQ ε Set.univ) fun g => x * A.uH ε s g + y * A.uH ε Set.univ g
def SgStep : Prop := ForAd fun {_} {_} _ _ _ _ A => A.MirGL → ∀ (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι],
  2 ≤ Fintype.card ι → (∀ (κ : Type) [Fintype κ] [DecidableEq κ], 1 ≤ Fintype.card κ → Fintype.card κ < Fintype.card ι →
    A.Sg ε κ) → A.Sg ε ι
end PositivityTheory.RgEis


