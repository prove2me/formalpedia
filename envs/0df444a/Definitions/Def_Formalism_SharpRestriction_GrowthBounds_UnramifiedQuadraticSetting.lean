-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
-- name    : Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:19:21.710734+00:00
-- url     : https://prove2.me/theorems/42a709d2-b0e6-46f6-bc5e-15723c3265de
-- title:
--   Unramified Quadratic Setting
-- statement:
--   Definitions and structural lemmas for Unramified Quadratic Setting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.MainNotions.G
open Formalism.GradedWeylDivisibility
structure HidaSetting (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  two_le : 2 ≤ n'
  even : Even n'
  frac_alt : IsFractionRing W Qq
  frac_O : IsFractionRing O Kf
  p_unif : Irreducible (p : W)
  res_card : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n'
  eq_sum_herm_smul_frame_of_inW : IsAdicComplete (Ideal.span {(p : W)}) W
  frob : ∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)
  period : σ ^ n' = 1
  ι_comp : ∀ x : W, ι (algebraMap W Qq x) = algebraMap O Kf (j x)
  finite : j.Finite
  complete_O : IsAdicComplete (IsLocalRing.maximalIdeal O) O
  w_sq : w ^ 2 = (p : O)
def UnramifiedQuadraticSetting (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O) : Prop :=
  HidaSetting p n' W Qq O Kf ι σ j w ∧ Irreducible w ∧ Nat.card (O ⧸ Ideal.span {w}) = p ^ (2 * n') ∧
    ∀ z : ℤ, ∃ y : O, y ^ 2 = (z : O)
def colSpan (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ}
    (g : Matrix (Fin k) (Fin k) K) : Submodule R (Fin k → K) :=
  Submodule.span R (Set.range fun c : Fin k => fun i => g i c)
def IsLattice (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ}
    (L : Submodule R (Fin k → K)) : Prop :=
  ∃ g : Matrix (Fin k) (Fin k) K, IsUnit g.det ∧ L = colSpan R g
def twistVec {Qq Kf : Type*} [Field Qq] [Field Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) {k : ℕ}
    (v : Fin k → Qq) : Fin k → Kf :=
  fun i => ι ((σ ^ s) (v i))
def extO (O : Type*) {W Qq Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf]
    [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) {k : ℕ} (L : Submodule W (Fin k → Qq)) :
    Submodule O (Fin k → Kf) :=
  Submodule.span O (twistVec ι σ s '' (L : Set (Fin k → Qq)))
def IsTypeV {n' : ℕ} (s : Fin n') : Prop := Even s.val
def posAdd {n' : ℕ} (s : Fin n') (e : ℕ) : Fin n' :=
  ⟨(s.val + e) % n', Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt)⟩
def IsBaseWeight {n' m : ℕ} (TT : Finset (Fin n')) (a b : Fin n' → ℤ) (c : ℕ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) : Prop :=
  ∀ s, (s ∈ TT → lam0 s 0 = a s ∧ lam0 s (Fin.last m) = -b s ∧
      ∀ i : Fin (m + 1), 0 < i.val → i.val < m → |lam0 s i| ≤ c) ∧
    (s ∉ TT → ∀ i, |lam0 s i| ≤ c)
def IsDominant {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) : Prop := ∀ s, Antitone (lam0 s)
def lamAt {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') : Fin (m + 1) → ℤ :=
  if Even s.val then lam0 s else fun i => -lam0 s i.rev
def H0 (O : Type*) {Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (Λ : Submodule O (Fin (m + 1) → Kf)) : Submodule O (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :=
  if Antitone lam then
    ⨅ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (_ : IsUnit g.det ∧ Λ = colSpan O g), nablaLTw O Kf m lam g
  else ⊥
def Hten (O : Type*) {Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ}
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf)) :
    Submodule O (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat O Kf fun s => H0 O m (lamAt lam0 s) (Λ s)
def nuOf {m : ℕ} (lam : Fin (m + 1) → ℤ) : Fin (m + 1) → ℕ :=
  fun t => (lam t - lam (Fin.last m)).toNat
def Vsp (Kf : Type*) [Field Kf] {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    Submodule Kf (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat Kf Kf fun s => if Antitone (lamAt lam0 s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥
def dimV (Kf : Type*) [Field Kf] {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) : ℕ :=
  Module.finrank Kf (Vsp Kf lam0)
def toV {O Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (M : Submodule O (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) : Submodule O (Vsp Kf lam0) :=
  M.comap ((Vsp Kf lam0).subtype.restrictScalars O)
def HL {W Qq O Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (L : Submodule W (Fin (m + 1) → Qq)) : Submodule O (Vsp Kf lam0) :=
  toV lam0 (Hten O lam0 fun s => extO O ι σ s.val L)
structure Edge (W Qq : Type*) [CommRing W] [Field Qq] [Algebra W Qq] (k : ℕ) where
  src : Submodule W (Fin k → Qq)
  tgt : Submodule W (Fin k → Qq)
def IsEdge {W Qq : Type*} [CommRing W] [Field Qq] [Algebra W Qq] (p n' r : ℕ) {k : ℕ} (e : Edge W Qq k) : Prop :=
  IsLattice W e.src ∧ IsLattice W e.tgt ∧ e.src ≤ e.tgt ∧ (∀ x ∈ e.tgt, (p : W) • x ∈ e.src) ∧
    Nat.card (↥e.tgt ⧸ Submodule.comap e.tgt.subtype e.src) = p ^ (n' * r)
def IsEdgeBasis {W Qq : Type*} [CommRing W] [Field Qq] [Algebra W Qq] (p r : ℕ) {k : ℕ} (e : Edge W Qq k)
    (g : Matrix (Fin k) (Fin k) Qq) : Prop :=
  IsUnit g.det ∧ e.src = colSpan W g ∧
    e.tgt = colSpan W (g * Matrix.diagonal fun c => if c.val < r then ((p : Qq))⁻¹ else 1)
def LeAt {W Qq O Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
    (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (s : ℕ) {k : ℕ} (e : Edge W Qq k) :
    Submodule O (Fin k → Kf) :=
  extO O ι σ s e.src ⊔
    Submodule.span O ((fun v => (algebraMap O Kf w)⁻¹ • twistVec ι σ s ((p : W) • v)) '' (e.tgt : Set (Fin k → Qq)))
def HLe {W Qq O Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
    (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (e : Edge W Qq (m + 1)) : Submodule O (Vsp Kf lam0) :=
  toV lam0 (Hten O lam0 fun s => LeAt p ι σ w s.val e)
def Ar {n' m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) : ℤ :=
  ∑ s : Fin n', ∑ i : Fin (m + 1) with i.val < r, lamAt lam0 s i
def scale {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
    [IsScalarTower O Kf X] (c : Kf) (M : Submodule O X) : Submodule O X :=
  M.map ((LinearMap.lsmul Kf X c).restrictScalars O)
def Re {W Qq O Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
    (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {n' m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (e : Edge W Qq (m + 1)) : Submodule O (Vsp Kf lam0) :=
  scale (algebraMap O Kf w ^ (-Ar r lam0)) (HLe p ι σ w lam0 e)
def Re' {W Qq O Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
    (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {n' m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (e : Edge W Qq (m + 1)) : Submodule O (Module.Dual Kf (Vsp Kf lam0)) :=
  scale (algebraMap O Kf w ^ (-Ar r lam0)) (dualLat O Kf (HLe p ι σ w lam0 e))
def be {Kf : Type*} [Field Kf] {n' m : ℕ} (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (F : Vsp Kf lam0) (G : Module.Dual Kf (Vsp Kf lam0)) : Kf :=
  G (((p : Kf) ^ Ar r lam0) • F)
def order {n' m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (π : ℤ) : ℤ := Ar r lam0 - π
def predual {O Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] {V : Type*} [AddCommGroup V] [Module Kf V]
    [Module O V] [IsScalarTower O Kf V] (A : Submodule O (Module.Dual Kf V)) : Submodule O V where
  carrier := {x | ∀ φ ∈ A, φ x ∈ Set.range (algebraMap O Kf)}
  add_mem' := by
    intro x y hx hy φ hφ
    obtain ⟨a, ha⟩ := hx φ hφ
    obtain ⟨b, hb⟩ := hy φ hφ
    exact ⟨a + b, by simp [ha, hb]⟩
  zero_mem' := by
    intro φ _
    exact ⟨0, by simp⟩
  smul_mem' := by
    intro c x hx φ hφ
    obtain ⟨a, ha⟩ := hx φ hφ
    refine ⟨c * a, ?_⟩
    rw [map_mul, ha, ← Algebra.smul_def, ← φ.map_smul_of_tower]
def ofV {O Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ} {lam0 : Fin n' → Fin (m + 1) → ℤ}
    (A : Submodule O (Vsp Kf lam0)) : Submodule O (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  A.map ((Vsp Kf lam0).subtype.restrictScalars O)
def latDual {W Qq : Type*} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ} (L : Submodule W (Fin k → Qq)) :
    Submodule W (Fin k → Qq) where
  carrier := {x | ∀ y ∈ L, ∑ i, x i * y i ∈ Set.range (algebraMap W Qq)}
  add_mem' := by
    intro x x' hx hx' y hy
    obtain ⟨a, ha⟩ := hx y hy
    obtain ⟨b, hb⟩ := hx' y hy
    exact ⟨a + b, by simp [add_mul, Finset.sum_add_distrib, ha, hb]⟩
  zero_mem' := by
    intro y _
    exact ⟨0, by simp⟩
  smul_mem' := by
    intro c x hx y hy
    obtain ⟨a, ha⟩ := hx y hy
    refine ⟨c * a, ?_⟩
    simp only [Pi.smul_apply, Algebra.smul_def, mul_assoc, ← Finset.mul_sum, map_mul, ha]
def Edge.dual {W Qq : Type*} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ} (e : Edge W Qq k) : Edge W Qq k :=
  ⟨latDual e.tgt, latDual e.src⟩
def Nsrc {W Qq O Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
    (p n' : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (t : ℕ) (L'' : Submodule W (Fin (m + 1) → Qq)) : Submodule O (Vsp Kf lam0) :=
  scale (algebraMap O Kf w ^ (-(t : ℤ))) (HL ι σ lam0 L'') ⊓
    ⨅ (e : Edge W Qq (m + 1)) (_ : IsEdge p n' r e ∧ e.src = L''), Re p ι σ w r lam0 e
def Ntgt {W Qq O Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
    (p n' : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (t : ℕ) (L : Submodule W (Fin (m + 1) → Qq)) : Submodule O (Module.Dual Kf (Vsp Kf lam0)) :=
  scale (algebraMap O Kf w ^ (-(t : ℤ))) (dualLat O Kf (HL ι σ lam0 L)) ⊓
    ⨅ (e : Edge W Qq (m + 1)) (_ : IsEdge p n' r e ∧ e.tgt = L), Re' p ι σ w r lam0 e
def GoodRankK {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module O X]
    (π : O) (A : Submodule O X) {I : Type*} [Fintype I] (φ : I → X → Kf) (n D : ℕ) : Prop :=
  ∃ (u : (Fin n → O) →ₗ[O] A) (M : Matrix (Fin n) I O), ∀ (x : Fin n → O) (j : Fin n),
    ∑ i, algebraMap O Kf (M j i) * φ i (u x : X) = algebraMap O Kf (π ^ D * x j)
def LPprimeAt {W Qq O Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
    (p n' : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (t D : ℕ) (κ : ℝ) (cStar : ℕ) (L : Submodule W (Fin (m + 1) → Qq)) : Prop :=
  ∃ (M : ℕ) (e : Fin M → Edge W Qq (m + 1)) (F : Fin M → Vsp Kf lam0),
    (∀ i, IsEdge p n' r (e i) ∧ (e i).tgt = L) ∧
    (∀ i, F i ∈ Nsrc p n' ι σ w r lam0 t (e i).src) ∧
    (∀ i (e' : Edge W Qq (m + 1)), IsEdge p n' r e' → e'.src = (e i).src → e' ≠ e i →
      F i ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re p ι σ w r lam0 e')) ∧
    ∃ n : ℕ, (1 - κ) * (dimV Kf lam0 : ℝ) ≤ n ∧
      GoodRankK (p : O) (Ntgt p n' ι σ w r lam0 t L) (fun i G => be p r lam0 (F i) G) n D
def LPprime {W Qq O Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
    (p n' : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (t D : ℕ) (κ : ℝ) (cStar : ℕ) : Prop :=
  4 * (D + 1) ≤ cStar ∧
  ∀ L : Submodule W (Fin (m + 1) → Qq), IsLattice W L → LPprimeAt p n' ι σ w r lam0 t D κ cStar L
def LPprimeOne {W Qq O Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
    (p n' : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (t D : ℕ) (κ : ℝ) (cStar : ℕ) : Prop :=
  4 * (D + 1) ≤ cStar ∧
  ∃ L : Submodule W (Fin (m + 1) → Qq), IsLattice W L ∧ LPprimeAt p n' ι σ w r lam0 t D κ cStar L
def LPBaseChange : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf O' Kf' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field Kf'] [Algebra O' Kf']
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O) (φ : O →+* O') (φK : Kf →+* Kf'),
    (∀ x : O, φK (algebraMap O Kf x) = algebraMap O' Kf' (φ x)) → φ.Finite →
    HidaSetting p n' W Qq O Kf ι σ j w → HidaSetting p n' W Qq O' Kf' (φK.comp ι) σ (φ.comp j) (φ w) →
    ∀ (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (t D : ℕ) (κ : ℝ) (cStar : ℕ),
      LPprime (W := W) p n' ι σ w r lam0 t D κ cStar →
        LPprime (W := W) p n' (φK.comp ι) σ (φ w) r lam0 t D κ cStar
def goodU (de : ℝ) : ℕ := ⌈1 / de⌉₊
def goodEll (r : ℕ) (de : ℝ) : ℕ := (6 * r + 1) * goodU de
def orbitSmallMultiplicity (r : ℕ) (h x : ℝ) : ℕ := ⌈(h + 3) * Real.log x / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ))⌉₊
def goodG' (r : ℕ) (de h x : ℝ) : ℕ := (orbitSmallMultiplicity r h x + 5) * goodEll r de
def orbitWindowCount (r : ℕ) (de h x : ℝ) : ℕ :=
  ⌈max (6 * Real.exp 1 * (goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x)⌉₊ + 1
def IsGoodOrbit (n' : ℕ) (TT : Finset (Fin n')) (L₂ K r : ℕ) (de h x : ℝ) : Prop :=
  Formalism.G0.GoodOrbitIntervalTileCondition n' (TT.map Fin.valEmbedding) L₂ K r (goodU de) (orbitSmallMultiplicity r h x) (goodG' r de h x)
    (orbitWindowCount r de h x)
end Formalism.MainNotions.G


