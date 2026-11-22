-- Prove2me | Definitions.Def_Formalism_DegreeFormula_Statement
-- name    : Formalism_DegreeFormula_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:16.621964+00:00
-- url     : https://prove2.me/theorems/95280f2b-9307-4f71-875e-f314d08d79ff
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/Statement.lean

import Mathlib
import Definitions.Def_Formalism_MoebiusJetDuality_StatementU
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ComplexOrder
namespace Formalism.DegreeFormula
open Formalism.MJ Formalism.UG
section One
variable {p q : ℕ}
def kapP (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁).map (starRingEnd ℂ) +
    ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂).map (starRingEnd ℂ) * zᵀ
def kapQ (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ * z +
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₂
def hQ (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ := 1 - zᴴ * z
def hP (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ := 1 - z * zᴴ
def toGL {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : GL (Fin m) ℂ :=
  open Classical in
  if h : IsUnit M.det then Matrix.nonsingInvUnit M h else 1
def KapQUnit : Prop :=
  ∀ (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    g ∈ Upq p q → z ∈ hcDom p q → IsUnit (kapQ g z).det
def KapPUnit : Prop :=
  ∀ (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    g ∈ Upq p q → z ∈ hcDom p q → IsUnit (kapP g z).det
def KapQCocycle : Prop :=
  ∀ (p q : ℕ) (g h : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    g ∈ Upq p q → h ∈ Upq p q → z ∈ hcDom p q →
      kapQ (g * h) z = kapQ g (moeb (h : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapQ h z
def KapPCocycle : Prop :=
  ∀ (p q : ℕ) (g h : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    g ∈ Upq p q → h ∈ Upq p q → z ∈ hcDom p q →
      kapP (g * h) z = kapP g (moeb (h : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapP h z
def HQTrans : Prop :=
  ∀ (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    g ∈ Upq p q → z ∈ hcDom p q →
      (kapQ g z)ᴴ * hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapQ g z = hQ z
def HPTrans : Prop :=
  ∀ (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    g ∈ Upq p q → z ∈ hcDom p q →
      ((kapP g z).map (starRingEnd ℂ))ᴴ * hP (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) *
        (kapP g z).map (starRingEnd ℂ) = hP z
def DetHEq : Prop :=
  ∀ (p q : ℕ) (z : Matrix (Fin p) (Fin q) ℂ), (hP z).det = (hQ z).det
def DetHPos : Prop :=
  ∀ (p q : ℕ) (z : Matrix (Fin p) (Fin q) ℂ), z ∈ hcDom p q → 0 < (hQ z).det
def KapAbsEq : Prop :=
  ∀ (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    g ∈ Upq p q → z ∈ hcDom p q → ‖(kapP g z).det‖ = ‖(kapQ g z).det‖
def DomOpenConvex : Prop :=
  ∀ p q : ℕ, IsOpen (hcDom p q) ∧ Convex ℝ (hcDom p q)
def DomTransitive : Prop :=
  ∀ (p q : ℕ) (z : Matrix (Fin p) (Fin q) ℂ), z ∈ hcDom p q →
    ∃ g ∈ Upq p q, moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0 = z
def MoebOne : Prop :=
  ∀ (p q : ℕ) (z : Matrix (Fin p) (Fin q) ℂ),
    moeb ((1 : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z = z
def DomBounded : Prop :=
  ∀ (p q : ℕ) (z : Matrix (Fin p) (Fin q) ℂ), z ∈ hcDom p q → ∀ i j, ‖z i j‖ < 1
end One
section Two
variable {ι : Type} [Fintype ι] {p q r : ℕ}
def DomI (ι : Type) (p q : ℕ) : Set (ι → Matrix (Fin p) (Fin q) ℂ) := {z | ∀ i, z i ∈ hcDom p q}
def UpqI (ι : Type) (p q : ℕ) : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ) :=
  Subgroup.pi Set.univ (fun _ => Upq p q)
def moebI (g : ι → GL (Fin p ⊕ Fin q) ℂ) (z : ι → Matrix (Fin p) (Fin q) ℂ) :
    ι → Matrix (Fin p) (Fin q) ℂ :=
  fun i => moeb (g i : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (z i)
def jI (g : ι → GL (Fin p ⊕ Fin q) ℂ) (z : ι → Matrix (Fin p) (Fin q) ℂ) :
    ι → GL (Fin p) ℂ × GL (Fin q) ℂ :=
  fun i => (toGL (kapP (g i) (z i)), toGL (kapQ (g i) (z i)))
def unflat (v : ι × Fin p × Fin q → ℂ) : ι → Matrix (Fin p) (Fin q) ℂ :=
  fun i => Matrix.of (fun a b => v (i, a, b))
def flat (z : ι → Matrix (Fin p) (Fin q) ℂ) : ι × Fin p × Fin q → ℂ := fun x => z x.1 x.2.1 x.2.2
def DomFlat (ι : Type) (p q : ℕ) : Set (ι × Fin p × Fin q → ℂ) := {v | unflat v ∈ DomI ι p q}
def IsHoloOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : (ι → Matrix (Fin p) (Fin q) ℂ) → V) : Prop :=
  DifferentiableOn ℂ (fun v => f (unflat v)) (DomFlat ι p q)
def AutForm (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ))
    (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) :
    Submodule ℂ ((ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ)) where
  carrier := {f | IsHoloOn f ∧ (∀ z, z ∉ DomI ι p q → f z = 0) ∧
    ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, f (moebI γ z) = (ρ (jI γ z) : Matrix (Fin r) (Fin r) ℂ).mulVec (f z)}
  zero_mem' := ⟨by simpa [IsHoloOn] using (differentiableOn_const (c := (0 : Fin r → ℂ))),
    fun _ _ => rfl, fun γ _ z _ => by simp⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    refine ⟨hf1.add hg1, fun z hz => by simp [hf2 z hz, hg2 z hz], fun γ hγ z hz => ?_⟩
    simp [hf3 γ hγ z hz, hg3 γ hγ z hz, Matrix.mulVec_add]
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3⟩
    refine ⟨hf1.const_smul c, fun z hz => by simp [hf2 z hz], fun γ hγ z hz => ?_⟩
    simp [hf3 γ hγ z hz, Matrix.mulVec_smul]
def slash (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) (g : ι → GL (Fin p ⊕ Fin q) ℂ)
    (f : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ)) : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ) :=
  open Classical in
  fun z => if z ∈ DomI ι p q then
    (((ρ (jI g z))⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).mulVec (f (moebI g z)) else 0
def detChar (ι : Type) [Fintype ι] (p q : ℕ) (k₁ k₂ : ι → ℤ) :
    (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin 1) ℂ :=
  (Units.map (algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ)).toMonoidHom).comp
    { toFun := fun g => ∏ i, (Matrix.GeneralLinearGroup.det (g i).1) ^ (k₁ i) *
        (Matrix.GeneralLinearGroup.det (g i).2) ^ (k₂ i)
      map_one' := by simp
      map_mul' := by
        intro a b
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        simp only [Pi.mul_apply, Prod.fst_mul, Prod.snd_mul, map_mul, mul_zpow]
        exact mul_mul_mul_comm _ _ _ _ }
def IsHoloRep (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) : Prop :=
  ∀ a b : Fin r, DifferentiableOn ℂ
    (fun v : (ι × Fin p × Fin p → ℂ) × (ι × Fin q × Fin q → ℂ) =>
      (ρ (fun i => (toGL (Matrix.of fun x y => v.1 (i, x, y)), toGL (Matrix.of fun x y => v.2 (i, x, y))))
        : Matrix (Fin r) (Fin r) ℂ) a b)
    {v | ∀ i, IsUnit (Matrix.of fun x y => v.1 (i, x, y)).det ∧ IsUnit (Matrix.of fun x y => v.2 (i, x, y)).det}
def IsKUnitary (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) : Prop :=
  ∀ k ∈ UpqI ι p q, moebI k 0 = 0 →
    ((ρ (jI k 0) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)ᴴ * (ρ (jI k 0) : Matrix (Fin r) (Fin r) ℂ) = 1
def MoebIAction : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q : ℕ),
    (∀ g ∈ UpqI ι p q, ∀ z ∈ DomI ι p q, moebI g z ∈ DomI ι p q) ∧
    (∀ z, moebI (1 : ι → GL (Fin p ⊕ Fin q) ℂ) z = z) ∧
    (∀ g ∈ UpqI ι p q, ∀ h ∈ UpqI ι p q, ∀ z ∈ DomI ι p q, moebI (g * h) z = moebI g (moebI h z))
def JICocycle : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q : ℕ) (g h : ι → GL (Fin p ⊕ Fin q) ℂ) (z : ι → Matrix (Fin p) (Fin q) ℂ),
    g ∈ UpqI ι p q → h ∈ UpqI ι p q → z ∈ DomI ι p q → jI (g * h) z = jI g (moebI h z) * jI h z
def SlashMul : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q r : ℕ) (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ)
    (g h : ι → GL (Fin p ⊕ Fin q) ℂ) (f : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ)),
    g ∈ UpqI ι p q → h ∈ UpqI ι p q → slash ρ (g * h) f = slash ρ h (slash ρ g f)
def AutFormSlash : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q r : ℕ) (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ))
    (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) (f : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ)),
    Γ ≤ UpqI ι p q →
      (f ∈ AutForm Γ ρ ↔ IsHoloOn f ∧ (∀ z, z ∉ DomI ι p q → f z = 0) ∧ ∀ γ ∈ Γ, slash ρ γ f = f)
def SlashConj : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q r : ℕ) (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ))
    (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) (g : ι → GL (Fin p ⊕ Fin q) ℂ)
    (f : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ)),
    IsHoloRep ρ → Γ ≤ UpqI ι p q → g ∈ UpqI ι p q → f ∈ AutForm Γ ρ →
      slash ρ g f ∈ AutForm (Γ.map (MulAut.conj g⁻¹).toMonoidHom) ρ
def AutFormAnti : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q r : ℕ) (Γ Γ' : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ))
    (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ), Γ' ≤ Γ → AutForm Γ ρ ≤ AutForm Γ' ρ
def AutFormMul : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q : ℕ) (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)) (k₁ k₂ l₁ l₂ : ι → ℤ)
    (f g : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin 1 → ℂ)),
    Γ ≤ UpqI ι p q → f ∈ AutForm Γ (detChar ι p q k₁ k₂) → g ∈ AutForm Γ (detChar ι p q l₁ l₂) →
      (f * g) ∈ AutForm Γ (detChar ι p q (k₁ + l₁) (k₂ + l₂))
def AutFormConst : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q : ℕ) (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)),
    Γ ≤ UpqI ι p q → (DomI ι p q).indicator (fun _ => (1 : Fin 1 → ℂ)) ∈ AutForm Γ (detChar ι p q 0 0)
end Two
section Three
variable {ι : Type} [Fintype ι] {p q r : ℕ}
def hodgeSq (k₁ k₂ : ι → ℤ) (f : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin 1 → ℂ))
    (z : ι → Matrix (Fin p) (Fin q) ℂ) : ℝ :=
  ‖f z 0‖ ^ 2 * ∏ i, ((hQ (z i)).det.re) ^ (k₁ i + k₂ i)
def l2sq (v : Fin r → ℂ) : ℝ := ∑ a, Complex.normSq (v a)
def liftPt (ι : Type) [Fintype ι] (p q : ℕ) (z : ι → Matrix (Fin p) (Fin q) ℂ) : ι → GL (Fin p ⊕ Fin q) ℂ :=
  open Classical in
  if h : ∃ g ∈ UpqI ι p q, moebI g 0 = z then h.choose else 1
def hodgeVSq (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ)
    (f : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ)) (z : ι → Matrix (Fin p) (Fin q) ℂ) : ℝ :=
  l2sq ((((ρ (jI (liftPt ι p q z) 0))⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).mulVec (f z))
def HodgeSqInv : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q : ℕ) (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)) (k₁ k₂ : ι → ℤ)
    (f : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin 1 → ℂ)),
    Γ ≤ UpqI ι p q → f ∈ AutForm Γ (detChar ι p q k₁ k₂) →
      ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, hodgeSq k₁ k₂ f (moebI γ z) = hodgeSq k₁ k₂ f z
def DetCharKUnitary : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q : ℕ) (k₁ k₂ : ι → ℤ), IsKUnitary (detChar ι p q k₁ k₂)
def HodgeVInv : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q r : ℕ) (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ))
    (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) (f : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ)),
    IsKUnitary ρ → Γ ≤ UpqI ι p q → f ∈ AutForm Γ ρ →
      ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, hodgeVSq ρ f (moebI γ z) = hodgeVSq ρ f z
def HodgeVScalar : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q : ℕ) (k₁ k₂ : ι → ℤ) (f : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin 1 → ℂ)),
    ∀ z ∈ DomI ι p q, hodgeVSq (detChar ι p q k₁ k₂) f z = hodgeSq k₁ k₂ f z
end Three
section Four
variable {ι : Type} [Fintype ι] {p q r : ℕ}
def muD (ι : Type) [Fintype ι] (p q : ℕ) : Measure (ι × Fin p × Fin q → ℂ) :=
  (volume.restrict (DomFlat ι p q)).withDensity
    (fun v => ENNReal.ofReal (∏ i, ((hQ (unflat v i)).det.re) ^ (-((p + q : ℕ) : ℤ))))
def IsFD (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)) (F : Set (ι × Fin p × Fin q → ℂ)) : Prop :=
  MeasurableSet F ∧ F ⊆ DomFlat ι p q ∧
    (∀ z ∈ DomI ι p q, ∃ γ ∈ Γ, flat (moebI γ z) ∈ F) ∧
    muD ι p q {v | v ∈ F ∧ ∃ γ ∈ Γ, flat (moebI γ (unflat v)) ∈ F ∧ moebI γ (unflat v) ≠ unflat v} = 0
def petSq (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) (F : Set (ι × Fin p × Fin q → ℂ))
    (f : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ)) : ENNReal :=
  ∫⁻ v in F, ENNReal.ofReal (hodgeVSq ρ f (unflat v)) ∂(muD ι p q)
def supSq (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ)
    (f : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ)) : ENNReal :=
  ⨆ z ∈ DomI ι p q, ENNReal.ofReal (hodgeVSq ρ f z)
def MuDInv : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q : ℕ) (g : ι → GL (Fin p ⊕ Fin q) ℂ), g ∈ UpqI ι p q →
    ∀ φ : (ι × Fin p × Fin q → ℂ) → ENNReal, Measurable φ →
      ∫⁻ v, φ (flat (moebI g (unflat v))) ∂(muD ι p q) = ∫⁻ v, φ v ∂(muD ι p q)
def PetIndep : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q r : ℕ) (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ))
    (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) (f : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ))
    (F F' : Set (ι × Fin p × Fin q → ℂ)),
    Countable Γ → Γ ≤ UpqI ι p q → IsKUnitary ρ → f ∈ AutForm Γ ρ → IsFD Γ F → IsFD Γ F' →
      petSq ρ F f = petSq ρ F' f ∧ muD ι p q F = muD ι p q F'
def PetLeSup : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q r : ℕ) (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ)
    (f : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ)) (F : Set (ι × Fin p × Fin q → ℂ)),
    F ⊆ DomFlat ι p q → petSq ρ F f ≤ supSq ρ f * muD ι p q F
end Four
section Five
variable {ι : Type} [Fintype ι] {p q r : ℕ} {G Gf : Type} [Group G] [Group Gf]
def AutFormAd (φ : G →* (ι → GL (Fin p ⊕ Fin q) ℂ)) (ψ : G →* Gf) (U K : Subgroup Gf)
    (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) :
    Submodule ℂ ((ι → Matrix (Fin p) (Fin q) ℂ) × Gf → (Fin r → ℂ)) where
  carrier := {F | (∀ g, IsHoloOn (fun z => F (z, g))) ∧ (∀ z g, z ∉ DomI ι p q → F (z, g) = 0) ∧
    (∀ z g, g ∉ U → F (z, g) = 0) ∧
    ∀ γ : G, ∀ z ∈ DomI ι p q, ∀ g : Gf, ∀ κ ∈ K,
      F (moebI (φ γ) z, ψ γ * g * κ) = (ρ (jI (φ γ) z) : Matrix (Fin r) (Fin r) ℂ).mulVec (F (z, g))}
  zero_mem' := ⟨fun g => by simpa [IsHoloOn] using (differentiableOn_const (c := (0 : Fin r → ℂ))),
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun γ z _ g κ _ => by simp⟩
  add_mem' := by
    rintro F F' ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
    refine ⟨fun g => (h1 g).add (h1' g), fun z g hz => by simp [h2 z g hz, h2' z g hz],
      fun z g hg => by simp [h3 z g hg, h3' z g hg], fun γ z hz g κ hκ => ?_⟩
    simp [h4 γ z hz g κ hκ, h4' γ z hz g κ hκ, Matrix.mulVec_add]
  smul_mem' := by
    rintro c F ⟨h1, h2, h3, h4⟩
    refine ⟨fun g => (h1 g).const_smul c, fun z g hz => by simp [h2 z g hz],
      fun z g hg => by simp [h3 z g hg], fun γ z hz g κ hκ => ?_⟩
    simp [h4 γ z hz g κ hκ, Matrix.mulVec_smul]
def compGamma (φ : G →* (ι → GL (Fin p ⊕ Fin q) ℂ)) (ψ : G →* Gf) (K : Subgroup Gf) (g : Gf) :
    Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ) :=
  ((K.map (MulAut.conj g).toMonoidHom).comap ψ).map φ
def AdComp : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q r : ℕ) (G Gf : Type) [Group G] [Group Gf]
    (φ : G →* (ι → GL (Fin p ⊕ Fin q) ℂ)) (ψ : G →* Gf) (U K : Subgroup Gf)
    (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) (F : (ι → Matrix (Fin p) (Fin q) ℂ) × Gf → (Fin r → ℂ)),
    F ∈ AutFormAd φ ψ U K ρ → ∀ g : Gf, (fun z => F (z, g)) ∈ AutForm (compGamma φ ψ K g) ρ
def AdInj : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q r : ℕ) (G Gf : Type) [Group G] [Group Gf]
    (φ : G →* (ι → GL (Fin p ⊕ Fin q) ℂ)) (ψ : G →* Gf) (U K : Subgroup Gf)
    (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) (F : (ι → Matrix (Fin p) (Fin q) ℂ) × Gf → (Fin r → ℂ))
    (C : Type) (s : C → Gf),
    φ.range ≤ UpqI ι p q → (∀ g : Gf, ∃ c, ∃ γ : G, ∃ κ ∈ K, g = ψ γ * s c * κ) →
      F ∈ AutFormAd φ ψ U K ρ → (∀ c z, F (z, s c) = 0) → F = 0
end Five
section CompanionTheory
variable {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n] {ι : Type} {p q : ℕ}
def embI (τ : ι → E →+* ℂ) (e : ι → n ≃ Fin p ⊕ Fin q) (P : ι → GL (Fin p ⊕ Fin q) ℂ) :
    GL n E →* (ι → GL (Fin p ⊕ Fin q) ℂ) :=
  MonoidHom.pi (fun i => (MulAut.conj (P i)⁻¹).toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.map (τ i)).comp
      (Units.map (Matrix.reindexAlgEquiv E E (e i)).toMonoidHom)))
def EmbUpq : Prop :=
  ∀ (E : Type) [Field E] (n : Type) [Fintype n] [DecidableEq n] (ι : Type) (p q : ℕ)
    (σ : E →+* E) (J : Matrix n n E) (τ : ι → E →+* ℂ) (e : ι → n ≃ Fin p ⊕ Fin q)
    (P : ι → GL (Fin p ⊕ Fin q) ℂ),
    (∀ i x, τ i (σ x) = starRingEnd ℂ (τ i x)) →
    (∀ i, cT (starRingEnd ℂ) (P i : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *
        ((J.map (τ i)).reindex (e i) (e i)) * (P i : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q) →
      (UJ σ J).map (embI τ e P) ≤ UpqI ι p q
end CompanionTheory
section LateralTheory
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
def latDeg (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] : ℝ :=
  -Real.log (ZLattice.covolume L)
def latSlope (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] : ℝ :=
  latDeg L / (Module.finrank ℤ L : ℝ)
def LatDegOrtho : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V),
    ∃ _ : DiscreteTopology (Submodule.span ℤ (Set.range b)), ∃ _ : IsZLattice ℝ (Submodule.span ℤ (Set.range b)),
      latDeg (Submodule.span ℤ (Set.range b)) = 0
def LatDegScale : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (c : ℝ), c ≠ 0 →
      ∃ _ : DiscreteTopology (L.map (c • LinearMap.id : V →ₗ[ℤ] V)),
      ∃ _ : IsZLattice ℝ (L.map (c • LinearMap.id : V →ₗ[ℤ] V)),
        latDeg (L.map (c • LinearMap.id : V →ₗ[ℤ] V)) = latDeg L - (Module.finrank ℝ V : ℝ) * Real.log |c|
end LateralTheory
end Formalism.DegreeFormula


