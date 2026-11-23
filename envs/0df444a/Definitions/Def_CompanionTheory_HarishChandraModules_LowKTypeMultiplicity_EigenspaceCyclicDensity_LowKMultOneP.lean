-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
-- name    : CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:02.592452+00:00
-- url     : https://prove2.me/theorems/f7db00d3-797d-4bcb-a586-61763a0573ef
-- title:
--   Low KMult One P
-- statement:
--   Definitions and structural lemmas for Low KMult One P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/LowKMultOneP.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply


set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace CompanionTheory.D.LK
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight CasK Cas)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsDS inG rhoC nsq CDom)
open CompanionTheory.D.DSIC (KRel KUnit KStab NC)
variable {n : ℕ}
abbrev Pos (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}
abbrev Cn (n : ℕ) (V : Type) : Type := Finset (Pos n) → V
def key (i : Pos n) : ℕ := (i.1.1 : ℕ) * n + (i.1.2 : ℕ)
def sg (i : Pos n) (A : Finset (Pos n)) : ℂ := (-1) ^ (A.filter fun j => key j < key i).card
abbrev cpt (ε : Fin n → Bool) (i : Pos n) : Prop := ε i.1.1 = ε i.1.2
abbrev allT (n : ℕ) : Fin n → Bool := fun _ => true
def wt (A : Finset (Pos n)) : Fin n → ℝ := fun c =>
  ((A.filter fun i => i.1.1 = c).card : ℝ) - ((A.filter fun i => i.1.2 = c).card : ℝ)
def om (ε : Fin n → Bool) : Finset (Pos n) := univ.filter (cpt ε)
def pot (B : Finset (Pos n)) : ℕ := ∑ i ∈ B, (n - ((i.1.2 : ℕ) - (i.1.1 : ℕ)))
section Chains
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def ann (i : Pos n) : Module.End ℂ (Cn n V) where
  toFun x := fun A => if i ∈ A then 0 else sg i A • x (insert i A)
  map_add' x y := by funext A; by_cases h : i ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : i ∈ A <;> simp [h, smul_comm c]
def cre (i : Pos n) : Module.End ℂ (Cn n V) where
  toFun x := fun A => if i ∈ A then sg i A • x (A.erase i) else 0
  map_add' x y := by funext A; by_cases h : i ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : i ∈ A <;> simp [h, smul_comm c]
def lift (n : ℕ) {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') : Cn n V →ₗ[ℂ] Cn n V' :=
  T.compLeft (Finset (Pos n))
@[simp] theorem lift_apply {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') (x : Cn n V)
    (A : Finset (Pos n)) : lift n T x A = T (x A) := rfl
def bd (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cn n V) :=
  (∑ i : Pos n, if cpt ε i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0) +
    ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      if cpt ε i ∧ cpt ε j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then cre k * ann j * ann i else 0
def Ft (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) : Module.End ℂ (Cn n V) where
  toFun x := fun A => E c c (x A) + (wt (A.filter (cpt ε)) c : ℂ) • x A
  map_add' x y := by funext A; simp only [Pi.add_apply, map_add, smul_add]; abel
  map_smul' s x := by funext A; simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, smul_comm s]
def Sup (ε : Fin n → Bool) (B : Finset (Pos n)) (j : ℕ) (x : Cn n V) : Prop :=
  ∀ A, x A ≠ 0 → (A.filter fun i => ¬cpt ε i) = B ∧ (A.filter (cpt ε)).card = j
def Ref (ε₀ ε : Fin n → Bool) (x : Cn n V) : Prop := ∀ A, x A ≠ 0 → ∀ i ∈ A, cpt ε₀ i → cpt ε i
def Wt (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (τ : Fin n → ℝ) (x : Cn n V) : Prop :=
  ∀ c, Ft ε E c x = (τ c : ℂ) • x
def InN (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (y : V) : Prop :=
  ∃ w : Pos n → V, y = ∑ i : Pos n, if cpt ε i then E i.1.1 i.1.2 (w i) else 0
def evK (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) :
    FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => if ε p.1 = ε p.2 then E p.1 p.2 else 0
def ev (E : Fin n → Fin n → Module.End ℂ V) : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => E p.1 p.2
def evd (F : Fin n → Module.End ℂ V) : FreeAlgebra ℂ (Fin n) →ₐ[ℂ] Module.End ℂ V := FreeAlgebra.lift ℂ F
def Cyc (E : Fin n → Fin n → Module.End ℂ V) (v : V) : Submodule ℂ V :=
  LinearMap.range ((LinearMap.applyₗ v).comp (ev E).toLinearMap)
def LocFin (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Prop :=
  ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ KStab ε E S ∧ x ∈ S
def IsMin (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) : Prop :=
  ∀ (μ : Fin n → ℝ) (x : V), x ≠ 0 → KHighest ε E μ x → vNormSq ε (lowK ε lam) ≤ vNormSq ε μ
structure Filt (R : Pos n → Prop) (M : Fin n → Fin n → Module.End ℂ V) (a d : Pos n → Module.End ℂ V)
    (Fil : ℕ → Submodule ℂ V) : Prop where
  a_comm : ∀ i j, Commute (a i) (a j)
  d_comm : ∀ i j, Commute (d i) (d j)
  da : ∀ i j, R i → d i * a j - a j * d i = if i = j then 1 else 0
  mono : Monotone Fil
  exh : ∀ z, ∃ k, z ∈ Fil k
  a_mem : ∀ i k, ∀ z ∈ Fil k, a i z ∈ Fil (k + 1)
  r_mem : ∀ i k, ∀ z ∈ Fil k, M i.1.1 i.1.2 z - a i z ∈ Fil k
  d_mem : ∀ i k, ∀ z ∈ Fil (k + 1), d i z ∈ Fil k
  d_zero : ∀ i, ∀ z ∈ Fil 0, d i z = 0
end Chains
def Inv (ε : Fin n → Bool) (a : FreeAlgebra ℂ (Fin n × Fin n)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
    ∀ c d, ε c = ε d → Commute (E c d) (ev E a)
def Free (n m : ℕ) : Prop :=
  ∃ (Z : Type) (_ : AddCommGroup Z) (_ : Module ℂ Z) (M : Fin n → Fin n → Module.End ℂ Z) (χ : Z →ₗ[ℂ] ℂ) (z₀ : Z)
    (a d : Pos n → Module.End ℂ Z) (Fil : ℕ → Submodule ℂ Z),
    GlRel M ∧ χ z₀ = 1 ∧ (∀ c e z, χ (M c e z) = 0) ∧ Filt (fun i => (i.1.1 : ℕ) < m) M a d Fil
def CARp : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (i j : Pos n),
    (ann i * ann j + ann j * ann i : Module.End ℂ (Cn n V)) = 0 ∧
    (cre i * cre j + cre j * cre i : Module.End ℂ (Cn n V)) = 0 ∧
    (ann i * cre j + cre j * ann i : Module.End ℂ (Cn n V)) = if i = j then 1 else 0
def BdSq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    KRel ε E → bd ε E * bd ε E = 0
def BdWt : Prop :=
  ∀ (n : ℕ) (ε₀ ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    (∀ a b, ε a = ε b → ε₀ a = ε₀ b) → KRel ε E → ∀ c, Commute (Ft ε₀ E c) (bd ε E)
def BdSup : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    (∀ B j (x : Cn n V), Sup ε B (j + 1) x → Sup ε B j (bd ε E x)) ∧
    (∀ B (x : Cn n V), Sup ε B 0 x → bd ε E x = 0) ∧
    (∀ (ε₀ : Fin n → Bool) (x : Cn n V), (∀ a b, ε a = ε b → ε₀ a = ε₀ b) → Ref ε₀ ε x →
      bd ε₀ E x = bd ε E x ∧ Ref ε₀ ε (bd ε E x)) ∧
    ∀ B j (x : Cn n V), Sup ε B j x → ∀ A, (bd (allT n) E x - bd ε E x) A ≠ 0 →
      pot (A.filter fun i => ¬cpt ε i) < pot B ∧ A.card + 1 = B.card + j
def AcycAbs : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Type) [AddCommGroup Z] [Module ℂ Z] (E : Fin n → Fin n → Module.End ℂ Z)
    (a d : Pos n → Module.End ℂ Z) (Fil : ℕ → Submodule ℂ Z), KRel ε E → Filt (cpt ε) E a d Fil →
    ∀ B j (x : Cn n Z), Sup ε B (j + 1) x → bd ε E x = 0 → ∃ t : Cn n Z, Sup ε B (j + 2) t ∧ bd ε E t = x
def Verma2 : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ M : Fin n → Fin n → Module.End ℂ (MvPolynomial (NC ε) ℂ),
    GlRel M ∧ (∀ (i : NC ε) (f : MvPolynomial (NC ε) ℂ), M i.1.1 i.1.2 f = MvPolynomial.X i * f) ∧
      (∀ a b f, MvPolynomial.constantCoeff (M a b f) = 0) ∧
      ∀ a b f, ε a = ε b → (M a b f).totalDegree ≤ f.totalDegree
def FreeStep : Prop := ∀ n m : ℕ, Free n m → Free n (m + 1)
def Cover2 : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    KRel ε E → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (EY : Fin n → Fin n → Module.End ℂ Y)
      (π : Y →ₗ[ℂ] V), KRel ε EY ∧ Function.Surjective π ∧ (∀ a b y, π (EY a b y) = E a b (π y)) ∧
      ∀ B j (x : Cn n Y), Sup ε B (j + 1) x → bd ε EY x = 0 → ∃ t : Cn n Y, Sup ε B (j + 2) t ∧ bd ε EY t = x
def GenCO : Prop :=
  ∀ (n : ℕ) (ε₀ ε : Fin n → Bool) (a : FreeAlgebra ℂ (Fin n × Fin n)) (b : FreeAlgebra ℂ (Fin n)),
    (∀ c d, ε c = ε d → ε₀ c = ε₀ d) →
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), KRel ε₀ E →
      (∀ i : Pos n, cpt ε i → Commute (E i.1.1 i.1.2) (evK ε₀ E a)) ∧
      ∀ x : V, InN ε₀ E (evK ε₀ E a x - evd (fun c => E c c) b x)) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), KRel ε₀ E →
      ∀ B j (x : Cn n V), Sup ε₀ B j x → Ref ε₀ ε x → bd ε₀ E x = 0 →
        ∃ w : Cn n V, Sup ε₀ B (j + 1) w ∧ lift n (evK ε₀ E a) x - evd (Ft ε₀ E) b x = bd ε₀ E w
def COK : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    KRel ε E → ∀ B j (τ : Fin n → ℝ) (x : Cn n V), Sup ε B j x → Wt ε E τ x → bd ε E x = 0 →
      ∃ w : Cn n V, Sup ε B (j + 1) w ∧
        lift n (CasK ε E) x - ((nsq (τ - rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • x = bd ε E w
def WtProj : Prop :=
  ∀ (n : ℕ) (ε₀ ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), KRel ε E → KUnit ε E → LocFin ε E →
    ∀ (D : Module.End ℂ (Cn n V)), (∀ c, Commute (Ft ε₀ E c) D) → ∀ (τ : Fin n → ℝ) (t : Cn n V),
      Wt ε₀ E τ (D t) → ∃ t' : Cn n V, Wt ε₀ E τ t' ∧ D t' = D t ∧ ∀ A, t A = 0 → t' A = 0
def WtMajor : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), KRel ε E → KUnit ε E → LocFin ε E →
    ∀ (μ : Fin n → ℝ) (s : ℂ) (x : V), x ≠ 0 → IsWeight E μ x → CasK ε E x = s • x →
      ∃ (ν : Fin n → ℝ) (y : V), y ≠ 0 ∧ KHighest ε E ν y ∧ s = ((nsq (ν + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) ∧
        (∀ c d, c < d → ε c = ε d → ν d ≤ ν c) ∧
        ∀ w : Equiv.Perm (Fin n), (∀ c, ε (w c) = ε c) → CDom ε (μ ∘ w) ν
def SignIneq : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ), StrictAnti lam → ∀ D : Finset (Pos n), D.Nonempty →
    nsq ((fun c => lam c + (((n : ℝ) - 1) / 2 - ((c : ℕ) : ℝ))) - wt D) <
      nsq fun c => lam c + (((n : ℝ) - 1) / 2 - ((c : ℕ) : ℝ))
def NumK : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam ν : Fin n → ℝ) (B C : Finset (Pos n)), StrictAnti lam → B.Nonempty →
    (∀ i ∈ B, ¬cpt ε i) → (∀ i ∈ C, cpt ε i) → (∀ c d, c < d → ε c = ε d → ν d ≤ ν c) →
    (∀ w : Equiv.Perm (Fin n), (∀ c, ε (w c) = ε c) →
      CDom ε ((lowK ε lam + (2 : ℝ) • rhoC ε - wt B - wt C) ∘ w) ν) →
    nsq (ν + rhoC ε) = nsq (lowK ε lam + rhoC ε - wt B) → vNormSq ε ν < vNormSq ε (lowK ε lam)
def VanK : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), StrictAnti lam → KRel ε E → KUnit ε E → LocFin ε E → IsMin ε E lam →
    ∀ B j (z : Cn n V), B.Nonempty → Sup ε B j z → Wt (allT n) E (lowK ε lam + (2 : ℝ) • rhoC ε) z → bd ε E z = 0 →
      ∃ t : Cn n V, Sup ε B (j + 1) t ∧ Wt (allT n) E (lowK ε lam + (2 : ℝ) • rhoC ε) t ∧ bd ε E t = z
def Inj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), StrictAnti lam → GlRel E → KUnit ε E → LocFin ε E → IsMin ε E lam →
    ∀ (u : V) (y : Cn n V), IsWeight E (lowK ε lam) u → Sup (allT n) ∅ ((om ε).card + 1) y →
      bd (allT n) E y = Pi.single (om ε) u → u = 0
def TopCycle : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
    (μ : Fin n → ℝ) (v : V), wt (om ε) = (2 : ℝ) • rhoC ε ∧ (KHighest ε E μ v →
      bd (allT n) E (Pi.single (om ε) v) = 0 ∧ Wt (allT n) E (μ + (2 : ℝ) • rhoC ε) (Pi.single (om ε) v))
def HCdec : Prop :=
  ∀ (n : ℕ) (a : FreeAlgebra ℂ (Fin n × Fin n)),
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
      ∀ c, Commute (E c c) (ev E a)) →
    ∃ b : FreeAlgebra ℂ (Fin n), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
      GlRel E → ∀ x : V, InN (allT n) E (ev E a x - evd (fun c => E c c) b x)
def Dens : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (v : V) (L : Submodule ℂ V), KRel ε E → KUnit ε E →
    v ≠ 0 → v ∈ L → IsWeight E μ v → FiniteDimensional ℂ L → KStab ε E L →
    (∀ L' ≤ L, KStab ε E L' → L' = ⊥ ∨ L' = L) → (∀ x ∈ L, IsWeight E μ x → ∃ c : ℂ, x = c • v) →
    L ≤ Cyc E v ∧ ∀ φ : L →ₗ[ℂ] V, (∀ s, φ s ∈ Cyc E v) → ∃ a, ∀ s : L, ev E a s = φ s
def InvLift : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
    (L : Submodule ℂ V) (a : FreeAlgebra ℂ (Fin n × Fin n)), GlRel E → KStab ε E L →
    (∀ c d, ε c = ε d → ∀ s ∈ L, E c d (ev E a s) = ev E a (E c d s)) →
      ∃ a', Inv ε a' ∧ ∀ s ∈ L, ev E a' s = ev E a s
def MultAlg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), StrictAnti lam → GlRel E → KUnit ε E → LocFin ε E → IsMin ε E lam →
    ∀ v w : V, v ≠ 0 → KHighest ε E (lowK ε lam) v → KHighest ε E (lowK ε lam) w → w ∈ Cyc E v → ∃ c : ℂ, w = c • v
structure IsKMod {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) : Prop where
  mem : ∀ v, v ∈ D ↔ IsKFin ε σ v
  real : ∀ X, inG ε X → ∀ v : D, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v)
    (∑ a, ∑ b, X a b • (E a b v : H)) 0
  gl : GlRel E
  unit : IsUnitary ε E
  locFin : LocFin ε E
  hw : ∀ (μ : Fin n → ℝ) (T : Submodule ℂ H), IsKTypeOf ε σ μ T → ∃ v : D, v ≠ 0 ∧ (v : H) ∈ T ∧ KHighest ε E μ v
  ty : ∀ (μ : Fin n → ℝ) (x : D), x ≠ 0 → KHighest ε E μ x → ∃ T : Submodule ℂ H, IsKTypeOf ε σ μ T
def KModExists : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∃ (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), IsKMod ε σ D E
def CycDense : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ (v : D) (c : ℂ), v ≠ 0 → Cas E v = c • v →
      ((Cyc E v).map D.subtype).topologicalClosure = ⊤
def OrthCyc : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (v u : V), GlRel E → KUnit ε E → LocFin ε E →
    (∀ w ∈ Cyc E v, KHighest ε E μ w → ∃ c : ℂ, w = c • v) → KHighest ε E μ u → ⟪v, u⟫_ℂ = 0 →
      ∀ m ∈ Cyc E v, ⟪m, u⟫_ℂ = 0
def LowKMultOneP : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    ∀ S S' : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S → IsKTypeOf ε σ (lowK ε lam) S' → S = S'
end CompanionTheory.D.LK


