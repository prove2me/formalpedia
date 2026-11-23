-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
-- name    : CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:15.80264+00:00
-- url     : https://prove2.me/theorems/4b9a7c0c-2a4f-4f7c-b0cc-2580251853ff
-- title:
--   Capelli Determinant Block Product
-- statement:
--   Definitions and structural lemmas for Capelli Determinant Block Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/CapelliDeterminantBlockProduct.lean

import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace CompanionTheory.D.DSIC
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight qdet qminor)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsWtOn inG inK IsKStableOn)
open PI.DSInfCharCap (dsigC actU Egl)
open PI.PhMeasCore (dsig smoothVecs)
variable {n : ℕ}
abbrev NC (ε : Fin n → Bool) : Type := {p : Fin n × Fin n // ε p.1 = true ∧ ε p.2 = false}
abbrev Ch (ε : Fin n → Bool) (V : Type) : Type := Finset (NC ε) → V
def key {ε : Fin n → Bool} (i : NC ε) : ℕ := (i.1.1 : ℕ) * n + (i.1.2 : ℕ)
def sg {ε : Fin n → Bool} (i : NC ε) (A : Finset (NC ε)) : ℂ := (-1) ^ (A.filter fun j => key j < key i).card
section Chains
variable {ε : Fin n → Bool} {V : Type} [AddCommGroup V] [Module ℂ V]
def ann (i : NC ε) : Module.End ℂ (Ch ε V) where
  toFun x := fun A => if i ∈ A then 0 else sg i A • x (insert i A)
  map_add' x y := by funext A; by_cases h : i ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : i ∈ A <;> simp [h, smul_comm c]
def cre (i : NC ε) : Module.End ℂ (Ch ε V) where
  toFun x := fun A => if i ∈ A then sg i A • x (A.erase i) else 0
  map_add' x y := by funext A; by_cases h : i ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : i ∈ A <;> simp [h, smul_comm c]
def lift (ε : Fin n → Bool) {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') : Ch ε V →ₗ[ℂ] Ch ε V' :=
  T.compLeft (Finset (NC ε))
def Gop (ε : Fin n → Bool) (c d : Fin n) : Module.End ℂ (Ch ε V) :=
  ∑ i : NC ε, ∑ j : NC ε,
    ((if i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2 then 1 else 0) -
      (if i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1 then 1 else 0) : ℂ) • (cre i * ann j)
def Fop (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) : Module.End ℂ (Ch ε V) :=
  lift ε (E c d) + Gop ε c d
def Fdual (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) : Module.End ℂ (Ch ε V) :=
  lift ε (E c d) - Gop ε d c
def bdA (a : NC ε → Module.End ℂ V) : Module.End ℂ (Ch ε V) :=
  ∑ i : NC ε, (lift ε (a i) : Module.End ℂ (Ch ε V)) * ann i
def bd (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Ch ε V) :=
  bdA fun i : NC ε => E i.1.1 i.1.2
def cob (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Ch ε V) :=
  ∑ i : NC ε, (lift ε (E i.1.2 i.1.1) : Module.End ℂ (Ch ε V)) * cre i
def Deg (j : ℕ) (x : Ch ε V) : Prop := ∀ A : Finset (NC ε), A.card ≠ j → x A = 0
end Chains
def KRel {A : Type} [Ring A] (ε : Fin n → Bool) (F : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, ε a = ε b → ε c = ε d → F a b * F c d - F c d * F a b =
    (if b = c then F a d else 0) - (if d = a then F c b else 0)
def KUnit {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) : Prop :=
  ∀ a b : Fin n, ε a = ε b → ∀ x y : V, ⟪E a b x, y⟫_ℂ = ⟪x, E b a y⟫_ℂ
def KStab {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (S : Submodule ℂ V) : Prop :=
  ∀ a b : Fin n, ε a = ε b → ∀ v ∈ S, E a b v ∈ S
def nb (ε : Fin n → Bool) (s : Bool) : ℕ := (univ.filter fun a => ε a = s).card
def blk (ε : Fin n → Bool) (s : Bool) : Fin (nb ε s) → Fin n :=
  fun i => (univ.filter fun a => ε a = s).orderEmbOfFin rfl i
def zeta {A : Type} [Ring A] [Algebra ℂ A] (ε : Fin n → Bool) (F : Fin n → Fin n → A) (u : ℂ) : A :=
  qminor F (blk ε false) (blk ε false) u * qminor F (blk ε true) (blk ε true) (u - (nb ε false : ℂ))
def wtA {ε : Fin n → Bool} (A : Finset (NC ε)) : Fin n → ℝ := fun c =>
  ((A.filter fun i => i.1.1 = c).card : ℝ) - ((A.filter fun i => i.1.2 = c).card : ℝ)
def A1 (ε : Fin n → Bool) : Finset (NC ε) := univ.filter fun i => i.1.2 < i.1.1
def gam (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := lowK ε lam + wtA (A1 ε)
def ip {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x y : Ch ε V) : ℂ :=
  ∑ A, ⟪x A, y A⟫_ℂ
def CAR : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (i j : NC ε),
    (ann i * ann j + ann j * ann i : Module.End ℂ (Ch ε V)) = 0 ∧
    (cre i * cre j + cre j * cre i : Module.End ℂ (Ch ε V)) = 0 ∧
    (ann i * cre j + cre j * ann i : Module.End ℂ (Ch ε V)) = if i = j then 1 else 0
def FRel : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    KRel ε E → KRel ε (Fop ε E) ∧ KRel ε (Fdual ε E)
def BdFacts : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    GlRel E → bd ε E * bd ε E = 0 ∧
      ∀ c d, ε c = ε d → Commute (Fop ε E c d) (bd ε E) ∧ Commute (Fop ε E c d) (cob ε E)
def GFacts : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ g : Fin n → Fin n → Finset (NC ε) → Finset (NC ε) → ℝ,
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (c d : Fin n) (x : Ch ε V) (A : Finset (NC ε)),
      Gop ε c d x A = ∑ B, (g c d A B : ℂ) • x B) ∧
    (∀ c d A B, g c d A B = g d c B A) ∧
    (∀ c d A B, g c d A B ≠ 0 → A.card = B.card ∧ wtA A = wtA B + Pi.single c 1 - Pi.single d 1) ∧
    (∀ c A B, g c c A B = if A = B then wtA A c else 0) ∧
    (∀ c d A, d < c → g c d A (A1 ε) = 0)
def Koszul : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Type) [AddCommGroup Z] [Module ℂ Z] (a d : NC ε → Module.End ℂ Z),
    (∀ i j, Commute (a i) (a j)) → (∀ i j, Commute (d i) (d j)) →
    (∀ i j, d i * a j - a j * d i = if i = j then 1 else 0) →
    (∀ z : Z, ∃ m : ℕ, ∀ l : List (NC ε), l.length = m → (l.map d).prod z = 0) →
    ∀ (j : ℕ) (x : Ch ε Z), Deg (j + 1) x → bdA a x = 0 → ∃ t : Ch ε Z, Deg (j + 2) t ∧ bdA a t = x
def Verma : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ M : Fin n → Fin n → Module.End ℂ (MvPolynomial (NC ε) ℂ),
    GlRel M ∧ (∀ (i : NC ε) (f : MvPolynomial (NC ε) ℂ), M i.1.1 i.1.2 f = MvPolynomial.X i * f) ∧
      ∀ a b f, MvPolynomial.constantCoeff (M a b f) = 0
def Cover : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    GlRel E → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (EY : Fin n → Fin n → Module.End ℂ Y)
      (π : Y →ₗ[ℂ] V), GlRel EY ∧ Function.Surjective π ∧ (∀ a b y, π (EY a b y) = E a b (π y)) ∧
      ∀ (j : ℕ) (x : Ch ε Y), Deg (j + 1) x → bd ε EY x = 0 → ∃ t : Ch ε Y, Deg (j + 2) t ∧ bd ε EY t = x
def CapelliDeterminantBlockProduct : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    GlRel E → ∀ (u : ℂ) (v : V), ∃ w : NC ε → V, qdet E u v - zeta ε E u v = ∑ i : NC ε, E i.1.1 i.1.2 (w i)
def CO : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    GlRel E → ∀ (u : ℂ) (j : ℕ) (x : Ch ε V), Deg j x → bd ε E x = 0 →
      ∃ w : Ch ε V, Deg (j + 1) w ∧ lift ε (qdet E u) x - zeta ε (Fop ε E) u x = bd ε E w
def ZetaHW : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (F : Fin n → Fin n → Module.End ℂ V) (x : V), KRel ε F → KHighest ε F (gam ε lam) x → ∀ Y : ℂ,
      zeta ε F (Y + ((n : ℂ) - 1) / 2) x = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • x
def WLem : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
    (γ : Fin n → ℝ) (x : Ch ε V), x ≠ 0 → KHighest ε (Fop ε E) γ x →
      ∃ A, x A ≠ 0 ∧ KHighest ε E (γ - wtA A) (x A)
def NormLt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), StrictAnti lam → ∀ A : Finset (NC ε), A ≠ A1 ε →
    vNormSq ε (gam ε lam - wtA A) < vNormSq ε (lowK ε lam)
def Adj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), IsUnitary ε E → ∀ w x : Ch ε V, ip (bd ε E w) x = -ip w (cob ε E x)
def GamDom : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam →
    ∃ γ : Fin n → ℤ, (∀ a, gam ε lam a = γ a) ∧ ∀ c d, c < d → ε c = ε d → γ d ≤ γ c
def KHWExists : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℤ), (∀ c d, c < d → ε c = ε d → γ d ≤ γ c) →
    ∃ (U : Type) (_ : NormedAddCommGroup U) (_ : InnerProductSpace ℂ U) (_ : FiniteDimensional ℂ U)
      (E : Fin n → Fin n → Module.End ℂ U) (u : U),
      KRel ε E ∧ KUnit ε E ∧ u ≠ 0 ∧ KHighest ε E (fun a => (γ a : ℝ)) u
def HWMap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (T : Type) [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ET : Fin n → Fin n → Module.End ℂ T) (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (t : T) (v : V)
    (S : Submodule ℂ V), KRel ε ET → KUnit ε ET → KRel ε E → KUnit ε E → t ≠ 0 → KHighest ε ET μ t →
    KHighest ε E μ v → FiniteDimensional ℂ S → KStab ε E S → v ∈ S →
      ∃ φ : T →ₗ[ℂ] V, φ t = v ∧ ∀ a b, ε a = ε b → ∀ y, φ (ET a b y) = E a b (φ y)
def PRV : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (S : Submodule ℂ V), IsHCParam lam → KRel ε E → KUnit ε E →
    KHighest ε E (lowK ε lam) v → FiniteDimensional ℂ S → KStab ε E S → v ∈ S →
      ∃ c : Ch ε V, Deg (A1 ε).card c ∧ KHighest ε (Fop ε E) (gam ε lam) c ∧ c (A1 ε) = v
def AlgCore : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (S : Submodule ℂ V), IsHCParam lam → GlRel E → IsUnitary ε E →
    KHighest ε E (lowK ε lam) v → FiniteDimensional ℂ S → KStab ε E S → v ∈ S →
    (∀ (μ : Fin n → ℝ) (x : V), x ≠ 0 → KHighest ε E μ x → vNormSq ε (lowK ε lam) ≤ vNormSq ε μ) →
      ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v
def AlgCoreSub : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (V₀ : Submodule ℂ V) (v : V) (S : Submodule ℂ V), IsHCParam lam → GlRel E →
    IsUnitary ε E → (∀ a b, ∀ x ∈ V₀, E a b x ∈ V₀) → S ≤ V₀ →
    KHighest ε E (lowK ε lam) v → FiniteDimensional ℂ S → KStab ε E S → v ∈ S →
    (∀ (μ : Fin n → ℝ), ∀ x ∈ V₀, x ≠ 0 → KHighest ε E μ x → vNormSq ε (lowK ε lam) ≤ vNormSq ε μ) →
      ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v
section Analytic
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
structure IsSmMod (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H)
    (E : Fin n → Fin n → Module.End ℂ S) : Prop where
  mem : ∀ v, v ∈ S ↔ v ∈ smoothVecs (Formalism.REAL.Jm ε) σ
  act : ∀ a b (v : S), (E a b v : H) = dsigC ε σ (Matrix.single a b 1) v
  real : ∀ X, inG ε X → ∀ v : S, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v)
    (∑ a, ∑ b, X a b • (E a b v : H)) 0
  gl : GlRel E
  unit : IsUnitary ε E
  stab : ∀ g ∈ UJset ε, ∀ v ∈ S, σ g v ∈ S
  conj : ∀ g ∈ UJset ε, ∀ a b (v w : S), (w : H) = σ g v →
    σ g (E a b v) = ∑ c, ∑ d, (g c a * g⁻¹ b d) • (E c d w : H)
end Analytic
def SmLin : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ →
    (0 : H) ∈ smoothVecs (Formalism.REAL.Jm ε) σ ∧
    (∀ v ∈ smoothVecs (Formalism.REAL.Jm ε) σ, ∀ w ∈ smoothVecs (Formalism.REAL.Jm ε) σ, v + w ∈ smoothVecs (Formalism.REAL.Jm ε) σ) ∧
    (∀ (c : ℂ), ∀ v ∈ smoothVecs (Formalism.REAL.Jm ε) σ, c • v ∈ smoothVecs (Formalism.REAL.Jm ε) σ) ∧
    (∀ g ∈ UJset ε, ∀ v ∈ smoothVecs (Formalism.REAL.Jm ε) σ, σ g v ∈ smoothVecs (Formalism.REAL.Jm ε) σ) ∧
    (∀ X, inG ε X → ∀ v ∈ smoothVecs (Formalism.REAL.Jm ε) σ, dsig σ X v ∈ smoothVecs (Formalism.REAL.Jm ε) σ ∧
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dsig σ X v) 0) ∧
    ∀ X Y, inG ε X → inG ε Y → ∀ v ∈ smoothVecs (Formalism.REAL.Jm ε) σ,
      dsig σ (X + Y) v = dsig σ X v + dsig σ Y v ∧ ∀ s : ℝ, dsig σ ((s : ℂ) • X) v = (s : ℂ) • dsig σ X v
def SmBracket : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ →
    ∀ X Y, inG ε X → inG ε Y → ∀ v ∈ smoothVecs (Formalism.REAL.Jm ε) σ,
      dsig σ X (dsig σ Y v) - dsig σ Y (dsig σ X v) = dsig σ (X * Y - Y * X) v
def SmMod : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ →
    ∃ (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S), IsSmMod ε σ S E
def ActQ : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S),
    IsSmMod ε σ S E → ∀ (u : ℂ) (v : S), actU ε σ (qdet (Egl n) u) v = (qdet E u v : H)
def Spread : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S),
    IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsSmMod ε σ S E → ∀ v₀ : S, v₀ ≠ 0 →
    (∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) v₀ = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v₀) →
      ∀ (v : S) (Y : ℂ), qdet E (Y + ((n : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v
def KFinSm : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ v : H, IsKFin ε σ v → v ∈ smoothVecs (Formalism.REAL.Jm ε) σ
def KFinStab : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S),
    IsURepOn (UJset ε) σ → IsSmMod ε σ S E →
      ∃ V₀ : Submodule ℂ S, (∀ x : S, x ∈ V₀ ↔ IsKFin ε σ (x : H)) ∧ ∀ a b, ∀ x ∈ V₀, E a b x ∈ V₀
def KExp : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∀ g ∈ Kset ε, ∃ X, inK ε X ∧ g = NormedSpace.exp X
def StabLink : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S),
    IsURepOn (UJset ε) σ → IsSmMod ε σ S E → ∀ U : Submodule ℂ S, FiniteDimensional ℂ U →
      (KStab ε E U ↔ IsKStableOn ε σ (U.map S.subtype))
def WtLink : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S),
    IsURepOn (UJset ε) σ → IsSmMod ε σ S E → ∀ (μ : Fin n → ℝ) (v : S),
      (IsWeight E μ v ↔ IsWtOn (Kset ε) σ μ (v : H))
def HWofType : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S),
    IsURepOn (UJset ε) σ → IsSmMod ε σ S E → ∀ (μ : Fin n → ℝ) (T : Submodule ℂ H), IsKTypeOf ε σ μ T → T ≤ S →
      ∃ v : S, v ≠ 0 ∧ (v : H) ∈ T ∧ KHighest ε E μ v
def LowSpan : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (v : V) (S : Submodule ℂ V), KRel ε E → KUnit ε E →
    v ≠ 0 → KHighest ε E μ v → FiniteDimensional ℂ S → KStab ε E S → v ∈ S →
      ∃ L : Submodule ℂ V, L ≤ S ∧ v ∈ L ∧ KStab ε E L ∧ (∀ L' ≤ L, KStab ε E L' → L' = ⊥ ∨ L' = L) ∧
        (∀ (ν : Fin n → ℝ), ∀ x ∈ L, x ≠ 0 → IsWeight E ν x → PI.UpqRep.CDom ε ν μ) ∧
        ∀ x ∈ L, IsWeight E μ x → ∃ c : ℂ, x = c • v
def TypeOfHW : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S),
    IsURepOn (UJset ε) σ → IsSmMod ε σ S E → ∀ (μ : Fin n → ℝ) (x : S), x ≠ 0 → IsKFin ε σ (x : H) →
      KHighest ε E μ x → ∃ T : Submodule ℂ H, IsKTypeOf ε σ μ T
end CompanionTheory.D.DSIC


