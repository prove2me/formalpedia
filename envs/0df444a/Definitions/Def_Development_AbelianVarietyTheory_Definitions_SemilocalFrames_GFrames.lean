-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:00.243728+00:00
-- url     : https://prove2.me/theorems/e7b4cc9a-7587-4ca2-a96b-cc0c23897118
-- title:
--   GFrames
-- statement:
--   Definitions and structural lemmas for GFrames, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/GFrames.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL
structure Places (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) where
  quad : Module.finrank F E = 2
  loc : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p
  L : ∀ p, LocE (loc p).Fp (loc p).Ep
  L_cj : ∀ p, (L p).cj = (loc p).cj
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
namespace Places
variable (A : Places F E sig) {n : ℕ}
def bc (p : HeightOneSpectrum (𝓞 F)) (x : Fin n → E) : Fin n → (A.loc p).Ep := fun i => (A.loc p).ιE (x i)
def lat (p : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (A.L p).O (Fin n → (A.loc p).Ep) :=
  Submodule.span (A.L p).O (A.bc p '' (Λ : Set (Fin n → E)))
def Ext (p : HeightOneSpectrum (𝓞 F)) (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)) : Prop :=
  ∀ x, g' (A.bc p x) = A.bc p (g x)
def rat (K : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) where
  carrier := {g | ∀ p, ∃ g' ∈ K p, A.Ext p g g'}
  one_mem' := fun p => ⟨1, (K p).one_mem, fun _ => rfl⟩
  mul_mem' := by
    intro a b ha hb p
    obtain ⟨a', ha1, ha2⟩ := ha p
    obtain ⟨b', hb1, hb2⟩ := hb p
    refine ⟨a' * b', (K p).mul_mem ha1 hb1, fun x => ?_⟩
    change a' (b' (A.bc p x)) = A.bc p (a (b x))
    rw [hb2 x, ha2 (b x)]
  inv_mem' := by
    intro a ha p
    obtain ⟨a', ha1, ha2⟩ := ha p
    refine ⟨a'⁻¹, (K p).inv_mem ha1, fun x => ?_⟩
    have h := ha2 (a.symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    change a'.symm (A.bc p x) = A.bc p (a.symm x)
    rw [← h, LinearEquiv.symm_apply_apply]
end Places
structure GFrames (A : Places F E sig) (r k : ℕ) where
  Hm : Matrix (Fin (k + 2 * r + 1)) (Fin (k + 2 * r + 1)) E
  f : Fin (r + 1) → Fin (k + 2 * r + 1) → E
  f' : Fin (r + 1) → Fin (k + 2 * r + 1) → E
  es : Fin r → Fin (k + 2 * r + 1) → E
  es' : Fin r → Fin (k + 2 * r + 1) → E
  c : ∀ p, ((A.loc p).Fp)ˣ
  S : ∀ p, Frames (A.L p) r k
  Hm_eq : ∀ p, (S p).Hm = Hm.map (A.loc p).ιE
  f_eq : ∀ p (a : Fin (r + 1)), algebraMap (A.loc p).Fp (A.loc p).Ep ((c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • (S p).f a = A.bc p (f a)
  f'_eq : ∀ p (a : Fin (r + 1)), algebraMap (A.loc p).Fp (A.loc p).Ep ((c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • (S p).f' a = A.bc p (f' a)
  es_eq : ∀ p (a : Fin r), (S p).es a =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es a)
  es'_eq : ∀ p (a : Fin r), (S p).es' a =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es' a)
  c_unit : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite
  gg_fin : {p | (S p).gg = true}.Finite
namespace GFrames
variable {A : Places F E sig} {r k : ℕ} (G : GFrames A r k)
abbrev V (_ : GFrames A r k) : Type := Fin (k + 2 * r + 1) → E
abbrev GLV : Type := G.V ≃ₗ[E] G.V
abbrev Lt : Type := Submodule (𝓞 E) G.V
abbrev Dat : Type := ∀ p, (G.S p).Datum
def N : Subgroup G.GLV := A.rat fun p => (G.S p).N
def N' : Subgroup G.GLV := A.rat fun p => (G.S p).N'
def St : Subgroup G.GLV := A.rat fun p => (G.S p).St
def K0 : Subgroup G.GLV := A.rat fun p => (G.S p).K0
def H0 : Subgroup G.GLV := A.rat fun p => (G.S p).H0
def stabD (d : G.Dat) : Subgroup G.GLV :=
  A.rat fun p => (G.S p).H0 ⊓ MulAction.stabilizer (G.S p).GLV (d p)
def IsTerm (d : G.Dat) (Λ : G.Lt) : Prop :=
  Submodule.IsLattice E Λ ∧ ∀ p, (G.S p).IsTerm (d p) (A.lat p Λ)
def DRel (d d' : G.Dat) : Prop :=
  ∃ g : G.GLV, ∀ p, ∃ g' ∈ (G.S p).H0, A.Ext p g g' ∧ g' • d p = d' p
def LRel (Λ Λ' : G.Lt) : Prop := ∃ g ∈ G.St, Λ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E)) = Λ'
def stabL (Λ : G.Lt) : Subgroup G.GLV :=
  A.rat fun p => (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ)
def mu (Λ : G.Lt) : ℝ := invVol G.K0 (G.stabL Λ)
def om (d : G.Dat) (Λ : G.Lt) : ℂ := ∏ᶠ p, (G.S p).om (d p) (A.lat p Λ)
def amp (d : G.Dat) (P : G.Lt → Prop) : ℂ :=
  ∑' o : Quot G.LRel, if G.IsTerm d o.out ∧ P o.out then (G.mu o.out : ℂ) * G.om d o.out else 0
def mass (d : G.Dat) (P : G.Lt → Prop) : ℝ≥0∞ :=
  ∑' o : Quot G.LRel, if G.IsTerm d o.out ∧ P o.out then ENNReal.ofReal (G.mu o.out) else 0
def sumD (φ : G.Dat → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' o : Quot G.DRel, if ∃ Λ, G.IsTerm o.out Λ then
    (((G.stabD o.out : Set G.GLV).encard : ℝ≥0∞))⁻¹ * φ o.out else 0
def Gen (d : G.Dat) (Λ : G.Lt) : Prop := ∀ p, (G.S p).BBzero (d p) (A.lat p Λ)
def Om : Set (HeightOneSpectrum (𝓞 F)) := {p | (G.S p).Hp ≠ 1}
def Ht : ℝ := ∏ᶠ p, (G.S p).Hp
def ngen (d₁ : G.Dat) (Λ₁ : G.Lt) : ℝ≥0∞ :=
  G.sumD fun d => G.mass d fun Λ => G.Gen d Λ ∧
    ∀ p, ∃ h ∈ (G.S p).St, (G.S p).Fr (d p) (A.lat p Λ) = h • (G.S p).Fr (d₁ p) (A.lat p Λ₁)
def Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => ∑ i, ∑ j, G.f' b i * G.Hm i j * sig (G.f a j)
def D (l : Fin (r + 2)) : E := lead G.Zh l
def TT : E := (∑ i, ∑ j, G.f (Fin.last r) i * G.Hm i j * sig (G.f (Fin.last r) j)) *
  ∑ i, ∑ j, G.f' (Fin.last r) i * G.Hm i j * sig (G.f' (Fin.last r) j)
def Gr : E := G.D (Fin.last (r + 1)) * sig (G.D (Fin.last (r + 1))) -
  G.TT * (G.D (Fin.last r).castSucc * sig (G.D (Fin.last r).castSucc))
end GFrames
end GlobalTheory.HL


