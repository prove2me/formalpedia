-- Prove2me | Definitions.Def_Formalism_GaloisCohomology_Statement
-- name    : Formalism_GaloisCohomology_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:20.369487+00:00
-- url     : https://prove2.me/theorems/b0d1dd5e-927e-40d7-a9ad-d97e09691850
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisCohomology/Statement.lean

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Theorems.Thm_ReciprocityTheory_Gal_continuous_toGS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
namespace Formalism.GaloisCohomology
section Coeff
variable (l : ℕ) [Fact l.Prime]
abbrev ZlSub : Submodule ℤ_[l] ℚ_[l] := LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l])
def QZ : Type := ℚ_[l] ⧸ ZlSub l
instance : AddCommGroup (QZ l) := inferInstanceAs (AddCommGroup (ℚ_[l] ⧸ ZlSub l))
instance : Module ℤ_[l] (QZ l) := inferInstanceAs (Module ℤ_[l] (ℚ_[l] ⧸ ZlSub l))
instance : TopologicalSpace (QZ l) := ⊥
instance : DiscreteTopology (QZ l) := ⟨rfl⟩
instance : IsTopologicalAddGroup (QZ l) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology
def QZ.mk (x : ℚ_[l]) : QZ l := Submodule.Quotient.mk (p := ZlSub l) x
end Coeff
def scalRep {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] (M : Type*) [AddCommGroup M]
    [Module R M] (ψ : Γ →* Rˣ) : Representation R Γ M where
  toFun g := ((ψ g : Rˣ) : R) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by
    ext x
    simp only [map_mul, Units.val_mul, mul_smul, LinearMap.smul_apply, LinearMap.id_apply,
      Module.End.mul_apply, map_smul]
    first | rfl | exact smul_comm _ _ _
section Field
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime]
variable (F) in

def Above : Set (HeightOneSpectrum (𝓞 F)) := {v | ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}
variable (F Ω) in

structure LData where

  S : Finset (HeightOneSpectrum (𝓞 F))
  hS : (S : Set (HeightOneSpectrum (𝓞 F))) = Above F l

  A : S → ValuationSubring Ω
  hA : ∀ v, IsPlaceOver (A v) v.1

  chi : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* ℤ_[l]ˣ
  hchi : chi.comp (toGS Ω _) = cycZ F Ω l
variable {l}
def qzTw (D : LData F Ω l) (e : ℤ) :
    Representation ℤ_[l] (GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) (QZ l) :=
  scalRep (QZ l) (D.chi ^ (-e))
def zlTw (D : LData F Ω l) (n : ℤ) :
    Representation ℤ_[l] (GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) ℤ_[l] :=
  scalRep ℤ_[l] (D.chi ^ n)
def Sha (D : LData F Ω l) (e : ℤ) : Submodule ℤ_[l] (H1 (qzTw D e)) :=
  Sha1 (qzTw D e) (locFam D.S D.A) (continuous_locFam D.S D.A)
def shaLen (D : LData F Ω l) (e : ℤ) : ℕ∞ := Module.length ℤ_[l] (Sha D e)
def VLen (D : LData F Ω l) (e : ℤ) : ℕ∞ := Module.length ℤ_[l] (H2 (zlTw D (e + 1)))
def Sha2Zl (D : LData F Ω l) (e : ℤ) : Submodule ℤ_[l] (H2 (zlTw D (e + 1))) :=
  Sha2 (zlTw D (e + 1)) (locFam D.S D.A) (continuous_locFam D.S D.A)
def localH2 (D : LData F Ω l) (e : ℤ) :
    H2 (zlTw D (e + 1)) →ₗ[ℤ_[l]] ∀ v : D.S, H2 ((zlTw D (e + 1)).comp (locFam D.S D.A v)) :=
  LinearMap.pi fun v => resH2 (zlTw D (e + 1)) (locFam D.S D.A v) (continuous_locFam D.S D.A v)
def sumLocalH0TwistLength (D : LData F Ω l) (e : ℤ) : ℕ∞ :=
  ∑ v : D.S, Module.length ℤ_[l] (H0 ((qzTw D e).comp (locFam D.S D.A v)))
def PTCase (F : Type) [Field F] [NumberField F] (l : ℕ) : Prop :=
  l ≠ 2 ∨ InfinitePlace.nrRealPlaces F = 0
def PTCokerAt (D : LData F Ω l) (e : ℤ) : Prop :=
  PTCase F l →
    Module.length ℤ_[l] ((∀ v : D.S, H2 ((zlTw D (e + 1)).comp (locFam D.S D.A v))) ⧸
        LinearMap.range (localH2 D e)) =
      Module.length ℤ_[l] (H0 (qzTw D e))
def PTShaAt (D : LData F Ω l) (e : ℤ) : Prop :=
  PTCase F l → Module.length ℤ_[l] (Sha2Zl D e) = shaLen D e
def TateLocalDualityH2AtPlaces (D : LData F Ω l) (e : ℤ) : Prop :=
  ∀ v : D.S, Module.length ℤ_[l] (H2 ((zlTw D (e + 1)).comp (locFam D.S D.A v))) =
    Module.length ℤ_[l] (H0 ((qzTw D e).comp (locFam D.S D.A v)))
def PTCoker : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), PTCokerAt D e
def PTSha : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), PTShaAt D e
def TateLocalDualityH2Hypothesis : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), TateLocalDualityH2AtPlaces D e
end Field
def LDataExists : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], Nonempty (LData F Ω l)
def Indep : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D D' : LData F Ω l) (e : ℤ),
  shaLen D e = shaLen D' e ∧ VLen D e = VLen D' e ∧ sumLocalH0TwistLength D e = sumLocalH0TwistLength D' e
def ContTw : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ),
  ContAction (qzTw D e) ∧ ContAction (zlTw D e)
def GlobalH0TwistFiniteLength : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), e ≠ 0 →
  Module.length ℤ_[l] (H0 (qzTw D e)) < ⊤
def LocalH0TwistFiniteLength : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), e ≠ 0 → ∀ v : D.S,
  Module.length ℤ_[l] (H0 ((qzTw D e).comp (locFam D.S D.A v))) < ⊤
def VFormula : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), PTCase F l →
  PTCokerAt D e → PTShaAt D e → TateLocalDualityH2AtPlaces D e →
    VLen D e + Module.length ℤ_[l] (H0 (qzTw D e)) = shaLen D e + sumLocalH0TwistLength D e
section Sel
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (F Ω) in

abbrev Places : Type :=
  {A : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω // ∀ v, IsPlaceOver (A v) v}
def unrAt (rho : Representation R (G F Ω) M) (A : ValuationSubring Ω) :
    Submodule R (H1 (rho.comp (Dec (F := F) A).subtype)) :=
  H1ur (rho.comp (Dec (F := F) A).subtype) ((Ine (F := F) A).subgroupOf (Dec (F := F) A))
def SelAll (rho : Representation R (G F Ω) M) (A : Places F Ω)
    (L : ∀ v, Submodule R (H1 (rho.comp (Dec (F := F) (A.1 v)).subtype))) : Submodule R (H1 rho) :=
  Sel rho (fun v => (Dec (F := F) (A.1 v)).subtype) (fun _ => continuous_subtype_val) L
def bkCond (rho : Representation R (G F Ω) M) (A : Places F Ω)
    (l : ℕ) (Sig : Set (HeightOneSpectrum (𝓞 F)))
    (Ll : ∀ v, Submodule R (H1 (rho.comp (Dec (F := F) (A.1 v)).subtype))) :
    ∀ v, Submodule R (H1 (rho.comp (Dec (F := F) (A.1 v)).subtype)) :=
  open Classical in
  fun v => if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then Ll v else if v ∈ Sig then ⊤ else unrAt rho (A.1 v)
def selLen (rho : Representation R (G F Ω) M) (A : Places F Ω)
    (l : ℕ) (Sig : Set (HeightOneSpectrum (𝓞 F)))
    (Ll : ∀ v, Submodule R (H1 (rho.comp (Dec (F := F) (A.1 v)).subtype))) : ℕ∞ :=
  Module.length R (SelAll rho A (bkCond rho A l Sig Ll))
end Sel
def InfUnram : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  (S : Set (HeightOneSpectrum (𝓞 F))) (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [T2Space M]
  (rhoS : Representation R (GS Ω S) M), ContAction rhoS →
    Function.Injective (resH1 rhoS (toGS Ω S) (continuous_toGS Ω S)) ∧
    ∀ x : H1 (rhoS.comp (toGS Ω S)),
      x ∈ LinearMap.range (resH1 rhoS (toGS Ω S) (continuous_toGS Ω S)) ↔
        ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
          resH1 (rhoS.comp (toGS Ω S)) (Ine (F := F) A).subtype continuous_subtype_val x = 0
end Formalism.GaloisCohomology


