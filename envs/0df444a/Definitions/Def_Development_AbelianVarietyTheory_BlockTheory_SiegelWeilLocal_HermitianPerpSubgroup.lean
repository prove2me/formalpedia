-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_HermitianPerpSubgroup
-- name    : Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_HermitianPerpSubgroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:19.416666+00:00
-- url     : https://prove2.me/theorems/1cbac829-92f5-4955-aa95-234aadda2a7f
-- title:
--   Hermitian Perp Subgroup
-- statement:
--   Definitions and structural lemmas for Hermitian Perp Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelWeilLocal/HermitianPerpSubgroup.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers
section Unip
variable {A : Type} [CommRing A] {n : ℕ}
def stabAdd (M : AddSubgroup (Fin n → A)) : Subgroup (GL (Fin n) A) where
  carrier := {g | ∀ v, v ∈ M ↔ (g : Matrix (Fin n) (Fin n) A) *ᵥ v ∈ M}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro a b ha hb x
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb x).trans (ha _)
  inv_mem' := by
    intro g hg x
    have := hg (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *ᵥ x)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    exact this.symm
def unip (M M' : AddSubgroup (Fin n → A)) : Subgroup (GL (Fin n) A) where
  carrier := {g | g ∈ stabAdd M ∧ g ∈ stabAdd M' ∧
    ∀ v ∈ M, (g : Matrix (Fin n) (Fin n) A) *ᵥ v - v ∈ M'}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun v _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨Subgroup.mul_mem _ ha1 hb1, Subgroup.mul_mem _ ha2 hb2, fun v hv => ?_⟩
    have h := M'.add_mem (ha3 _ ((hb1 v).1 hv)) (hb3 v hv)
    simpa only [Units.val_mul, ← Matrix.mulVec_mulVec, sub_add_sub_cancel] using h
  inv_mem' := by
    rintro g ⟨h1, h2, h3⟩
    refine ⟨Subgroup.inv_mem _ h1, Subgroup.inv_mem _ h2, fun v hv => ?_⟩
    have h := M'.neg_mem (h3 _ ((Subgroup.inv_mem _ h1 v).1 hv))
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, neg_sub] at h
    exact h
def colSpan {m : ℕ} (Q : Matrix (Fin n) (Fin m) A) (a : ℕ) : AddSubgroup (Fin n → A) :=
  (Submodule.span A {v : Fin n → A | ∃ b : Fin m, (b : ℕ) < a ∧ v = fun i => Q i b}).toAddSubgroup
def flagUnip {m : ℕ} (Q : Matrix (Fin n) (Fin m) A) : Subgroup (GL (Fin n) A) :=
  ⨅ a : Fin m, unip (colSpan Q ((a : ℕ) + 1)) (colSpan Q a)
example (M : AddSubgroup (Fin n → A)) : unip M M = stabAdd M := by
  ext g
  exact ⟨fun h => h.1, fun h => ⟨h, h, fun v hv => M.sub_mem ((h v).1 hv) hv⟩⟩
end Unip
section Groups
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n r : ℕ}
  (J : Matrix (Fin n) (Fin n) E)
def matHom : HA R σ J →* GL (Fin n) (R ⊗[F] E) := (HR R σ J).subtype
def ratG : Subgroup (HA R σ J) := HFinIn R σ J
def Hgp (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E) : Subgroup (HA R σ J) :=
  (unip (colSpan (P.map (inclR (F := F) R)) (r + 1) ⊔ colSpan (f.map (inclR (F := F) R)) r) ⊥).comap
    (matHom R σ J)
def Ngp (P : Matrix (Fin n) (Fin (r + 1)) E) : Subgroup (HA R σ J) :=
  (flagUnip ((GlobalTheory.SgAlg.eOf P).map (inclR (F := F) R)) ⊓
    unip (LinearMap.ker (GlobalTheory.SgAlg.cT (sigR R σ) ((GlobalTheory.SgAlg.eOf P).map (inclR (F := F) R)) *
        JR R J).mulVecLin).toAddSubgroup
      (colSpan ((GlobalTheory.SgAlg.eOf P).map (inclR (F := F) R)) r)).comap (matHom R σ J)
def Sgp (P : Matrix (Fin n) (Fin (r + 1)) E) : Subgroup (HA R σ J) :=
  (flagUnip (P.map (inclR (F := F) R))).comap (matHom R σ J)
end Groups
section Lattices
variable {E : Type} [Field E] [NumberField E] {n r : ℕ}
def perp (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) {m : ℕ} (Q : Matrix (Fin n) (Fin m) E) :
    Submodule (𝓞 E) (Fin n → E) :=
  (LinearMap.ker (GlobalTheory.SgAlg.cT σ Q * J).mulVecLin).restrictScalars (𝓞 E)
def Wb (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (f : Matrix (Fin n) (Fin r) E) : Submodule (𝓞 E) (Fin n → E) :=
  perp σ J (GlobalTheory.SgAlg.eOf P) ⊓ perp σ J f
def Wsp (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (f : Matrix (Fin n) (Fin r) E) : Submodule (𝓞 E) (Fin n → E) :=
  perp σ J P ⊓ perp σ J f
def bigLat (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E)
    (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {v | ∃ (b : Fin r) (a : E), a ∈ GlobalTheory.SgGlob.dInv E (r - (b : ℕ)) ∧
      v = a • fun i => P i b.castSucc} ⊔ L ⊔
    Submodule.span (𝓞 E) {v | ∃ (b : Fin r) (a : E), a ∈ (GlobalTheory.SgGlob.dInv E (r - (b : ℕ)))⁻¹ ∧
      v = a • fun i => f i b}
def flagLat {k : ℕ} (L₀ : Submodule (𝓞 E) (Fin n → E)) (w : Ideal (𝓞 E)) (ε : Fin k → Fin n → E)
    (a : ℕ) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {v | ∃ j : Fin k, (j : ℕ) < a ∧ v = ε j} ⊔ w • L₀
def SplitsCompletely (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  Nat.card {w : HeightOneSpectrum (𝓞 E) // (p : 𝓞 E) ∈ w.asIdeal} = Module.finrank ℚ E
def gammaOne (SG : Finset (HeightOneSpectrum (𝓞 E))) (k : ℕ) : ℝ≥0∞ :=
  ∏ w ∈ SG, (Nat.card (GL (Fin k) (𝓞 E ⧸ w.asIdeal)) : ℝ≥0∞) /
    (Nat.card (Formalism.L2.Col.HU (𝓞 E ⧸ w.asIdeal) k) : ℝ≥0∞)
end Lattices
section Levels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {n r k : ℕ} (J : Matrix (Fin n) (Fin n) E)
variable (F) in

def hat (M : Submodule (𝓞 E) (Fin n → E)) : AddSubgroup (Fin n → Af F ⊗[F] E) :=
  AddSubgroup.closure {x | ∃ (a : Af F) (m : Fin n → E),
    (∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F) ∧ m ∈ M ∧
      x = fun i => a ⊗ₜ[F] m i}
def Kgp (Λ : Submodule (𝓞 E) (Fin n → E)) : Subgroup (HA (Af F) σ J) :=
  (stabAdd (hat F Λ)).comap (matHom (Af F) σ J)
def Kprin (Λ : Submodule (𝓞 E) (Fin n → E)) (g : ℕ) : Subgroup (HA (Af F) σ J) :=
  (unip (hat F Λ) (hat F (Ideal.span {(g : 𝓞 E)} • Λ))).comap (matHom (Af F) σ J)
variable (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E)
  (L : Submodule (𝓞 E) (Fin n → E)) (SG : Finset (HeightOneSpectrum (𝓞 E)))
  (ε : HeightOneSpectrum (𝓞 E) → Fin k → Fin n → E)
def KHpp : Subgroup (HA (Af F) σ J) :=
  Hgp (Af F) σ J P f ⊓ Kgp σ J (bigLat P f L) ⊓
    ⨅ w ∈ SG, ⨅ a : Fin k,
      (unip (hat F (flagLat (L ⊓ Wsp (σ : E →+* E) J P f) w.asIdeal (ε w) ((a : ℕ) + 1)))
        (hat F (flagLat (L ⊓ Wsp (σ : E →+* E) J P f) w.asIdeal (ε w) a))).comap (matHom (Af F) σ J)
def Kpp (g : ℕ) : Subgroup (HA (Af F) σ J) :=
  (Ngp (Af F) σ J P ⊓ Kgp σ J (bigLat P f L)) ⊔ KHpp σ J P f L SG ε ⊔ Kprin σ J (bigLat P f L) g
def KSpp (g : ℕ) : Subgroup (HA (Af F) σ J) := Sgp (Af F) σ J P ⊓ Kpp σ J P f L SG ε g
def ratDiag (A : Subgroup (HA (Ainf F) σ J)) (B : Subgroup (HA (Af F) σ J)) : Subgroup (A × B) :=
  ((Formalism.UG.bc (n := Fin n) (inclR (F := F) (E := E) (Ainf F))).prod
      (Formalism.UG.bc (n := Fin n) (inclR (F := F) (E := E) (Af F)))).range.comap
    (((matHom (Ainf F) σ J).comp A.subtype).prodMap ((matHom (Af F) σ J).comp B.subtype))
def intInf (A : Subgroup (HA (Ainf F) σ J)) (B K : Subgroup (HA (Af F) σ J)) : Subgroup A :=
  (ratDiag σ J A B ⊓ (K.subgroupOf B).comap (MonoidHom.snd A B)).map (MonoidHom.fst A B)
def columns (A : Subgroup (HA (Ainf F) σ J)) (B : Subgroup (HA (Af F) σ J)) (K : Subgroup B)
    (ψ : K →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ A V) :
    Submodule ℂ (B → V) where
  carrier := {φ | ∀ γ ∈ ratDiag σ J A B, ∀ (x : B) (κ : K),
    φ (γ.2 * x * (κ : B)) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π γ.1 (φ x)}
  zero_mem' := by intro γ _ x κ; simp
  add_mem' := by intro a b ha hb γ hγ x κ; simp [ha γ hγ x κ, hb γ hγ x κ]
  smul_mem' := by
    intro c a ha γ hγ x κ
    simp only [Pi.smul_apply, ha γ hγ x κ, map_smul]
    exact smul_comm _ _ _
end Levels
def cosetMass {G : Type} [Group G] (Γ K : Subgroup G) : ℝ≥0∞ :=
  ∑' c : Formalism.UG.ClassSet Γ K, (ENat.toENNReal (ENat.card (Formalism.UG.stabAt Γ K (Quotient.out c))))⁻¹
def volMul {G : Type} [Group G] [MeasurableSpace G] {A B : Subgroup G} (μ : Measure A)
    (ν : Measure B) (C : Set G) : ℝ≥0∞ :=
  (μ.prod ν) {p | (p.1 : G) * (p.2 : G) ∈ C}
def cZero (volN volH : ℝ≥0∞) (d : ℕ) : ℝ≥0∞ := volN * volH / d
def HidaSetting {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n r k : ℕ} (J : Matrix (Fin n) (Fin n) E) (T g₁ g₂ : ℕ)
    (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (SG : Finset (HeightOneSpectrum (𝓞 E)))
    (ε : HeightOneSpectrum (𝓞 E) → Fin k → Fin n → E) : Prop :=
  IsCMExt F E σ ∧ Algebra.Unramified (𝓞 F) (𝓞 E) ∧
  n = k + 2 * r + 1 ∧ IsHermND σ J ∧
  GlobalTheory.SgAlg.IsFrame (σ : E →+* E) J (T : E) P ∧ GlobalTheory.SgAlg.IsDual (σ : E →+* E) J P f ∧
  (∀ v ∈ Wsp (σ : E →+* E) J P f, v ≠ 0 → GlobalTheory.SgGlob.TotPos (GlobalTheory.SgAlg.form (σ : E →+* E) J v v)) ∧
  (L.FG ∧ ∀ v, v ∈ L ↔ v ∈ Wb (σ : E →+* E) J P f ∧
    ∀ w ∈ L, GlobalTheory.SgAlg.form (σ : E →+* E) J v w ∈ (algebraMap (𝓞 E) E).range) ∧
  GlobalTheory.SgGlob.PrimIn (Submodule.span (𝓞 E) {fun i => P i (Fin.last r)}) L ∧
  0 < T ∧ g₁.Prime ∧ g₂.Prime ∧ g₁ ≠ g₂ ∧ SplitsCompletely E g₁ ∧ SplitsCompletely E g₂ ∧
  T.Coprime (g₁ * g₂) ∧ 2 * k < g₁ ∧ 2 * k < g₂ ∧
  (∀ w ∈ SG, ((g₁ * g₂ : ℕ) : 𝓞 E) ∈ w.asIdeal) ∧
  (∀ v : HeightOneSpectrum (𝓞 F), ((g₁ * g₂ : ℕ) : 𝓞 F) ∈ v.asIdeal →
    ∃! w, w ∈ SG ∧ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal) ∧
  ∀ w ∈ SG, (∀ j, ε w j ∈ L ⊓ Wsp (σ : E →+* E) J P f) ∧
    L ⊓ Wsp (σ : E →+* E) J P f ≤ flagLat (L ⊓ Wsp (σ : E →+* E) J P f) w.asIdeal (ε w) k
def ColumnDimension : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n r k : ℕ) (J : Matrix (Fin n) (Fin n) E) (T g₁ g₂ : ℕ)
    (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (SG : Finset (HeightOneSpectrum (𝓞 E)))
    (ε : HeightOneSpectrum (𝓞 E) → Fin k → Fin n → E),
    HidaSetting σ J T g₁ g₂ P f L SG ε →
    let Hi := Hgp (Ainf F) σ J P f
    let Hf := Hgp (Af F) σ J P f
    let Ni := Ngp (Ainf F) σ J P
    let Nf := Ngp (Af F) σ J P
    let K := Kgp σ J (bigLat P f L)
    let HF : Subgroup Hf := (ratG (Af F) σ J).subgroupOf Hf
    let KH : Subgroup Hf := K.subgroupOf Hf
    let upperUnitriangularLevelSubgroup : Subgroup Hf := (KHpp σ J P f L SG ε).subgroupOf Hf
    ∀ (ψ : upperUnitriangularLevelSubgroup →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (π : Representation ℂ Hi V), π.IsIrreducible →
    let d : ℕ := Module.finrank ℂ (columns σ J Hi Hf upperUnitriangularLevelSubgroup ψ π)
    let dπ : ℕ := Module.finrank ℂ V
    (FiniteDimensional ℂ (columns σ J Hi Hf upperUnitriangularLevelSubgroup ψ π) ∧ Finite (Formalism.UG.ClassSet HF upperUnitriangularLevelSubgroup) ∧
      d = dπ * Nat.card (Formalism.UG.ClassSet HF upperUnitriangularLevelSubgroup)) ∧
    (d : ℝ≥0∞) = dπ * gammaOne SG k * cosetMass HF KH ∧
    (∀ B : Matrix (Fin n) (Fin (k + 1)) E, GlobalTheory.SgAlg.Free B →
      (∀ j, (fun i => B i j) ∈ Wb (σ : E →+* E) J P f) →
      cosetMass HF KH =
        GlobalTheory.SgGlob.massLz (σ : E →+* E) (GlobalTheory.SgAlg.pairM (σ : E →+* E) J B B) (T : E)) ∧
    ∀ (μHi : Measure Hi) (μHf : Measure Hf) (𝓕H : Set (Hi × Hf)),
      μHi.IsHaarMeasure → μHf.IsHaarMeasure →
      IsFundamentalDomain (ratDiag σ J Hi Hf) 𝓕H (μHi.prod μHf) →
      (μHi Set.univ ≠ 0 ∧ μHi Set.univ ≠ ⊤ ∧ μHf upperUnitriangularLevelSubgroup ≠ 0 ∧ μHf upperUnitriangularLevelSubgroup ≠ ⊤ ∧
        (d : ℝ≥0∞) = dπ * (μHi.prod μHf) 𝓕H / (μHi Set.univ * μHf upperUnitriangularLevelSubgroup)) ∧
      ∀ (μNi : Measure Ni) (μNf : Measure Nf) (𝓕N : Set (Ni × Nf)) (𝓓 : Set Ni),
        μNi.IsHaarMeasure → μNf.IsHaarMeasure →
        IsFundamentalDomain (ratDiag σ J Ni Nf) 𝓕N (μNi.prod μNf) →
        IsFundamentalDomain (intInf σ J Ni Nf K) 𝓓 μNi →
        (μHi.prod μHf) 𝓕H = 1 → (μNi.prod μNf) 𝓕N = 1 →
        μNi 𝓓 ≠ 0 ∧ μNi 𝓓 ≠ ⊤ ∧
        (cZero (μNi 𝓓) (μHi Set.univ) dπ)⁻¹ = dπ / (μNi 𝓓 * μHi Set.univ) ∧
        (dπ : ℝ≥0∞) / (μNi 𝓓 * μHi Set.univ) =
          d * volMul μNf μHf (KSpp σ J P f L SG ε (g₁ * g₂) : Set (HA (Af F) σ J))
example (E : Type) [Field E] [NumberField E] (k : ℕ) :
    gammaOne (∅ : Finset (HeightOneSpectrum (𝓞 E))) k = 1 := by simp [gammaOne]
end GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers


