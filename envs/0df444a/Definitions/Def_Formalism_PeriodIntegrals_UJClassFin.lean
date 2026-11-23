-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UJClassFin
-- name    : Formalism_PeriodIntegrals_UJClassFin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:38.869748+00:00
-- url     : https://prove2.me/theorems/963e3fe0-263e-40d7-a8c1-e4b4c1231794
-- title:
--   UJClass Fin
-- statement:
--   Definitions and structural lemmas for UJClass Fin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UJClassFin.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
namespace PI.UJClassFin
section Group
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
def cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ
theorem cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]
theorem cT_one (σ : A →+* A) : cT σ (1 : Matrix n n A) = 1 := by
  unfold cT
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
def UJ (σ : A →+* A) (J : Matrix n n A) : Subgroup (GL n A) where
  carrier := {g | cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J}
  one_mem' := by simp [cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc cT σ ((a : Matrix n n A) * (b : Matrix n n A)) * J * ((a : Matrix n n A) * (b : Matrix n n A))
        = cT σ (b : Matrix n n A) * (cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc cT σ ((g⁻¹ : GL n A) : Matrix n n A) * J * ((g⁻¹ : GL n A) : Matrix n n A)
        = cT σ ((g⁻¹ : GL n A) : Matrix n n A) * (cT σ (g : Matrix n n A) * J * (g : Matrix n n A))
            * ((g⁻¹ : GL n A) : Matrix n n A) := by rw [hg]
      _ = cT σ ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) * J
            * ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]
def bc {B : Type} [CommRing B] (φ : A →+* B) : GL n A →* GL n B :=
  Units.map (RingHom.mapMatrix φ).toMonoidHom
end Group
def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)
def HasSignature {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n ℂ) (p q : ℕ) : Prop :=
  ∃ e : n ≃ Fin p ⊕ Fin q, ∃ P : GL (Fin p ⊕ Fin q) ℂ,
    cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * J.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q
section Adeles
variable (F : Type) [Field F] [NumberField F]
abbrev AF := AdeleRing (𝓞 F) F
abbrev Ainf := InfiniteAdeleRing F
abbrev Af := FiniteAdeleRing (𝓞 F) F
abbrev Fv (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F
def sndA : AF F →ₐ[F] Af F := AlgHom.snd F (Ainf F) (Af F)
def evalV (v : HeightOneSpectrum (𝓞 F)) : Af F →ₐ[F] Fv F v where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
end Adeles
section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
def sigR (σ : E →ₐ[F] E) : R ⊗[F] E →+* R ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom
def inclR : E →+* R ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom
def JR {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  J.map (inclR R)
def HR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Subgroup (GL (Fin M) (R ⊗[F] E)) :=
  UJ (sigR R σ) (JR R J)
def HFin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Subgroup (GL (Fin M) (R ⊗[F] E)) :=
  (UJ (σ : E →+* E) J).map (bc (inclR R))
def HFinIn (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HR R σ J) :=
  (HFin R σ J).subgroupOf (HR R σ J)
def HA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Type := HR R σ J
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
instance : Group (HA R σ J) := inferInstanceAs (Group (HR R σ J))
def HA.mat (h : HA R σ J) : GL (Fin M) (R ⊗[F] E) := let h' : HR R σ J := h; h'.1
end Alg
section Vol
def intAf (F : Type) [Field F] [NumberField F] : Set (Af F) :=
  {a | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v a ∈ v.adicCompletionIntegers F}
def latHat (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Set (Fin M → E)) : AddSubgroup (Fin M → Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x ∈ L, y = fun i => a ⊗ₜ[F] x i}
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
def finMat (h : HA (AF F) σ J) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E) :=
  ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).map
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))
theorem mapAlg_mul {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) {n : ℕ} (X Y : Matrix (Fin n) (Fin n) A) : (X * Y).map φ = X.map φ * Y.map φ :=
  Matrix.map_mul (f := φ.toRingHom)
theorem mapAlg_one {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) {n : ℕ} : (1 : Matrix (Fin n) (Fin n) A).map φ = 1 :=
  Matrix.map_one _ (map_zero φ) (map_one φ)
theorem HA_mat_mul (h h' : HA (AF F) σ J) :
    HA.mat (AF F) σ J (h * h') = HA.mat (AF F) σ J h * HA.mat (AF F) σ J h' :=
  rfl
theorem HA_mat_one : HA.mat (AF F) σ J 1 = 1 := rfl
theorem finMat_mul (h h' : HA (AF F) σ J) : finMat σ J (h * h') = finMat σ J h * finMat σ J h' := by
  unfold finMat
  rw [HA_mat_mul, Units.val_mul]
  exact mapAlg_mul _ _ _
theorem finMat_one : finMat σ J (1 : HA (AF F) σ J) = 1 := by
  unfold finMat
  rw [HA_mat_one, Units.val_one]
  exact mapAlg_one _
def SFin (L : Set (Fin M → E)) : Subgroup (HA (AF F) σ J) where
  carrier := {h | ∀ y, y ∈ latHat F E L ↔ (finMat σ J h).mulVec y ∈ latHat F E L}
  mul_mem' := by
    intro h h' hh hh' y
    rw [finMat_mul, ← Matrix.mulVec_mulVec, hh' y]
    exact hh _
  one_mem' := by intro y; rw [finMat_one, Matrix.one_mulVec]
  inv_mem' := by
    intro h hh y
    have e : (finMat σ J h).mulVec ((finMat σ J h⁻¹).mulVec y) = y := by
      rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_inv_cancel, finMat_one, Matrix.one_mulVec]
    have := hh ((finMat σ J h⁻¹).mulVec y)
    rw [e] at this
    exact this.symm
abbrev GamG : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
end Vol
def UJClassFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)),
    (∀ a, σ a = star a) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, HasSignature (J.map τ) M 0) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((c : F) • x i)) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ L) →
    ∃ (n : ℕ) (g : Fin n → HA (AF F) σ J),
      (∀ x, ∃ i, ∃ γ : GamG σ J, ∃ k : SFin σ J L, x = (γ : HA (AF F) σ J) * g i * k) ∧
      (∀ i j (γ γ' : GamG σ J) (k k' : SFin σ J L),
        (γ : HA (AF F) σ J) * g i * k = (γ' : HA (AF F) σ J) * g j * k' → i = j)
end PI.UJClassFin


