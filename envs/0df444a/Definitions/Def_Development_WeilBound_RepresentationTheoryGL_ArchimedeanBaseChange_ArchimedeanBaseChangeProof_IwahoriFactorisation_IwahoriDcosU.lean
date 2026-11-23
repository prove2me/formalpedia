-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IwahoriFactorisation_IwahoriDcosU
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IwahoriFactorisation_IwahoriDcosU
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:36.666261+00:00
-- url     : https://prove2.me/theorems/355f8909-b323-4228-aa2a-495de70a20d0
-- title:
--   Iwahori Dcos U
-- statement:
--   Definitions and structural lemmas for Iwahori Dcos U, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/IwahoriFactorisation/IwahoriDcosU.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Polynomial
open scoped ENNReal
namespace PositivityTheory.Rg.Bc.ArchbcB.B
open PositivityTheory.Rg.Tf.Loc
noncomputable section
section Helpers
variable {n : ℕ} {k E : Type*} [Field k] [Field E] [Algebra k E]
def starσ (σ : E ≃ₐ[k] E) (M : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  (M.map σ).transpose
variable [ValuativeRel E]
def EntriesIn (ϖ : E) (m : ℕ) (M : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ i j, ValuativeRel.valuation E (M i j) ≤ ValuativeRel.valuation E ϖ ^ m
def IsUnitLift (σ : E ≃ₐ[k] E) (γ : unitaryGL σ (1 : GL (Fin n) E)) (c : GL (Fin n) E) : Prop :=
  c ∈ unitGL (n := Fin n) E ∧
    (∃ p : E[X], (∀ i, ValuativeRel.valuation E (p.coeff i) ≤ 1) ∧
      (c : Matrix (Fin n) (Fin n) E) = aeval ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p) ∧
    c * theta1 σ c = (γ : GL (Fin n) E)
def congSet (ϖ : E) (m : ℕ) : Set (GL (Fin n) E) :=
  {g | g ∈ unitGL (n := Fin n) E ∧ EntriesIn ϖ m ((g : Matrix (Fin n) (Fin n) E) - 1)}
def kmFn (σ : E ≃ₐ[k] E) (ϖ : E) (m : ℕ) : unitaryGL σ (1 : GL (Fin n) E) → ℂ :=
  Set.indicator {u | (u : GL (Fin n) E) ∈ congSet ϖ m} 1
def liftSet (σ : E ≃ₐ[k] E) (ϖ : E) (m : ℕ) : Set (GL (Fin n) E) :=
  {δ | δ ∈ unitGL (n := Fin n) E ∧
    EntriesIn ϖ m ((δ : Matrix (Fin n) (Fin n) E) - starσ σ (δ : Matrix (Fin n) (Fin n) E))}
def liftFn (σ : E ≃ₐ[k] E) (ϖ : E) (m : ℕ) : GL (Fin n) E → ℂ :=
  Set.indicator (liftSet σ ϖ m) 1
end Helpers
def B1 : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    Module.finrank k E = 2 → IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, σ ≠ 1 →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      (μE : Measure (GL (Fin n) E)) (μU : Measure (unitaryGL σ (1 : GL (Fin n) E))),
      μE.IsHaarMeasure → μU.IsHaarMeasure →
      μE (unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 →
      μU {u | (u : GL (Fin n) E) ∈ unitGL (n := Fin n) E} = 1 →
      (∀ (γ : unitaryGL σ (1 : GL (Fin n) E)) (c : GL (Fin n) E)
          (μc : Measure (twCent (theta1 σ) c))
          (μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ (1 : GL (Fin n) E))))),
          ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable →
          IsUnitLift σ γ c → μγ.IsHaarMeasure →
          Measure.map (fun x : twCent (theta1 σ) c => (x : GL (Fin n) E)) μc =
            Measure.map (fun t : Subgroup.centralizer ({γ} : Set (unitaryGL σ (1 : GL (Fin n) E))) =>
              ((t : unitaryGL σ (1 : GL (Fin n) E)) : GL (Fin n) E)) μγ →
          twOrbIntegralC (theta1 σ) μE c μc (unitFnC E) = orbIntegralC μU γ μγ (unitFnUC σ 1)) ∧
      (∀ (δ : GL (Fin n) E) (μδ : Measure (twCent (theta1 σ) δ)),
          ((normU σ 1 δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable →
          (¬ ∃ (γ : unitaryGL σ (1 : GL (Fin n) E)) (c : GL (Fin n) E),
              IsUnitLift σ γ c ∧ TwConjugate (theta1 σ) c δ) →
          twOrbIntegralC (theta1 σ) μE δ μδ (unitFnC E) = 0) ∧
      (∀ (γ : unitaryGL σ (1 : GL (Fin n) E))
          (μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ (1 : GL (Fin n) E))))),
          (∃ i, 1 < ValuativeRel.valuation E
              (((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.coeff i)) →
          orbIntegralC μU γ μγ (unitFnUC σ 1) = 0)
def B2 : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    Module.finrank k E = 2 → IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, σ ≠ 1 →
    ∀ ϖ : k, IsUniformiser (algebraMap k E ϖ) →
    ∀ m : ℕ, 1 ≤ m →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      (μE : Measure (GL (Fin n) E)) (μU : Measure (unitaryGL σ (1 : GL (Fin n) E))),
      μE.IsHaarMeasure → μU.IsHaarMeasure →
      μE (unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 →
      μU {u | (u : GL (Fin n) E) ∈ unitGL (n := Fin n) E} = 1 →
      (∀ (γ : unitaryGL σ (1 : GL (Fin n) E)) (c : GL (Fin n) E)
          (μc : Measure (twCent (theta1 σ) c))
          (μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ (1 : GL (Fin n) E))))),
          ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable →
          IsUnitLift σ γ c → μγ.IsHaarMeasure →
          Measure.map (fun x : twCent (theta1 σ) c => (x : GL (Fin n) E)) μc =
            Measure.map (fun t : Subgroup.centralizer ({γ} : Set (unitaryGL σ (1 : GL (Fin n) E))) =>
              ((t : unitaryGL σ (1 : GL (Fin n) E)) : GL (Fin n) E)) μγ →
          twOrbIntegralC (theta1 σ) μE c μc (liftFn σ (algebraMap k E ϖ) m) =
            orbIntegralC μU γ μγ (kmFn σ (algebraMap k E ϖ) m)) ∧
      (∀ (δ : GL (Fin n) E) (μδ : Measure (twCent (theta1 σ) δ)),
          ((normU σ 1 δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable →
          (¬ ∃ (γ : unitaryGL σ (1 : GL (Fin n) E)) (c : GL (Fin n) E),
              IsUnitLift σ γ c ∧ TwConjugate (theta1 σ) c δ) →
          twOrbIntegralC (theta1 σ) μE δ μδ (liftFn σ (algebraMap k E ϖ) m) = 0) ∧
      (∀ α : E, ValuativeRel.valuation E α ≤ 1 → ValuativeRel.valuation E (α - σ α) = 1 →
        ∀ δ : GL (Fin n) E, δ ∈ liftSet σ (algebraMap k E ϖ) m ↔
          ∃ h h' : Matrix (Fin n) (Fin n) E, starσ σ h = h ∧ starσ σ h' = h' ∧
            (∀ i j, ValuativeRel.valuation E (h i j) ≤ 1) ∧ ValuativeRel.valuation E h.det = 1 ∧
            EntriesIn (algebraMap k E ϖ) m h' ∧ (δ : Matrix (Fin n) (Fin n) E) = h + α • h')
section Split
variable {F : Type*} [Field F]
def thetaSplit {n : ℕ} : Monoid.End (GL (Fin n) F × GL (Fin n) F) where
  toFun p := (invTransposeGL p.2, invTransposeGL p.1)
  map_one' := Prod.ext (map_one _) (map_one _)
  map_mul' _ _ := Prod.ext (map_mul _ _ _) (map_mul _ _ _)
variable {a b : ℕ}
def blockDiag (A : GL (Fin a) F) (D : GL (Fin b) F) : GL (Fin a ⊕ Fin b) F :=
  ⟨Matrix.fromBlocks (A : Matrix (Fin a) (Fin a) F) 0 0 (D : Matrix (Fin b) (Fin b) F),
    Matrix.fromBlocks ((A⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) 0 0
      ((D⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F),
    by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩
def unipN (X : Matrix (Fin a) (Fin b) F) : GL (Fin a ⊕ Fin b) F :=
  ⟨Matrix.fromBlocks 1 X 0 1, Matrix.fromBlocks 1 (-X) 0 1,
    by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩
def adN (A : GL (Fin a) F) (D : GL (Fin b) F) :
    Matrix (Fin a) (Fin b) F →ₗ[F] Matrix (Fin a) (Fin b) F where
  toFun X := (A : Matrix (Fin a) (Fin a) F) * X * ((D⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]
def adNbar (A : GL (Fin a) F) (D : GL (Fin b) F) :
    Matrix (Fin b) (Fin a) F →ₗ[F] Matrix (Fin b) (Fin a) F where
  toFun Y := (D : Matrix (Fin b) (Fin b) F) * Y * ((A⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]
def discrGM (A : GL (Fin a) F) (D : GL (Fin b) F) : F :=
  LinearMap.det (LinearMap.id - adN A D) * LinearMap.det (LinearMap.id - adNbar A D)
def intSet (F : Type*) [Field F] [ValuativeRel F] : Set F := {y | ValuativeRel.valuation F y ≤ 1}
variable [ValuativeRel F] [MeasurableSpace F]
def modF (μF : Measure F) (x : F) : ℝ :=
  (μF ((fun y => x * y) '' intSet F) / μF (intSet F)).toReal
variable [TopologicalSpace F] [MeasurableSpace (GL (Fin a ⊕ Fin b) F)]
def constTerm (μF : Measure F) (μG : Measure (GL (Fin a ⊕ Fin b) F))
    (μN : Measure (Fin a → Fin b → F)) (f : GL (Fin a ⊕ Fin b) F → ℂ)
    (p : GL (Fin a) F × GL (Fin b) F) : ℂ :=
  (((modF μF ((p.1 : Matrix (Fin a) (Fin a) F).det)) ^ ((b : ℝ) / 2) *
      (modF μF ((p.2 : Matrix (Fin b) (Fin b) F).det)) ^ (-((a : ℝ) / 2)) : ℝ) : ℂ) *
    ∫ k, Set.indicator ((unitGL (n := Fin a ⊕ Fin b) F : Subgroup _) : Set (GL (Fin a ⊕ Fin b) F))
      (fun k => ∫ X, f (k⁻¹ * blockDiag p.1 p.2 * unipN (Matrix.of X) * k) ∂μN) k ∂μG
end Split
def B3 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (μF : Measure F), μF.IsAddHaarMeasure →
    (∀ (n : ℕ) [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
        (μ : Measure (GL (Fin n) F)), μ.IsHaarMeasure →
      ∀ (f₁ f₂ : GL (Fin n) F → ℂ), IsLocallyConstant f₁ → HasCompactSupport f₁ →
        IsLocallyConstant f₂ → HasCompactSupport f₂ →
      ∀ (δ : GL (Fin n) F × GL (Fin n) F) (μδ : Measure (twCent thetaSplit δ))
        (μγ : Measure (Subgroup.centralizer ({δ.1 * invTransposeGL δ.2} : Set (GL (Fin n) F)))),
        ((δ.1 * invTransposeGL δ.2 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).charpoly.Separable →
        μγ.IsHaarMeasure →
        Measure.map (fun x : twCent thetaSplit δ => (x : GL (Fin n) F × GL (Fin n) F).1) μδ =
          Measure.map (fun t : Subgroup.centralizer ({δ.1 * invTransposeGL δ.2} : Set (GL (Fin n) F)) =>
            (t : GL (Fin n) F)) μγ →
        twOrbIntegralC thetaSplit (μ.prod μ) δ μδ (fun p => f₁ p.1 * f₂ p.2) =
          orbIntegralC μ (δ.1 * invTransposeGL δ.2) μγ
            (fun y => ∫ h, f₁ h * f₂ (invTransposeGL (h⁻¹ * y)) ∂μ)) ∧
    (∀ (a b : ℕ) [MeasurableSpace (GL (Fin a ⊕ Fin b) F)] [BorelSpace (GL (Fin a ⊕ Fin b) F)]
        [MeasurableSpace (GL (Fin a) F)] [BorelSpace (GL (Fin a) F)]
        [MeasurableSpace (GL (Fin b) F)] [BorelSpace (GL (Fin b) F)]
        (μG : Measure (GL (Fin a ⊕ Fin b) F)) (μa : Measure (GL (Fin a) F))
        (μb : Measure (GL (Fin b) F)) (μN : Measure (Fin a → Fin b → F)),
        μG.IsHaarMeasure → μa.IsHaarMeasure → μb.IsHaarMeasure → μN.IsAddHaarMeasure →
        μG (unitGL (n := Fin a ⊕ Fin b) F : Set (GL (Fin a ⊕ Fin b) F)) = 1 →
        μa (unitGL (n := Fin a) F : Set (GL (Fin a) F)) = 1 →
        μb (unitGL (n := Fin b) F : Set (GL (Fin b) F)) = 1 →
        μN {X | ∀ i j, ValuativeRel.valuation F (X i j) ≤ 1} = 1 →
      ∀ (f : GL (Fin a ⊕ Fin b) F → ℂ), IsLocallyConstant f → HasCompactSupport f →
      ∀ (A : GL (Fin a) F) (D : GL (Fin b) F)
        (μγG : Measure (Subgroup.centralizer ({blockDiag A D} : Set (GL (Fin a ⊕ Fin b) F))))
        (μγM : Measure (Subgroup.centralizer ({(A, D)} : Set (GL (Fin a) F × GL (Fin b) F)))),
        ((blockDiag A D : GL (Fin a ⊕ Fin b) F) :
          Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) F).charpoly.Separable →
        μγM.IsHaarMeasure →
        Measure.map (fun t : Subgroup.centralizer ({(A, D)} : Set (GL (Fin a) F × GL (Fin b) F)) =>
            blockDiag (t : GL (Fin a) F × GL (Fin b) F).1 (t : GL (Fin a) F × GL (Fin b) F).2) μγM =
          Measure.map (fun t : Subgroup.centralizer ({blockDiag A D} : Set (GL (Fin a ⊕ Fin b) F)) =>
            (t : GL (Fin a ⊕ Fin b) F)) μγG →
        orbIntegralC μG (blockDiag A D) μγG f =
          (((modF μF (discrGM A D)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            orbIntegralC (μa.prod μb) (A, D) μγM (constTerm μF μG μN f))
def torusO (F : Type*) [Field F] [ValuativeRel F] {m : ℕ} : Set (GL (Fin m) F) :=
  {t | t ∈ unitGL (n := Fin m) F ∧ ∀ i j : Fin m, i ≠ j → (t : Matrix (Fin m) (Fin m) F) i j = 0}
def w0GL (E : Type*) [Field E] (n : ℕ) : GL (Fin n) E :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Fin.revPerm : Equiv.Perm (Fin n)).permMatrix E) (by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;>
      simp [h])
def reGL (F : Type*) [Field F] (a b : ℕ) : GL (Fin a ⊕ Fin b) F →* GL (Fin (a + b)) F :=
  Units.map (Matrix.reindexAlgEquiv F F finSumFinEquiv).toMonoidHom
def iwahoriDcosU {k E : Type*} [Field k] [Field E] [Algebra k E] [ValuativeRel E] {n : ℕ}
    (σ : E ≃ₐ[k] E) (y : unitaryGL σ (w0GL E n)) : Set (unitaryGL σ (w0GL E n)) :=
  {u | ∃ i₁ : unitaryGL σ (w0GL E n), (i₁ : GL (Fin n) E) ∈ iwahori (m := n) E ∧
    ∃ i₂ : unitaryGL σ (w0GL E n), (i₂ : GL (Fin n) E) ∈ iwahori (m := n) E ∧ u = i₁ * y * i₂}
def B4 : Prop :=
  (∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    Module.finrank k E = 2 → IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, σ ≠ 1 →
    ∀ (ϖ : kˣ), IsUniformiser (algebraMap k E ϖ) →
    ∀ (n : ℕ) (μ : Fin n → ℤ), StrictlyDominant μ → (∀ i, μ (Fin.rev i) = -μ i) →
    ∀ y : unitaryGL σ (w0GL E n),
      (y : GL (Fin n) E) = diagPow (Units.map (algebraMap k E).toMonoidHom ϖ) μ →
      (∀ u ∈ iwahoriDcosU σ y, ∃ i : unitaryGL σ (w0GL E n), (i : GL (Fin n) E) ∈ iwahori (m := n) E ∧
        ∃ t : unitaryGL σ (w0GL E n), (t : GL (Fin n) E) ∈ torusO E (m := n) ∧ u = i⁻¹ * (y * t) * i) ∧
      (∀ [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
          (μU : Measure (unitaryGL σ (w0GL E n))), μU.IsHaarMeasure →
          μU {u | (u : GL (Fin n) E) ∈ iwahori (m := n) E} = 1 →
        ∀ t : unitaryGL σ (w0GL E n), (t : GL (Fin n) E) ∈ torusO E (m := n) →
        ∀ μγ : Measure (Subgroup.centralizer ({y * t} : Set (unitaryGL σ (w0GL E n)))),
          μγ.IsHaarMeasure → μγ {s | ((s : unitaryGL σ (w0GL E n)) : GL (Fin n) E) ∈ torusO E (m := n)} = 1 →
          orbIntegralC μU (y * t) μγ (Set.indicator (iwahoriDcosU σ y) 1) = 1)) ∧
  (∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (μF : Measure F), μF.IsAddHaarMeasure →
    ∀ (a b : ℕ) (ϖ : Fˣ) (lam : Fin (a + b) → ℤ), IsUniformiser (ϖ : F) → StrictlyDominant lam →
    ∀ [MeasurableSpace (GL (Fin (a + b)) F)] [BorelSpace (GL (Fin (a + b)) F)]
      [MeasurableSpace (GL (Fin a) F)] [BorelSpace (GL (Fin a) F)]
      [MeasurableSpace (GL (Fin b) F)] [BorelSpace (GL (Fin b) F)]
      (μG : Measure (GL (Fin (a + b)) F)) (μa : Measure (GL (Fin a) F)) (μb : Measure (GL (Fin b) F)),
      μG.IsHaarMeasure → μa.IsHaarMeasure → μb.IsHaarMeasure →
      μG (iwahori (m := a + b) F) = 1 → μa (iwahori (m := a) F) = 1 → μb (iwahori (m := b) F) = 1 →
    ∀ (A : GL (Fin a) F) (D : GL (Fin b) F)
      (μγG : Measure (Subgroup.centralizer ({reGL F a b (blockDiag A D)} : Set (GL (Fin (a + b)) F))))
      (μγM : Measure (Subgroup.centralizer ({(A, D)} : Set (GL (Fin a) F × GL (Fin b) F)))),
      ((reGL F a b (blockDiag A D) : GL (Fin (a + b)) F) :
        Matrix (Fin (a + b)) (Fin (a + b)) F).charpoly.Separable →
      μγM.IsHaarMeasure →
      Measure.map (fun t : Subgroup.centralizer ({(A, D)} : Set (GL (Fin a) F × GL (Fin b) F)) =>
          reGL F a b (blockDiag (t : GL (Fin a) F × GL (Fin b) F).1 (t : GL (Fin a) F × GL (Fin b) F).2))
          μγM =
        Measure.map (fun t : Subgroup.centralizer ({reGL F a b (blockDiag A D)} : Set (GL (Fin (a + b)) F)) =>
          (t : GL (Fin (a + b)) F)) μγG →
      (((modF μF (discrGM A D)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          orbIntegralC μG (reGL F a b (blockDiag A D)) μγG (iwahoriFn F (diagPow ϖ lam)) =
        ∑ S : Finset (Fin (a + b)),
          if h : S.card = a then
            (((modF μF (ϖ : F)) ^ (-((∑ i ∈ S, ∑ j ∈ Sᶜ, |lam i - lam j| : ℤ) : ℝ) / 2) : ℝ) : ℂ) *
              orbIntegralC (μa.prod μb) (A, D) μγM (fun p =>
                iwahoriFn F (diagPow ϖ (lam ∘ S.orderEmbOfFin h)) p.1 *
                  iwahoriFn F (diagPow ϖ (lam ∘ Sᶜ.orderEmbOfFin
                    (by rw [Finset.card_compl, Fintype.card_fin, h, Nat.add_sub_cancel_left]))) p.2)
          else 0)
end
end PositivityTheory.Rg.Bc.ArchbcB.B


