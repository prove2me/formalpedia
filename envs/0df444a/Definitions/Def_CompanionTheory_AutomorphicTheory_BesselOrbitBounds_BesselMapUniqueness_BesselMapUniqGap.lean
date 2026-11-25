-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
-- name    : CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:02:15.467975+00:00
-- url     : https://prove2.me/theorems/1ee7fce2-8990-4326-9477-c2e439cc5599
-- title:
--   Bessel Map Uniq Gap
-- statement:
--   Definitions and structural lemmas for Bessel Map Uniq Gap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/BesselMapUniqGap.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
namespace CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section general
variable {n : ℕ}
def Lie (Hm X : Mat n) : Prop := Xᴴ * Hm + Hm * X = 0
def LieWd (Hm : Mat n) (W : List (Mat n)) : Prop := ∀ X ∈ W, Lie Hm X
structure URep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Hm : Mat n) (σ : Mat n → (H →L[ℂ] H)) :
    Prop where
  sq : Hm * Hm = 1
  grp : PI.IsMatGroup (UH Hm)
  rep : RepOn (UH Hm) σ
  iso : ∀ g ∈ UH Hm, ∀ v, ‖σ g v‖ = ‖v‖
structure CWLin {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Hm : Mat n) (σ : Mat n → (H →L[ℂ] H)) (B : H → V) : Prop where
  add : ∀ x, IsSm (UH Hm) σ x → ∀ y, IsSm (UH Hm) σ y → B (x + y) = B x + B y
  smul : ∀ (a : ℂ) x, IsSm (UH Hm) σ x → B (a • x) = a • B x
  bd : ∃ (C : ℝ) (Ws : List (List (Mat n))), (∀ W ∈ Ws, LieWd Hm W) ∧
    ∀ v, IsSm (UH Hm) σ v → ‖B v‖ ≤ C * (Ws.map fun W => ‖dsW σ W v‖).sum
def prodEx {d : ℕ} (X : Fin d → Mat n) (t : Fin d → ℝ) : Mat n := (List.ofFn fun j => ex (X j) (t j)).prod
def Spans (Hm : Mat n) {d e : ℕ} (X : Fin d → Mat n) (Q : Fin e → Mat n) : Prop :=
  ∀ Y, Lie Hm Y → ∃ (a : Fin d → ℝ) (b : Fin e → ℝ), Y = ∑ j, (a j : ℂ) • X j + ∑ i, (b i : ℂ) • Q i
structure Chart (Hm : Mat n) {d e : ℕ} (Q : Fin e → Mat n) (s : (Fin d → ℝ) → Mat n) (U : Set (Fin d → ℝ)) : Prop where
  isOpen : IsOpen U
  zero : (0 : Fin d → ℝ) ∈ U
  smooth : ContDiff ℝ ∞ s
  mem : ∀ t, s t ∈ UH Hm
  lieQ : ∀ i, Lie Hm (Q i)
  flow : ∃ Z : Fin d → (Fin d → ℝ) → Mat n, (∀ j t, Lie Hm (Z j t)) ∧
    (∀ j t (τ : ℝ), s (t + τ • (Pi.single j 1 : Fin d → ℝ)) = s t * ex (Z j t) τ) ∧
    ∀ Y, Lie Hm Y → ∃ (a : Fin d → (Fin d → ℝ) → ℝ) (b : Fin e → (Fin d → ℝ) → ℝ),
      (∀ j, ContDiffOn ℝ ∞ (a j) U) ∧ (∀ i, ContDiffOn ℝ ∞ (b i) U) ∧
      ∀ t ∈ U, (s t)⁻¹ * Y * s t = ∑ j, (a j t : ℂ) • Z j t + ∑ i, (b i t : ℂ) • Q i
def QBd {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V]
    (Hm : Mat n) (σ : Mat n → (H →L[ℂ] H)) (B : H → V) {e : ℕ} (Q : Fin e → Mat n) (C : ℝ) (m : ℕ) : Prop :=
  ∀ v, IsSm (UH Hm) σ v → ∀ R : ℝ, (∀ P : List (Fin e), P.length ≤ m → ‖dsW σ (P.map Q) v‖ ≤ R) → ‖B v‖ ≤ C * R
def cutI {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat n → (H →L[ℂ] H))
    (μ : Measure (PI.MtM n)) (w : H) (R : ℝ) (ρ : Mat n → ℝ) (v : H) : H :=
  ∫ y : PI.MtM n, ((ρ (R⁻¹ • Matrix.of y) : ℂ) * conj ⟪v, σ (Matrix.of y) w⟫_ℂ) • σ (Matrix.of y) w ∂μ
end general
def DsLin : Prop :=
  ∀ (n : ℕ) (Hm : Mat n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)), URep Hm σ →
    ∀ u, IsSm (UH Hm) σ u → ∃ Λ : Mat n →L[ℝ] H, ∀ X, Lie Hm X → ds σ X u = Λ X
def DsAd : Prop :=
  ∀ (n : ℕ) (Hm : Mat n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)), URep Hm σ →
    ∀ y ∈ UH Hm, ∀ W, LieWd Hm W → LieWd Hm (W.map fun X => y⁻¹ * X * y) ∧
      ∀ u, IsSm (UH Hm) σ u → dsW σ W (σ y u) = σ y (dsW σ (W.map fun X => y⁻¹ * X * y) u)
def DsDer : Prop :=
  ∀ (n : ℕ) (Hm : Mat n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)), URep Hm σ →
    ∀ W, LieWd Hm W → ∀ p ∈ UH Hm, ∀ X, Lie Hm X → ∀ x, IsSm (UH Hm) σ x →
      HasDerivAt (fun τ : ℝ => dsW σ W (σ (p * ex X τ) x)) (dsW σ W (σ p (ds σ X x))) 0
def WordBd : Prop :=
  ∀ (n : ℕ) (Hm : Mat n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)), URep Hm σ →
    ∀ w, IsSm (UH Hm) σ w → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ W, LieWd Hm W → W.length ≤ m →
      ‖dsW σ W w‖ ≤ C * (W.map fun X => ‖X‖).prod
def Factor : Prop :=
  ∀ (n : ℕ) (Hm : Mat n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)), URep Hm σ →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (B : H → V), CWLin Hm σ B →
    ∃ (N : ℕ) (W : Fin N → List (Mat n)) (β : Fin N → (H →L[ℂ] V)), (∀ i, LieWd Hm (W i)) ∧
      ∀ v, IsSm (UH Hm) σ v → B v = ∑ i, β i (dsW σ (W i) v)
def Reduce : Prop :=
  ∀ (n : ℕ) (Hm : Mat n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)), URep Hm σ →
    ∀ (d e : ℕ) (Q : Fin e → Mat n) (s : (Fin d → ℝ) → Mat n) (U : Set (Fin d → ℝ)), Chart Hm Q s U →
    ∀ W, LieWd Hm W → ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, IsSm (UH Hm) σ u → ∀ R : ℝ,
      (∀ P : List (Fin e), P.length ≤ W.length → ‖dsW σ (P.map Q) u‖ ≤ R) →
      ‖∫ t, (φ t : ℂ) • dsW σ W (σ (s t) u)‖ ≤ C * R
def ChartExists : Prop :=
  ∀ (n : ℕ) (Hm : Mat n), Hm * Hm = 1 → ∀ (d e : ℕ) (X : Fin d → Mat n) (Q : Fin e → Mat n),
    (∀ j, Lie Hm (X j)) → (∀ i, Lie Hm (Q i)) → Spans Hm X Q → ∃ U, Chart Hm Q (prodEx X) U
def QBound : Prop :=
  ∀ (n : ℕ) (Hm : Mat n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)), URep Hm σ →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (B : H → V), CWLin Hm σ B →
    ∀ (d e : ℕ) (X : Fin d → Mat n) (Q : Fin e → Mat n), (∀ j, Lie Hm (X j)) → (∀ i, Lie Hm (Q i)) → Spans Hm X Q →
    ∀ χ : Fin d → ℝ → (V →L[ℂ] V), (∀ j, Continuous (χ j)) → (∀ j, χ j 0 = 1) →
      (∀ j t v, IsSm (UH Hm) σ v → B (σ (ex (X j) t) v) = χ j t (B v)) →
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ QBd Hm σ B Q C m
def AbsBound : Prop :=
  ∀ (n : ℕ) (Hm : Mat n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)), URep Hm σ →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (B : H → V), CWLin Hm σ B →
    ∀ (e : ℕ) (Q : Fin e → Mat n), (∀ i, Lie Hm (Q i)) → ∀ (C : ℝ) (m : ℕ), 0 ≤ C → QBd Hm σ B Q C m →
    ∀ (C₀ : ℝ) (c : ℕ) (w : H), IsSm (UH Hm) σ w → ∃ K : ℝ, ∀ g ∈ UH Hm, ∀ M : ℝ, 1 ≤ M →
      (∀ i, ‖g⁻¹ * Q i * g‖ ≤ C₀ * M ^ c) →
      (M = 1 ∨ ∃ (Y : Mat n) (lam : ℝ), Lie Hm Y ∧ ‖Y‖ ≤ C₀ ∧ M ≤ |lam| ∧ ∀ (τ : ℝ) (u : H), IsSm (UH Hm) σ u →
        B (σ (g * ex Y τ) u) = Complex.exp (Complex.I * (lam * τ : ℝ)) • B (σ g u)) →
      ‖B (σ g w)‖ ≤ K
def CutDer : Prop :=
  ∀ (n : ℕ) (Hm : Mat n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)), URep Hm σ →
    ∀ μ : Measure (PI.MtM n), PI.IsHaarOnM (UH Hm) μ → ∀ w, IsSm (UH Hm) σ w → ∀ R : ℝ, 0 < R →
    ∀ ρ : Mat n → ℝ, ContDiff ℝ ∞ ρ → HasCompactSupport ρ → ∀ v, IsSm (UH Hm) σ v →
      IsSm (UH Hm) σ (cutI σ μ w R ρ v) ∧
      ∀ X, Lie Hm X → ds σ X (cutI σ μ w R ρ v) = cutI σ μ w R (Lx X ρ) v + cutI σ μ w R ρ (ds σ X v)
def CutLim : Prop :=
  ∀ (n : ℕ) (Hm : Mat n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)), URep Hm σ →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (B : H → V), CWLin Hm σ B →
    ∀ μ : Measure (PI.MtM n), PI.IsHaarOnM (UH Hm) μ → ∀ w, IsSm (UH Hm) σ w →
    (∀ v, IsSm (UH Hm) σ v → Integrable (fun y : PI.MtM n => ⟪v, σ (Matrix.of y) w⟫_ℂ) μ) →
    ∀ κ : ℂ, (∀ v, IsSm (UH Hm) σ v →
      ∫ y : PI.MtM n, conj ⟪v, σ (Matrix.of y) w⟫_ℂ • σ (Matrix.of y) w ∂μ = κ • v) →
    (∃ K : ℝ, ∀ g ∈ UH Hm, ‖B (σ g w)‖ ≤ K) →
    ∀ v, IsSm (UH Hm) σ v → κ • B v = ∫ y : PI.MtM n, conj ⟪v, σ (Matrix.of y) w⟫_ℂ • B (σ (Matrix.of y) w) ∂μ
section geom
def outer (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := i.val ≤ r ∨ r + k ≤ i.val
instance (k r : ℕ) (i : Fin (2 * r + k + 1)) : Decidable (outer k r i) := by unfold outer; infer_instance
def Hq (k r : ℕ) : Mat (2 * r + k + 1) := fun i j =>
  if outer k r i then (if i.val + j.val = 2 * r + k then 1 else 0) else if i = j then 1 else 0
def up (k r : ℕ) (i j : Fin (2 * r + k + 1)) : Prop := i < j ∧ (outer k r i ∨ outer k r j)
def nxt (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val + 1, by omega⟩
def IsTor (k r : ℕ) (d : Fin (2 * r + k + 1) → ℝ) : Prop :=
  (∀ i, 0 < d i) ∧ (∀ i j, outer k r i → i.val + j.val = 2 * r + k → d i * d j = 1) ∧
    (∀ i, ¬ outer k r i → d i = 1) ∧ d (wI k r 0) ≤ 1
def dg {m : ℕ} (d : Fin m → ℝ) : Mat m := Matrix.diagonal fun i => (d i : ℂ)
def IsAdapt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Γ : Mat (2 * r + k + 1)) : Prop :=
  Γᴴ * Hpk k r * Γ = Hq k r ∧
    (∀ a : Fin r, Γ *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ Γ *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    ∃ ρ : ℝ, 0 < ρ ∧ z = (ρ : ℂ) • (Γ *ᵥ (bvec (wI k r 0) - bvec (wI k r (Fin.last k))))
def Nq (k r : ℕ) : Set (Mat (2 * r + k + 1)) :=
  {g | g ∈ UH (Hq k r) ∧
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → g i (eI k r a) = if i = eI k r a then 1 else 0) ∧
    (∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val → g i j = if i = j then 1 else 0)}
def Wbq (k r : ℕ) : Set (Mat (2 * r + k + 1)) :=
  {g | g ∈ UH (Hq k r) ∧
    ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}
def InUw (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mat (2 * r + k + 1)) : Prop :=
  Lie (Hpk k r) X ∧ (∀ a : Fin r, X *ᵥ bvec (eI k r a) = 0 ∧ X *ᵥ bvec (esI k r a) = 0) ∧ X *ᵥ z = 0
def InN (k r : ℕ) (X : Mat (2 * r + k + 1)) : Prop :=
  Lie (Hpk k r) X ∧ (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → X i (eI k r a) = 0) ∧
    ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val → X i j = 0
def InQ (k r : ℕ) (Γ X : Mat (2 * r + k + 1)) : Prop :=
  Lie (Hpk k r) X ∧ ∀ i j, up k r i j → (Γ⁻¹ * X * Γ) i j = 0
end geom
def AdaptExists : Prop :=
  ∀ (k r : ℕ), 1 ≤ k → (∃ Γ₀ : Mat (2 * r + k + 1), Γ₀ᴴ * Γ₀ = 1 ∧ Γ₀ᴴ * Hpk k r * Γ₀ = Hq k r) ∧
    ∀ z : Fin (2 * r + k + 1) → ℂ, inWb k r z → 0 < Tz k r z → ∃ Γ, IsAdapt k r z Γ
def IwaQ : Prop :=
  ∀ (k r : ℕ), 1 ≤ k → ∀ x ∈ UH (Hq k r), ∃ s ∈ UH (Hq k r), ∃ κ ∈ UH (Hq k r),
    s.BlockTriangular id ∧ κᴴ * κ = 1 ∧ x = s * κ
def LeviQ : Prop :=
  ∀ (k r : ℕ), 1 ≤ k → ∀ s ∈ UH (Hq k r), s.BlockTriangular id →
    ∃ m ∈ Nq k r, ∃ t : Fin (2 * r + k + 1) → ℝ, ∃ μ ∈ Wbq k r, ∃ κ ∈ UH (Hq k r),
      IsTor k r t ∧ t (wI k r 0) = 1 ∧ κᴴ * κ = 1 ∧ s = m * dg t * μ * κ
def CartanQ : Prop :=
  ∀ (k r : ℕ), 1 ≤ k → ∀ μ ∈ Wbq k r, ∃ h ∈ Wbq k r, ∃ t : Fin (2 * r + k + 1) → ℝ, ∃ κ ∈ UH (Hq k r),
    h *ᵥ (bvec (wI k r 0) - bvec (wI k r (Fin.last k))) = bvec (wI k r 0) - bvec (wI k r (Fin.last k)) ∧
      IsTor k r t ∧ (∀ a : Fin r, t (eI k r a) = 1) ∧ κᴴ * κ = 1 ∧ μ = h * dg t * κ
def Decomp : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Γ : Mat (2 * r + k + 1)), 1 ≤ k → inWb k r z → IsAdapt k r z Γ →
    ∀ g ∈ UH (Hpk k r), ∃ h ∈ UWset k r z, ∃ m ∈ Nset k r, ∃ (d : Fin (2 * r + k + 1) → ℝ) (R : Mat (2 * r + k + 1)),
      IsTor k r d ∧ Rᴴ * R = 1 ∧ Γ * dg d * R ∈ UH (Hpk k r) ∧ g = h * m * (Γ * dg d * R)
def TorBound : Prop :=
  ∀ (k r : ℕ) (d : Fin (2 * r + k + 1) → ℝ) (R A : Mat (2 * r + k + 1)) (M : ℝ), 1 ≤ k → IsTor k r d → Rᴴ * R = 1 →
    1 ≤ M → (∀ a : Fin r, d (eI k r a) ≤ M * d (nxt k r a)) → (∀ i j, up k r i j → A i j = 0) →
    ‖(dg d * R)⁻¹ * A * (dg d * R)‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * ‖A‖ * M ^ (2 * r + k + 1)
def SpanG : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Γ : Mat (2 * r + k + 1)), 1 ≤ k → IsAdapt k r z Γ →
    ∀ Y, Lie (Hpk k r) Y → ∃ Y₁ Y₂ Y₃, InUw k r z Y₁ ∧ InN k r Y₂ ∧ InQ k r Γ Y₃ ∧ Y = Y₁ + Y₂ + Y₃
def ExpMem : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mat (2 * r + k + 1)) (t : ℝ),
    (InUw k r z X → ex X t ∈ UWset k r z) ∧ (InN k r X → ex X t ∈ Nset k r)
def RootVec : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Γ : Mat (2 * r + k + 1)) (c : Fin r → ℂ), 1 ≤ k → IsAdapt k r z Γ →
    (∀ a, c a ≠ 0) → ∃ C₀ : ℝ, ∀ (a : Fin r) (d : Fin (2 * r + k + 1) → ℝ) (R : Mat (2 * r + k + 1)),
      IsTor k r d → Rᴴ * R = 1 → Γ * dg d * R ∈ UH (Hpk k r) →
      ∃ Y, Lie (Hpk k r) Y ∧ ‖Y‖ ≤ C₀ ∧ ∀ τ : ℝ,
        Γ * dg d * R * ex Y τ * (Γ * dg d * R)⁻¹ ∈ Nset k r ∧
        PI.BesselMapUniq.psiGen k r z c (Γ * dg d * R * ex Y τ * (Γ * dg d * R)⁻¹) =
          Complex.exp (Complex.I * (d (eI k r a) / d (nxt k r a) * τ : ℝ))
def TorConj : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ), inWb k r z → (∀ a, c a ≠ 0) →
    ∃ τ ∈ UH (Hpk k r), (∀ h ∈ UWset k r z, τ * h = h * τ) ∧
      ∀ m ∈ Nset k r, τ * m * τ⁻¹ ∈ Nset k r ∧
        PI.BesselMapUniq.psiGen k r z c (τ * m * τ⁻¹) = psi k r z cStd m
def Bounded : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat (2 * r + k + 1) → (H →L[ℂ] H)), URep (Hpk k r) σ → 1 ≤ k →
    ∀ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ), inWb k r z → 0 < Tz k r z → (∀ a, c a ≠ 0) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
      (π : Mat (2 * r + k + 1) → (V →L[ℂ] V)), π 1 = 1 → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) →
      ContinuousOn π (UWset k r z) →
    ∀ B : H → V, CWLin (Hpk k r) σ B →
      (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, ∀ v, IsSm (UH (Hpk k r)) σ v →
        B (σ (h * m) v) = PI.BesselMapUniq.psiGen k r z c m • π h (B v)) →
      ∀ w, IsSm (UH (Hpk k r)) σ w → ∃ K : ℝ, ∀ g ∈ UH (Hpk k r), ‖B (σ g w)‖ ≤ K
def BesselMapUniqGap : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat (2 * r + k + 1) → (H →L[ℂ] H))
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] (π : Mat (2 * r + k + 1) → (Wp →L[ℂ] Wp)),
    1 ≤ k → GapAtLeast ε lam h → 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h →
    IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → inWb k r z → 0 < Tz k r z →
    (∀ a, c a ≠ 0) → PI.UpqRep.IsHCTypeW k r z u π →
    ∀ B₁ B₂ : H → Wp,
      PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (PI.BesselMapUniq.psiGen k r z c) σ π B₁ →
      PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (PI.BesselMapUniq.psiGen k r z c) σ π B₂ →
      ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, a • B₁ v + b • B₂ v = 0
end CompanionTheory.Bmu


