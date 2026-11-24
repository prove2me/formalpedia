-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementB
-- name    : Formalism_HermitianCurvature_StatementB
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T13:49:40.521803+00:00
-- url     : https://prove2.me/theorems/0800d690-7e34-40cc-b7e3-18b0a8676c04
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementB.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.B
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def IsSesq {V : Type*} [AddCommGroup V] [Module ℂ V] (β : V → V → ℂ) : Prop :=
  (∀ x x' y, β (x + x') y = β x y + β x' y) ∧ (∀ x y y', β x (y + y') = β x y + β x y') ∧
  (∀ (a : ℂ) x y, β (a • x) y = a * β x y) ∧ (∀ (a : ℂ) x y, β x (a • y) = conj a * β x y)
def IsNonneg {V : Type*} (β : V → V → ℂ) : Prop := ∀ x, (β x x).im = 0 ∧ 0 ≤ (β x x).re
def SeminormIneq : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (β : V → V → ℂ), IsSesq β → IsNonneg β →
    ∀ x y : V, (Real.sqrt (β x x).re - Real.sqrt (β y y).re) ^ 2 ≤ (β (x - y) (x - y)).re
def Polarisation : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V) (β γ : V → V → ℂ), IsSesq β → IsSesq γ →
    (∀ x ∈ W, β x x = γ x x) → ∀ x ∈ W, ∀ y ∈ W, β x y = γ x y
def FormCoreC : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V) (β βi : V → V → ℂ),
    IsSesq β → IsSesq βi → IsNonneg β → (∀ x, (β x x).re ≤ (βi x x).re) →
    (∀ x ∈ W, ∃ (Φ : ℝ × ℝ → V) (c : ℝ × ℝ → ℂ) (t₀ : ℝ × ℝ),
        Φ t₀ = x ∧ c t₀ = βi x x ∧ ContinuousAt c t₀ ∧
        Tendsto (fun t => (βi (Φ t - x) (Φ t - x)).re) (𝓝 t₀) (𝓝 0) ∧
        ∃ U ∈ 𝓝 t₀, ∀ᵐ t ∂(volume.restrict U), β (Φ t) (Φ t) = c t) →
    ∀ x ∈ W, ∀ y ∈ W, β x y = βi x y
def FormCore : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V) (β βi : V → V → ℂ),
    IsSesq β → IsSesq βi → IsNonneg β → (∀ x, (β x x).re ≤ (βi x x).re) →
    (∀ x ∈ W, ∃ (Φ : ℝ × ℝ → V) (t₀ : ℝ × ℝ),
        Φ t₀ = x ∧ ContinuousAt (fun t => βi (Φ t) (Φ t)) t₀ ∧
        Tendsto (fun t => (βi (Φ t - x) (Φ t - x)).re) (𝓝 t₀) (𝓝 0) ∧
        ∃ U ∈ 𝓝 t₀, ∀ᵐ t ∂(volume.restrict U), β (Φ t) (Φ t) = βi (Φ t) (Φ t)) →
    ∀ x ∈ W, ∀ y ∈ W, β x y = βi x y
def Quad : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioi 0
def IsTest (w : ℝ → ℝ) : Prop := ContDiff ℝ 2 w ∧ HasCompactSupport w ∧ tsupport w ⊆ Set.Ioi 0
def AeFromTests : Prop :=
  ∀ (b : ℝ × ℝ → ℝ≥0∞) (c : ℝ × ℝ → ℂ),
    AEMeasurable b (volume.restrict Quad) → ContinuousOn c Quad →
    (∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ → (∀ x, 0 ≤ w₁ x) → (∀ x, 0 ≤ w₂ x) →
      (∫⁻ τ : ℝ × ℝ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * b τ) ≠ ∞ ∧
      (((∫⁻ τ : ℝ × ℝ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * b τ).toReal : ℝ) : ℂ) =
        ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * c τ) →
    ∀ᵐ τ ∂(volume.restrict Quad), b τ ≠ ∞ ∧ (((b τ).toReal : ℝ) : ℂ) = c τ
def FatouParam : Prop :=
  ∀ (Q : Type) [MeasurableSpace Q] (μ : Measure Q) (E : Type) [NormedAddCommGroup E]
    (U : Set (ℝ × ℝ)) (J : ℝ × ℝ → Q → E) (c : ℝ × ℝ → ℝ),
    IsOpen U → (∀ τ ∈ U, AEStronglyMeasurable (J τ) μ) →
    (∀ᵐ q ∂μ, ContinuousOn (fun τ => J τ q) U) → ContinuousOn c U →
    (∀ᵐ τ ∂(volume.restrict U), (∫⁻ q, ‖J τ q‖ₑ ^ 2 ∂μ) = ENNReal.ofReal (c τ)) →
    ∀ τ ∈ U, (∫⁻ q, ‖J τ q‖ₑ ^ 2 ∂μ) ≤ ENNReal.ofReal (c τ)
def RegIBP : Prop :=
  ∀ h : ℝ → ℂ, ContDiff ℝ 2 h → HasCompactSupport h → ∀ x : ℝ,
    (∫ t : ℝ, (h t - iteratedDeriv 2 h t) * Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))) =
      ((1 + x ^ 2 : ℝ) : ℂ) * ∫ t : ℝ, h t * Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))
def om (wh : ℝ → ℝ) (x : ℝ) : ℂ := ∫ τ : ℝ, (wh τ : ℂ) * Complex.exp (Complex.I * ((τ * x : ℝ) : ℂ))
def TestDecay : Prop :=
  ∀ wh : ℝ → ℝ, IsTest wh → ∃ C : ℝ, ∀ x : ℝ, ‖om wh x‖ ≤ C * ((1 + |x|) ^ 2)⁻¹
def rmulF {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ := Matrix.of x * a
def IntRdZeroInv : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → Fin n → ℂ)) [SigmaFinite μ] (X : Matrix (Fin n) (Fin n) ℂ)
    (h : Matrix (Fin n) (Fin n) ℂ → ℂ),
    (∀ t : ℝ, μ.map (rmulF (NormedSpace.exp ((t : ℂ) • X))) = μ) →
    (∀ᵐ g ∂μ, ContDiff ℝ 1 fun t : ℝ => h (Matrix.of g * NormedSpace.exp ((t : ℂ) • X))) →
    Integrable (fun g => h (Matrix.of g)) μ → Integrable (fun g => RdV X h (Matrix.of g)) μ →
    (∫ g, RdV X h (Matrix.of g) ∂μ) = 0
abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
abbrev GV (k r : ℕ) : Set (Mat k r) := UH (Hpk k r)
structure IsHaarOn {k r : ℕ} (U : Set (Mat k r)) (μ : Measure (Mt k r)) : Prop where
  conc : μ Uᶜ = 0
  left : ∀ a ∈ U, μ.map (lmulM a) = μ
  right : ∀ a ∈ U, μ.map (rmulF a) = μ
  finite_compact : ∀ K : Set (Mt k r), IsCompact K → μ K < ∞
  ne_zero : μ ≠ 0
structure RealPlaceData (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] where
  z : Fin (2 * r + k + 1) → ℂ
  z' : Fin (2 * r + k + 1) → ℂ
  π : Mat k r → (Wp →L[ℂ] Wp)
  π' : Mat k r → (Wq →L[ℂ] Wq)
  μG : Measure (Mt k r)
  μW : Measure (Mt k r)
  μN : Measure (Mt k r)
  μW' : Measure (Mt k r)
  μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ
  χ : ℝ → ℝ
  k_pos : 1 ≤ k
  z_mem : inWb k r z
  z'_mem : inWb k r z'
  T_pos : 0 < Tz k r z
  T'_pos : 0 < Tz k r z'
  π_rep : IsCRepOn (UWset k r z) π
  π'_rep : IsCRepOn (UWset k r z') π'
  π_unitary : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖
  π'_unitary : ∀ h ∈ UWset k r z', ∀ v, ‖π' h v‖ = ‖v‖
  π_cont : ContinuousOn π (UWset k r z)
  π'_cont : ContinuousOn π' (UWset k r z')
  haarG : IsHaarOn (GV k r) μG
  haarW : IsHaarOn (UWset k r z) μW
  haarN : IsHaarOn (Nset k r) μN
  haarW' : IsHaarOn (UWset k r z') μW'
  sec : IsSection k r z z' μsec
  χ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ
  χ_supp : tsupport χ ⊆ Set.Ioo (1 / 2) 2
  χ_int : (∫ t, χ t) = 1
section objects
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
def lam (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (n : Mat k r) : ℝ := (cStd * ell k r z n).re
abbrev SS (k r : ℕ) := (Mt k r × Mt k r) × (Mt k r × Mt k r)
def RealPlaceData.μSS (D : RealPlaceData k r Wp Wq) : Measure (SS k r) := (D.μW.prod D.μN).prod (D.μW'.prod D.μN)
def RealPlaceData.inSS (D : RealPlaceData k r Wp Wq) (p : SS k r) : Prop :=
  Matrix.of p.1.1 ∈ UWset k r D.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧
    Matrix.of p.2.1 ∈ UWset k r D.z' ∧ Matrix.of p.2.2 ∈ Nset k r
def sgs (p : SS k r) (g : Mat k r) : Mat k r :=
  (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1
def rho (D : RealPlaceData k r Wp Wq) (p : SS k r) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) : Wq →L[ℂ] Wp :=
  (D.π (Matrix.of p.1.1)).comp ((F (sgs p g)).comp (D.π' (Matrix.of p.2.1)⁻¹))
def xiTau (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (p : SS k r) : ℂ :=
  Complex.exp (Complex.I *
    ((τ.1 * lam k r D.z (Matrix.of p.1.2) - τ.2 * lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ))
def Jtau (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) : Wq →L[ℂ] Wp :=
  ∫ p, xiTau D τ p • rho D p F g ∂D.μSS
def JF (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) : Wq →L[ℂ] Wp :=
  besselJ k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F g
def gq (D : RealPlaceData k r Wp Wq) (q : (Fin r → ℂ) × ℂ) : Mat k r := bigCell k r q.1 (D.μsec q.2)
variable [FiniteDimensional ℂ Wq]
def hsVec (A : Wq →L[ℂ] Wp) : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  WithLp.toLp 2 fun i => A (stdOrthonormalBasis ℂ Wq i)
def hsInner (A B : Wq →L[ℂ] Wp) : ℂ := inner ℂ (hsVec B) (hsVec A)
def normSqTau (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) : ℝ≥0∞ :=
  jNormSq k r (Tz k r D.z) (Tz k r D.z') fun q => hsVec (Jtau D τ F (gq D q))
def betaTau (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (F F' : Mat k r → (Wq →L[ℂ] Wp)) : ℂ :=
  betaBig k r (Tz k r D.z) (Tz k r D.z') D.μsec (fun g => hsVec (Jtau D τ F g)) (fun g => hsVec (Jtau D τ F' g))
def normSq (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) : ℝ≥0∞ :=
  jNormSq k r (Tz k r D.z) (Tz k r D.z') fun q => hsVec (JF D F (gq D q))
def beta (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) : ℂ :=
  betaBig k r (Tz k r D.z) (Tz k r D.z') D.μsec (fun g => hsVec (JF D F g)) (fun g => hsVec (JF D F' g))
def Ph (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) : ℂ :=
  ∫ g, hsInner (rho D p F (Matrix.of g)) (F' (Matrix.of g)) ∂D.μG
def aDil (k r : ℕ) (t : ℝ) : Mat k r :=
  Matrix.diagonal fun i => if i.val < r then ((t ^ (r - i.val) : ℝ) : ℂ)
    else if i.val ≤ r + k then 1 else (((t ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ)
def dilation₂ (t : ℝ × ℝ) (p : SS k r) : SS k r :=
  ((p.1.1, conjM (aDil k r t.1) p.1.2), (p.2.1, conjM (aDil k r t.2) p.2.2))
def dilF (t : ℝ × ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) : Wq →L[ℂ] Wp :=
  F ((aDil k r t.1)⁻¹ * g * aDil k r t.2)
def kap (k r : ℕ) : ℕ := ∑ a : Fin r, 2 * (Mdim k r a - 1) * (r - a.val)
def oneMinusDD (h : ℝ → ℝ → ℂ) (t₁ t₂ : ℝ) : ℂ :=
  (h t₁ t₂ - iteratedDeriv 2 (fun y => h t₁ y) t₂) -
    iteratedDeriv 2 (fun x => h x t₂ - iteratedDeriv 2 (fun y => h x y) t₂) t₁
def regBracket (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) (t₁ t₂ : ℝ) : ℂ :=
  ((D.χ t₁ * D.χ t₂ * (t₁ * t₂) ^ kap k r : ℝ) : ℂ) * Ph D F F' (dilation₂ (t₁, t₂) p)
def betaInfTau (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (F F' : Mat k r → (Wq →L[ℂ] Wp)) : ℂ :=
  ∫ p, ((((1 + τ.1 ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2)⁻¹ *
        (1 + τ.2 ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ × ℝ, oneMinusDD (regBracket D F F' p) t.1 t.2 *
        Complex.exp (Complex.I * ((τ.1 * t.1 * lam k r D.z (Matrix.of p.1.2) -
          τ.2 * t.2 * lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ))) ∂D.μSS
def betaInf (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) : ℂ := betaInfTau D (1, 1) F F'
end objects
section spaces
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def inLie (k r : ℕ) (X : Mat k r) : Prop := Xᴴ * Hpk k r + Hpk k r * X = 0
def unitLie (k r : ℕ) (X : Mat k r) : Prop := inLie k r X ∧ ∀ i j, ‖X i j‖ ≤ 1
def LdV (X : Mat k r) (f : Mat k r → E) : Mat k r → E :=
  fun g => deriv (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0
def Rw (v : List (Mat k r)) (f : Mat k r → E) : Mat k r → E := v.foldr RdV f
def dLR (u v : List (Mat k r)) (f : Mat k r → E) : Mat k r → E := u.foldr LdV (Rw v f)
def gN (g : Mat k r) : ℝ := Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j))
def CkOn (m : ℕ∞) (UU : Set (Mat k r)) (f : Mat k r → E) : Prop :=
  ∀ g₀ ∈ UU, ∃ (U : Set (Mat k r)) (f' : Mat k r → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ (m : WithTop ℕ∞) f' U ∧ ∀ g ∈ U, g ∈ GV k r → f g = f' g
def CCle (A : ℝ) (m : ℕ) (F : Mat k r → E) (c : ℝ) : Prop :=
  CkOn (m : ℕ∞) (GV k r) F ∧
  ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
    ∀ g ∈ GV k r, gN g ^ A * ‖dLR u v F g‖ ≤ c
def InCC (A : ℝ) (m : ℕ) (F : Mat k r → E) : Prop := ∃ c, CCle A m F c
def AB (k r : ℕ) : ℝ := 2 * ((k : ℝ) + r) * ((r : ℝ) + 1) + 1
end spaces
section diffop
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
structure DTerm (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] where
  coef : Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))
  coefAdj : Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))
  word : List (Mat k r)
  word_lie : ∀ X ∈ word, inLie k r X
  adj_id : ∀ (x : Mat k r) (A B : Wq →L[ℂ] Wp), hsInner (coef x A) B = hsInner A (coefAdj x B)
abbrev DiffOp (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] := List (DTerm k r Wp Wq)
def opApply (Θ : DiffOp k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) : Wq →L[ℂ] Wp :=
  (Θ.map fun T => T.coef g (Rw T.word F g)).sum
def opAdj (Θ : DiffOp k r Wp Wq) (F' : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) : Wq →L[ℂ] Wp :=
  (Θ.map fun T => ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g).sum
def opOrder (Θ : DiffOp k r Wp Wq) : ℕ := (Θ.map fun T => T.word.length).foldr max 0
def IsStableOpen (D : RealPlaceData k r Wp Wq) (UU : Set (Mat k r)) : Prop :=
  (∃ O : Set (Mat k r), IsOpen O ∧ UU = O ∩ GV k r) ∧
  ∀ s ∈ Sset k r D.z, ∀ s' ∈ Sset k r D.z', ∀ g ∈ UU, s * g * s' ∈ UU
def SmoothCoef (UU : Set (Mat k r)) (Θ : DiffOp k r Wp Wq) : Prop :=
  ∀ T ∈ Θ, CkOn ⊤ UU T.coef ∧ CkOn ⊤ UU T.coefAdj
def Commutes (D : RealPlaceData k r Wp Wq) (UU : Set (Mat k r)) (Θ : DiffOp k r Wp Wq) : Prop :=
  ∀ p, D.inSS p → ∀ f : Mat k r → (Wq →L[ℂ] Wp), CkOn (opOrder Θ : ℕ∞) (GV k r) f →
    ∀ g ∈ UU, opApply Θ (rho D p f) g = rho D p (opApply Θ f) g
def SuppIn (UU : Set (Mat k r)) (F : Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  closure {g | g ∈ GV k r ∧ F g ≠ 0} ⊆ UU
def IntClause (D : RealPlaceData k r Wp Wq) (Θ : DiffOp k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ p, D.inSS p → ∀ T ∈ Θ, ∀ i j : ℕ, i ≤ j → j ≤ T.word.length →
    Integrable (fun g : Mt k r =>
      ‖Rw (T.word.take i).reverse (fun x => T.coefAdj x (F' x)) (Matrix.of g)‖ *
        ‖Rw (T.word.drop j) (rho D p F) (Matrix.of g)‖) D.μG
end diffop
section lemmaB
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def IntFormula (D : RealPlaceData k r Wp Wq) : Prop :=
  ∀ f : Mt k r → ℝ≥0∞, Measurable f →
    (∫⁻ g, f g ∂D.μG) = ∫⁻ q : (Fin r → ℂ) × ℂ,
      ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) * ∫⁻ p, f (sgs p (gq D q)) ∂D.μSS
def ConjInv (D : RealPlaceData k r Wp Wq) : Prop :=
  ∀ h₀ ∈ UWset k r D.z ∪ UWset k r D.z', D.μN.map (conjM h₀) = D.μN
def DilJac (D : RealPlaceData k r Wp Wq) : Prop :=
  ∀ t : ℝ, 0 < t → D.μN.map (conjM (aDil k r t)) = ENNReal.ofReal ((t ^ kap k r)⁻¹) • D.μN
def CCIntegrable (D : RealPlaceData k r Wp Wq) (A : ℝ) : Prop :=
  ∀ (F : Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), AEStronglyMeasurable (fun g : Mt k r => F (Matrix.of g)) D.μG →
    (∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c) → (∫⁻ g : Mt k r, ‖F (Matrix.of g)‖ₑ ∂D.μG) < ∞
def CoefBound (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (A : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (F F' : Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ),
    AEStronglyMeasurable (fun g : Mt k r => F (Matrix.of g)) D.μG →
    AEStronglyMeasurable (fun g : Mt k r => F' (Matrix.of g)) D.μG →
    (∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c) → (∀ g ∈ GV k r, gN g ^ A * ‖F' g‖ ≤ c') →
    ∀ x ∈ GV k r, ∀ y ∈ GV k r,
      (∫⁻ g : Mt k r, ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ ∂D.μG) ≤
        ENNReal.ofReal (C * c * c') * Ξ x * Ξ y
def XiInt (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (δ : ℝ) : Prop :=
  (Measurable fun x : Mt k r => Ξ (Matrix.of x)) ∧
  (∫⁻ p : Mt k r × Mt k r, Ξ (Matrix.of p.2 * Matrix.of p.1) *
      ENNReal.ofReal ((1 + |lam k r D.z (Matrix.of p.2)|) ^ (-δ)) ∂(D.μW.prod D.μN)) < ∞ ∧
  (∫⁻ p : Mt k r × Mt k r, Ξ (Matrix.of p.2 * Matrix.of p.1) *
      ENNReal.ofReal ((1 + |lam k r D.z' (Matrix.of p.2)|) ^ (-δ)) ∂(D.μW'.prod D.μN)) < ∞
def PairingContinuityBound (D : RealPlaceData k r Wp Wq) (A : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (F F' : Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ), InCC A 5 F → InCC A 5 F' →
    CCle A 4 F c → CCle A 4 F' c' →
    normSq D F ≠ ∞ ∧ normSq D F' ≠ ∞ ∧ ‖beta D F F'‖ ≤ C * c * c'
def PairingEqLimitPairing (D : RealPlaceData k r Wp Wq) (A : ℝ) : Prop :=
  ∀ F F' : Mat k r → (Wq →L[ℂ] Wp), InCC A 5 F → InCC A 5 F' → beta D F F' = betaInf D F F'
def PairingAdjointness (D : RealPlaceData k r Wp Wq) (A : ℝ) : Prop :=
  ∀ (UU : Set (Mat k r)) (Θ : DiffOp k r Wp Wq), IsStableOpen D UU → SmoothCoef UU Θ → Commutes D UU Θ →
    ∀ F F' : Mat k r → (Wq →L[ℂ] Wp),
      CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) F → CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) F' →
      SuppIn UU F → SuppIn UU F' →
      InCC A 5 F → InCC A 5 F' → InCC A 5 (opApply Θ F) → InCC A 5 (opAdj Θ F') → IntClause D Θ F F' →
      beta D (opApply Θ F) F' = beta D F (opAdj Θ F')
def SesqOn {V : Type*} [AddCommGroup V] [Module ℂ V] (P : V → Prop) (β : V → V → ℂ) : Prop :=
  (∀ x x' y, P x → P x' → P y → β (x + x') y = β x y + β x' y) ∧
  (∀ x y y', P x → P y → P y' → β x (y + y') = β x y + β x y') ∧
  (∀ (a : ℂ) x y, P x → P y → β (a • x) y = a * β x y) ∧
  (∀ (a : ℂ) x y, P x → P y → β x (a • y) = conj a * β x y)
def RegBound (D : RealPlaceData k r Wp Wq) (A : ℝ) : Prop :=
  (∀ τ₀ ∈ Quad, ∃ C : ℝ, ∃ U ∈ 𝓝 τ₀, ∀ τ ∈ U, ∀ (F F' : Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ),
      CCle A 4 F c → CCle A 4 F' c' → ‖betaInfTau D τ F F'‖ ≤ C * c * c') ∧
  (∀ F F' : Mat k r → (Wq →L[ℂ] Wp), InCC A 4 F → InCC A 4 F' →
      ContinuousOn (fun τ => betaInfTau D τ F F') Quad) ∧
  ∀ τ ∈ Quad, SesqOn (InCC A 4) (betaInfTau D τ)
def RegAverage (D : RealPlaceData k r Wp Wq) (A : ℝ) : Prop :=
  ∀ F F' : Mat k r → (Wq →L[ℂ] Wp), InCC A 4 F → InCC A 4 F' →
    ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ →
      Integrable (fun p : SS k r => om w₁ (lam k r D.z (Matrix.of p.1.2)) *
        om w₂ (-lam k r D.z' (Matrix.of p.2.2)) * Ph D F F' p) D.μSS ∧
      (∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * betaInfTau D τ F F') =
        ∫ p : SS k r, om w₁ (lam k r D.z (Matrix.of p.1.2)) *
          om w₂ (-lam k r D.z' (Matrix.of p.2.2)) * Ph D F F' p ∂D.μSS
def Unfold (D : RealPlaceData k r Wp Wq) (A : ℝ) : Prop :=
  ∀ F : Mat k r → (Wq →L[ℂ] Wp), InCC A 4 F →
    AEMeasurable (fun τ => normSqTau D τ F) (volume.restrict Quad) ∧
    ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ → (∀ x, 0 ≤ w₁ x) → (∀ x, 0 ≤ w₂ x) →
      (∫⁻ τ : ℝ × ℝ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * normSqTau D τ F) ≠ ∞ ∧
      (((∫⁻ τ : ℝ × ℝ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * normSqTau D τ F).toReal : ℝ) : ℂ) =
        ∫ p : SS k r, om w₁ (lam k r D.z (Matrix.of p.1.2)) *
          om w₂ (-lam k r D.z' (Matrix.of p.2.2)) * Ph D F F p ∂D.μSS
def Qset (D : RealPlaceData k r Wp Wq) : Set ((Fin r → ℂ) × ℂ) :=
  {q | 0 < bcWeight k r (Tz k r D.z) (Tz k r D.z') q}
def JCont (D : RealPlaceData k r Wp Wq) (A : ℝ) : Prop :=
  ∀ F : Mat k r → (Wq →L[ℂ] Wp), InCC A 4 F →
    (∀ᵐ q ∂(volume.restrict (Qset D)), Integrable (fun p => rho D p F (gq D q)) D.μSS) ∧
    (∀ᵐ q ∂(volume.restrict (Qset D)), ContinuousOn (fun τ => Jtau D τ F (gq D q)) Quad) ∧
    ∀ τ ∈ Quad, AEStronglyMeasurable (fun q => Jtau D τ F (gq D q)) (volume.restrict (Qset D))
def DilBeta (D : RealPlaceData k r Wp Wq) (A : ℝ) : Prop :=
  ∀ F : Mat k r → (Wq →L[ℂ] Wp), InCC A 4 F → ∀ τ ∈ Quad, ∀ t ∈ Quad,
    normSqTau D τ (dilF t F) = ENNReal.ofReal ((t.1 * t.2) ^ kap k r) * normSqTau D (τ.1 * t.1, τ.2 * t.2) F
def DiagDom (D : RealPlaceData k r Wp Wq) (A : ℝ) : Prop :=
  ∀ F : Mat k r → (Wq →L[ℂ] Wp), InCC A 4 F → ∀ τ ∈ Quad,
    (betaInfTau D τ F F).im = 0 ∧ normSqTau D τ F ≤ ENNReal.ofReal (betaInfTau D τ F F).re
def DiagEq (D : RealPlaceData k r Wp Wq) (A : ℝ) : Prop :=
  ∀ F : Mat k r → (Wq →L[ℂ] Wp), InCC A 5 F → ∀ τ ∈ Quad,
    normSqTau D τ F ≠ ∞ ∧ (((normSqTau D τ F).toReal : ℝ) : ℂ) = betaInfTau D τ F F
end lemmaB
def DilMem : Prop := ∀ (k r : ℕ) (t : ℝ), t ≠ 0 → aDil k r t ∈ GV k r
def DilN : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (t : ℝ), t ≠ 0 → inWb k r z → ∀ n ∈ Nset k r,
    aDil k r t * n * (aDil k r t)⁻¹ ∈ Nset k r ∧
    ell k r z (aDil k r t * n * (aDil k r t)⁻¹) = (t : ℂ) * ell k r z n ∧
    lam k r z (aDil k r t * n * (aDil k r t)⁻¹) = t * lam k r z n
def DilUW : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (t : ℝ), ∀ h ∈ UWset k r z, aDil k r t * h = h * aDil k r t
def DilBigCell : Prop :=
  ∀ (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (t₁ t₂ : ℝ), t₁ ≠ 0 → t₂ ≠ 0 →
    (aDil k r t₁)⁻¹ * bigCell k r c μ * aDil k r t₂ =
      bigCell k r (fun a => (((t₁ * t₂) ^ (r - a.val) : ℝ) : ℂ) * c a) μ
def CCLin : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (m : ℕ) (F F' : Mat k r → E) (c c' : ℝ)
    (a : ℂ), CCle A m F c → CCle A m F' c' → CCle A m (F + F') (c + c') ∧ CCle A m (a • F) (‖a‖ * c)
def DilCC : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (A : ℝ), 0 ≤ A →
    ∃ C : ℝ, ∀ t ∈ Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2, ∀ (F : Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ),
      CCle A 5 F c → CCle A 5 (dilF t F) (C * c) ∧
        CCle A 4 (dilF t F - F) (C * (|t.1 - 1| + |t.2 - 1|) * c)
def JtauOne : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r), Jtau D (1, 1) F g = JF D F g
def StepPhBound : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (Ξ : Mat k r → NNReal) (A : ℝ), CoefBound D Ξ A →
    ∃ C : ℝ, ∀ (F F' : Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ), CCle A 0 F c → CCle A 0 F' c' →
      ∀ p, D.inSS p → ‖Ph D F F' p‖ ≤ C * c * c' * Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) *
        Ξ (Matrix.of p.2.2 * Matrix.of p.2.1)
def XiExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) (A : ℝ),
    AB k r ≤ A → ∃ Ξ : Mat k r → NNReal, CoefBound D Ξ A ∧ XiInt D Ξ 2
def StepRegBound : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (Ξ : Mat k r → NNReal) (A : ℝ), AB k r ≤ A → CoefBound D Ξ A → XiInt D Ξ 2 → RegBound D A
def StepRegAverage : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (Ξ : Mat k r → NNReal) (A : ℝ), AB k r ≤ A → CoefBound D Ξ A → XiInt D Ξ 2 → DilJac D → RegAverage D A
def StepUnfold : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (Ξ : Mat k r → NNReal) (A : ℝ), AB k r ≤ A → IntFormula D → ConjInv D → CCIntegrable D A →
    CoefBound D Ξ A → XiInt D Ξ 2 → Unfold D A
def StepJCont : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (A : ℝ), IntFormula D → CCIntegrable D A → JCont D A
def StepDilBeta : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (A : ℝ), DilJac D → DilBeta D A
def StepRegPh : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (τ : ℝ × ℝ) (F₁ F₁' F₂ F₂' : Mat k r → (Wq →L[ℂ] Wp)),
    (∀ p, D.inSS p → Ph D F₁ F₁' p = Ph D F₂ F₂' p) → betaInfTau D τ F₁ F₁' = betaInfTau D τ F₂ F₂'
def StepPhAdj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (UU : Set (Mat k r)) (Θ : DiffOp k r Wp Wq), IsStableOpen D UU → SmoothCoef UU Θ → Commutes D UU Θ →
    ∀ F F' : Mat k r → (Wq →L[ℂ] Wp),
      CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) F → CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) F' →
      SuppIn UU F → SuppIn UU F' → IntClause D Θ F F' →
      ∀ p, D.inSS p → Ph D (opApply Θ F) F' p = Ph D F (opAdj Θ F') p
def AssembleEq : Prop :=
  FormCoreC → AeFromTests → FatouParam → CCLin → DilCC → JtauOne →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (A : ℝ), 0 ≤ A → RegBound D A → RegAverage D A → Unfold D A → JCont D A → DilBeta D A →
    PairingContinuityBound D A ∧ PairingEqLimitPairing D A
def AssembleDiag : Prop :=
  FormCoreC → AeFromTests → FatouParam → CCLin → DilCC →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (A : ℝ), 0 ≤ A → RegBound D A → RegAverage D A → Unfold D A → JCont D A → DilBeta D A →
    DiagDom D A ∧ DiagEq D A
def AssembleAdj : Prop :=
  StepPhAdj → StepRegPh →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (A : ℝ), PairingEqLimitPairing D A → PairingAdjointness D A
def LemmaB : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (Ξ : Mat k r → NNReal) (A : ℝ), AB k r ≤ A →
    IntFormula D → ConjInv D → DilJac D → CCIntegrable D A → CoefBound D Ξ A → XiInt D Ξ 2 →
    PairingContinuityBound D A ∧ PairingEqLimitPairing D A ∧ PairingAdjointness D A
def LemmaBFromSteps : Prop :=
  FormCoreC → AeFromTests → FatouParam → CCLin → DilCC → JtauOne →
  StepRegBound → StepRegAverage → StepUnfold → StepJCont → StepDilBeta → StepPhAdj → StepRegPh →
  AssembleEq → AssembleAdj → LemmaB
section poly
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def GPos (D : RealPlaceData k r Wp Wq) : Set (Mat k r) := {g | g ∈ GV k r ∧ 0 < Gf k r D.z D.z' g}
def PolyCoef (D : RealPlaceData k r Wp Wq) (ε d : ℝ) (m : ℕ) (Θ : DiffOp k r Wp Wq) : Prop :=
  ∀ T ∈ Θ, ∃ C : ℝ, ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
    u.length + v.length ≤ m → ∀ g ∈ GV k r, ε ≤ Gf k r D.z D.z' g →
      ‖dLR u v T.coef g‖ ≤ C * gN g ^ d ∧ ‖dLR u v T.coefAdj g‖ ≤ C * gN g ^ d
def AdjointnessPolynomialCoefficients (D : RealPlaceData k r Wp Wq) (A : ℝ) : Prop :=
  ∀ (Θ : DiffOp k r Wp Wq) (ε d : ℝ), 0 < ε → 0 ≤ d → SmoothCoef (GPos D) Θ → Commutes D (GPos D) Θ →
    PolyCoef D ε d (opOrder Θ + 5) Θ →
    ∀ F F' : Mat k r → (Wq →L[ℂ] Wp), InCC (A + d) (opOrder Θ + 5) F → InCC (A + d) (opOrder Θ + 5) F' →
      (∀ g ∈ GV k r, F g ≠ 0 → ε ≤ Gf k r D.z D.z' g) → (∀ g ∈ GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
      beta D (opApply Θ F) F' = beta D F (opAdj Θ F')
end poly
def StepClause : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (A : ℝ), 0 ≤ A → CCIntegrable D A →
    IsStableOpen D (GPos D) ∧
    ∀ (Θ : DiffOp k r Wp Wq) (ε d : ℝ), 0 < ε → 0 ≤ d → SmoothCoef (GPos D) Θ →
      PolyCoef D ε d (opOrder Θ + 5) Θ →
      ∀ F F' : Mat k r → (Wq →L[ℂ] Wp), InCC (A + d) (opOrder Θ + 5) F → InCC (A + d) (opOrder Θ + 5) F' →
        (∀ g ∈ GV k r, F g ≠ 0 → ε ≤ Gf k r D.z D.z' g) → (∀ g ∈ GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
        SuppIn (GPos D) F ∧ SuppIn (GPos D) F' ∧ InCC A 5 F ∧ InCC A 5 F' ∧
          InCC A 5 (opApply Θ F) ∧ InCC A 5 (opAdj Θ F') ∧ IntClause D Θ F F'
def AssemblePoly : Prop :=
  StepClause →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (A : ℝ), 0 ≤ A → CCIntegrable D A → PairingAdjointness D A → AdjointnessPolynomialCoefficients D A
def LemmaBClosed : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (A : ℝ), AB k r ≤ A → IntFormula D → ConjInv D → DilJac D → CCIntegrable D A →
    PairingContinuityBound D A ∧ PairingEqLimitPairing D A ∧ PairingAdjointness D A ∧ AdjointnessPolynomialCoefficients D A
def LemmaBClosedFromParts : Prop :=
  XiExists → LemmaB → StepClause → AssemblePoly → LemmaBClosed
end Formalism.FourierDecayAlt.B


