-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
-- name    : Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:59.657272+00:00
-- url     : https://prove2.me/theorems/aea934f9-092a-4f29-a914-8ba09318b145
-- title:
--   Theta Existence Inductive From Pieces
-- statement:
--   Definitions and structural lemmas for Theta Existence Inductive From Pieces, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/ThetaExistenceInductiveFromPieces.lean

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Filter Topology
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.A6
section Defs
variable {K : Type} [CommRing K]
def IsLat [TopologicalSpace K] (L : AddSubgroup K) : Prop :=
  IsOpen (L : Set K) ∧ IsCompact (L : Set K)
def perp (ψ : AddChar K ℂ) (L : AddSubgroup K) : AddSubgroup K where
  carrier := {a | ∀ l ∈ L, ψ (a * l) = 1}
  zero_mem' := by intro l _; simp
  add_mem' := by
    intro a b ha hb l hl
    have ha' : ψ (a * l) = 1 := ha l hl
    have hb' : ψ (b * l) = 1 := hb l hl
    rw [add_mul, AddChar.map_add_eq_mul, ha', hb', one_mul]
  neg_mem' := by
    intro a ha l hl
    have ha' : ψ (a * l) = 1 := ha l hl
    rw [neg_mul, AddChar.map_neg_eq_inv, ha', inv_one]
def volL (R : Subring K) (L : AddSubgroup K) : ℝ :=
  (R.toAddSubgroup.relIndex L : ℝ) / (L.relIndex R.toAddSubgroup : ℝ)
def mulLat (b : K) (L : AddSubgroup K) : AddSubgroup K := L.map (AddMonoidHom.mulLeft b)
def IsReps (S : Finset K) (L M : AddSubgroup K) : Prop :=
  (∀ a ∈ S, a ∈ L) ∧ ∀ l ∈ L, ∃! a, a ∈ S ∧ l - a ∈ M
def LatInv (Λ : AddSubgroup K) (Om : Set K) (f : K → ℂ) : Prop :=
  ∀ z ∈ Om, ∀ l ∈ Λ, f (z + l) = f z
def LatInvN (Λ : AddSubgroup K) {d : ℕ} (f : (Fin d → K) → ℂ) : Prop :=
  ∀ x l : Fin d → K, (∀ i, l i ∈ Λ) → f (x + l) = f x
open Classical in

def intLat (R : Subring K) (Λ : AddSubgroup K) (Om : Set K) (f : K → ℂ) : ℂ :=
  (volL R Λ : ℂ) * ∑ᶠ y : K ⧸ Λ, if (Quotient.out y : K) ∈ Om then f (Quotient.out y) else 0
def intK (R : Subring K) (Λ : AddSubgroup K) (d : ℕ) (f : (Fin d → K) → ℂ) : ℂ :=
  (volL R Λ : ℂ) ^ d * ∑ᶠ y : Fin d → K ⧸ Λ, f (fun i => Quotient.out (y i))
def IsOmega [TopologicalSpace K] (s : ℕ) (Om : Set K) : Prop :=
  IsOpen Om ∧ IsCompact Om ∧ (∀ z ∈ Om, IsUnit z) ∧ ∀ z ∈ Om, ∀ ζ : K, ζ ^ s = 1 → ζ * z ∈ Om
def IsShift (t t₁ : Kˣ) (σ : K) : Prop := ((t₁⁻¹ : Kˣ) : K) = ((t⁻¹ : Kˣ) : K) + σ
def IsCr (R : Subring K) (cr : K ⧸ R.toAddSubgroup → Kˣ) : Prop :=
  ∀ x, ((cr x : K) : K ⧸ R.toAddSubgroup) = x
open Classical in

def NsK (R : Subring K) (ψ : AddChar K ℂ) (s : ℕ) (h h' : Point K) (z : K) : ℂ :=
  if hz : IsUnit z then Ns R ψ s h h' hz.unit hz.unit else 0
def h0 : Point K := ([], fun _ => 1)
def pt2 (h : Point K) (m : ℕ) (t c : Kˣ) : Point K := addBlock (addBlock h m t) 1 c
def cutSet (m : ℕ) (Om : Set K) (t : Kˣ) : Set K :=
  {c | ∃ z ∈ Om, z ^ (m + 1) = (-(t : K)) ^ m * c}
open Classical in

def uGram (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (cr : K ⧸ R.toAddSubgroup → Kˣ) (S : Set K)
    (h h' : Point K) (t t' : Kˣ) : ℂ :=
  ((modK R ((t : K) * (t' : K)) ^ (m * (m + 1) / 2) : ℝ) : ℂ) *
    ∑ᶠ x : K ⧸ R.toAddSubgroup,
      if (cr x : K) ∈ S then Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) else 0
def thx (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (cr : K ⧸ R.toAddSubgroup → Kˣ)
    (A B : Finset K) (τ : K → Kˣ) (z : K) (h h' : Point K) : ℂ :=
  (A.card : ℂ)⁻¹ * ∑ ρ ∈ A, ((B.card : ℂ)⁻¹) ^ 2 * ∑ b ∈ B, ∑ b' ∈ B,
    ψ (-(z * b)) * conj (ψ (-(z * b'))) *
      uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b'))
open Classical in

def bbZ (R : Subring K) (ψ : AddChar K ℂ) (w : Point K) {n' : ℕ}
    (Z' : Matrix (Fin n') (Fin n') K) : ℂ :=
  ∑ᶠ q : Cos R w, (if IsInt R (orbZ w (rep R q)) then
    (Nat.card (isoZZ R (orbZ w (rep R q)) Z') : ℂ) else 0) * phase ψ (rep R q)
def omPhi (R : Subring K) (ψ : AddChar K ℂ) (w : Point K)
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ) : ℂ :=
  ∑ᶠ q : Cos R w, Φ w.1.sum (orbZ w (rep R q)) * phase ψ (rep R q)
def PhiHyp (R : Subring K) (s : ℕ) (L₀ Λ₀ : AddSubgroup K) (Q : Set K)
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ) : Prop :=
  (∀ Z a b : Matrix (Fin s) (Fin s) K, IsLowUni a → IsInt R a → IsUpUni b → IsInt R b →
    Φ s (a * Z * b) = Φ s Z) ∧
  (∀ Z : Matrix (Fin s) (Fin s) K, Φ s Z ≠ 0 → ∀ i j, Z i j ∈ L₀) ∧
  (∀ Z Y : Matrix (Fin s) (Fin s) K, (Z.det ∈ Q ∨ -Z.det ∈ Q) → (∀ i j, Y i j ∈ Λ₀) →
    Φ s (Z + Y) = Φ s Z)
def hessM (m : ℕ) (a : Kˣ) : Matrix (Fin m) (Fin m) K :=
  ((a⁻¹ : Kˣ) : K) • (1 + Matrix.of fun _ _ => (1 : K))
open Classical in

def gaussF (ψ : AddChar K ℂ) (L : AddSubgroup K) {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (ξ : Fin m → K) : ℂ :=
  if ∀ i, ξ i ∈ L then ψ (Ring.inverse 2 * (ξ ⬝ᵥ (M *ᵥ ξ))) else 0
def GaussAdm (ψ : AddChar K ℂ) (L : AddSubgroup K) {m : ℕ} (M : Matrix (Fin m) (Fin m) K) : Prop :=
  ∀ y : Fin m → K, (∀ i, y i ∈ perp ψ L) → ψ (Ring.inverse 2 * (y ⬝ᵥ (M⁻¹ *ᵥ y))) = 1
def IsGamma [TopologicalSpace K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ) : Prop :=
  (∀ a, ‖γ a‖ = 1) ∧ (∀ a b : Kˣ, γ (a * b ^ 2) = γ a) ∧
  ∀ (a : Kˣ) (L Λ : AddSubgroup K), IsLat L → IsLat Λ → GaussAdm ψ L (hessM m a) →
    LatInvN Λ (gaussF ψ L (hessM m a)) →
    intK R Λ m (gaussF ψ L (hessM m a)) =
      γ a * ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) * modK R (a : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ)
def g0 {m : ℕ} (D' : K) (x : Fin m → K) : K := ∑ k, x k + D' * Ring.inverse (∏ k, x k)
def germCoef (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ) (t z : Kˣ) : ℂ :=
  γ (z * t) *
    ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) * modK R (z : K) ^ ((m : ℝ) ^ 2 / 2) : ℝ) : ℂ) *
    ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K))
open Classical in

def germSum (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ) (t c : Kˣ) (f : Kˣ → ℂ) : ℂ :=
  ((modK R (t : K) ^ (-((m : ℝ) ^ 2) / 2) : ℝ) : ℂ) *
    ∑ᶠ z : Kˣ, if z ^ (m + 1) = (-t) ^ m * c then germCoef R ψ m γ t z * f z else 0
def AmpHyp (L₀ Λ₁ : AddSubgroup K) {m : ℕ} (A : (Fin m → K) → ℂ) : Prop :=
  (∀ x, A x ≠ 0 → ∀ k, x k ∈ L₀ ∧ IsUnit (x k) ∧ Ring.inverse (x k) ∈ L₀) ∧ LatInvN Λ₁ A
end Defs
def MeanSplit : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A B : Type) [Fintype A] [Fintype B]
    (u : A × B → E) (e₁ : A → ℂ) (e₂ : B → ℂ),
    ((Fintype.card A : ℂ) * (Fintype.card B : ℂ))⁻¹ • ∑ p : A × B, (e₁ p.1 * e₂ p.2) • u p =
      (Fintype.card A : ℂ)⁻¹ • ∑ ρ, e₁ ρ • ((Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b))
def POrth : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A B : Type) [Fintype A] [Fintype B]
    (u : A × B → E) (e₂ : B → ℂ),
    (∀ ρ ρ' b b', ρ ≠ ρ' → inner ℂ (u (ρ, b)) (u (ρ', b')) = 0) →
    ∀ ρ ρ', ρ ≠ ρ' →
      inner ℂ ((Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b))
        ((Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ', b)) = 0
def OrthNorm : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A : Type) [Fintype A]
    (P : A → E) (e₁ : A → ℂ), (∀ ρ, ‖e₁ ρ‖ = 1) →
    (∀ ρ ρ', ρ ≠ ρ' → inner ℂ (P ρ) (P ρ') = 0) →
    ‖(Fintype.card A : ℂ)⁻¹ • ∑ ρ, e₁ ρ • P ρ‖ ^ 2 =
      ((Fintype.card A : ℝ)⁻¹) ^ 2 * ∑ ρ, ‖P ρ‖ ^ 2
def AvgBound : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A B : Type) [Fintype A] [Fintype B]
    (u : A × B → E) (T : E →ₗ[ℂ] E) (e₁ : A → ℂ) (e₂ : B → ℂ),
    (∀ v, ‖T v‖ ≤ ‖v‖) → (∀ ρ, ‖e₁ ρ‖ = 1) →
    (∀ ρ ρ' b b', ρ ≠ ρ' → inner ℂ (u (ρ, b)) (u (ρ', b')) = 0) →
    ‖T (((Fintype.card A : ℂ) * (Fintype.card B : ℂ))⁻¹ • ∑ p : A × B, (e₁ p.1 * e₂ p.2) • u p)‖ ^ 2 ≤
      (Fintype.card A : ℝ)⁻¹ * ((Fintype.card A : ℝ)⁻¹ *
        ∑ ρ, ‖(Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b)‖ ^ 2)
def AvgBoundAssemble : Prop := MeanSplit → POrth → OrthNorm → AvgBound
def ParsevalGroup : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (G : Type) [AddCommGroup G]
    [Fintype G] (v : G → E),
    ∑ᶠ χ : AddChar G ℂ, ‖(Fintype.card G : ℂ)⁻¹ • ∑ g, χ (-g) • v g‖ ^ 2 =
      (Fintype.card G : ℝ)⁻¹ * ∑ g, ‖v g‖ ^ 2
def GramRealiseCut : Prop :=
  ∀ (X : Type) (F : Finset X) (G Gc : X → X → ℂ), IsPSD F Gc → IsPSD F (fun x y => G x y - Gc x y) →
    ∃ (n : ℕ) (u : X → EuclideanSpace ℂ (Fin n))
      (T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)),
      (∀ v, ‖T v‖ ≤ ‖v‖) ∧ (∀ x ∈ F, ∀ y ∈ F, inner ℂ (u y) (u x) = G x y) ∧
      ∀ x ∈ F, ∀ y ∈ F, inner ℂ (T (u y)) (T (u x)) = Gc x y
def PSDEntryBound : Prop :=
  ∀ (X : Type) (F : Finset X) (k M : X → X → ℂ), IsPSD F k → IsPSD F (fun x y => M x y - k x y) →
    ∀ x ∈ F, ∀ y ∈ F, ‖k x y‖ ^ 2 ≤ (M x x).re * (M y y).re
def PSDClosed : Prop :=
  ∀ (X : Type) (F : Finset X) (k : ℕ → X → X → ℂ) (l : X → X → ℂ), (∀ j, IsPSD F (k j)) →
    (∀ x ∈ F, ∀ y ∈ F, Tendsto (fun j => k j x y) atTop (𝓝 (l x y))) → IsPSD F l
def BoundedSubseq : Prop :=
  ∀ (I : Type) [Finite I] (θ : ℕ → I → ℂ) (C : ℝ), (∀ j i, ‖θ j i‖ ≤ C) →
    ∃ (φ : ℕ → ℕ) (l : I → ℂ), StrictMono φ ∧ ∀ i, Tendsto (fun j => θ (φ j) i) atTop (𝓝 (l i))
def LatFinite : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (L M : AddSubgroup K),
    IsLat L → IsLat M → M.relIndex L ≠ 0
def IntLatRefine : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (Λ Λ' : AddSubgroup K) (Om : Set K) (f : K → ℂ),
    IsLat Λ → IsLat Λ' → Λ' ≤ Λ → IsCompact Om → (∀ z ∈ Om, ∀ l ∈ Λ, z + l ∈ Om) → LatInv Λ Om f →
      intLat R Λ' Om f = intLat R Λ Om f
def IntKRefine : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (Λ Λ' L : AddSubgroup K) (d : ℕ)
    (f : (Fin d → K) → ℂ), IsLat Λ → IsLat Λ' → IsLat L → Λ' ≤ Λ →
    (∀ x, f x ≠ 0 → ∀ i, x i ∈ L) → LatInvN Λ f → intK R Λ' d f = intK R Λ d f
def VolScale : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (b : Kˣ) (L : AddSubgroup K), IsLat L →
      IsLat (mulLat (b : K) L) ∧ volL R (mulLat (b : K) L) = modK R (b : K) * volL R L
def PerpLat : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ L : AddSubgroup K, IsLat L →
      IsLat (perp ψ L) ∧ perp ψ (perp ψ L) = L ∧ volL R L * volL R (perp ψ L) = 1
open Classical in

def CharMean : Prop :=
  ∀ (K : Type) [CommRing K] (ψ : AddChar K ℂ) (L₁ L₂ : AddSubgroup K) (S : Finset K),
    L₁ ≤ L₂ → IsReps S L₂ L₁ → ∀ a ∈ perp ψ L₁,
      (S.card : ℂ)⁻¹ * ∑ σ ∈ S, ψ (a * σ) = if a ∈ perp ψ L₂ then 1 else 0
def PerpDual : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ L₁ : AddSubgroup K, IsLat L₁ → L₁ ≤ R.toAddSubgroup →
    ∀ χ : AddChar R ℂ, (∀ r : R, (r : K) ∈ L₁ → χ r = 1) →
      (∃ z ∈ perp ψ L₁, ∀ r : R, χ r = ψ (z * (r : K))) ∧
      ∀ z z' : K, (∀ r : R, χ r = ψ (z * (r : K))) → (∀ r : R, χ r = ψ (z' * (r : K))) → z - z' ∈ R
def LatChoice : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    (∀ C : Set K, IsCompact C → ∃ L₁ : AddSubgroup K, IsLat L₁ ∧ L₁ ≤ R.toAddSubgroup ∧
      ∀ z ∈ C, z ∈ perp ψ L₁) ∧
    (∀ V ∈ 𝓝 (0 : K), ∃ L₂ : AddSubgroup K, IsLat L₂ ∧ R.toAddSubgroup ≤ L₂ ∧
      ∀ z ∈ perp ψ L₂, z ∈ V)
def ModLocConst : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ Om : Set K, IsCompact Om → (∀ z ∈ Om, IsUnit z) → ∀ E ∈ 𝓝 (0 : K),
      ∃ Λ : AddSubgroup K, IsLat Λ ∧ ∀ z ∈ Om, ∀ l ∈ Λ,
        IsUnit (z + l) ∧ modK R (z + l) = modK R z ∧ l * Ring.inverse z ∈ E
def SmallUnits : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ V ∈ 𝓝 (0 : K), ∃ t : Kˣ, (t : K) ∈ V
def SmallModules : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ V ∈ 𝓝 (0 : K), ∃ B : Submodule R K, IsLat B.toAddSubgroup ∧ (B : Set K) ⊆ V
def RootsFinite : Prop :=
  ∀ (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (s : ℕ), 1 ≤ s → ∀ D : Kˣ,
    {z : Kˣ | z ^ s = D}.Finite
def RootsSeparated : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ s : ℕ, 1 ≤ s → ∀ Q : Set K, IsCompact Q → (∀ d ∈ Q, IsUnit d) →
    ∃ V ∈ 𝓝 (0 : K), ∀ z z' : Kˣ, (z : K) ^ s ∈ Q → z ^ s = z' ^ s → (z : K) - (z' : K) ∈ V → z = z'
def Exhaust : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) → ∀ s : ℕ, 1 ≤ s →
    ∃ Om : ℕ → Set K, (∀ j, IsOmega s (Om j)) ∧ (∀ j, Om j ⊆ Om (j + 1)) ∧
      ∀ z : Kˣ, ∃ j, (z : K) ∈ Om j
def Param : Prop :=
  ∀ (K : Type) [CommRing K] (m : ℕ) (t : Kˣ) (c : K) (u' : Matrix (Fin m) (Fin m) K)
    (a : Matrix Unit (Fin m) K) (b : Matrix (Fin m) Unit K), IsUpUni u' →
    ∀ w : Matrix (Fin m) (Fin m) K, (w = Matrix.of fun i j => if j = Fin.rev i then 1 else 0) →
    fromBlocks 1 0 a 1 * fromBlocks ((t : K) • w) 0 0 (Matrix.of fun _ _ => c) *
        fromBlocks u' b 0 1 =
      fromBlocks (w * ((t : K) • u')) (w * ((t : K) • b)) (a * w * ((t : K) • u'))
        ((Matrix.of fun _ _ => c) + a * w * ((t : K) • u') * ((t : K) • u')⁻¹ * ((t : K) • b)) ∧
    ∀ i : Fin m, i.val = 0 → (a * w * ((t : K) • u')) () i = (t : K) * a () (Fin.rev i)
def CritPoints : Prop :=
  ∀ (K : Type) [CommRing K] (m : ℕ), 1 ≤ m → ∀ (D' : Kˣ) (x : Fin m → Kˣ),
    (∀ k, x k * ∏ j, x j = D') ↔ ∃ z : Kˣ, (∀ k, x k = z) ∧ z ^ (m + 1) = D'
def CritValue : Prop :=
  ∀ (K : Type) [CommRing K] (m : ℕ) (z : Kˣ),
    g0 ((z : K) ^ (m + 1)) (fun _ : Fin m => (z : K)) = ((m + 1 : ℕ) : K) * (z : K)
def HessianJet : Prop :=
  ∀ (m : ℕ) (d : Fin m →₀ ℕ),
    d ∈ ((∏ k : Fin m, (1 + MvPolynomial.X k)) *
      (1 - ∑ k : Fin m, MvPolynomial.X k + MvPolynomial.C (1 / 2 : ℚ) *
        (∑ k : Fin m, MvPolynomial.X k ^ 2 + (∑ k : Fin m, MvPolynomial.X k) ^ 2)) -
      1 : MvPolynomial (Fin m) ℚ).support → 3 ≤ d.sum fun _ e => e
def HessDet : Prop :=
  ∀ (K : Type) [CommRing K] (m : ℕ) (a : Kˣ),
    (hessM m a).det = ((m + 1 : ℕ) : K) * ((a⁻¹ : Kˣ) : K) ^ m
def GaussModulus : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ (m : ℕ) (M : Matrix (Fin m) (Fin m) K), M.IsSymm → IsUnit M.det →
    ∀ L Λ : AddSubgroup K, IsLat L → IsLat Λ → GaussAdm ψ L M → LatInvN Λ (gaussF ψ L M) →
      ‖intK R Λ m (gaussF ψ L M)‖ = modK R M.det ^ (-(1 : ℝ) / 2)
def GaussIndep : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ (m : ℕ) (M : Matrix (Fin m) (Fin m) K), M.IsSymm → IsUnit M.det →
    ∀ L Λ L' Λ' : AddSubgroup K, IsLat L → IsLat Λ → IsLat L' → IsLat Λ' →
      GaussAdm ψ L M → LatInvN Λ (gaussF ψ L M) → GaussAdm ψ L' M → LatInvN Λ' (gaussF ψ L' M) →
      intK R Λ m (gaussF ψ L M) = intK R Λ' m (gaussF ψ L' M)
def GaussHess : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ m : ℕ, ∃ γ : Kˣ → ℂ, IsGamma R ψ m γ
def GaussHessAssemble : Prop :=
  GaussModulus → GaussIndep → HessDet → ModMul → VolScale → GaussHess
def GaussAdmSmall : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ (m : ℕ) (L : AddSubgroup K) (Q : Set K), IsLat L → IsCompact Q → (∀ d ∈ Q, IsUnit d) →
    ∃ V ∈ 𝓝 (0 : K), ∀ t z : Kˣ, (t : K) ∈ V → (z : K) ^ (m + 1) ∈ Q →
      GaussAdm ψ L (hessM m (z * t))
open Classical in

def NonStationary : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ m : ℕ, 1 ≤ m → ∀ (L₀ Λ₁ B : AddSubgroup K) (Q : Set K), IsLat L₀ → IsLat Λ₁ → IsLat B →
    IsCompact Q → (∀ d ∈ Q, IsUnit d) →
    ∃ V ∈ 𝓝 (0 : K), ∀ (t D' : Kˣ) (A : (Fin m → K) → ℂ), (t : K) ∈ V → (D' : K) ∈ Q →
      AmpHyp L₀ Λ₁ A → ∀ Λ : AddSubgroup K, IsLat Λ →
      LatInvN Λ (fun x : Fin m → K => if ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B then 0
        else A x * ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K))) →
      intK R Λ m (fun x : Fin m → K => if ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B then 0
        else A x * ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K))) = 0
def MorseLemma : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ m : ℕ, 1 ≤ m → ∀ Q : Set K, IsCompact Q → (∀ d ∈ Q, IsUnit d) →
    ∃ V ∈ 𝓝 (0 : K), ∀ B : Submodule R K, IsLat B.toAddSubgroup → (B : Set K) ⊆ V →
      ∀ z : Kˣ, (z : K) ^ (m + 1) ∈ Q →
      ∃ φ : (Fin m → K) → (Fin m → K),
        Set.BijOn φ {ξ | ∀ k, ξ k ∈ B} {ξ | ∀ k, ξ k ∈ B} ∧
        (∀ Λ : Submodule R K, Λ ≤ B → ∀ ξ η : Fin m → K, (∀ k, ξ k ∈ B) → (∀ k, η k ∈ B) →
          ((∀ k, φ ξ k - φ η k ∈ Λ) ↔ ∀ k, ξ k - η k ∈ Λ)) ∧
        ∀ ξ : Fin m → K, (∀ k, ξ k ∈ B) →
          (∀ k, IsUnit ((z : K) + φ ξ k)) ∧
          g0 ((z : K) ^ (m + 1)) (fun k => (z : K) + φ ξ k) =
            ((m + 1 : ℕ) : K) * (z : K) + Ring.inverse 2 * (ξ ⬝ᵥ (hessM m z *ᵥ ξ))
open Classical in

def StationaryPhase : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ m : ℕ, 1 ≤ m → ∀ γ : Kˣ → ℂ, IsGamma R ψ m γ →
    ∀ (L₀ Λ₁ : AddSubgroup K) (Q : Set K), IsLat L₀ → IsLat Λ₁ → IsCompact Q →
    (∀ d ∈ Q, IsUnit d) →
    ∃ V ∈ 𝓝 (0 : K), ∀ (t D' : Kˣ) (A : (Fin m → K) → ℂ), (t : K) ∈ V → (D' : K) ∈ Q →
      AmpHyp L₀ Λ₁ A → ∀ Λ : AddSubgroup K, IsLat Λ →
      LatInvN Λ (fun x : Fin m → K => A x * ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K))) →
      intK R Λ m (fun x : Fin m → K => A x * ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K))) =
        ((modK R (t : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) * ∑ᶠ z : Kˣ, if z ^ (m + 1) = D' then
          γ (z * t) * ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) *
            modK R (z : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
          ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) * A (fun _ => (z : K)) else 0
def OscInvariant : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ (m : ℕ) (L₁ Λ₁ : AddSubgroup K), IsLat L₁ → IsLat Λ₁ → ∀ (A : (Fin m → K) → ℂ) (a D' : K),
      AmpHyp L₁ Λ₁ A → ∃ Λ : AddSubgroup K, IsLat Λ ∧
        LatInvN Λ (fun x : Fin m → K => A x * ψ (g0 D' x * a))
def StationaryAssemble : Prop :=
  NonStationary → MorseLemma → IntKRefine → ModMul → RootsFinite → LatChoice → PerpLat →
    ModLocConst → OscInvariant → VolScale → RootsSeparated → SmallModules → GaussAdmSmall →
    LatFinite → StationaryPhase
def OscReduction : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ m : ℕ, 1 ≤ m → ∀ (L₀ Λ₀ : AddSubgroup K) (Q : Set K), IsLat L₀ → IsLat Λ₀ → IsCompact Q →
    (∀ d ∈ Q, IsUnit d) →
    ∃ L₁ Λ₁ : AddSubgroup K, IsLat L₁ ∧ IsLat Λ₁ ∧ ∃ V ∈ 𝓝 (0 : K),
      ∀ (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ), PhiHyp R (m + 1) L₀ Λ₀ Q Φ →
      ∀ D : Kˣ, (D : K) ∈ Q → ∃ A : (Fin m → K) → ℂ, AmpHyp L₁ Λ₁ A ∧
        (∀ z : Kˣ, z ^ (m + 1) = (-1) ^ m * D → A (fun _ => (z : K)) =
          ((modK R (z : K) ^ (m * (m - 1) / 2) : ℝ) : ℂ) * omPhi R ψ (addBlock h0 (m + 1) z) Φ) ∧
        ∀ t c : Kˣ, (t : K) ∈ V → c * t ^ m = D → ∀ Λ : AddSubgroup K, IsLat Λ →
          LatInvN Λ (fun x : Fin m → K =>
            A x * ψ (g0 (((-1) ^ m * D : Kˣ) : K) x * ((t⁻¹ : Kˣ) : K))) →
          omPhi R ψ (pt2 h0 m t c) Φ = ((((modK R (t : K)) ^ (m * (m + 1) / 2))⁻¹ : ℝ) : ℂ) *
            intK R Λ m (fun x : Fin m → K =>
              A x * ψ (g0 (((-1) ^ m * D : Kˣ) : K) x * ((t⁻¹ : Kˣ) : K)))
def GermPhi : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ m : ℕ, 1 ≤ m → ∀ γ : Kˣ → ℂ, IsGamma R ψ m γ →
    ∀ (L₀ Λ₀ : AddSubgroup K) (Q : Set K), IsLat L₀ → IsLat Λ₀ → IsCompact Q →
    (∀ d ∈ Q, IsUnit d) →
    ∃ V ∈ 𝓝 (0 : K), ∀ (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ),
      PhiHyp R (m + 1) L₀ Λ₀ Q Φ → ∀ t c : Kˣ, (t : K) ∈ V → (c : K) * (t : K) ^ m ∈ Q →
      omPhi R ψ (pt2 h0 m t c) Φ =
        germSum R ψ m γ t c (fun z => omPhi R ψ (addBlock h0 (m + 1) z) Φ)
def GermPhiAssemble : Prop :=
  OscReduction → StationaryPhase → OscInvariant → ModMul → GermPhi
def HeadReduction : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ (m : ℕ) (h : Point K) (Q : Set K), IsCompact Q →
    (∀ d ∈ Q, IsUnit d) →
    ∃ L₀ Λ₀ : AddSubgroup K, IsLat L₀ ∧ IsLat Λ₀ ∧
      ∀ (n' : ℕ) (Z' : Matrix (Fin n') (Fin n') K),
      ∃ Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ, PhiHyp R (m + 1) L₀ Λ₀ Q Φ ∧
        (∀ t c : Kˣ, bbZ R ψ (pt2 h m t c) Z' = omPhi R ψ (pt2 h0 m t c) Φ) ∧
        ∀ z : Kˣ, bbZ R ψ (addBlock h (m + 1) z) Z' = omPhi R ψ (addBlock h0 (m + 1) z) Φ
def Germ : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ m : ℕ, 1 ≤ m → ∀ γ : Kˣ → ℂ, IsGamma R ψ m γ → ∀ (h : Point K) (Q : Set K), IsCompact Q →
    (∀ d ∈ Q, IsUnit d) →
    ∃ V ∈ 𝓝 (0 : K), ∀ t c : Kˣ, (t : K) ∈ V → (c : K) * (t : K) ^ m ∈ Q →
      ∀ (n' : ℕ) (Z' : Matrix (Fin n') (Fin n') K),
      bbZ R ψ (pt2 h m t c) Z' = germSum R ψ m γ t c (fun z => bbZ R ψ (addBlock h (m + 1) z) Z')
def GermAssemble : Prop := HeadReduction → GermPhi → Germ
open Classical in

def KpFromBB : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ w w' : Point K,
      Kp R ψ w w' = ∑ᶠ q : Cos R w', (if IsInt R (orbZ w' (rep R q)) then
        bbZ R ψ w (orbZ w' (rep R q)) else 0) * conj (phase ψ (rep R q))
def KpHerm : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (w w' : Point K),
    Kp R ψ w' w = conj (Kp R ψ w w')
def GermKernel : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ m : ℕ, 1 ≤ m → ∀ γ : Kˣ → ℂ, IsGamma R ψ m γ → ∀ (h : Point K) (Q : Set K), IsCompact Q →
    (∀ d ∈ Q, IsUnit d) →
    ∃ V ∈ 𝓝 (0 : K), ∀ t c : Kˣ, (t : K) ∈ V → (c : K) * (t : K) ^ m ∈ Q → ∀ w' : Point K,
      Kp R ψ (pt2 h m t c) w' = germSum R ψ m γ t c (fun z => Kp R ψ (addBlock h (m + 1) z) w')
def GermKernelAssemble : Prop := Germ → KpFromBB → IntFinite → RootsFinite → GermKernel
def ShiftUnit : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) → ∀ Sg : Finset K,
    ∃ V ∈ 𝓝 (0 : K), ∀ t : Kˣ, (t : K) ∈ V → ∀ σ ∈ Sg,
      IsUnit (((t⁻¹ : Kˣ) : K) + σ) ∧ modK R (((t⁻¹ : Kˣ) : K) + σ) = modK R ((t⁻¹ : Kˣ) : K)
def ShiftSmall : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) → ∀ Sg : Finset K,
    ∀ W ∈ 𝓝 (0 : K), ∃ V ∈ 𝓝 (0 : K), ∀ t t₁ : Kˣ, (t : K) ∈ V → ∀ σ ∈ Sg, IsShift t t₁ σ →
      (t₁ : K) ∈ W
def CutSame : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ m : ℕ, 1 ≤ m → ∀ (Om : Set K) (Sg : Finset K), IsOmega (m + 1) Om →
    ∃ V ∈ 𝓝 (0 : K), ∀ t : Kˣ, (t : K) ∈ V →
      (∀ σ ∈ Sg, ∀ t₁ : Kˣ, IsShift t t₁ σ → cutSet m Om t₁ = cutSet m Om t) ∧
      ∀ c ∈ cutSet m Om t, ∀ r ∈ R, c + r ∈ cutSet m Om t
def RootCorr : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ (m : ℕ) (Sg : Finset K), ∀ E ∈ 𝓝 (0 : K),
    ∃ V ∈ 𝓝 (0 : K), ∀ t t₁ t₂ : Kˣ, (t : K) ∈ V → ∀ σ ∈ Sg, ∀ σ' ∈ Sg, IsShift t t₁ σ →
      IsShift t t₂ σ' → ∃ κ : Kˣ, κ ^ (m + 1) = (t₂ * t₁⁻¹) ^ m ∧ (κ : K) - 1 ∈ E
def SquareNear : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∃ E ∈ 𝓝 (0 : K), ∀ a : Kˣ, (a : K) - 1 ∈ E → ∃ b : Kˣ, a = b ^ 2
def PhaseDiff : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ (m : ℕ) (Om : Set K) (Sg : Finset K), IsCompact Om →
    ∃ E ∈ 𝓝 (0 : K), ∃ V ∈ 𝓝 (0 : K), ∀ t t₁ t₂ κ : Kˣ, (t : K) ∈ V → ∀ σ ∈ Sg, ∀ σ' ∈ Sg,
      IsShift t t₁ σ → IsShift t t₂ σ' → κ ^ (m + 1) = (t₂ * t₁⁻¹) ^ m → (κ : K) - 1 ∈ E →
      ∀ z ∈ Om, ((m + 1 : ℕ) : K) * z * ((t₁⁻¹ : Kˣ) : K) -
        ((m + 1 : ℕ) : K) * ((κ : K) * z) * ((t₂⁻¹ : Kˣ) : K) - z * (σ - σ') ∈ R
def LocConst : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ (s : ℕ) (h : Point K) (Om : Set K), 1 ≤ s → IsCompact Om → (∀ z ∈ Om, IsUnit z) →
    ∃ Λ : AddSubgroup K, IsLat Λ ∧ ∀ z z' : Kˣ, (z : K) ∈ Om → (z' : K) - (z : K) ∈ Λ →
      ∀ w' : Point K, Kp R ψ (addBlock h s z') w' = Kp R ψ (addBlock h s z) w'
open Classical in

def ChangeVar : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ m : ℕ, 1 ≤ m → ∀ (Om : Set K) (Λ : AddSubgroup K), IsOmega (m + 1) Om → IsLat Λ →
    (∀ z ∈ Om, ∀ l ∈ Λ, z + l ∈ Om) → (∀ z ∈ Om, ∀ l ∈ Λ, modK R (z + l) = modK R z) →
    ∃ V ∈ 𝓝 (0 : K), ∀ (t : Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ) (f : K → ℂ), (t : K) ∈ V →
      IsCr R cr → LatInv Λ Om f →
      ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (cr x : K) ∈ cutSet m Om t then
        ∑ᶠ z : Kˣ, if z ^ (m + 1) = (-t) ^ m * cr x then f (z : K) else 0 else 0) =
      (((modK R (t : K) ^ m)⁻¹ * modK R ((m + 1 : ℕ) : K) : ℝ) : ℂ) *
        intLat R Λ Om (fun z => ((modK R z ^ m : ℝ) : ℂ) * f z)
open Classical in

def CrossVanish : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ m : ℕ, 1 ≤ m → ∀ (Om : Set K) (Λ : AddSubgroup K) (Sg : Finset K) (ζ : Kˣ),
    IsOmega (m + 1) Om → IsLat Λ → (∀ z ∈ Om, ∀ l ∈ Λ, z + l ∈ Om) → ζ ^ (m + 1) = 1 → ζ ≠ 1 →
    ∃ E ∈ 𝓝 (0 : K), ∃ V ∈ 𝓝 (0 : K), ∀ (t t₁ t₂ κ : Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ)
      (g : K → ℂ), (t : K) ∈ V → ∀ σ ∈ Sg, ∀ σ' ∈ Sg, IsShift t t₁ σ → IsShift t t₂ σ' →
      κ ^ (m + 1) = (t₂ * t₁⁻¹) ^ m → (κ : K) - 1 ∈ E → IsCr R cr → LatInv Λ Om g →
      (∀ z : Kˣ, (z : K) ∈ Om → g (z : K) ≠ 0 → ((z⁻¹ : Kˣ) : K) - (((ζ * z)⁻¹ : Kˣ) : K) ∈ R) →
      ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (cr x : K) ∈ cutSet m Om t then
        ∑ᶠ z : Kˣ, if z ^ (m + 1) = (-t₁) ^ m * cr x then
          g (z : K) * ψ (((m + 1 : ℕ) : K) * (z : K) * ((t₁⁻¹ : Kˣ) : K) -
            ((m + 1 : ℕ) : K) * ((ζ : K) * (κ : K) * (z : K)) * ((t₂⁻¹ : Kˣ) : K)) else 0
        else 0) = 0
def GermIdentity : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ m : ℕ, 1 ≤ m → ∀ (n₀ : ℕ) (F : Finset (Point K)), (∀ h ∈ F, h.1.sum = n₀) →
    ∀ (Om : Set K) (Sg : Finset K) (Λ : AddSubgroup K), IsOmega (m + 1) Om → IsLat Λ →
    (∀ z ∈ Om, ∀ l ∈ Λ, z + l ∈ Om) →
    (∀ h ∈ F, ∀ h' ∈ F, LatInv Λ Om (NsK R ψ (m + 1) h h')) →
    (∀ σ ∈ Sg, ∀ σ' ∈ Sg, ∀ l ∈ Λ, ψ (l * (σ - σ')) = 1) →
    ∃ V ∈ 𝓝 (0 : K), ∀ (t t₁ t₂ : Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ), (t : K) ∈ V → IsCr R cr →
      ∀ σ ∈ Sg, ∀ σ' ∈ Sg, IsShift t t₁ σ → IsShift t t₂ σ' → ∀ h ∈ F, ∀ h' ∈ F,
      uGram R ψ m cr (cutSet m Om t) h h' t₁ t₂ =
        intLat R Λ Om (fun z => NsK R ψ (m + 1) h h' z * ψ (z * (σ - σ')))
def GermIdentityAssemble : Prop :=
  GaussHess → GermKernel → KpHerm → BlockKernelSupport → ModMul → RootsFinite → ShiftUnit → ShiftSmall →
    CutSame → RootCorr → SquareNear → PhaseDiff → LocConst → ModLocConst → IntLatRefine → ChangeVar →
    CrossVanish → GermIdentity
def CSizeAddBlock : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (h : Point K) (m : ℕ) (t : Kˣ),
      cSize R (addBlock h m t) = cSize R h * ((modK R (t : K)) ^ m)⁻¹
def UGramEq : Prop :=
  SingleBlockParseval → CSizeAddBlock → ModMul →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (m : ℕ) (h h' : Point K) (t t' : Kˣ)
    (cr : K ⧸ R.toAddSubgroup → Kˣ), h.1.sum = h'.1.sum → IsCr R cr →
      uGram R ψ m cr Set.univ h h' t t' =
        ((cSize R h * cSize R h' : ℝ) : ℂ) * Ns R ψ m h h' t t'
def UNormBound : Prop :=
  UGramEq → SingleBlockParseval → CSizeAddBlock → ModMul → LatFinite →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (m n₀ : ℕ) (F : Finset (Point K))
    (Θ : K → Point K → Point K → ℂ), (∀ h ∈ F, h.1.sum = n₀) → ThetaProps R ψ m F Θ →
    ∀ (t : Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ), IsCr R cr →
      IsPSD F (fun h h' => ((cSize R h ^ (m + 1) * cSize R h' ^ (m + 1) : ℝ) : ℂ) * N0 R ψ h h' -
        uGram R ψ m cr Set.univ h h' t t)
def CutPSD : Prop :=
  KpGram → SingleBlockParseval → ModMul →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (m : ℕ) (cr : K ⧸ R.toAddSubgroup → Kˣ) (S : Set K)
    (F : Finset (Point K × Kˣ)), IsCr R cr → (∀ p ∈ F, ∀ p' ∈ F, p.1.1.sum = p'.1.1.sum) →
      IsPSD F (fun p p' => uGram R ψ m cr S p.1 p'.1 p.2 p'.2) ∧
      IsPSD F (fun p p' => uGram R ψ m cr Set.univ p.1 p'.1 p.2 p'.2 -
        uGram R ψ m cr S p.1 p'.1 p.2 p'.2)
def UBlock : Prop :=
  KpBlockDiag → CSizeAddBlock → ModMul →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (m : ℕ) (cr : K ⧸ R.toAddSubgroup → Kˣ) (S : Set K)
    (h h' : Point K) (t t' : Kˣ), modK R (t : K) = modK R (t' : K) →
    modK R (pt h.1 h.2).det ≠ modK R (pt h'.1 h'.2).det → uGram R ψ m cr S h h' t t' = 0
structure AvgData {K : Type} [CommRing K] [TopologicalSpace K] (R : Subring K) (ψ : AddChar K ℂ)
    (s : ℕ) (F : Finset (Point K)) (Om Lc : Set K) where

  L₁ : AddSubgroup K

  L₂ : AddSubgroup K

  A : Finset K

  B : Finset K
  lat₁ : IsLat L₁
  lat₂ : IsLat L₂
  le₁ : L₁ ≤ R.toAddSubgroup
  le₂ : R.toAddSubgroup ≤ L₂
  omPerp : ∀ z ∈ Om, z ∈ perp ψ L₁
  cutPerp : ∀ z ∈ Lc, z ∈ perp ψ L₁
  omStable : ∀ z ∈ Om, ∀ l ∈ perp ψ L₂, z + l ∈ Om
  nsInv : ∀ h ∈ F, ∀ h' ∈ F, LatInv (perp ψ L₂) Om (NsK R ψ s h h')
  repsA : IsReps A L₂ R.toAddSubgroup
  repsB : IsReps B R.toAddSubgroup L₁
def AvgDataExists : Prop :=
  LocConst → KpHerm → ModLocConst → LatChoice → LatFinite →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ (s : ℕ) (F : Finset (Point K)) (Om Lc : Set K), 1 ≤ s → IsOmega s Om → IsCompact Lc →
      Nonempty (AvgData R ψ s F Om Lc)
def CutNormEval : Prop :=
  CharMean → PerpLat →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ (s : ℕ) (F : Finset (Point K)) (Om Lc : Set K)
    (D : AvgData R ψ s F Om Lc), IsCompact Om → ∀ z₁ ∈ Om, ∀ h ∈ F, ∀ h' ∈ F,
      (((D.A.card : ℂ) * (D.B.card : ℂ))⁻¹) ^ 2 *
        ∑ p ∈ D.A ×ˢ D.B, ∑ p' ∈ D.A ×ˢ D.B,
          ψ (-(z₁ * (p.1 + p.2))) * conj (ψ (-(z₁ * (p'.1 + p'.2)))) *
            intLat R (perp ψ D.L₂) Om
              (fun z => NsK R ψ s h h' z * ψ (z * ((p.1 + p.2) - (p'.1 + p'.2)))) =
        (D.A.card : ℂ)⁻¹ * NsK R ψ s h h' z₁
def ThxLower : Prop :=
  GermIdentity → BlockKernelSupport → UGramEq → SingleBlockParseval → CSizeAddBlock → ModMul → CutPSD → KpGram →
  GramRealiseCut → AvgBound → CutNormEval → CharMean → PerpLat →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ m : ℕ, 1 ≤ m → ∀ (n₀ : ℕ) (F : Finset (Point K)) (Om Lc : Set K), (∀ h ∈ F, h.1.sum = n₀) →
    IsOmega (m + 1) Om → ∀ D : AvgData R ψ (m + 1) F Om Lc,
    ∃ V ∈ 𝓝 (0 : K), ∀ (t : Kˣ) (τ : K → Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ), (t : K) ∈ V →
      IsCr R cr → (∀ ρ ∈ D.A, ∀ b ∈ D.B, IsShift t (τ (ρ + b)) (ρ + b)) → ∀ z₁ ∈ Om,
      IsPSD F (fun h h' => thx R ψ m cr D.A D.B τ z₁ h h' - NsK R ψ (m + 1) h h' z₁)
def ThxBasic : Prop :=
  CutPSD → KpGram → SingleBlockParseval → ModMul →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (m n₀ : ℕ) (F : Finset (Point K)) (A B : Finset K)
    (τ : K → Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ), (∀ h ∈ F, h.1.sum = n₀) → IsCr R cr →
    (∀ b ∈ B, b ∈ R) →
      (∀ z, ∀ r ∈ R, thx R ψ m cr A B τ (z + r) = thx R ψ m cr A B τ z) ∧
      ∀ z, IsPSD F (thx R ψ m cr A B τ z)
open Classical in

def ThxSum : Prop :=
  ParsevalGroup → PerpDual → PerpLat → LatFinite → GramRealiseCut → CutPSD → KpGram → SingleBlockParseval →
  ModMul →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ (m s n₀ : ℕ) (F : Finset (Point K)) (Om Lc : Set K)
    (D : AvgData R ψ s F Om Lc) (τ : K → Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ),
    (∀ h ∈ F, h.1.sum = n₀) → IsCr R cr → ∀ h ∈ F, ∀ h' ∈ F,
      ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (Quotient.out x : K) ∈ perp ψ D.L₁ then
        thx R ψ m cr D.A D.B τ (Quotient.out x) h h' else 0) =
      ((D.A.card : ℂ) * (D.B.card : ℂ))⁻¹ * ∑ ρ ∈ D.A, ∑ b ∈ D.B,
        uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b))
def ThetaPropsOn {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (s : ℕ)
    (F : Finset (Point K)) (Lc : Submodule R K) (Om : Set K) (Θ : K → Point K → Point K → ℂ) :
    Prop :=
  (∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) ∧
  (∀ x, IsPSD F (Θ x)) ∧
  (∀ x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0) ∧
  (∀ t : Kˣ, (t : K) ∈ Om → IsPSD F (fun h h' => Θ (t : K) h h' - Ns R ψ s h h' t t)) ∧
  IsPSD F (fun h h' => ((cSize R h ^ s * cSize R h' ^ s : ℝ) : ℂ) * N0 R ψ h h' -
    ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h') ∧
  (∀ x, ∀ h ∈ F, ∀ h' ∈ F, modK R (pt h.1 h.2).det ≠ modK R (pt h'.1 h'.2).det → Θ x h h' = 0)
def IsCutModule {K : Type} [CommRing K] [TopologicalSpace K] (R : Subring K) (ψ : AddChar K ℂ)
    (s : ℕ) (F : Finset (Point K)) (Lc : Submodule R K) : Prop :=
  IsOpen (Lc : Set K) ∧ IsCompact (Lc : Set K) ∧ (∀ r ∈ R, r ∈ Lc) ∧
    ∀ t : Kˣ, (t : K) ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Ns R ψ s h h' t t = 0
def SupportModule : Prop :=
  NsSupport →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ (s : ℕ) (F : Finset (Point K)), 1 ≤ s →
    ∃ Lc : Submodule R K, IsCutModule R ψ s F Lc ∧
      ((∀ h ∈ F, InGLR R h) → ∀ x, x ∈ Lc ↔ x ∈ R)
def CSizeOne : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → ∀ h : Point K, InGLR R h → cSize R h = 1
def ThOm : Prop :=
  A2 → SingleBlockParseval →
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ), LocalDatum K R ψ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) →
    ∀ m : ℕ, 1 ≤ m → ThetaExists R ψ m → ∀ (n₀ : ℕ) (F : Finset (Point K)) (Lc : Submodule R K)
    (Om : Set K), (∀ h ∈ F, h.1.sum = n₀) → IsCutModule R ψ (m + 1) F Lc → IsOmega (m + 1) Om →
      ∃ Θ : K → Point K → Point K → ℂ, ThetaPropsOn R ψ (m + 1) F Lc Om Θ
def ThOmAssemble : Prop :=
  GermIdentity → AvgDataExists → LocConst → KpHerm → ModLocConst → LatChoice → LatFinite →
    ShiftUnit → SmallUnits → UGramEq → UNormBound → CutPSD → UBlock → CSizeAddBlock → ModMul → KpGram →
    KpBlockDiag → GramRealiseCut → AvgBound → ParsevalGroup → PerpDual → PerpLat → CharMean →
    CutNormEval → ThxLower → ThxBasic → ThxSum → ThOm
def ThetaExistenceInductive : Prop :=
  ThOm → SupportModule → NsSupport → CSizeOne → Exhaust → LatFinite → PSDEntryBound → PSDClosed →
    BoundedSubseq → ThetaExistsStep
def ThetaExistenceInductiveFromPieces : Prop :=
  AvgBoundAssemble → GaussHessAssemble → StationaryAssemble → GermPhiAssemble → GermAssemble →
    GermKernelAssemble → GermIdentityAssemble → ThOmAssemble → ThetaExistenceInductive →
  MeanSplit → POrth → OrthNorm → ParsevalGroup → GramRealiseCut → PSDEntryBound → PSDClosed →
  BoundedSubseq → LatFinite → IntLatRefine → IntKRefine → VolScale → PerpLat → CharMean → PerpDual →
  LatChoice → ModLocConst → SmallUnits → SmallModules → RootsFinite → RootsSeparated → Exhaust →
  HessDet → GaussModulus → GaussIndep → GaussAdmSmall →
  NonStationary → MorseLemma → OscReduction → OscInvariant → HeadReduction → KpFromBB → KpHerm →
  ShiftUnit → ShiftSmall → CutSame → RootCorr → SquareNear → PhaseDiff → LocConst → ChangeVar → CrossVanish →
  CSizeAddBlock → UGramEq → UNormBound → CutPSD → UBlock → AvgDataExists → CutNormEval → ThxLower →
  ThxBasic → ThxSum → SupportModule → CSizeOne →
  ModMul → IntFinite → KpGram → KpBlockDiag → NsSupport → ThetaExistsStep
end Formalism.FourierDecayAlt.A6


