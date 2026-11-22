-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
-- name    : Formalism_HermitianCurvature_LevelRecursionCondNeeded
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:11.954337+00:00
-- url     : https://prove2.me/theorems/2f4531c0-d3d6-4e4e-b664-f25d522b6c62
-- title:
--   Level Recursion Cond Needed
-- statement:
--   Definitions and structural lemmas for Level Recursion Cond Needed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/LevelRecursionCondNeeded.lean

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_YangianSpanCharacter_StatementT
import Definitions.Def_Formalism_LatticeTheta_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.F7
open Finset Polynomial
noncomputable section
abbrev Sesq (M : Type) [AddCommGroup M] [Module ℂ M] : Type := M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ
section Defs
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
def evR (P : R[X]) (Y : ℝ) : R := P.eval (algebraMap ℂ R (Y : ℂ))
def Shape (n : ℕ) (A B : R[X]) : Prop := A.Monic ∧ A.natDegree = n ∧ B.degree < n
def vec (A B : R[X]) (Y : ℝ) (X : M) : Fin 2 → M := ![evR A Y • X, evR B Y • X]
def act2 (T : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → M) : Fin 2 → M := fun i => ∑ j, T i j • v j
def pair2 (Ξ : Sesq M) (v v' : Fin 2 → M) : ℂ := ∑ i, Ξ (v i) (v' i)
def IsTopCoeff (W : ℝ → ℂ) (d : ℕ) (c : ℂ) : Prop :=
  ∃ P : ℂ[X], P.natDegree ≤ d ∧ P.coeff d = c ∧ ∀ Y : ℝ, W Y = P.eval (Y : ℂ)
structure Dat (R : Type) [Ring R] where

  A : R[X]

  B : R[X]

  Av : R[X]

  Bv : R[X]

  s : ℂ
def Fw (Ξ : Sesq M) (X X' : M) : List (Dat R × ℝ) → R → R → ℂ
  | [], P, P' => Ξ (P • X) (P' • X')
  | l :: w, P, P' =>
      Fw Ξ X X' w (P * (evR l.1.B l.2 + algebraMap ℂ R l.1.s * evR l.1.A l.2))
          (P' * evR l.1.Av (l.2 + 1)) -
        Fw Ξ X X' w (P * evR l.1.A l.2) (P' * evR l.1.Bv (l.2 + 1))
end Defs
def lagCo {d : ℕ} (y : Fin (d + 1) → ℝ) (j : Fin (d + 1)) : ℝ := ∏ i ∈ univ.erase j, (y j - y i)⁻¹
def PairTop : Prop :=
  ∀ (R M : Type) [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsScalarTower ℂ R M] (Ξ : Sesq M) (P₁ P₂ : R[X]) (a b : ℕ) (h : ℝ) (X X' : M),
    P₁.natDegree ≤ a → P₂.natDegree ≤ b →
    IsTopCoeff (fun Y => Ξ (evR P₁ Y • X) (evR P₂ (Y + h) • X')) (a + b)
      (Ξ (P₁.coeff a • X) (P₂.coeff b • X'))
def JPairing : Prop :=
  ∀ (R M : Type) [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsScalarTower ℂ R M] (Ξ : Sesq M) (A B Av Bv : R[X]) (s : ℂ) (Y Y' : ℝ) (X X' : M),
    pair2 Ξ (act2 (Formalism.YangianSpanCharacter.T.J R * Formalism.YangianSpanCharacter.T.Uinv (A := R) s) (vec A B Y X)) (vec Av Bv Y' X') =
      Ξ ((evR B Y + algebraMap ℂ R s * evR A Y) • X) (evR Av Y' • X') -
        Ξ (evR A Y • X) (evR Bv Y' • X')
def PlaneWaveTop : Prop :=
  ∀ (R M : Type) [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsScalarTower ℂ R M] (Ξ : Sesq M) (n : ℕ) (A B Av Bv : R[X]) (s : ℂ) (X X' : M),
    Shape n A B → Shape n Av Bv →
    IsTopCoeff (fun Y => pair2 Ξ (act2 (Formalism.YangianSpanCharacter.T.J R * Formalism.YangianSpanCharacter.T.Uinv (A := R) s) (vec A B Y X))
      (vec Av Bv (Y + 1) X')) (2 * n) (s * Ξ X X')
def LiftTop : Prop :=
  ∀ (R M : Type) [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsScalarTower ℂ R M] (Ξ : Sesq M) (n s : ℕ) (A B Av Bv A₀ A₀v : R[X]) (e t t' : ℂ) (h : ℝ)
    (X X' : M),
    1 ≤ s → (e = 1 ∨ e = -1) → t ≠ 0 → t' ≠ 0 →
    A.Monic → A.natDegree = n + s → Av.Monic → Av.natDegree = n + s →
    A₀.Monic → A₀.natDegree = n → A₀v.Monic → A₀v.natDegree = n →
    (∀ Y : ℝ, evR B Y • X = (e * t⁻¹) • (evR A₀ Y • X)) →
    (∀ Y : ℝ, evR Bv Y • X' = (e * (starRingEnd ℂ t')⁻¹) • (evR A₀v Y • X')) →
    IsTopCoeff (fun Y => pair2 Ξ (act2 (Formalism.YangianSpanCharacter.T.J R) (vec A B Y X)) (vec Av Bv (Y + h) X'))
      (2 * n + s) (e * (1 / t - 1 / t') * Ξ X X')
def PlaneWaveWord : Prop :=
  ∀ (R M : Type) [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsScalarTower ℂ R M] (Ξ : Sesq M) (n K : ℕ) (dat : Fin K → Dat R)
    (grid : Fin K → Fin (2 * n + 1) → ℝ) (X X' : M),
    (∀ a, Shape n (dat a).A (dat a).B ∧ Shape n (dat a).Av (dat a).Bv) →
    (∀ a, Function.Injective (grid a)) →
    (∏ a, (dat a).s) * Ξ X X' =
      ∑ j : Fin K → Fin (2 * n + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) *
        Fw Ξ X X' (List.ofFn fun a => (dat a, grid a (j a))) 1 1
def LiftWord : Prop :=
  ∀ (R M : Type) [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsScalarTower ℂ R M] (Ξ : Sesq M) (n s K : ℕ) (dat : Fin K → Dat R) (A₀ A₀v : Fin K → R[X])
    (e t t' : Fin K → ℂ) (grid : Fin K → Fin (2 * n + s + 1) → ℝ) (X X' : M),
    1 ≤ s → (∀ a, (dat a).s = 0) → (∀ a, e a = 1 ∨ e a = -1) → (∀ a, t a ≠ 0 ∧ t' a ≠ 0) →
    (∀ a, (dat a).A.Monic ∧ (dat a).A.natDegree = n + s ∧
      (dat a).Av.Monic ∧ (dat a).Av.natDegree = n + s) →
    (∀ a, (A₀ a).Monic ∧ (A₀ a).natDegree = n ∧ (A₀v a).Monic ∧ (A₀v a).natDegree = n) →
    (∀ a (Y : ℝ) (Q Q' : R), Ξ (evR (dat a).B Y • Q • X) (Q' • X') =
      Ξ ((e a * (t a)⁻¹) • evR (A₀ a) Y • Q • X) (Q' • X')) →
    (∀ a (Y : ℝ) (Q Q' : R), Ξ (Q • X) (evR (dat a).Bv Y • Q' • X') =
      Ξ (Q • X) ((e a * (starRingEnd ℂ (t' a))⁻¹) • evR (A₀v a) Y • Q' • X')) →
    (∀ a, Function.Injective (grid a)) →
    (∏ a, e a * (1 / t a - 1 / t' a)) * Ξ X X' =
      ∑ j : Fin K → Fin (2 * n + s + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) *
        Fw Ξ X X' (List.ofFn fun a => (dat a, grid a (j a))) 1 1
def LiftVectorWord : Prop :=
  ∀ (R M V : Type) [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsScalarTower ℂ R M] [AddCommGroup V] [Module ℂ V] (ev : M →ₗ[ℂ] V) (n K : ℕ)
    (G : Fin K → ℝ → R) (A₀ : Fin K → R[X]) (c : Fin K → ℂ) (grid : Fin K → Fin (n + 1) → ℝ)
    (X₀ : M),
    (∀ a, (A₀ a).Monic ∧ (A₀ a).natDegree = n) →
    (∀ a (Y : ℝ) (Q : R), ev (G a Y • Q • X₀) = c a • ev (evR (A₀ a) Y • Q • X₀)) →
    (∀ a, Function.Injective (grid a)) →
    (∏ a, c a) • ev X₀ =
      ∑ j : Fin K → Fin (n + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) •
        ev ((List.ofFn fun a => G a (grid a (j a))).prod • X₀)
def LagrangeLead : Prop :=
  ∀ (d : ℕ) (y : Fin (d + 1) → ℝ), Function.Injective y →
    ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (a : Fin (d + 1) → V),
      a (Fin.last d) = ∑ j, lagCo y j • ∑ k : Fin (d + 1), (y j) ^ (k : ℕ) • a k
def PolyStep {V : Type} [AddCommGroup V] [Module ℂ V] (K d : ℕ) (s : Fin K → ℂ)
    (W : ℕ → (Fin K → ℝ) → V) : Prop :=
  ∀ (a : Fin K) (y : Fin K → ℝ), ∃ c : Fin (d + 1) → V, c (Fin.last d) = s a • W (a : ℕ) y ∧
    ∀ t : ℝ, W ((a : ℕ) + 1) (Function.update y a t) = ∑ k : Fin (d + 1), ((t : ℂ) ^ (k : ℕ)) • c k
def ExtractK : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (K d : ℕ) (s : Fin K → ℂ)
    (W : ℕ → (Fin K → ℝ) → V) (grid : Fin K → Fin (d + 1) → ℝ),
    PolyStep K d s W → (∀ a, Function.Injective (grid a)) → ∀ y₀ : Fin K → ℝ,
    (∏ a, s a) • W 0 y₀ =
      ∑ j : Fin K → Fin (d + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) • W K fun a => grid a (j a)
def ExtractBound : Prop :=
  ∀ (V : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V] (K d : ℕ) (s : Fin K → ℂ)
    (W : ℕ → (Fin K → ℝ) → V) (grid : Fin K → Fin (d + 1) → ℝ),
    PolyStep K d s W → (∀ a, Function.Injective (grid a)) → ∀ (y₀ : Fin K → ℝ) (B : ℝ),
    (∀ j : Fin K → Fin (d + 1), ‖W K fun a => grid a (j a)‖ ≤ B) →
    (∏ a, ‖s a‖) * ‖W 0 y₀‖ ≤ (∏ a, ∑ i, |lagCo (grid a) i|) * B
def thGrid {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (j : Fin K → Fin (d + 1)) : ℝ :=
  ∏ a, (|lagCo (grid a) (j a)| / ∑ i, |lagCo (grid a) i|)
def ExtractProb : Prop :=
  ∀ (V : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V] (K d : ℕ) (s : Fin K → ℂ)
    (W : ℕ → (Fin K → ℝ) → V) (grid : Fin K → Fin (d + 1) → ℝ),
    PolyStep K d s W → (∀ a, Function.Injective (grid a)) → ∀ y₀ : Fin K → ℝ,
    (∀ j, 0 ≤ thGrid grid j) ∧ (∑ j, thGrid grid j) = 1 ∧
    (∏ a, ‖s a‖) * ‖W 0 y₀‖ ≤
      (∏ a, ∑ i, |lagCo (grid a) i|) * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖) ∧
    ((∏ a, ‖s a‖) * ‖W 0 y₀‖) ^ 2 ≤
      (∏ a, ∑ i, |lagCo (grid a) i|) ^ 2 * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖ ^ 2)
def DualWeights : Prop :=
  ∀ (Ls : Type) [Fintype Ls] (ω N N' : Ls → ℝ), (∀ L, 0 ≤ ω L) → (∀ L, 0 ≤ N L) → (∀ L, 0 ≤ N' L) →
    0 < ∑ L, ω L →
    (∑ L, (ω L / (2 * ∑ L', ω L') + ω L / (2 * ∑ L', ω L'))) = 1 ∧
    (∑ L, ω L * √(N L * N' L)) ≤
      (∑ L, ω L) * (∑ L, (ω L / (2 * ∑ L', ω L') * N L + ω L / (2 * ∑ L', ω L') * N' L))
def ExtractCheb : Prop :=
  ∀ (V : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V] (K d : ℕ) (s : Fin K → ℂ)
    (W : ℕ → (Fin K → ℝ) → V) (α β : Fin K → ℝ),
    1 ≤ d → (∀ a, α a < β a) → PolyStep K d s W → ∀ (y₀ : Fin K → ℝ) (B : ℝ),
    (∀ j : Fin K → Fin (d + 1), ‖W K fun a => Formalism.SA.C.chebPt (α a) (β a) d (j a)‖ ≤ B) →
    (∏ a, ‖s a‖) * ‖W 0 y₀‖ ≤ (∏ a, (1 / 2) * (4 / (β a - α a)) ^ d) * B
def PlaneWaveWordCheb : Prop :=
  ∀ (R M : Type) [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsScalarTower ℂ R M] (Ξ : Sesq M) (n K : ℕ) (dat : Fin K → Dat R) (α β : Fin K → ℝ)
    (X X' : M) (B : ℝ),
    1 ≤ n → (∀ a, α a < β a) →
    (∀ a, Shape n (dat a).A (dat a).B ∧ Shape n (dat a).Av (dat a).Bv) →
    (∀ j : Fin K → Fin (2 * n + 1),
      ‖Fw Ξ X X' (List.ofFn fun a => (dat a, Formalism.SA.C.chebPt (α a) (β a) (2 * n) (j a))) 1 1‖ ≤ B) →
    (∏ a, ‖(dat a).s‖) * ‖Ξ X X'‖ ≤ (∏ a, (1 / 2) * (4 / (β a - α a)) ^ (2 * n)) * B
def LiftWordCheb : Prop :=
  ∀ (R M : Type) [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsScalarTower ℂ R M] (Ξ : Sesq M) (n s K : ℕ) (dat : Fin K → Dat R) (A₀ A₀v : Fin K → R[X])
    (e t t' : Fin K → ℂ) (α β : Fin K → ℝ) (X X' : M) (B : ℝ),
    1 ≤ s → (∀ a, (dat a).s = 0) → (∀ a, e a = 1 ∨ e a = -1) → (∀ a, t a ≠ 0 ∧ t' a ≠ 0) →
    (∀ a, (dat a).A.Monic ∧ (dat a).A.natDegree = n + s ∧
      (dat a).Av.Monic ∧ (dat a).Av.natDegree = n + s) →
    (∀ a, (A₀ a).Monic ∧ (A₀ a).natDegree = n ∧ (A₀v a).Monic ∧ (A₀v a).natDegree = n) →
    (∀ a (Y : ℝ) (Q Q' : R), Ξ (evR (dat a).B Y • Q • X) (Q' • X') =
      Ξ ((e a * (t a)⁻¹) • evR (A₀ a) Y • Q • X) (Q' • X')) →
    (∀ a (Y : ℝ) (Q Q' : R), Ξ (Q • X) (evR (dat a).Bv Y • Q' • X') =
      Ξ (Q • X) ((e a * (starRingEnd ℂ (t' a))⁻¹) • evR (A₀v a) Y • Q' • X')) →
    (∀ a, α a < β a) →
    (∀ j : Fin K → Fin (2 * n + s + 1),
      ‖Fw Ξ X X' (List.ofFn fun a => (dat a, Formalism.SA.C.chebPt (α a) (β a) (2 * n + s) (j a))) 1 1‖ ≤ B) →
    (∏ a, ‖1 / t a - 1 / t' a‖) * ‖Ξ X X'‖ ≤ (∏ a, (1 / 2) * (4 / (β a - α a)) ^ (2 * n + s)) * B
def ChebSharp : Prop :=
  ∀ (α β : ℝ) (n : ℕ), α < β → 1 ≤ n →
    Function.Injective (Formalism.SA.C.chebPt α β n) ∧
      ∑ j, |lagCo (Formalism.SA.C.chebPt α β n) j| = (1 / 2) * (4 / (β - α)) ^ n
def ChebCoValue : Prop :=
  ∀ (α β : ℝ) (n : ℕ), α < β → 1 ≤ n → ∀ j : Fin (n + 1),
    lagCo (Formalism.SA.C.chebPt α β n) j =
      (-1) ^ (j : ℕ) * (if (j : ℕ) = 0 ∨ (j : ℕ) = n then 1 / 2 else 1) *
        ((2 : ℝ) ^ (n - 1) / n) * (2 / (β - α)) ^ n
def ChebAttained : Prop :=
  ∀ (α β : ℝ) (n : ℕ), α < β → 1 ≤ n →
    let W : ℝ[X] := (Chebyshev.T ℝ n).comp (C (2 / (β - α)) * X - C ((α + β) / (β - α)))
    W.natDegree = n ∧ W.coeff n = (1 / 2) * (4 / (β - α)) ^ n ∧
      (∀ j : Fin (n + 1), W.eval (Formalism.SA.C.chebPt α β n j) = (-1) ^ (j : ℕ)) ∧
      ∀ Y ∈ Set.Icc α β, |W.eval Y| ≤ 1
def ChebLeadBound : Prop :=
  ∀ (V : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V] (α β : ℝ) (n : ℕ) (a : Fin (n + 1) → V)
    (B : ℝ), α < β → 1 ≤ n →
    (∀ j, ‖∑ k : Fin (n + 1), ((Formalism.SA.C.chebPt α β n j : ℂ) ^ (k : ℕ)) • a k‖ ≤ B) →
    ‖a (Fin.last n)‖ ≤ (1 / 2) * (4 / (β - α)) ^ n * B
def ChebSpacing : Prop :=
  ∀ (α β : ℝ) (n : ℕ), α < β → 1 ≤ n → ∀ j : Fin n,
    (β - α) / (n : ℝ) ^ 2 ≤ |Formalism.SA.C.chebPt α β n j.succ - Formalism.SA.C.chebPt α β n j.castSucc|
def EquiCo : Prop :=
  ∀ (n : ℕ) (y₀ h : ℝ), 0 < h →
    ∑ j : Fin (n + 1), |lagCo (fun i : Fin (n + 1) => y₀ + (i : ℕ) * h) j| = (2 / h) ^ n / (n.factorial : ℝ)
def EquiCoBound : Prop :=
  ∀ (n : ℕ) (L : ℝ), 1 ≤ n → (n : ℝ) ≤ L →
    (2 / ((⌊L / (n : ℝ)⌋ : ℤ) : ℝ)) ^ n / (n.factorial : ℝ) ≤ (4 * Real.exp 1 / L) ^ n
def SchurTwo : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (G : Type) [AddCommGroup G]
    (La : AddSubgroup G) (ι PP : Type) [Fintype PP] (T : Finset ι) (τ : ι → G) (V : ι → H)
    (P : ι → ι → PP) (φ : PP → G → ℝ) (a b : PP → ι → ℝ) (ε : ℝ),
    Set.InjOn τ T → (∀ t ∈ T, ∀ t' ∈ T, τ t - τ t' ∈ La) →
    (∀ p, ∀ l ∈ La, 0 ≤ φ p l) →
    (∀ p, ∀ S : Finset G, (∀ l ∈ S, l ∈ La ∧ l ≠ 0) → ∑ l ∈ S, φ p l ≤ ε) →
    (∀ p, ∀ t ∈ T, 0 ≤ a p t ∧ 0 ≤ b p t) →
    (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
      ‖inner ℂ (V t) (V t')‖ ≤ φ (P t t') (τ t - τ t') * ((a (P t t') t + b (P t t') t') / 2)) →
    ‖∑ t ∈ T, V t‖ ^ 2 ≤ (∑ t ∈ T, ‖V t‖ ^ 2) + ε * (∑ p, ∑ t ∈ T, (a p t + b p t) / 2)
def SchurLattice : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (G : Type) [AddCommGroup G]
    (La : AddSubgroup G) (ι PP : Type) [Fintype PP] (T : Finset ι) (τ : ι → G) (V : ι → H)
    (P : ι → ι → PP) (φ : PP → G → ℝ) (a : PP → ι → ℝ) (ε : ℝ),
    Set.InjOn τ T → (∀ t ∈ T, ∀ t' ∈ T, τ t - τ t' ∈ La) →
    (∀ p, ∀ l ∈ La, 0 ≤ φ p l) →
    (∀ p, ∀ S : Finset G, (∀ l ∈ S, l ∈ La ∧ l ≠ 0) → ∑ l ∈ S, φ p l ≤ ε) →
    (∀ p, ∀ t ∈ T, 0 ≤ a p t) →
    (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
      ‖inner ℂ (V t) (V t')‖ ≤ φ (P t t') (τ t - τ t') * ((a (P t t') t + a (P t t') t') / 2)) →
    ‖∑ t ∈ T, V t‖ ^ 2 ≤ (∑ t ∈ T, ‖V t‖ ^ 2) + ε * (∑ t ∈ T, ∑ p, a p t) ∧
    ∀ (f : ℕ) (m : ι → ℝ), Fintype.card PP ≤ 3 ^ f → 0 ≤ ε → (∀ t ∈ T, 0 ≤ m t) →
      (∀ p, ∀ t ∈ T, a p t ≤ m t) →
      (∑ t ∈ T, ‖V t‖ ^ 2) + ε * (∑ t ∈ T, ∑ p, a p t) ≤
        (∑ t ∈ T, ‖V t‖ ^ 2) + (3 : ℝ) ^ f * ε * (∑ t ∈ T, m t)
def SchurWords : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (G : Type) [AddCommGroup G]
    (La : AddSubgroup G) (ι PP Wd : Type) [Fintype PP] [Fintype Wd] (T : Finset ι) (τ : ι → G)
    (V : ι → H) (P : ι → ι → PP) (φ : PP → G → ℝ) (θ θ' : PP → Wd → ℝ) (N : Wd → ι → ℝ) (ε D : ℝ),
    Set.InjOn τ T → (∀ t ∈ T, ∀ t' ∈ T, τ t - τ t' ∈ La) →
    (∀ p, ∀ l ∈ La, 0 ≤ φ p l) →
    (∀ p, ∀ S : Finset G, (∀ l ∈ S, l ∈ La ∧ l ≠ 0) → ∑ l ∈ S, φ p l ≤ ε) →
    (∀ p, (∀ w, 0 ≤ θ p w) ∧ (∑ w, θ p w) = 1 ∧ (∀ w, 0 ≤ θ' p w) ∧ (∑ w, θ' p w) = 1) →
    (∀ w, ∀ t ∈ T, 0 ≤ N w t) → (∀ w, ∑ t ∈ T, N w t ≤ D) →
    (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
      ‖inner ℂ (V t) (V t')‖ ≤ φ (P t t') (τ t - τ t') *
        (((∑ w, θ (P t t') w * N w t) + (∑ w, θ' (P t t') w * N w t')) / 2)) →
    ‖∑ t ∈ T, V t‖ ^ 2 ≤ (∑ t ∈ T, ‖V t‖ ^ 2) + (Fintype.card PP : ℝ) * ε * D
def LevelRecursionLS : Prop :=
  ∀ (r : ℕ) (ε δ : ℝ) (e a : ℕ → ℝ), 0 ≤ ε → 0 ≤ δ → δ ≤ 1 / 2 → (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ a i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      a i ≤ √(1 + e i) * ((1 + ε) * a (i - 1) + ∑ s ∈ Icc 2 i, δ ^ (s - 1) * a (i - s))) →
    (∀ i ≤ r + 1, a i ≤ (1 + (ε + 2 * δ)) ^ i * (∏ l ∈ Icc 1 i, √(1 + e l)) * a 0) ∧
    (((r : ℝ) + 1) * (ε + 2 * δ) ≤ 1 / 2 →
      a (r + 1) ^ 2 ≤
        (1 + 4 * ((r : ℝ) + 1) * (ε + 2 * δ)) * (∏ l ∈ Icc 1 (r + 1), (1 + e l)) * a 0 ^ 2)
def LevelRecursion : Prop :=
  ∀ (r : ℕ) (ε δ : ℝ) (e a : ℕ → ℝ), 0 ≤ ε → 0 ≤ δ → δ ≤ 1 / 2 → (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ a i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      a i ≤ (1 + ε) * √(1 + e i) * a (i - 1) + ∑ s ∈ Icc 2 i, δ ^ (s - 1) * a (i - s)) →
    (∀ i ≤ r + 1, a i ≤ (1 + (ε + 2 * δ)) ^ i * (∏ l ∈ Icc 1 i, √(1 + e l)) * a 0) ∧
    (((r : ℝ) + 1) * (ε + 2 * δ) ≤ 1 / 2 →
      a (r + 1) ^ 2 ≤
        (1 + 4 * ((r : ℝ) + 1) * (ε + 2 * δ)) * (∏ l ∈ Icc 1 (r + 1), (1 + e l)) * a 0 ^ 2)
def LevelRecursionCondNeeded : Prop :=
  ¬ ∀ (r : ℕ) (ε δ : ℝ) (e a : ℕ → ℝ), 0 ≤ ε → 0 ≤ δ → δ ≤ 1 / 2 → (∀ i, 0 ≤ e i) →
    (∀ i, e i ≤ 1) → (∀ i, 0 ≤ a i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      a i ≤ (1 + ε) * √(1 + e i) * a (i - 1) + ∑ s ∈ Icc 2 i, δ ^ (s - 1) * a (i - s)) →
    ((r : ℝ) + 1) * (ε + 2 * δ) ≤ 1 →
      a (r + 1) ^ 2 ≤
        (1 + 4 * ((r : ℝ) + 1) * (ε + 2 * δ)) * (∏ l ∈ Icc 1 (r + 1), (1 + e l)) * a 0 ^ 2
def ChoiceOfConstants : Prop :=
  ∀ (C₁ CE C' C Θ Kx : ℝ) (f r : ℕ), 0 < C₁ → 0 < CE → 1 ≤ f → 4 ≤ Kx →
    8 * (C₁ + CE) ≤ C' → 12 * (C₁ + CE) ≤ C → C' ≤ Θ → 1 ≤ Θ → (r : ℝ) * (C / Θ) ^ f ≤ 1 →
    (C₁ / Θ) ^ f ≤ (1 / 8) ^ f ∧ (C₁ / Θ) ^ f ≤ 1 / 8 ∧
    (CE * Θ ^ (-(Kx - 5 / 2))) ^ f ≤ (CE / Θ) ^ f ∧
    (CE * Θ ^ (-(Kx - 5 / 2))) ^ f + 2 * (C₁ / Θ) ^ f ≤ 3 * ((C₁ + CE) / Θ) ^ f ∧
    ((r : ℝ) + 1) * ((CE * Θ ^ (-(Kx - 5 / 2))) ^ f + 2 * (C₁ / Θ) ^ f) ≤ 1 / 2
def TheoremAConstants : Prop :=
  ∀ (C₁ CE C' C Θ Kx : ℝ) (f r : ℕ) (e a : ℕ → ℝ), 0 < C₁ → 0 < CE → 1 ≤ f → 4 ≤ Kx →
    8 * (C₁ + CE) ≤ C' → 12 * (C₁ + CE) ≤ C → C' ≤ Θ → 1 ≤ Θ → (r : ℝ) * (C / Θ) ^ f ≤ 1 →
    (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ a i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      a i ≤ (1 + (CE * Θ ^ (-(Kx - 5 / 2))) ^ f) * √(1 + e i) * a (i - 1) +
        ∑ s ∈ Icc 2 i, (C₁ / Θ) ^ (f * (s - 1)) * √(1 + e i) * a (i - s)) →
    a (r + 1) ^ 2 ≤
      (1 + 12 * ((r : ℝ) + 1) * ((C₁ + CE) / Θ) ^ f) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * a 0 ^ 2
section Poisson
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace
def PoissonAt {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (φ : V → ℂ) (x : V) : Prop :=
  Summable (fun μ : dual Λ =>
      (𝓕 φ : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) ∧
  HasSum (fun l : Λ => φ ((l : V) + x))
    ((ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ,
      (𝓕 φ : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)))
def poissonBound {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (φ : V → ℝ) : ℝ :=
  (ZLattice.covolume Λ)⁻¹ * (((𝓕 (fun v => (φ v : ℂ)) : V → ℂ) 0).re +
    ∑' μ : {μ : dual Λ // μ ≠ 0}, ‖(𝓕 (fun v => (φ v : ℂ)) : V → ℂ) (μ : dual Λ)‖)
def PoissonStep : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (φ : V → ℝ) (x : V),
    PoissonAt Λ (fun v => (φ v : ℂ)) x → (∀ l : Λ, 0 ≤ φ ((l : V) + x)) →
    ∀ S : Finset Λ, ∑ l ∈ S, φ ((l : V) + x) ≤ poissonBound Λ φ
def PoissonStepDecay : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V], Formalism.H.PoissonDecay V →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (φ : V → ℝ) (b : ℝ) (x : V),
    Continuous φ → (Module.finrank ℝ V : ℝ) < b →
    (fun v => (φ v : ℂ)) =O[Filter.cocompact V] (fun v => ‖v‖ ^ (-b)) →
    (𝓕 (fun v => (φ v : ℂ)) : V → ℂ) =O[Filter.cocompact V] (fun v => ‖v‖ ^ (-b)) →
    (∀ l : Λ, 0 ≤ φ ((l : V) + x)) →
    ∀ S : Finset Λ, ∑ l ∈ S, φ ((l : V) + x) ≤ poissonBound Λ φ
def LocSummable {V : Type} [NormedAddCommGroup V] (Λ : Submodule ℤ V) (φ : V → ℂ) : Prop :=
  ∀ Kc : Set V, IsCompact Kc → ∃ b : Λ → ℝ, Summable b ∧ ∀ (l : Λ), ∀ x ∈ Kc, ‖φ ((l : V) + x)‖ ≤ b l
def PoissonSummable : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (φ : V → ℂ),
    Continuous φ → LocSummable Λ φ → Summable (fun μ : dual Λ => ‖(𝓕 φ : V → ℂ) μ‖) →
    ∀ x : V, PoissonAt Λ φ x
def ProductDecaySummable : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (ι : Type) [Fintype ι] (π : ι → V →L[ℝ] ℂ), (Function.Bijective fun (c : V) (v : ι) => π v c) →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (φ : V → ℂ) (C : ℝ),
    (∀ c, ‖φ c‖ ≤ C * ∏ v, ((1 + ‖π v c‖) ^ 3)⁻¹) → LocSummable Λ φ
def PoissonStepText : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] (ι : Type) [Fintype ι] (π : ι → V →L[ℝ] ℂ),
    (Function.Bijective fun (c : V) (v : ι) => π v c) →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (φ : V → ℝ) (C : ℝ) (x : V),
    Continuous φ → (∀ c, |φ c| ≤ C * ∏ v, ((1 + ‖π v c‖) ^ 3)⁻¹) →
    Summable (fun μ : dual Λ => ‖(𝓕 (fun v => (φ v : ℂ)) : V → ℂ) μ‖) →
    (∀ l : Λ, 0 ≤ φ ((l : V) + x)) →
    PoissonAt Λ (fun v => (φ v : ℂ)) x ∧
      ∀ S : Finset Λ, ∑ l ∈ S, φ ((l : V) + x) ≤ poissonBound Λ φ
end Poisson
structure WLetter (K : Type) where

  plus : Bool

  pt : K

  first : Bool
section Weights
variable {K : Type} [Field K]
def qW (q : K → K) : List (WLetter K) → K → K
  | [], Y => q Y
  | l :: w, Y => qW q w Y *
      (if l.plus then (Y - l.pt + 1) / (Y - l.pt) else (l.pt - Y) / (l.pt - Y - 1))
def xW (x : K → K) : List (WLetter K) → K → K
  | [], Y => x Y
  | l :: w, Y => xW x w Y *
      (if l.first then
        (if l.plus then (Y - l.pt) / (Y - l.pt - 1) else (l.pt - Y) / (l.pt - Y - 1)) else 1)
def wFactor (l : WLetter K) (Y : K) : K :=
  if l.plus then (if l.first then 1 else (Y - l.pt + 1) / (Y - l.pt))
  else (if l.first then 1 - 1 / (l.pt - Y - 1) ^ 2 else (l.pt - Y) / (l.pt - Y - 1))
def OffPoles (l : WLetter K) (Y : K) : Prop :=
  if l.plus then Y - l.pt ≠ 0 ∧ Y - l.pt ≠ -1 else l.pt - Y ≠ 1 ∧ l.pt - Y ≠ 2
end Weights
def WordWeight : Prop :=
  ∀ (K : Type) [Field K] (q x : K → K) (w : List (WLetter K)) (Y : K), (∀ l ∈ w, OffPoles l Y) →
    qW q w Y / xW x w (Y + 1) = q Y / x (Y + 1) * (w.map fun l => wFactor l Y).prod
def PlusUnchanged : Prop :=
  ∀ (K : Type) [Field K] (q x : K → K) (w : List (WLetter K)) (Y : K), (∀ l ∈ w, OffPoles l Y) →
    (∀ l ∈ w, l.plus = true ∧ l.first = true) → qW q w Y / xW x w (Y + 1) = q Y / x (Y + 1)
def AllFirstWeight : Prop :=
  ∀ (K : Type) [Field K] (q x : K → K) (w : List (WLetter K)) (Y : K), (∀ l ∈ w, OffPoles l Y) →
    (∀ l ∈ w, l.first = true) →
    qW q w Y / xW x w (Y + 1) =
      q Y / x (Y + 1) * ((w.filter fun l => !l.plus).map fun l => 1 - 1 / (l.pt - Y - 1) ^ 2).prod
def WeightBounds : Prop :=
  ∀ (N : ℕ) (w : List (WLetter ℝ)) (Y : ℝ), 2 ≤ N → w.length ≤ N →
    (∀ l ∈ w, (N : ℝ) ^ 2 ≤ |Y - l.pt|) →
    1 - 1 / (N : ℝ) ≤ (w.map fun l => wFactor l Y).prod ∧
      (w.map fun l => wFactor l Y).prod ≤ 1 + 3 / (N : ℝ)
def AllFirstBounds : Prop :=
  ∀ (N : ℕ) (w : List (WLetter ℝ)) (Y : ℝ), 2 ≤ N → w.length ≤ N →
    (∀ l ∈ w, (N : ℝ) ^ 2 ≤ |Y - l.pt|) → (∀ l ∈ w, l.first = true) →
    1 - 2 / (N : ℝ) ^ 3 ≤ (w.map fun l => wFactor l Y).prod ∧
      (w.map fun l => wFactor l Y).prod ≤ 1
end
end Formalism.FourierDecayAlt.F7


