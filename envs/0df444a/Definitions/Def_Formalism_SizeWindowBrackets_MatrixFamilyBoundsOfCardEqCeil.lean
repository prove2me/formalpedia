-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
-- name    : Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:21.31501+00:00
-- url     : https://prove2.me/theorems/00b07c34-571b-4153-b0e9-c1c25f470cae
-- title:
--   Matrix Family Bounds Of Card Eq Ceil
-- statement:
--   Definitions and structural lemmas for Matrix Family Bounds Of Card Eq Ceil, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/MatrixFamilyBoundsOfCardEqCeil.lean

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module NumberField
open scoped ComplexOrder
namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
def IsUni {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (V : Matrix m n ℂ) : Prop :=
  Vᴴ * V = 1 ∧ V * Vᴴ = 1
def Btwist {ι : Type} {D D' : ℕ} {d : ι → ℕ} (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (c : ι → ℂ)
    (V : Matrix (Fin D') (Fin D) ℂ) (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ) :
    ∀ u, Matrix (Fin D') (Fin (d u)) ℂ :=
  fun u => c u • (V * B u * U u)
def gaTw {ι : Type} (ga : ι → ℝ) (c : ι → ℂ) : ι → ℝ :=
  fun u => ga u / ‖c u‖ ^ 2
def phase {ι : Type} (c : ι → ℂ) (u u' : ι) : ℂ :=
  (starRingEnd ℂ (c u) * c u') / ((‖c u‖ * ‖c u'‖ : ℝ) : ℂ)
def Gram {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (Y⁻¹)ᴴ * Y⁻¹
def Bin {ι : Type} {D : ℕ} {d : ι → ℕ} (A : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (Y' : Matrix (Fin D) (Fin D) ℂ) (Y : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ) :
    ∀ u, Matrix (Fin D) (Fin (d u)) ℂ :=
  fun u => Y'⁻¹ * A u * Y u
def adjG {D n : ℕ} (A : Matrix (Fin D) (Fin n) ℂ) (Y' : Matrix (Fin D) (Fin D) ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin D) ℂ :=
  (Gram Y)⁻¹ * Aᴴ * Gram Y'
def OrthFrame {Dall D D1 : ℕ} (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) :
    Prop :=
  Jᴴ * J = 1 ∧ J1ᴴ * J1 = 1 ∧ J * Jᴴ + J1 * J1ᴴ = 1
def Wfr {Dall D D1 : ℕ} (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) :
    Matrix (Fin (D + D1)) (Fin Dall) ℂ :=
  (Matrix.fromRows Jᴴ J1ᴴ).submatrix finSumFinEquiv.symm id
def Brow {ι : Type} {D D' : ℕ} {d : ι → ℕ} (W : Matrix (Fin D') (Fin D) ℂ)
    (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) : ∀ u, Matrix (Fin D') (Fin (d u)) ℂ :=
  fun u => W * B u
def UniSquare : Prop :=
  ∀ (n : ℕ) (V : Matrix (Fin n) (Fin n) ℂ),
    (IsUni V ↔ V ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧ (IsUni V ↔ Vᴴ * V = 1)
def UniDim : Prop :=
  ∀ (m n : ℕ) (V : Matrix (Fin m) (Fin n) ℂ), IsUni V → m = n
def HsUni : Prop :=
  ∀ (a b a' b' : ℕ) (M : Matrix (Fin a) (Fin b) ℂ) (S : Matrix (Fin a') (Fin a) ℂ)
    (T : Matrix (Fin b) (Fin b') ℂ), Sᴴ * S = 1 → T * Tᴴ = 1 → hsSq (S * M * T) = hsSq M
def TwKp : Prop :=
  ∀ (ι : Type) [Fintype ι] (D D' : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin D') (Fin D) ℂ)
    (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ),
    (∀ u, c u ≠ 0) → IsUni V →
    ∀ u u', Kp (Btwist B c V U) (gaTw ga c) u u' = phase c u u' • ((U u)ᴴ * Kp B ga u u' * U u') ∧
      ‖phase c u u'‖ = 1 ∧ phase c u u = 1
def TwKd : Prop :=
  ∀ (ι : Type) [Fintype ι] (D D' : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin D') (Fin D) ℂ)
    (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ),
    (∀ u, c u ≠ 0) → IsUni V → (∀ u, IsUni (U u)) →
    ∀ u, Kd (Btwist B c V U) (gaTw ga c) u = (U u)ᴴ * Kd B ga u * U u ∧
      Kd (Btwist B c V U) (gaTw ga c) u - 1 = (U u)ᴴ * (Kd B ga u - 1) * U u
def TwHS : Prop :=
  ∀ (ι : Type) [Fintype ι] (D D' : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin D') (Fin D) ℂ)
    (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ),
    (∀ u, c u ≠ 0) → IsUni V → (∀ u, IsUni (U u)) →
    (∀ u u', hsSq (Kp (Btwist B c V U) (gaTw ga c) u u') = hsSq (Kp B ga u u')) ∧
    (∀ u, hsSq (Kd (Btwist B c V U) (gaTw ga c) u - 1) = hsSq (Kd B ga u - 1))
def TwQ : Prop :=
  ∀ (ι : Type) [Fintype ι] (D D' : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin D') (Fin D) ℂ)
    (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ),
    (∀ u, c u ≠ 0) → IsUni V → (∀ u, IsUni (U u)) →
    Qm (Btwist B c V U) (gaTw ga c) = V * Qm B ga * Vᴴ ∧
    (Qm (Btwist B c V U) (gaTw ga c)).trace = (Qm B ga).trace ∧
    (Qm (Btwist B c V U) (gaTw ga c) * Qm (Btwist B c V U) (gaTw ga c)).trace
      = (Qm B ga * Qm B ga).trace
def TwInv : Prop :=
  ∀ (ι : Type) [Fintype ι] (D D' : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin D') (Fin D) ℂ)
    (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ),
    (∀ u, c u ≠ 0) → IsUni V → (∀ u, IsUni (U u)) →
    (∀ u, 0 < gaTw ga c u ↔ 0 < ga u) ∧
    (∀ η, F1 (Btwist B c V U) (gaTw ga c) η ↔ F1 B ga η) ∧
    (∀ e, F2 (Btwist B c V U) (gaTw ga c) e ↔ F2 B ga e) ∧
    (∀ Dstar η0 η1 e0, InputS (Btwist B c V U) (gaTw ga c) Dstar η0 η1 e0 ↔
      InputS B ga Dstar η0 η1 e0)
def RowUnitaryOne : Prop :=
  ∃ (B : ∀ _u : Fin 2, Matrix (Fin 2) (Fin 1) ℂ) (Vu : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ u, IsUni (Vu u)) ∧
    F1 (d := fun _ => 1) B (fun _ => 1) 0 ∧ F2 (d := fun _ => 1) B (fun _ => 1) 0 ∧
    F2 (d := fun _ => 1) (fun u => Vu u * B u) (fun _ => 1) 0 ∧
    ∀ η : ℝ, η < 1 → ¬ F1 (d := fun _ => 1) (fun u => Vu u * B u) (fun _ => 1) η
def GramAny : Prop :=
  ∀ (n : ℕ), (∀ G : Matrix (Fin n) (Fin n) ℂ, G.PosDef → ∃ Y, IsUnit Y.det ∧ Gram Y = G) ∧
    (∀ Y : Matrix (Fin n) (Fin n) ℂ, IsUnit Y.det → (Gram Y).PosDef) ∧
    (∀ (Y : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ),
      star x ⬝ᵥ (Gram Y *ᵥ y) = star (Y⁻¹ *ᵥ x) ⬝ᵥ (Y⁻¹ *ᵥ y))
def HsInner : Prop :=
  ∀ (m n : ℕ) (T : Matrix (Fin m) (Fin n) ℂ) (Y2 : Matrix (Fin m) (Fin m) ℂ)
    (Y1 : Matrix (Fin n) (Fin n) ℂ), IsUnit Y2.det → IsUnit Y1.det →
    (adjG T Y2 Y1 * T).trace = ((hsSq (Y2⁻¹ * T * Y1) : ℝ) : ℂ)
def InnerModel : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (A : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (Y' : Matrix (Fin D) (Fin D) ℂ) (Y : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ) (ga : ι → ℝ),
    IsUnit Y'.det → (∀ u, IsUnit (Y u).det) →
    (∀ u (x : Fin (d u) → ℂ) (y : Fin D → ℂ),
      star (A u *ᵥ x) ⬝ᵥ (Gram Y' *ᵥ y) = star x ⬝ᵥ (Gram (Y u) *ᵥ (adjG (A u) Y' (Y u) *ᵥ y))) ∧
    (∀ u u', (Bin A Y' Y u)ᴴ * Bin A Y' Y u' = (Y u)⁻¹ * (adjG (A u) Y' (Y u) * A u') * Y u') ∧
    (∀ u, Bin A Y' Y u * (Bin A Y' Y u)ᴴ = Y'⁻¹ * (A u * adjG (A u) Y' (Y u)) * Y') ∧
    Qm (Bin A Y' Y) ga = Y'⁻¹ * (∑ u, ((ga u : ℝ) : ℂ) • (A u * adjG (A u) Y' (Y u))) * Y' ∧
    (Qm (Bin A Y' Y) ga).trace = (∑ u, ((ga u : ℝ) : ℂ) • (A u * adjG (A u) Y' (Y u))).trace ∧
    (Qm (Bin A Y' Y) ga * Qm (Bin A Y' Y) ga).trace
      = ((∑ u, ((ga u : ℝ) : ℂ) • (A u * adjG (A u) Y' (Y u))) *
         (∑ u, ((ga u : ℝ) : ℂ) • (A u * adjG (A u) Y' (Y u)))).trace
def GramOnly : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (A : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (Y1' Y2' : Matrix (Fin D) (Fin D) ℂ) (Y1 Y2 : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ)
    (ga : ι → ℝ),
    IsUnit Y1'.det → IsUnit Y2'.det → (∀ u, IsUnit (Y1 u).det) → (∀ u, IsUnit (Y2 u).det) →
    Gram Y1' = Gram Y2' → (∀ u, Gram (Y1 u) = Gram (Y2 u)) →
    IsUni (Y2'⁻¹ * Y1') ∧ (∀ u, IsUni ((Y1 u)⁻¹ * Y2 u)) ∧
    Bin A Y2' Y2 = Btwist (Bin A Y1' Y1) (fun _ => 1) (Y2'⁻¹ * Y1') (fun u => (Y1 u)⁻¹ * Y2 u) ∧
    (∀ η, F1 (Bin A Y2' Y2) ga η ↔ F1 (Bin A Y1' Y1) ga η) ∧
    (∀ e, F2 (Bin A Y2' Y2) ga e ↔ F2 (Bin A Y1' Y1) ga e) ∧
    (∀ Dstar η0 η1 e0, InputS (Bin A Y2' Y2) ga Dstar η0 η1 e0 ↔
      InputS (Bin A Y1' Y1) ga Dstar η0 η1 e0)
def BasisFree : Prop :=
  ∀ (ι : Type) (D : ℕ) (d : ι → ℕ) (A : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (P' Y' : Matrix (Fin D) (Fin D) ℂ) (P Y : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ),
    IsUnit P'.det → IsUnit Y'.det → (∀ u, IsUnit (P u).det) → (∀ u, IsUnit (Y u).det) →
    IsUnit (P'⁻¹ * Y').det ∧ (∀ u, IsUnit ((P u)⁻¹ * Y u).det) ∧
    Gram (P'⁻¹ * Y') = P'ᴴ * Gram Y' * P' ∧ (∀ u, Gram ((P u)⁻¹ * Y u) = (P u)ᴴ * Gram (Y u) * P u) ∧
    Bin (fun u => P'⁻¹ * A u * P u) (P'⁻¹ * Y') (fun u => (P u)⁻¹ * Y u) = Bin A Y' Y
def TwAsInner : Prop :=
  ∀ (ι : Type) (D : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (c : ι → ℂ)
    (V : Matrix (Fin D) (Fin D) ℂ) (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ),
    (∀ u, c u ≠ 0) → IsUni V → (∀ u, IsUni (U u)) →
    IsUnit V.det ∧ (∀ u, IsUnit ((U u)ᴴ).det) ∧ (∀ u, IsUnit ((c u)⁻¹ • (U u)ᴴ).det) ∧
    Gram V = 1 ∧ (∀ u, Gram ((U u)ᴴ) = 1) ∧
    (∀ u, Gram ((c u)⁻¹ • (U u)ᴴ) = (((‖c u‖ ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin (d u)) (Fin (d u)) ℂ)) ∧
    Bin (Btwist B c V U) V (fun u => (c u)⁻¹ • (U u)ᴴ) = B ∧
    Bin (Btwist B c V U) V (fun u => (U u)ᴴ) = fun u => c u • B u
def FullRankSpan : Prop :=
  ∀ (O K W : Type) [CommRing O] [Field K] [Algebra O K] [AddCommGroup W] [Module K W] [Module O W]
    [IsScalarTower O K W] [FiniteDimensional K W] (M N : Submodule O W), N ≤ M →
    finrank K (Submodule.span K (N : Set W)) = finrank K (Submodule.span K (M : Set W)) →
    Submodule.span K (N : Set W) = Submodule.span K (M : Set W)
def FullRankMultiple : Prop :=
  ∀ (O K W : Type) [CommRing O] [Field K] [Algebra O K] [AddCommGroup W] [Module K W] [Module O W]
    [IsScalarTower O K W] (M N : Submodule O W) (a : K), N ≤ M → a ≠ 0 →
    (∀ x ∈ M, a • x ∈ N) →
    Submodule.span K (N : Set W) = Submodule.span K (M : Set W)
def RowsCount : Prop :=
  ∀ (Dall D : ℕ) (del : ℝ), del < 1 →
    ((1 - del) * (Dall : ℝ) ≤ (D : ℝ) ↔ (Dall : ℝ) ≤ (D : ℝ) / (1 - del))
def FrameFacts : Prop :=
  ∀ (Dall D D1 : ℕ) (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ),
    OrthFrame J J1 →
    Jᴴ * J1 = 0 ∧ J1ᴴ * J = 0 ∧ Dall = D + D1 ∧
    (J * Jᴴ)ᴴ = J * Jᴴ ∧ (J * Jᴴ) * (J * Jᴴ) = J * Jᴴ ∧ (J * Jᴴ) * (J1 * J1ᴴ) = 0 ∧
    IsUni (Wfr J J1) ∧
    Wfr J J1 * (J * Jᴴ) * (Wfr J J1)ᴴ =
      (Matrix.fromBlocks (1 : Matrix (Fin D) (Fin D) ℂ) 0 0 (0 : Matrix (Fin D1) (Fin D1) ℂ)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm
def RowsBlock : Prop :=
  ∀ (ι : Type) [Fintype ι] (Dall D D1 : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ),
    OrthFrame J J1 →
    (∀ u k j, Brow (Wfr J J1) B u (Fin.castAdd D1 k) j = (Jᴴ * B u) k j) ∧
    (∀ u k j, Brow (Wfr J J1) B u (Fin.natAdd D k) j = (J1ᴴ * B u) k j) ∧
    (∀ η, F1 (Brow (Wfr J J1) B) ga η ↔ F1 B ga η) ∧
    (∀ e, F2 (Brow (Wfr J J1) B) ga e ↔ F2 B ga e) ∧
    (∀ Dstar η0 η1 e0, InputS (Brow (Wfr J J1) B) ga Dstar η0 η1 e0 ↔ InputS B ga Dstar η0 η1 e0)
def FrameExists : Prop :=
  ∀ (Dall : ℕ) (E : Submodule ℂ (Fin Dall → ℂ)),
    ∃ (D1 : ℕ) (J : Matrix (Fin Dall) (Fin (finrank ℂ E)) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ),
      OrthFrame J J1 ∧ (∀ x, x ∈ E ↔ (J * Jᴴ) *ᵥ x = x) ∧
      (∀ y, (∀ x ∈ E, star x ⬝ᵥ y = 0) ↔ (J1 * J1ᴴ) *ᵥ y = y)
def CorTransport : Prop :=
  ∀ (ι : Type) [Fintype ι] (Dall D D1 : ℕ) (d : ι → ℕ) (P : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (A : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (Y' : Matrix (Fin D) (Fin D) ℂ)
    (Y : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ) (η e del : ℝ),
    (∀ u, 0 < ga u) → (∀ u, c u ≠ 0) → IsUni V → (∀ u, IsUni (U u)) → OrthFrame J J1 →
    del < 1 → (1 - del) * (Dall : ℝ) ≤ (D : ℝ) →
    (∀ u, Y'⁻¹ * A u * Y u = c u • (Jᴴ * (V * P u * U u))) →
    F1 P ga η → F2 P ga e →
    (∀ u, 0 < gaTw ga c u) ∧
    (∀ u k j, Brow (Wfr J J1) (Btwist P c V U) u (Fin.castAdd D1 k) j = (Y'⁻¹ * A u * Y u) k j) ∧
    F1 (Brow (Wfr J J1) (Btwist P c V U)) (gaTw ga c) η ∧
    F2 (Brow (Wfr J J1) (Btwist P c V U)) (gaTw ga c) e ∧
    (1 - del) * ((D + D1 : ℕ) : ℝ) ≤ (D : ℝ) ∧ ((D + D1 : ℕ) : ℝ) ≤ (D : ℝ) / (1 - del)
def WordCount : Prop :=
  ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (C0 Gam sg Dstar : ℝ),
    0 < C0 → 0 < Gam → 0 < sg → 0 ≤ Dstar →
    Fintype.card ι = ⌈C0 * Gam ^ 2 / sg⌉₊ →
    (∀ u, Dstar / Gam ^ 2 / C0 ≤ (d u : ℝ)) →
    Dstar / sg ≤ Rs d
def WordCountUpper : Prop :=
  ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (C0 Gam sg Dstar : ℝ),
    0 < C0 → 0 < Gam → 0 < sg → 0 ≤ Dstar →
    Fintype.card ι = ⌈C0 * Gam ^ 2 / sg⌉₊ →
    (∀ u, (d u : ℝ) ≤ C0 * Dstar / Gam ^ 2) →
    Rs d ≤ (C0 * Gam ^ 2 / sg + 1) * (C0 * Dstar / Gam ^ 2)
def WordLog : Prop :=
  ∀ (k : ℕ) (X : ℝ), 3 ≤ k →
    (⌈X⌉₊ ≤ 2 ^ (k - 3) ↔ X ≤ (2 : ℝ) ^ (k - 3)) ∧
    (X ≤ (2 : ℝ) ^ (k - 3) →
      Real.log (⌈X⌉₊ : ℝ) ≤ ((k : ℝ) - 3) * Real.log 2 ∧ Real.log (⌈X⌉₊ : ℝ) ≤ (k : ℝ))
def WordLogReal : Prop :=
  ∀ (k X : ℝ), 0 ≤ X → X + 1 ≤ (2 : ℝ) ^ (k - 3) →
    Real.log (⌈X⌉₊ : ℝ) ≤ (k - 3) * Real.log 2
def MatrixFamilyBoundsOfCardEqCeil : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (Dstar sg η0 η1 e0 C0 Gam : ℝ),
    (∀ u, 0 ≤ ga u) → 0 < Dstar → 0 < sg → sg ≤ 1 / 4 → 0 < C0 → 0 < Gam →
    Fintype.card ι = ⌈C0 * Gam ^ 2 / sg⌉₊ → (∀ u, Dstar / Gam ^ 2 / C0 ≤ (d u : ℝ)) →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    InputS B ga Dstar η0 η1 e0 →
    F1 B ga (5 * sg) ∧ F2 B ga e0 ∧ e0 ≤ 1 / 4
def ChainHyp {ι : Type} [Fintype ι] {Dall D D1 : ℕ} {d r : ι → ℕ}
    (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ) (Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (A : ∀ u, Matrix (Fin D) (Fin (r u)) ℂ) (Y' : Matrix (Fin D) (Fin D) ℂ)
    (Y : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ) (Dstar sg η0 η1 e0 de del C0 Gam : ℝ) : Prop :=
  (∀ u, 0 < ga u) ∧ 0 < Dstar ∧ 0 < sg ∧ sg ≤ 1 / 20 ∧ 0 < C0 ∧ 0 < Gam ∧
  Fintype.card ι = ⌈C0 * Gam ^ 2 / sg⌉₊ ∧ (∀ u, Dstar / Gam ^ 2 / C0 ≤ (d u : ℝ)) ∧
  -1 ≤ η0 ∧ η0 ≤ sg / 2 ∧ η1 ≤ sg / 2 ∧ 0 ≤ e0 ∧ Real.sqrt e0 ≤ sg / 2 ∧
  InputS Pf ga Dstar η0 η1 e0 ∧
  Isom Vr ∧ 0 ≤ de ∧ de ≤ 1 / 4 ∧ ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * Rs d ∧
  (∀ u, c u ≠ 0) ∧ IsUni V ∧ (∀ u, IsUni (U u)) ∧ OrthFrame J J1 ∧
  del < 1 ∧ (1 - del) * (Dall : ℝ) ≤ (D : ℝ) ∧
  IsUnit Y'.det ∧ (∀ u, IsUnit (Y u).det) ∧
  (∀ u, Y'⁻¹ * A u * Y u = c u • (Jᴴ * (V * Bram Pf Vr u * U u)))
def CorChain : Prop :=
  ∀ (ι : Type) [Fintype ι] (Dall D D1 : ℕ) (d r : ι → ℕ)
    (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ) (Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (A : ∀ u, Matrix (Fin D) (Fin (r u)) ℂ) (Y' : Matrix (Fin D) (Fin D) ℂ)
    (Y : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ) (Dstar sg η0 η1 e0 de del C0 Gam : ℝ),
    ChainHyp Pf Vr ga c V U J J1 A Y' Y Dstar sg η0 η1 e0 de del C0 Gam →
    (∀ u, 0 < gaTw ga c u) ∧
    (∀ u k j, Brow (Wfr J J1) (Btwist (Bram Pf Vr) c V U) u (Fin.castAdd D1 k) j
      = (Y'⁻¹ * A u * Y u) k j) ∧
    F1 (Brow (Wfr J J1) (Btwist (Bram Pf Vr) c V U)) (gaTw ga c) (5 * sg + 3 * Real.sqrt de) ∧
    F2 (Brow (Wfr J J1) (Btwist (Bram Pf Vr) c V U)) (gaTw ga c) (2 * e0) ∧ 2 * e0 ≤ 1 / 4 ∧
    (1 - del) * ((D + D1 : ℕ) : ℝ) ≤ (D : ℝ) ∧ ((D + D1 : ℕ) : ℝ) ≤ (D : ℝ) / (1 - del) ∧
    0 < Rs r ∧ 0 ≤ 5 * sg + 3 * Real.sqrt de ∧ 0 ≤ 2 * e0 ∧ 0 < Dall ∧ 0 ≤ del
def ChainModel : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (Dall D D1 : ℕ) (d r : ι → ℕ)
    (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ) (Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (A : ∀ u, Matrix (Fin D) (Fin (r u)) ℂ) (Y' : Matrix (Fin D) (Fin D) ℂ)
    (Y : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ) (Dstar sg η0 η1 e0 de del C0 Gam : ℝ),
    ChainHyp Pf Vr ga c V U J J1 A Y' Y Dstar sg η0 η1 e0 de del C0 Gam ∧
    0 < D ∧ 0 < D1 ∧ 0 < del ∧ (∀ u, (c u).im ≠ 0 ∧ ‖c u‖ ≠ 1) ∧ Nonempty ι ∧
    (∃ u, r u < d u) ∧ 0 < de ∧ J1ᴴ * V * J ≠ 0
def WfrS {Dall D D1 : ℕ} (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) :
    Matrix (Fin D ⊕ Fin D1) (Fin Dall) ℂ :=
  Matrix.fromRows Jᴴ J1ᴴ
def BfS {ι : Type} {Dall D D1 : ℕ} {d : ι → ℕ} (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ)
    (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) :
    ∀ u, Matrix (Fin D ⊕ Fin D1) (Fin (d u)) ℂ :=
  fun u => c u • (WfrS J J1 * (V * Pf u))
def VrS {ι : Type} {d r : ι → ℕ} (Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ) : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ :=
  fun u => Vr u * U u
def TwRamFactor : Prop :=
  ∀ (ι : Type) [Fintype ι] (Dall D' : ℕ) (d r : ι → ℕ)
    (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ) (Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ) (W : Matrix (Fin D') (Fin Dall) ℂ),
    (∀ u, c u ≠ 0) → IsUni V → (∀ u, IsUni (U u)) → IsUni W → Isom Vr →
    (∀ u, Brow W (Btwist (Bram Pf Vr) c V U) u
      = Brow W (Btwist Pf c V (fun _ => 1)) u * VrS Vr U u) ∧
    Isom (VrS Vr U) ∧
    (∀ Dstar η0 η1 e0, InputS (Brow W (Btwist Pf c V (fun _ => 1))) (gaTw ga c) Dstar η0 η1 e0 ↔
      InputS Pf ga Dstar η0 η1 e0)
def ChainCondition : Prop :=
  ∀ (ι : Type) [Fintype ι] (Dall D D1 : ℕ) (d r : ι → ℕ)
    (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ) (Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (A : ∀ u, Matrix (Fin D) (Fin (r u)) ℂ) (Y' : Matrix (Fin D) (Fin D) ℂ)
    (Y : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ) (Dstar sg η0 η1 e0 de del C0 Gam : ℝ),
    ChainHyp Pf Vr ga c V U J J1 A Y' Y Dstar sg η0 η1 e0 de del C0 Gam →
    (∀ u, 0 < gaTw ga c u) ∧
    (∀ u, (VrS Vr U u)ᴴ * VrS Vr U u = 1) ∧
    Dstar / sg ≤ MatrixLatticeEstimates.RsG (fun u => Fin (d u)) ∧
    ∑ u, ((Fintype.card (Fin (d u)) : ℝ) - (Fintype.card (Fin (r u)) : ℝ))
      ≤ de * MatrixLatticeEstimates.RsG (fun u => Fin (d u)) ∧
    MatrixLatticeEstimates.InputSG (BfS Pf c V J J1) (gaTw ga c) Dstar η0 η1 e0 ∧
    (∀ u k j, (BfS Pf c V J J1 u * VrS Vr U u) (Sum.inl k) j = (Y'⁻¹ * A u * Y u) k j) ∧
    (∀ u i j, (BfS Pf c V J J1 u * VrS Vr U u) i j
      = Brow (Wfr J J1) (Btwist (Bram Pf Vr) c V U) u (finSumFinEquiv i) j) ∧
    0 < ∑ u, Fintype.card (Fin (r u)) ∧ 0 ≤ del ∧ del < 1 ∧
    (1 - del) * (Fintype.card (Fin D ⊕ Fin D1) : ℝ) ≤ (Fintype.card (Fin D) : ℝ)
def ChainJoint : Prop :=
  ∀ (K W I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype I] [Nonempty I] (Dall D D1 : ℕ) (d r : I → ℕ)
    (Vs : I → Type) [∀ i, AddCommGroup (Vs i)] [∀ i, Module K (Vs i)] [∀ i, Module (𝓞 K) (Vs i)]
    [∀ i, IsScalarTower (𝓞 K) K (Vs i)]
    (b' : Basis (Fin D) K W) (X' : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (Fin (r i)) K (Vs i))
    (X : ∀ i, InfinitePlace K → Matrix (Fin (r i)) (Fin (r i)) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (Vs i)) (B : ∀ i, Vs i →ₗ[K] W) (h : I → ℝ) (v : InfinitePlace K)
    (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ) (Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : I → ℝ) (c : I → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (Y' : Matrix (Fin D) (Fin D) ℂ) (Y : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ)
    (s u HH Dstar sg η0 η1 e0 de del C0 Gam : ℝ),
    (∀ w, IsUnit (X' w).det) → (∀ i w, IsUnit (X i w).det) →
    cc.FG → Submodule.span K (cc : Set W) = ⊤ →
    (∀ i, (N i).FG) → (∀ i, Submodule.span K (N i : Set (Vs i)) = ⊤) →
    (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) →
    (∀ i, B i ≠ 0 → Formalism.HN.htMap (b i) (X i) b' X' (B i) ≤ h i) →
    MatrixLatticeEstimates.LatNum b' X' cc b X N h s u HH →
    ChainHyp Pf Vr ga c V U J J1
      (fun i => (LinearMap.toMatrix (b i) b' (B i)).map v.embedding) Y' Y
      Dstar sg η0 η1 e0 de del C0 Gam →
    s - Real.log (Fintype.card I : ℝ) -
        (1 - del)⁻¹ * (4 * u * Real.log (1 + HH / u)
          + ((5 * sg + 3 * Real.sqrt de) + 4 * Real.sqrt (2 * e0)) * HH)
      ≤ Formalism.HN.muDef b' X' cc
end
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance


