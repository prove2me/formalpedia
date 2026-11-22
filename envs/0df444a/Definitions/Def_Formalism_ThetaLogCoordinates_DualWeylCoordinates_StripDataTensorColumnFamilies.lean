-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:35.214807+00:00
-- url     : https://prove2.me/theorems/37764784-12ed-4ea7-87db-d2fd9fc63744
-- title:
--   Strip Data Tensor Column Families
-- statement:
--   Definitions and structural lemmas for Strip Data Tensor Column Families, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/StripDataTensorColumnFamilies.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
open Classical in

def strUp {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun i => Finset.Icc (mu i) (mu i + b)).filter fun nu => HStrip mu nu b
open Classical in

def strDown {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun i => Finset.Icc (mu i - b) (mu i)).filter fun nu => HStrip nu mu b
open Classical in

def strVert {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun i => Finset.Icc (mu i) (mu i + 1)).filter fun nu =>
    Dominant nu ∧ ∑ a, (nu a - mu a) = (b : ℤ)
def IsStripData {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ (GLCoord ℤ n))
    (be : κ → Fin n → ℤ) (Str : (Fin n → ℤ) → Finset (Fin n → ℤ))
    (ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ) : Prop :=
  Function.Injective be ∧
  (∀ k l, evGL (torusPt n) (B k l) = if k = l then AddMonoidAlgebra.single (be k) 1 else 0) ∧
  (∀ mu, Dominant mu → ∀ nu ∈ Str mu, Dominant nu) ∧
  (∀ mu, Dominant mu → ∀ nu ∈ Str mu,
    (Matrix.of fun (x y : TIdx mu × κ) => TMat mu x.1 y.1 * B x.2 y.2) * (ps mu nu).map (Int.castRingHom _) =
      (ps mu nu).map (Int.castRingHom _) * TMat nu) ∧
  (∀ mu, Dominant mu → ∀ nu ∈ Str mu, ∃ k0, be k0 = nu - mu ∧
    (ps mu nu (canT mu, k0) (canT nu) = 1 ∨ ps mu nu (canT mu, k0) (canT nu) = -1)) ∧
  (∀ mu, Dominant mu → dMu mu * Fintype.card κ = ∑ nu ∈ Str mu, dMu nu)
def StripDataTensorColumnFamilies : Prop :=
  ∀ (n : ℕ) [NeZero n] (κ : Type) [Fintype κ] [DecidableEq κ] (B : Matrix κ κ (GLCoord ℤ n))
    (be : κ → Fin n → ℤ) (Str : (Fin n → ℤ) → Finset (Fin n → ℤ))
    (ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ), IsStripData B be Str ps →
    ∀ (M M' : GLMod n) (e : M'.ι ≃ M.ι × κ), IsTensor M M' B e → Nonempty (ColFam M) → Nonempty (ColFam M')
def SymStrip : Prop :=
  ∀ (n : ℕ) [NeZero n] (b : ℕ), ∃ be ps, IsStripData (SymMat n b) be (fun mu => strUp mu b) ps
def SymDStrip : Prop :=
  ∀ (n : ℕ) [NeZero n] (b : ℕ), ∃ be ps, IsStripData (SymDMat n b) be (fun mu => strDown mu b) ps
def LamStrip : Prop :=
  ∀ (n : ℕ) [NeZero n] (b : ℕ), ∃ be ps, IsStripData (LamMat n b) be (fun mu => strVert mu b) ps
def CntSym : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ) (b : ℕ), Dominant mu →
    dMu mu * Fintype.card (SymIdx n b) = ∑ nu ∈ strUp mu b, dMu nu
def CntSymD : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ) (b : ℕ), Dominant mu →
    dMu mu * Fintype.card (SymIdx n b) = ∑ nu ∈ strDown mu b, dMu nu
def CntLam : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ) (b : ℕ), Dominant mu →
    dMu mu * Fintype.card (LamIdx n b) = ∑ nu ∈ strVert mu b, dMu nu
def CntBranch : Prop :=
  ∀ (m : ℕ) [NeZero m] (lam : Fin (m + 1) → ℤ), Dominant lam → ∀ Sg : Finset (Fin m → ℤ),
    (∀ nu : Fin m → ℤ, nu ∈ Sg ↔ Dominant nu ∧ Interl lam nu) → dMu lam = ∑ nu ∈ Sg, dMu nu
end Formalism.InvariantFactorPaths.ColumnFamilies


