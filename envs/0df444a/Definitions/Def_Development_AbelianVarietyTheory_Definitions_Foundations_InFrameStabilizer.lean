-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:22.512635+00:00
-- url     : https://prove2.me/theorems/2f0cc04e-2a37-4114-b7d2-3c1cdb221e7a
-- title:
--   In Frame Stabilizer
-- statement:
--   Definitions and structural lemmas for In Frame Stabilizer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/InFrameStabilizer.lean

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
namespace GlobalTheory.SgAlg
variable {E : Type} [CommRing E]
def IsQA (σ : E →+* E) : Prop :=
  (∀ x, σ (σ x) = x) ∧ (∃ x, σ x ≠ x) ∧ IsReduced E ∧ IsUnit (2 : E) ∧
    ∀ x, σ x = x → x ≠ 0 → IsUnit x
def cT (σ : E →+* E) {a b : Type} (A : Matrix a b E) : Matrix b a E := (A.map σ).transpose
def IsHermU (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Prop := cT σ J = J ∧ IsUnit J.det
def form (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  dotProduct (fun i => σ (y i)) (J.mulVec x)
def pairM (σ : E →+* E) {n : ℕ} {a b : Type} (J : Matrix (Fin n) (Fin n) E)
    (P' : Matrix (Fin n) b E) (P : Matrix (Fin n) a E) : Matrix a b E := cT σ P * J * P'
def IsUn (σ : E →+* E) {n : ℕ} (J g : Matrix (Fin n) (Fin n) E) : Prop := cT σ g * J * g = J
def Free {n : ℕ} {a : Type} [Fintype a] [DecidableEq a] (P : Matrix (Fin n) a E) : Prop :=
  ∃ L : Matrix a (Fin n) E, L * P = 1
def IsUp {m : ℕ} (u : Matrix (Fin m) (Fin m) E) : Prop :=
  ∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1)
def IsLo {m : ℕ} (u : Matrix (Fin m) (Fin m) E) : Prop :=
  ∀ i j, (i < j → u i j = 0) ∧ (i = j → u i j = 1)
def lead {m : ℕ} (Z : Matrix (Fin m) (Fin m) E) (l : ℕ) (hl : l ≤ m) : E :=
  (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det
def TF (r : ℕ) (T : E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.diagonal fun a => if a = Fin.last r then -T else 0
def Gq (σ : E →+* E) {r : ℕ} (T T' : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E :=
  Z.det * σ Z.det - T * T' * (lead Z r (Nat.le_succ r) * σ (lead Z r (Nat.le_succ r)))
def IsFrame (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T : E)
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Prop := Free P ∧ pairM σ J P P = TF r T
def eOf {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Matrix (Fin n) (Fin r) E :=
  P.submatrix id Fin.castSucc
def IsDual (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E) : Prop :=
  pairM σ J f P = (Matrix.of fun a b => if a = Fin.castSucc b then 1 else 0) ∧ pairM σ J f f = 0
def InS (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (g : Matrix (Fin n) (Fin n) E) : Prop := IsUn σ J g ∧ ∃ ν, IsUp ν ∧ g * P = P * ν
def InFrameStabilizer (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (g : Matrix (Fin n) (Fin n) E) : Prop := IsUn σ J g ∧ g * P = P
def InN (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (g : Matrix (Fin n) (Fin n) E) : Prop :=
  IsUn σ J g ∧ (∃ ν, IsUp ν ∧ g * eOf P = eOf P * ν) ∧
    ∀ v : Fin n → E, (cT σ (eOf P) * J).mulVec v = 0 → ∃ c, g.mulVec v - v = (eOf P).mulVec c
def InH (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (f : Matrix (Fin n) (Fin r) E) (g : Matrix (Fin n) (Fin n) E) : Prop :=
  IsUn σ J g ∧ g * P = P ∧ g * f = f
def Zhat (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P P' : Matrix (Fin n) (Fin (r + 1)) E) (γ : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) E := pairM σ J (γ * P') P
def XZ (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : E)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Set (Matrix (Fin n) (Fin (r + 1)) E × Matrix (Fin n) (Fin (r + 1)) E) :=
  {p | IsFrame σ J T p.1 ∧ IsFrame σ J T' p.2 ∧ pairM σ J p.2 p.1 = Z}
def PosOnPerp {n : ℕ} {a : Type} [Fintype a] (J : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n) a ℂ) : Prop :=
  ∀ w : Fin n → ℂ, (cT (starRingEnd ℂ) A * J).mulVec w = 0 → w ≠ 0 →
    0 < (form (starRingEnd ℂ) J w w).re
end GlobalTheory.SgAlg


