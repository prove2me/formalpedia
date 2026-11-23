-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatement
-- name    : ReciprocityTheory_DualLattices_DiscriminantColengthStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:32.610827+00:00
-- url     : https://prove2.me/theorems/46619a02-c08e-415b-9a67-0433e387e7c0
-- title:
--   Discriminant Colength Statement
-- statement:
--   Definitions and structural lemmas for Discriminant Colength Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DiscriminantColengthStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
def discr {C : Type} [Field C] {n : ℕ} (a : Fin n → C) : C :=
  ∏ τ, ∏ τ' ∈ Finset.univ.erase τ, (a τ - a τ')
def freeMat {C : Type} [Field C] {n : ℕ} (a : Fin n → C) (h : ℕ) :
    Matrix (Fin n × Fin h) (Fin n × Fin h) C :=
  Matrix.of fun x y => if x.2 = y.2 then a x.1 ^ (y.1 : ℕ) else 0
def sumPts {C : Type} [Field C] {v : Valuation C NNReal} {n s : ℕ}
    (Mτ : Fin n → Lat v (Fin s)) : Set (Fin n × Fin s → C) :=
  {w | ∀ τ, (fun i => w (τ, i)) ∈ (Mτ τ).pts}
def projPts {C : Type} [Field C] {n s : ℕ} (M : Set (Fin n × Fin s → C)) (τ : Fin n) :
    Set (Fin s → C) :=
  (fun w i => w (τ, i)) '' M
def IsLaStable {C : Type} [Field C] {v : Valuation C NNReal} {n s : ℕ} (a : Fin n → C)
    (M : Lat v (Fin n × Fin s)) : Prop :=
  ∀ w ∈ M.pts, (fun y : Fin n × Fin s => a y.1 * w y) ∈ M.pts
def DiscriminantColengthStatement : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R → (∃ c : C, 0 < v c ∧ v c < 1) →
    ∀ (n : ℕ) (a : Fin n → C), Function.Injective a → (∀ τ, v (a τ) ≤ 1) →
    (∀ (s : ℕ) (F S : Lat v (Fin n × Fin s)), F.B = freeMat a s →
      S.pts = sumPts (fun _ => Lat.std v (Fin s)) →
      colen F S ^ 2 = v (discr a) ^ s) ∧
    (∀ (s : ℕ) (M S : Lat v (Fin n × Fin s)) (Mτ : Fin n → Lat v (Fin s)), IsLaStable a M →
      (∀ τ, (Mτ τ).pts = projPts M.pts τ) → S.pts = sumPts Mτ →
      v (discr a) ^ s ≤ colen M S ^ 2) ∧
    (∀ (s h : ℕ) (A : Fin n → Matrix (Fin s) (Fin h) C) (F : Lat v (Fin n × Fin h))
      (M' S : Lat v (Fin n × Fin s)) (Mτ : Fin n → Lat v (Fin s)), F.B = freeMat a h →
      (∀ τ, Function.Surjective (A τ).mulVec) →
      M'.pts = (fun w : Fin n × Fin h → C => fun y : Fin n × Fin s =>
        ∑ l, A y.1 y.2 l * w (y.1, l)) '' F.pts →
      (∀ τ, (Mτ τ).pts = projPts M'.pts τ) → S.pts = sumPts Mτ →
      colen M' S ^ 2 * v (discr a) ^ h ≤ v (discr a) ^ (2 * s))
end ReciprocityTheory.PGsh.Up


