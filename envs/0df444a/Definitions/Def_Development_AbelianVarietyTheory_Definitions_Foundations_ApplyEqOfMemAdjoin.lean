-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:45.618879+00:00
-- url     : https://prove2.me/theorems/cbc80667-b9b4-4ebe-9d4b-917166a054f9
-- title:
--   Apply Eq Of Mem Adjoin
-- statement:
--   Definitions and structural lemmas for Apply Eq Of Mem Adjoin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_EeProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
namespace GlobalTheory.Glue
open GlobalTheory.KZ GlobalTheory.K5
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
def zt (ε : Ω →+* ℂ) (l n : ℕ) : Ω := eOm ε (1 / (l : ℚ) ^ n)
def Stab (A : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) : Prop := ∀ x, s x ∈ A ↔ x ∈ A
def InZl (ε : Ω →+* ℂ) (l n : ℕ) (F : Ω) : Prop := ∃ D : ℕ, ¬ l ∣ D ∧ (D : Ω) * F ∈ Subring.closure {zt ε l n}
open Classical in

def IsNT (ε : Ω →+* ℂ) (l n m : ℕ) [NeZero l] (F F' : Ω) : Prop :=
  ∃ τ : (ZMod (l ^ n))ˣ → (Ω ≃ₐ[ℚ] Ω), (∀ a, τ a (zt ε l n) = zt ε l n ^ (a : ZMod (l ^ n)).val) ∧
    (l : Ω) ^ (n - m) * F' = ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ n))ˣ => (a : ZMod (l ^ n)).val ≡ 1 [MOD l ^ m]), τ a F
def KT (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) : Subfield X.K :=
  RingHom.eqLocusField (X.sl (ofSL (ModularGroup.T ^ L))).toRingEquiv.toRingHom (RingHom.id X.K)
variable {p : ℕ} [Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]
structure IsCusp (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) : Prop where
  int : ∀ x, x ∈ A ↔ IsInt p (j x)
  alg : ∀ x, IsAlgZp p (j x)
  root : ∀ n, j (zt ε p n) = T.ζ n
  dense : ∀ (k : ℕ) (e : Ωl), IsInt p e → IsAlgZp p e → ∃ a ∈ A, Cong p k e (j a)
  down : ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x)
  up : ∀ (n : ℕ) (s : Ω ≃ₐ[ℚ] Ω), Stab A s → ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x)
structure IsIo (X : GlobalTheory.KZ.Tower Ω ε) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) (n : ℕ)
    (ψ : O0 p →+* Ωl) (io : KT X (p ^ n) →+* Ωl) : Prop where
  ev : ∀ (y : KT X (p ^ n)) (S : Finset Ω),
    (∀ r, (X.exp y).coeff r ∈ A ∧ (X.exp y).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω)) →
    ∃ x', Ev ψ (fun r : ℤ => j ((X.exp y).coeff ((r : ℚ) / (p : ℚ) ^ n))) (io y) x'
  gal : ∀ (g : Gal p Ωl) (s : Ω ≃ₐ[ℚ] Ω), g (T.qq n) = T.qq n → (∀ x, g (j x) = j (s x)) →
    ∀ y y' : KT X (p ^ n), (y' : X.K) = X.gal s y → g (io y) = io y'
def IsNTr (ε : Ω →+* ℂ) (l n m : ℕ) [NeZero l] (F F' : Ω) : Prop :=
  1 ≤ m ∧ m ≤ n ∧ F ∈ IntermediateField.adjoin ℚ {zt ε l n} ∧ IsNT ε l n m F F'
example (l : ℕ) [NeZero l] (F F' : Ω) : ¬ IsNTr ε l 0 1 F F' ∧ ¬ IsNTr ε l 0 0 F F' ∧ ¬ IsNTr ε l 3 0 F F' :=
  ⟨fun h => by have := h.2.1; omega, fun h => by have := h.1; omega, fun h => by have := h.1; omega⟩
example (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (c : Ω) : X.jK ∈ KT X L ∧ algebraMap Ω X.K c ∈ KT X L :=
  ⟨X.j_inv _, (X.sl _).commutes c⟩
structure IsPlaceIn (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) : Prop where
  int : ∀ x, x ∈ A ↔ IsInt p (j x)
  alg : ∀ x, IsAlgZp p (j x)
  root : ∀ n, j (zt ε p n) = T.ζ n
structure IsExpIn (X : GlobalTheory.KZ.Tower Ω ε) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) (n : ℕ)
    (ψ : O0 p →+* Ωl) (io : KT X (p ^ n) →+* Ωl) : Prop where
  place : IsPlaceIn ε A T j
  rebase₂ : IsReb T n ψ
  ev : ∀ (y : KT X (p ^ n)) (S : Finset Ω),
    (∀ r, (X.exp y).coeff r ∈ A ∧ (X.exp y).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω)) →
    ∃ x', Ev ψ (fun r : ℤ => j ((X.exp y).coeff ((r : ℚ) / (p : ℚ) ^ n))) (io y) x'
def GalTr (X : GlobalTheory.KZ.Tower Ω ε) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) (n : ℕ) (io : KT X (p ^ n) →+* Ωl) : Prop :=
  ∀ (g : Gal p Ωl) (s : Ω ≃ₐ[ℚ] Ω) (b : ℕ), g (T.qq n) = T.ζ n ^ b * T.qq n → (∀ x, g (j x) = j (s x)) →
    ∀ y y' : KT X (p ^ n), (y' : X.K) = X.sl (ofSL (ModularGroup.T ^ b)) (X.gal s y) → g (io y) = io y'
section
variable {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} {n : ℕ} {ψ : O0 p →+* Ωl}
  {io : KT X (p ^ n) →+* Ωl}
end
end GlobalTheory.Glue


