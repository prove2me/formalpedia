-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_EeProd
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_EeProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:07.618844+00:00
-- url     : https://prove2.me/theorems/ea7a2fe9-bcbe-4fb1-9f6e-16100253ab9d
-- title:
--   Ee Prod
-- statement:
--   Definitions and structural lemmas for Ee Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/EeProd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Letter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SgC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PieceEqPieceT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IntegralLocallyConstCochainModPow
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
open GlobalTheory.KZ
section Global
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
def CgA (A : ValuationSubring Ω) (l n : ℕ) (x y : Ω) : Prop := ∃ z ∈ A, x - y = (l : Ω) ^ n * z
def theta (s : ℚ) (φ : HahnSeries ℚ Ω) : HahnSeries ℚ Ω where
  coeff r := algebraMap ℚ Ω (s * r) * φ.coeff r
  isPWO_support' := φ.isPWO_support.mono (fun r hr h => hr (by simp [h]))
def Prim (A : ValuationSubring Ω) (φ : HahnSeries ℚ Ω) : Prop :=
  (∀ r, φ.coeff r ∈ A) ∧ ∃ r, φ.coeff r ≠ 0 ∧ (φ.coeff r)⁻¹ ∈ A
def IsDl (X : Tower Ω ε) (A : ValuationSubring Ω) (l n : ℕ) (s : ℚ) (f : X.K) (φ : HahnSeries ℚ Ω) : Prop :=
  (∀ r, φ.coeff r ∈ A) ∧ ∃ (a b : X.K) (κ : Ω), κ ≠ 0 ∧ f * b = algebraMap Ω X.K κ * a ∧ Prim A (X.exp a) ∧ Prim A (X.exp b) ∧
    ∀ r, CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)).coeff r)
def Inv (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) (f : X.K) : Prop := ∀ γ ∈ H, X.sl (ofSL γ) f = f
def GamTop (N l n : ℕ) : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma (l ^ n) ⊓ CongruenceSubgroup.Gamma1 N
def IsThB (X : Tower Ω ε) (A : ValuationSubring Ω) (N l n : ℕ) [Fact l.Prime] (b : X.Fn l) (φ : HahnSeries ℚ Ω) : Prop :=
  ∃ f : X.Kˣ, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (f : X.K) ∧
    AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n f ∧
    (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (f : X.K) * X.sl (ofSL δ) f = g ^ (l ^ n)) ∧
    IsDl X A l n 1 f φ
def nrmT (X : Tower Ω ε) (M : ℕ) (f : X.K) : X.K := ∏ b ∈ Finset.range M, X.sl (ofSL (ModularGroup.T ^ b)) f
def sgN (X : Tower Ω ε) (c N M : ℕ) (a : ℤ × ℤ) : X.K :=
  X.sl (toGQ !![(N : ℤ), 0; 0, 1]) (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M])
def coefQ (M : ℕ) (f : ℕ → Ω) (r : ℚ) : Ω := if 0 ≤ r ∧ (r * M).den = 1 then f (r * M).num.toNat else 0
def eeProd [CharZero Ω] (N l n : ℕ) (c d : ℕ) (w w' : ℤ × ℤ) (ζ : Ω) (γ : GL (Fin 2) (ZMod (l ^ n))) : ℕ → Ω :=
  GlobalTheory.KummerEisensteinGalois.cmul (GlobalTheory.KummerEisensteinGalois.smF c 1 (N * l ^ n) ζ (GlobalTheory.KummerEisensteinGalois.rowT N l n γ 0 w).1 (GlobalTheory.KummerEisensteinGalois.rowT N l n γ 0 w).2)
    (GlobalTheory.KummerEisensteinGalois.smF d 1 (N * l ^ n) ζ (GlobalTheory.KummerEisensteinGalois.rowT N l n γ 1 w').1 (GlobalTheory.KummerEisensteinGalois.rowT N l n γ 1 w').2)
def IsLamG (ε : Ω →+* ℂ) (l n m : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (t : ZMod (l ^ n)) : Prop :=
  (s ^ (l ^ (n - m))) (eOm ε (1 / (l : ℚ) ^ (2 * n))) = eOm ε (1 / (l : ℚ) ^ n) ^ t.val * eOm ε (1 / (l : ℚ) ^ (2 * n))
end Global
section Local
open GlobalTheory.K5
variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]
structure IsReb (T : GlobalTheory.K5.Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω) : Prop where
  inj : Function.Injective ψ
  par : ψ (qO p) = T.qq n
  sub : ∀ a b : Lau p, (∀ i : ℤ, b.coeff ((p : ℤ) ^ n * i) = a.coeff i) → (∀ r : ℤ, ¬ (p : ℤ) ^ n ∣ r → b.coeff r = 0) →
    ψ (algebraMap (Lau p) (O0 p) b) = algebraMap (O0 p) Ω (algebraMap (Lau p) (O0 p) a)
  rng : ψ.range = (Algebra.adjoin (O0 p) {T.qq n}).toSubring
def thL (a : Lau p) : Lau p where
  coeff r := (r : ℤ_[p]) * a.coeff r
  isPWO_support' := a.isPWO_support.mono (fun r hr h => hr (by simp [h]))
def zp (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] (z : ℤ_[p]) : Ω :=
  algebraMap (O0 p) Ω (algebraMap (Lau p) (O0 p) (HahnSeries.single 0 z))
def Ev (ψ : O0 p →+* Ω) (c : ℤ → Ω) (x x' : Ω) : Prop :=
  ∃ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p), (∀ t, IsInt p (e t) ∧ IsAlgZp p (e t)) ∧
    (∀ r, c r = ∑ t, e t * zp Ω ((a t).coeff r)) ∧ x = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) ∧
    x' = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t)))
end Local
end GlobalTheory.Glue


