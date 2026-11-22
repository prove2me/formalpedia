-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:23.475111+00:00
-- url     : https://prove2.me/theorems/c73ccb98-a680-466d-8cd0-7ecf3706a778
-- title:
--   Statement D
-- statement:
--   Definitions and structural lemmas for Statement D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/StatementD.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset
noncomputable def Wm (p : ℕ) [Fact p.Prime] (K : ℕ) {r : ℕ} (a : Fin r) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  LinearMap.mulLeft ℚ_[p] (X (Fin.last K, a))
noncomputable def dW (p : ℕ) [Fact p.Prime] (K : ℕ) {r : ℕ} (a : Fin r) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  (pderiv (Fin.last K, a)).toLinearMap
noncomputable def eulW (p : ℕ) [Fact p.Prime] (K r : ℕ) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  ∑ a : Fin r, Wm p K a ∘ₗ dW p K a
noncomputable def Uop (p : ℕ) [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a : Fin r) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  Wm p K a ∘ₗ (((c : ℤ) : ℚ_[p]) • LinearMap.id - eulW p K r) - ∑ b ∈ Cs, Wm p K b ∘ₗ glAct p LL K a b
noncomputable def Omega (p : ℕ) [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1)) (c : ℤ) (ρ : Fin r) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  ∑ a ∈ univ.erase ρ, Uop p LL c (univ.erase ρ) a ∘ₗ dW p K a
def UComm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a s t : Fin r)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
    LL.vec (Fin.last K) = true → s ∈ Cs → t ∈ Cs →
    glAct p LL (K + 1) s t (Uop p LL c Cs a F) - Uop p LL c Cs a (glAct p LL (K + 1) s t F) =
      if t = a then Uop p LL c Cs s F else 0
def UKeepsLast : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (c : ℤ) (a : Fin r),
    LL.vec (Fin.last K) = true →
    ∀ F ∈ YCond p LL (K + 1) ((c : ℤ) : WithTop ℤ), Uop p LL c univ a F ∈ YCond p LL (K + 1) ((c : ℤ) : WithTop ℤ)
def UKeepsEarly : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a : Fin r)
    (j : ℕ) (M : WithTop ℤ), j ≤ K →
    ∀ F ∈ YCond p LL j M, Uop p LL c Cs a F ∈ YCond p LL j M
def UDeg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a : Fin r) (o : ℕ),
    ∀ F ∈ Pol p r (setLast LL o), Uop p LL c Cs a F ∈ Pol p r (setLast LL (o + 1))
def ResU : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) (LL : Letters (K + 1)) (c : ℤ) (ρ a : Fin r)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), a ≠ ρ →
    initPart (Fin.last K, ρ) 0 (Uop p LL c univ a F) = Uop p LL c (univ.erase ρ) a (initPart (Fin.last K, ρ) 0 F)
def DKeepsX : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ a : Fin r) (e1 o : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true → HypP p LL ρ e1 → a ≠ ρ →
    ∀ x ∈ XSp p (setLast LL (o + 1)) J M ρ, dW p K a x ∈ XSp p (setLast LL o) J M ρ
def Sl2Injective : Prop :=
  ∀ (k V : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] (e f h : V →ₗ[k] V),
    (∀ x, h (e x) - e (h x) = (2 : k) • e x) → (∀ x, h (f x) - f (h x) = -((2 : k) • f x)) →
    (∀ x, e (f x) - f (e x) = h x) →
    ∀ (u : V) (μ : ℤ) (j : ℕ), h u = ((μ : ℤ) : k) • u → (∃ s : ℕ, (f ^ s) u = 0) → μ + j ≤ 0 → (e ^ j) u = 0 → u = 0
def EArith : Prop :=
  ∀ (s : ℕ) (ka : ℕ → ℤ) (β : ℕ → ℕ) (c : ℤ),
    (∀ i, i + 1 < s → ka (i + 1) + β (i + 1) ≤ ka i) → (0 < s → ka 0 + β 0 ≤ c) →
    1 ≤ ∑ a ∈ range s, β a →
    0 < (c - (∑ a ∈ range s, (β a : ℤ)) + 1) * (∑ a ∈ range s, (β a : ℤ)) - (∑ a ∈ range s, (β a : ℤ) * ka a) +
      ∑ b ∈ range s, ∑ a ∈ range b, ((β a : ℤ) + 1) * (β b : ℤ)
def OmegaInj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (ρ : Fin r) (c : ℤ) (o : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true →
    ∀ x ∈ Pol p r (setLast LL (o + 1)) ⊓ FreeOf p (Fin.last K, ρ) ⊓
        TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ),
      Omega p LL c ρ x = 0 → x = 0
def ResOntoKThm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true → HypP p LL ρ e1 → ResOntoK p LL J M ρ
end Formalism.InvariantFactorPaths.L4


