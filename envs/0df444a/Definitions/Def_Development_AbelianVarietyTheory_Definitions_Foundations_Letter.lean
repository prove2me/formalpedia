-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Letter
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_Letter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:17.299865+00:00
-- url     : https://prove2.me/theorems/d2cc3273-537f-4afb-b710-46cbeb791e16
-- title:
--   Letter
-- statement:
--   Definitions and structural lemmas for Letter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/Letter.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExpUpper
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
open Matrix
namespace GlobalTheory.KZ
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
def Tower.OverY (X : Tower Ω ε) (W : ValuationSubring X.K) : Prop :=
  (∀ c : Ω, algebraMap Ω X.K c ∈ W) ∧ X.jK ∈ W
def Tower.Un (X : Tower Ω ε) (m : ℕ) : Set X.Kˣ :=
  {f | ∀ W, X.OverY W → ∃ g : X.Kˣ, W.valuation ((f : X.K) / (g : X.K) ^ m) = 1}
abbrev Tower.Kl (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := TensorProduct ℤ ℤ_[l] (Additive X.Kˣ)
abbrev idl (l : ℕ) [Fact l.Prime] : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l])}
abbrev Tower.Khat (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := AdicCompletion (idl l) (X.Kl l)
def Tower.cls (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.Kˣ) :
    X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l))) :=
  Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ Additive.ofMul f)
def Tower.ASet (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Set (X.Khat l) :=
  {a | ∀ n : ℕ, ∃ f ∈ X.Un (l ^ n), AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f}
def Tower.A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (X.Khat l) := Submodule.span ℤ_[l] (X.ASet l)
def Tower.kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) : X.Khat l →ₗ[ℤ_[l]] X.Khat l :=
  AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
    (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom))))
abbrev Tower.Fn (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := (Fin 2 → ℤ_[l]) → X.Khat l
def Tower.Pol (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) : Set (X.Fn l) :=
  {b | ∃ c : Fin (w + 1) → X.Khat l, (∀ i, c i ∈ X.A l) ∧
    ∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i}
def mZl (l : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ_[l] := m.map (Int.castRingHom ℤ_[l])
def Tower.act (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ) :
    X.Fn l →ₗ[ℤ_[l]] X.Fn l where
  toFun b u := X.kmap l (X.sl (toGQ m)).toRingEquiv (b (mZl l m *ᵥ u))
  map_add' b b' := by funext u; simp
  map_smul' c b := by funext u; simp
def Gam (N l : ℕ) : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l
def Tower.BSet (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] : Set (X.Fn l) :=
  {b | b ∈ X.Pol l w ∧ ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b}
def Tower.B (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (X.Fn l) := Submodule.span ℤ_[l] (X.BSet N l w)
def IsDiam (N l d : ℕ) (γ : SL(2, ℤ)) : Prop :=
  γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l ∧ (en γ 1 1 : ZMod N) = d
def sgD (N l d : ℕ) : SL(2, ℤ) := Classical.epsilon (IsDiam N l d)
def Tower.diam (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (d : ℕ) : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ)
def Tower.heckeT (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (q : ℕ) : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  (∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)]) +
    X.act l ((sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])
def Tower.heckeU (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  ∑ j ∈ Finset.range l, X.act l !![1, (j : ℤ); 0, (l : ℤ)]
def Tower.galB (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) : X.Fn l →ₗ[ℤ_[l]] X.Fn l where
  toFun b u := X.kmap l (X.gal s) (b ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1])
  map_add' b b' := by funext u; simp
  map_smul' c b := by funext u; simp
inductive Letter
  | T (q : ℕ)
  | U
  | D (d : ℕ)
def Tower.op (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] : Letter → (X.Fn l →ₗ[ℤ_[l]] X.Fn l)
  | Letter.T q => X.heckeT N l q
  | Letter.U => X.heckeU l
  | Letter.D d => X.diam N l d
end GlobalTheory.KZ


