-- Prove2me | Definitions.Def_AoP_EnsembleSpaces
-- name    : AoP_EnsembleSpaces
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T09:19:50.269443+00:00
-- url     : https://prove2.me/theorems/de2718ce-552c-4983-a46e-15effb76688b
-- title:
--   Assumptions of Physics II.4: axioms of ensemble, mixture and entropy
-- statement:
--   Axioms of ensemble spaces from Part II, Chapter 4 of *Assumptions of Physics* (Carcassi–Aidala, v3.0).
--
--   **Axiom of ensemble (4.4).** An ensemble space is a $T_0$, second countable topological space.
--
--   **Axiom of mixture (4.7).** A continuous operation $+:[0,1]\times E\times E\to E$, $pa+\bar pb$, satisfying identity, idempotence, commutativity and associativity (in the book's two-sided form).
--
--   **Axiom of entropy (4.55).** A continuous $S:E\to\mathbb R$ that is strictly concave, $S(pa+\bar pb)\ge pS(a)+\bar pS(b)$ with equality iff $a=b$ (for non-trivial $p\in(0,1)$, which the book leaves implicit); satisfies the upper variability bound $S(pa+\bar pb)\le I(p,\bar p)+pS(a)+\bar pS(b)$ for a universal function $I$; and such that mixtures preserve orthogonality. Orthogonality $a\perp b$ is saturation of the upper bound; it is taken to hold for every $p\in(0,1)$. The universal function $I$ is a parameter of the structure, shared by all ensemble spaces under consideration. The entropy's freedom up to a positive multiplicative constant is not encoded: a fixed choice of $S$ is part of the data.
--
--   **Derived notions.** Component (Definition 4.15, two-term form), separateness (Definition 4.21: no common component), mixing entropy (Definition 4.115).
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 4 (pp. 197–284), Axioms 4.4, 4.7, 4.55; Definitions 4.6, 4.15, 4.21, 4.115 (pp. 204–245)

import Mathlib

/-!
# Assumptions of Physics, Part II, Chapter 4: ensemble spaces (axioms)

Source: G. Carcassi, C. A. Aidala, *Assumptions of Physics*, Ver. 3.0 (December 31, 2025),
Part II, Chapter 4 "Ensemble spaces", Sections 4.2–4.5 (Axioms 4.4, 4.7, 4.55).

Mixing coefficients live in the unit interval `unitInterval = [0, 1]`; real-valued
coefficients that are known to lie in `[0, 1]` are converted with `clampI` (the projection of
`ℝ` onto `[0, 1]`, which is the identity on `[0, 1]`).
-/

namespace AssumptionsOfPhysics

universe u

/-- The projection of `ℝ` onto `[0, 1]` (identity on `[0, 1]`), used to write mixing
coefficients given by real expressions. -/
noncomputable def clampI (x : ℝ) : unitInterval :=
  Set.projIcc (0 : ℝ) 1 zero_le_one x

/-- Axioms 4.4 (ensemble), 4.7 (mixture) and 4.55 (entropy). An ensemble space with upper
variability bound `I` is a T₀, second countable topological space `E` with a continuous mixing
operation `mix p a b = p a + (1 - p) b` and a continuous entropy `S : E → ℝ` satisfying the
listed properties. The function `I` is the universal function of the upper variability bound
(the same for all ensemble spaces), so it is a parameter of the structure. -/
structure EnsembleSpace (I : ℝ → ℝ → ℝ) (E : Type u) [TopologicalSpace E] : Type u where
  /-- Axiom 4.4: the topology is T₀. -/
  t0 : T0Space E
  /-- Axiom 4.4: the topology is second countable. -/
  secondCountable : SecondCountableTopology E
  /-- Axiom 4.7: mixing `mix p a b = p a + p̄ b`. -/
  mix : unitInterval → E → E → E
  /-- Continuity of mixing on `[0, 1] × E × E`. -/
  continuous_mix : Continuous fun x : unitInterval × E × E => mix x.1 x.2.1 x.2.2
  /-- Identity: `1 a + 0 b = a`. -/
  mix_one : ∀ a b : E, mix 1 a b = a
  /-- Idempotence: `p a + p̄ a = a`. -/
  mix_self : ∀ (p : unitInterval) (a : E), mix p a a = a
  /-- Commutativity: `p a + p̄ b = p̄ b + p a`. -/
  mix_comm : ∀ (p : unitInterval) (a b : E), mix p a b = mix (unitInterval.symm p) b a
  /-- Associativity, for `p₁, p₃ ∈ [0, 1)` with `p₁ + p₃ ≤ 1`:
  `p₁ e₁ + p̄₁ ((1 - p₁ - p₃)/p̄₁ e₂ + p₃/p̄₁ e₃) = p̄₃ (p₁/p̄₃ e₁ + (1 - p₁ - p₃)/p̄₃ e₂) + p₃ e₃`. -/
  mix_assoc : ∀ (p₁ p₃ : ℝ) (e₁ e₂ e₃ : E), 0 ≤ p₁ → p₁ < 1 → 0 ≤ p₃ → p₃ < 1 →
    p₁ + p₃ ≤ 1 →
    mix (clampI p₁) e₁ (mix (clampI ((1 - p₁ - p₃) / (1 - p₁))) e₂ e₃) =
      mix (clampI (1 - p₃)) (mix (clampI (p₁ / (1 - p₃))) e₁ e₂) e₃
  /-- Axiom 4.55: the entropy. -/
  S : E → ℝ
  /-- Continuity of the entropy. -/
  continuous_S : Continuous S
  /-- Strict concavity (for non-trivial coefficients `p ∈ (0, 1)`):
  `S(p a + p̄ b) ≥ p S(a) + p̄ S(b)`, with equality if and only if `a = b`. -/
  concave_S : ∀ (p : unitInterval) (a b : E), 0 < (p : ℝ) → (p : ℝ) < 1 →
    (p : ℝ) * S a + (1 - p) * S b ≤ S (mix p a b) ∧
      ((p : ℝ) * S a + (1 - p) * S b = S (mix p a b) ↔ a = b)
  /-- Upper variability bound: `S(p a + p̄ b) ≤ I(p, p̄) + p S(a) + p̄ S(b)`. -/
  upper_bound_S : ∀ (p : unitInterval) (a b : E),
    S (mix p a b) ≤ I p (1 - p) + p * S a + (1 - p) * S b
  /-- Mixtures preserve orthogonality, where `a ⊥ b` means that the upper variability bound is
  saturated for every `p ∈ (0, 1)`. -/
  orth_mix_iff : ∀ (p : unitInterval) (a b c : E), 0 < (p : ℝ) → (p : ℝ) < 1 →
    ((∀ q : unitInterval, 0 < (q : ℝ) → (q : ℝ) < 1 →
        S (mix q a b) = I q (1 - q) + q * S a + (1 - q) * S b) ∧
      (∀ q : unitInterval, 0 < (q : ℝ) → (q : ℝ) < 1 →
        S (mix q a c) = I q (1 - q) + q * S a + (1 - q) * S c)) ↔
    (∀ q : unitInterval, 0 < (q : ℝ) → (q : ℝ) < 1 →
        S (mix q a (mix p b c)) = I q (1 - q) + q * S a + (1 - q) * S (mix p b c))

namespace EnsembleSpace

variable {I : ℝ → ℝ → ℝ} {E : Type u} [TopologicalSpace E] (X : EnsembleSpace I E)

/-- Orthogonality (mutual exclusion) `a ⊥ b`: the upper variability bound is saturated,
`S(p a + p̄ b) = I(p, p̄) + p S(a) + p̄ S(b)`, for every `p ∈ (0, 1)`. -/
def Orth (a b : E) : Prop :=
  ∀ q : unitInterval, 0 < (q : ℝ) → (q : ℝ) < 1 →
    X.S (X.mix q a b) = I q (1 - q) + q * X.S a + (1 - q) * X.S b

/-- Definition 4.15 (two-term form): `c` is a component of `a` if `a = p c + p̄ d` for some
ensemble `d` and some mixing coefficient `p ∈ (0, 1]`. -/
def IsComponent (c a : E) : Prop :=
  ∃ (p : unitInterval) (d : E), 0 < (p : ℝ) ∧ a = X.mix p c d

/-- Definition 4.21: two ensembles are separate if they have no common component. -/
def Separate (a b : E) : Prop :=
  ¬ ∃ c : E, X.IsComponent c a ∧ X.IsComponent c b

/-- Definition 4.115: the mixing entropy `MS(a, b) = S(½ a + ½ b) − (½ S(a) + ½ S(b))`. -/
noncomputable def mixingEntropy (a b : E) : ℝ :=
  X.S (X.mix (clampI (1 / 2)) a b) - (1 / 2 * X.S a + 1 / 2 * X.S b)

end EnsembleSpace

end AssumptionsOfPhysics


