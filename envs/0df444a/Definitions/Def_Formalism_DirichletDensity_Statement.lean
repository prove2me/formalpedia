-- Prove2me | Definitions.Def_Formalism_DirichletDensity_Statement
-- name    : Formalism_DirichletDensity_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:44.793275+00:00
-- url     : https://prove2.me/theorems/540f9ae5-cfbc-4ee4-96fa-df311be92815
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/Statement.lean

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Filter Topology Finset Formalism.Q3
noncomputable section
namespace Formalism.HF
def DirDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun x : ℝ =>
      (∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => 1 / (m : ℝ) ^ x) n)
        / Real.log (1 / (x - 1)))
    (𝓝[>] 1) (𝓝 δ)
def LogDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun x : ℝ =>
      (x - 1) * (∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n))
    (𝓝[>] 1) (𝓝 δ)
def QuadDiscr : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K),
    x ^ 2 = (a : K) → IntermediateField.adjoin ℚ {x} = ⊤ → Squarefree a → a % 4 = 1 →
    discr K = a
def MQDiscr : Prop :=
  ∀ (k : ℕ) (q : Fin k → ℕ), 1 ≤ k → (∀ i, (q i).Prime ∧ q i % 4 = 3) → Function.Injective q →
  ∀ (E : Type) [Field E] [NumberField E] (α : Fin k → E), IsMQ (fun i => -(q i : ℤ)) α →
    discr E = (-1) ^ (2 ^ (k - 1)) * ∏ i, (q i : ℤ) ^ (2 ^ (k - 1))
def HostDiscr : Prop :=
  ∀ q : Fin 3 → ℕ, Hyp3 q → ∀ (E : Type) [Field E] [NumberField E] (α : Fin 3 → E), IsHost q α →
    discr E = ((q 0 * q 1 * q 2 : ℕ) : ℤ) ^ 4
def APLogDensity : Prop :=
  ∀ (N : ℕ) [NeZero N] (a : ZMod N), IsUnit a →
    LogDensity {p : ℕ | (p : ZMod N) = a} (1 / (N.totient : ℝ))
def LogToDir : Prop := ∀ (S : Set ℕ) (δ : ℝ), LogDensity S δ → DirDensity S δ
def HostDensityArith : Prop :=
  ∀ q : Fin 3 → ℕ, Hyp3 q → ∀ g : Gal3,
    LogDensity {p : ℕ | (∀ i, p ≠ q i) ∧ ∀ i, chiQ (q i) p = ((g i : ℤˣ) : ℤ)} (1 / 8) ∧
    DirDensity {p : ℕ | (∀ i, p ≠ q i) ∧ ∀ i, chiQ (q i) p = ((g i : ℤˣ) : ℤ)} (1 / 8)
def HostDensity : Prop :=
  ∀ q : Fin 3 → ℕ, Hyp3 q → ∀ (E : Type) [Field E] [NumberField E] (α : Fin 3 → E), IsHost q α →
  ∀ g : Gal3,
    DirDensity {p : ℕ | (∀ i, p ≠ q i) ∧
      ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(E/ℚ)),
        IsArithFrobAt ℤ σ P → galSign α σ = g} (1 / 8)
end Formalism.HF


