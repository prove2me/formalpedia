-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_GLintCompactOpen
-- name    : Formalism_LocalToGlobal_AdelicCompactOpens_GLintCompactOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:53.574703+00:00
-- url     : https://prove2.me/theorems/cc2b8888-b88b-4fe4-9f26-beb1e033d77a
-- title:
--   GLint Compact Open
-- statement:
--   Definitions and structural lemmas for GLint Compact Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/AdelicCompactOpens/GLintCompactOpen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.Props
open Matrix
def GLintCompactOpen : Prop :=
  ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (O : Subring R),
    IsOpen (O : Set R) → IsCompact (O : Set R) → ∀ n : ℕ,
      IsOpen {g : GL (Fin n) R | (∀ a b, (g : Matrix (Fin n) (Fin n) R) a b ∈ O) ∧
          ∀ a b, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b ∈ O} ∧
      IsCompact {g : GL (Fin n) R | (∀ a b, (g : Matrix (Fin n) (Fin n) R) a b ∈ O) ∧
          ∀ a b, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b ∈ O}
section uni
variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {n : ℕ}
def ParaR (r : ℕ) (h : GL (Fin n) K) : Prop :=
  (∀ a b, Valued.v ((h : Matrix (Fin n) (Fin n) K) a b) ≤ 1) ∧
    (∀ a b, Valued.v (((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b) ≤ 1) ∧
    ∀ a b : Fin n, r ≤ a.val → b.val < r → Valued.v ((h : Matrix (Fin n) (Fin n) K) a b) < 1
def UniR (r : ℕ) (h : GL (Fin n) K) : Prop :=
  ParaR r h ∧ ∀ a b : Fin n, a.val < r → b.val < r →
    (b.val < a.val → Valued.v ((h : Matrix (Fin n) (Fin n) K) a b) < 1) ∧
    (a = b → Valued.v ((h : Matrix (Fin n) (Fin n) K) a b - 1) < 1)
def detDDR (r : ℕ) (h : GL (Fin n) K) : K :=
  (Matrix.of fun a b : {x : Fin n // r ≤ x.val} => (h : Matrix (Fin n) (Fin n) K) a.1 b.1).det
def supDiagR (r : ℕ) (h : GL (Fin n) K) : K :=
  ∑ a : Fin n, ∑ b : Fin n, if a.val + 1 = b.val ∧ b.val < r then (h : Matrix (Fin n) (Fin n) K) a b else 0
end uni
def ParaDetUnit : Prop :=
  ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (n r : ℕ) (h : GL (Fin n) K), ParaR r h → Valued.v (detDDR r h) = 1
def UniCharMul : Prop :=
  ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (n r : ℕ) (ψ₀ : AddChar K ℂ) (ξ : Kˣ →* ℂˣ),
    (∀ x : K, Valued.v x < 1 → ψ₀ x = 1) → (∀ u : Kˣ, Valued.v ((u : K) - 1) < 1 → ξ u = 1) →
    ∀ (g h : GL (Fin n) K) (ug uh ugh : Kˣ), UniR r g → UniR r h →
      (ug : K) = detDDR r g → (uh : K) = detDDR r h → (ugh : K) = detDDR r (g * h) →
      ψ₀ (supDiagR r (g * h)) * (ξ ugh : ℂ) = (ψ₀ (supDiagR r g) * (ξ ug : ℂ)) * (ψ₀ (supDiagR r h) * (ξ uh : ℂ))
end Formalism.L2.Props


