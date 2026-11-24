-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
-- name    : Formalism_UnipotentAdelicQuotients_CuspEllipticValues
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:50.373199+00:00
-- url     : https://prove2.me/theorems/ed661a26-d4c4-464a-9957-c316746ff226
-- title:
--   Cusp Elliptic Values
-- statement:
--   Definitions and structural lemmas for Cusp Elliptic Values, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/CuspEllipticValues.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
namespace CuspElliptic
def IsChar {G : Type} [Group G] (χ : G → ℂ) : Prop :=
  ∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)
def IsIrrChar {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : Prop :=
  IsChar χ ∧ (∑ x, χ x * star (χ x)) = (Fintype.card G : ℂ)
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
def unipBlock (d a : ℕ) : Set (GL (Fin d) F) :=
  {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}
def IsCuspChar {d : ℕ} (χ : GL (Fin d) F → ℂ) : Prop :=
  IsIrrChar χ ∧ ∀ a, 0 < a → a < d →
    ∑ u : GL (Fin d) F, (open Classical in if u ∈ (unipBlock d a : Set (GL (Fin d) F)) then χ u else 0) = 0
def Statement : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (d : ℕ) (χ χ' : GL (Fin d) F → ℂ),
    IsCuspChar χ → IsCuspChar χ' →
    (∀ x : GL (Fin d) F, Irreducible (Matrix.charpoly (x : Matrix (Fin d) (Fin d) F)) → χ x = χ' x) →
    χ = χ'
end CuspElliptic


