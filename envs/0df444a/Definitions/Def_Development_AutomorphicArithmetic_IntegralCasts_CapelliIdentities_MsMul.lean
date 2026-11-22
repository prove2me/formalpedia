-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MsMul
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MsMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:59.407627+00:00
-- url     : https://prove2.me/theorems/56243e93-73af-4536-80ba-69078ac22903
-- title:
--   Ms Mul
-- statement:
--   Definitions and structural lemmas for Ms Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MsMul.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj21.XZ :
    Type → ℕ → ℕ → Type :=
    fun (Lt : Type) (N0 N1 : ℕ) ↦ Lt × ℕ × Fin N0 ⊕ Lt × Fin N0 × Fin N1
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj21.PolyXZ :
    Type → ℕ → ℕ → Type :=
    fun (H : Type) (N0 N1 : ℕ) ↦ MvPolynomial (UpperTheory.Reformulated.B.Qj21.XZ (Bool × H) N0 N1) ℤ
noncomputable def UpperTheory.Reformulated.B.Qj21.lfo :
    {H : Type} → {N0 N1 : ℕ} → H → ℕ × Fin N1 → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (c : ℕ × Fin N1) ↦
      ∑ a : Fin N0, MvPolynomial.X (Sum.inl ((Bool.false, t), c.1, a)) * MvPolynomial.X (Sum.inr ((Bool.false, t), a, c.2))
noncomputable def UpperTheory.Reformulated.B.Qj21.tmL :
    {H : Type} → {N0 N1 : ℕ} → H → List (ℕ × Fin N1) → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (L : List (ℕ × Fin N1)) (h : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) ↦
      (List.map (UpperTheory.Reformulated.B.Qj21.lfo t) L).prod * h
noncomputable def UpperTheory.Reformulated.B.Qj21.nzc :
    {N1 : ℕ} → List (ℕ × Fin N1) → ℕ :=
    fun {N1 : ℕ} (L : List (ℕ × Fin N1)) ↦
      (List.map (fun (c : ℕ × Fin N1) ↦ if c.1 = (0 : ℕ) then (0 : ℕ) else (1 : ℕ)) L).sum
noncomputable def UpperTheory.Reformulated.B.Qj21.z0c :
    {N1 : ℕ} → List (ℕ × Fin N1) → ℕ :=
    fun {N1 : ℕ} (L : List (ℕ × Fin N1)) ↦
      (List.map (fun (c : ℕ × Fin N1) ↦ if c.1 = (0 : ℕ) then (1 : ℕ) else (0 : ℕ)) L).sum
noncomputable def UpperTheory.Reformulated.B.Qj21.MS :
    {H : Type} → {N0 N1 : ℕ} → H → ℕ → ℕ → Submodule ℤ (UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (a b : ℕ) ↦
      Submodule.span ℤ
        {Q : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 |
          ∃ (L : List (ℕ × Fin N1)),
            Q = UpperTheory.Reformulated.B.Qj21.tmL t L (1 : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) ∧
              UpperTheory.Reformulated.B.Qj21.nzc L = a ∧ UpperTheory.Reformulated.B.Qj21.z0c L = b}


