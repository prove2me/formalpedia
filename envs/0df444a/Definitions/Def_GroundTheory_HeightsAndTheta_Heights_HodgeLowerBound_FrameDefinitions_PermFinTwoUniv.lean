-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_PermFinTwoUniv
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_PermFinTwoUniv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:48.720305+00:00
-- url     : https://prove2.me/theorems/a1c3e800-d6c0-497d-aaad-0606b0b98710
-- title:
--   Perm Fin Two Univ
-- statement:
--   Definitions and structural lemmas for Perm Fin Two Univ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/PermFinTwoUniv.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial
section Roots
variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
abbrev RootPoly : Type := MvPolynomial (Ψ × Fin N) ℚ
def weylAct (w : Ψ → Equiv.Perm (Fin N)) (p : Ψ × Fin N) : Ψ × Fin N := (p.1, w p.1 p.2)
def weylSign (w : Ψ → Equiv.Perm (Fin N)) : ℚ :=
  ∏ τ, ((((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ)) : ℚ)
def antisym (P : RootPoly Ψ N) : RootPoly Ψ N :=
  ∑ w : Ψ → Equiv.Perm (Fin N), weylSign Ψ N w • rename (weylAct Ψ N w) P
def rhoMono : Ψ × Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => N - 1 - (p.2 : ℕ)
def flagInt (P : RootPoly Ψ N) : ℚ := coeff (rhoMono Ψ N) (antisym Ψ N P)
variable (j : ℕ)
def IsBlockPerm (w : Ψ → Equiv.Perm (Fin N)) : Prop := ∀ τ i, ((w τ i : ℕ) < j ↔ (i : ℕ) < j)
instance (w : Ψ → Equiv.Perm (Fin N)) : Decidable (IsBlockPerm Ψ N j w) := by
  unfold IsBlockPerm; infer_instance
def rhoBlock : Ψ × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => if (p.2 : ℕ) < j then j - 1 - (p.2 : ℕ) else N - 1 - (p.2 : ℕ)
def blockInt (P : RootPoly Ψ N) : ℚ :=
  coeff (rhoBlock Ψ N j)
    (∑ w ∈ Finset.univ.filter (IsBlockPerm Ψ N j), weylSign Ψ N w • rename (weylAct Ψ N w) P)
def la0 (p : Ψ × Fin N) : ℤ := if (p.2 : ℕ) < j then 0 else -1
def c1L (la : Ψ × Fin N → ℤ) : RootPoly Ψ N := -∑ p, (la p : ℚ) • X p
def muPoly : RootPoly Ψ N := ∑ p ∈ Finset.univ.filter (fun p : Ψ × Fin N => ¬ (p.2 : ℕ) < j), X p
def vandBlocks : RootPoly Ψ N :=
  ∏ τ, ∏ ab ∈ Finset.univ.filter
      (fun ab : Fin N × Fin N => ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)),
    (X (τ, ab.1) - X (τ, ab.2))
def fib (cf : ℚ) : RootPoly Ψ N := C cf * vandBlocks Ψ N j
def fdeg : ℚ := blockInt Ψ N j (vandBlocks Ψ N j)
def dimN : ℕ := Fintype.card Ψ * j * (N - j)
def FA (cf : ℚ) : RootPoly Ψ N := muPoly Ψ N j ^ (dimN Ψ N j + 1) * fib Ψ N j cf
def Jint (cf : ℚ) : ℚ := flagInt Ψ N (muPoly Ψ N j ^ dimN Ψ N j * fib Ψ N j cf)
end Roots
def abelian₂ (B rd Lval : ℝ) : ℝ := Real.log (B * rd) + |Lval|
section Line
end Line
end GroundTheory.Heights₂.Heights.LowerBoundFree


