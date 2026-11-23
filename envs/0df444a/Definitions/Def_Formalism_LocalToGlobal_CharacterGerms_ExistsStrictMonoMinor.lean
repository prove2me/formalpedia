-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
-- name    : Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:04.70883+00:00
-- url     : https://prove2.me/theorems/962dcd70-6582-464c-964e-78ddc4244fe6
-- title:
--   Exists Strict Mono Minor
-- statement:
--   Definitions and structural lemmas for Exists Strict Mono Minor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace Formalism.L2.FormalSeriesBounds.S4
section Minors
variable {R : Type*} [CommRing R]
def lenCoker (v : AddValuation R (WithTop ℝ)) {m h : ℕ} (B : Matrix (Fin m) (Fin h) R) :
    WithTop ℝ :=
  Finset.univ.inf fun g : Fin m → Fin h => v (B.submatrix id g).det
def fitt0 {m h : ℕ} (B : Matrix (Fin m) (Fin h) R) : Ideal R :=
  Ideal.span (Set.range fun g : Fin m → Fin h => (B.submatrix id g).det)
end Minors
section Numbers
def gam (l : ℕ) : ℝ := (l : ℝ) / ((l : ℝ) ^ 2 - 1)
def rho (l : ℕ) : ℝ := 1 / ((l : ℝ) ^ 2 - 1)
def frobSum {d : ℕ} (l : ℕ) (p : ZMod d → ℕ) (τ : ZMod d) : ℝ :=
  ∑' k : ℕ, ((l : ℝ) ^ (k + 1))⁻¹ * (p (τ + ((k + 1 : ℕ) : ZMod d)) : ℝ)
def CorDET {d : ℕ} (l : ℕ) (p : ZMod d → ℕ) (l1 l2 : ZMod d → ℝ) (τ : ZMod d) : Prop :=
  l1 τ - l2 τ = (p τ : ℝ) / ((l : ℝ) - 1) - frobSum l p τ
def ThmAi {d : ℕ} (l r rh : ℕ) (p : ZMod d → ℕ) (l2 : ZMod d → ℝ) (τ : ZMod d) : Prop :=
  l2 τ ≤ ((r : ℝ) - rh - p τ) / ((l : ℝ) - 1)
def ThmAiii {R : Type*} [CommRing R] (v : AddValuation R (WithTop ℝ)) {m h : ℕ}
    (α : Matrix (Fin m) (Fin h) R) (l1 : ℝ) : Prop :=
  lenCoker v α = (l1 : WithTop ℝ)
def xInert (l r j' rh : ℕ) : ℝ := ((r : ℝ) - 2 * j') * gam l + ((j' : ℝ) - rh) / ((l : ℝ) - 1)
end Numbers
section Derivatives
variable {R : Type*} [CommRing R]
def detOp {F : Type*} [AddCommGroup F] [Module R F] {n : ℕ}
    (D : Fin n → Fin n → Module.End R F) : Module.End R F :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) • (List.ofFn fun ρ => D ρ (σ ρ)).prod
end Derivatives
section Main
variable {R : Type*} [CommRing R]
end Main
end Formalism.L2.FormalSeriesBounds.S4


