-- Prove2me | Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central
-- name    : Formalism_CyclotomicNorms_NonsquarefreeBounds_Central
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:15:40.819817+00:00
-- url     : https://prove2.me/theorems/33aa5272-4874-4605-a20a-40823569b08d
-- title:
--   Central
-- statement:
--   Definitions and structural lemmas for Central, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.CyclotomicNorms
namespace CentralScalarSequence
variable {G : Type} [Group G]
def insN (i : ℕ) (a : G) (y : ℕ → G) : ℕ → G :=
  fun k => if k < i then y k else if k = i then a else y (k - 1)
def contrN (j : ℕ) (y : ℕ → G) : ℕ → G :=
  fun k => if k < j then y k else if k = j then y k * y (k + 1) else y (k + 1)
def extN {m : ℕ} (x : Fin m → G) : ℕ → G := fun k => if h : k < m then x ⟨k, h⟩ else 1
section seq
variable (a : G) (y : ℕ → G)
end seq
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
def prism (R : Type) [CommRing R] [Module R W] {n : ℕ} (z : G) (f : (Fin (n + 1) → G) → W)
    (x : Fin n → G) : W :=
  ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • f (Fin.insertNth (α := fun _ => G) i z x)
end CentralScalarSequence
end Formalism.CyclotomicNorms


