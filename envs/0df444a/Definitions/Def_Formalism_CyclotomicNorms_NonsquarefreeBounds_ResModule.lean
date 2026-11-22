-- Prove2me | Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
-- name    : Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:18:37.151367+00:00
-- url     : https://prove2.me/theorems/b5706112-ef46-44ff-b010-3fb38f9510b5
-- title:
--   Res Module
-- statement:
--   Definitions and structural lemmas for Res Module, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
namespace Formalism.CyclotomicNorms
noncomputable section
namespace residueMatrixData
section SNF
variable {R : Type*} [CommRing R]
def ext1 {a : ℕ} (P : Matrix (Fin a) (Fin a) R) : Matrix (Fin (a+1)) (Fin (a+1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => P i' j') j) i
end SNF
section Trunc
variable {K' : Type} [Field K'] {n : ℕ}
local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)
def pbT (K' : Type) [Field K'] (n : ℕ) : PowerBasis K' (TruncK K' n) :=
  AdjoinRoot.powerBasis' (monic_X_pow n)
instance (K' : Type) [Field K'] (n : ℕ) : FiniteDimensional K' (TruncK K' n) := (pbT K' n).finite
end Trunc
section Mod
variable {K' : Type} [Field K'] {n : ℕ}
local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)
instance finite_sub {a : ℕ} (p : Submodule (TruncK K' n) (Fin a → TruncK K' n)) :
    Module.Finite K' ↥p :=
  Module.Finite.of_injective (p.subtype.restrictScalars K') Subtype.val_injective
end Mod
section Cyc
variable {K' : Type} [Field K'] {n : ℕ}
local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)
end Cyc
section KerD
variable {K' : Type} [Field K'] {n : ℕ}
local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)
end KerD
end residueMatrixData
end
end Formalism.CyclotomicNorms


