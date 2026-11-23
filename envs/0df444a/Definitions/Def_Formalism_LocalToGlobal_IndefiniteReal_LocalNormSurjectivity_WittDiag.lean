-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittDiag
-- name    : Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittDiag
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:43.369804+00:00
-- url     : https://prove2.me/theorems/7fbe0055-fc36-46b3-b7f2-5f5989833297
-- title:
--   Witt Diag
-- statement:
--   Definitions and structural lemmas for Witt Diag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittDiag.lean

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
namespace Formalism.IndefR.LocBrg.Witt
variable {R : Type} [CommRing R]
def cTr (σ : R →+* R) {m p : Type} (M : Matrix m p R) : Matrix p m R := (M.map σ)ᵀ
def hq (σ : R →+* R) {m : Type} [Fintype m] (H : Matrix m m R) (x : m → R) : R :=
  ∑ a, ∑ b, σ (x a) * H a b * x b
def IsDiagU {m : Type} (M : Matrix m m R) : Prop := (∀ i j, i ≠ j → M i j = 0) ∧ ∀ i, IsUnit (M i i)
def blk0 {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of (Fin.cons (Fin.cons c fun _ => 0) fun i => Fin.cons 0 (M i))
section Local
variable [IsLocalRing R]
variable (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x)
end Local
section Main
variable [IsLocalRing R] (σ : R →+* R)
def colE {n : ℕ} (x : Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun a b => Fin.cases (x a) (fun b' => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) a b'.succ) b
def gsR {n : ℕ} (u : R) (m : Fin n → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of (Fin.cons (Fin.cons 1 fun j => -(u * m j)) fun i => Fin.cons 0 ((1 : Matrix (Fin n) (Fin n) R) i))
end Main
section Anti
variable [IsLocalRing R] (σ : R →+* R)
def antiJR (n : ℕ) : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => if i = Fin.rev j then 1 else 0
def sq {m : Type} [Fintype m] (x y : m → R) : R := ∑ a, σ (x a) * y a
end Anti
section Anti2
variable [IsLocalRing R] (σ : R →+* R)
def colQ {n : ℕ} (t h : R) (b : Fin n) : Fin n → R :=
  if b = Fin.rev b then Pi.single b 1
  else if b.val < (Fin.rev b).val then Pi.single b 1 + Pi.single (Fin.rev b) t
  else Pi.single (Fin.rev b) h + Pi.single b (-(t * h))
end Anti2
section Anti3
variable [IsLocalRing R] (σ : R →+* R)
def matQ {n : ℕ} (t h : R) : Matrix (Fin n) (Fin n) R := Matrix.of fun a b => colQ t h b a
end Anti3
end Formalism.IndefR.LocBrg.Witt


