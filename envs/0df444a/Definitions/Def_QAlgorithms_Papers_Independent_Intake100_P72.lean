-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P72
-- name    : QAlgorithms_Papers_Independent_Intake100_P72
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T14:48:00.158688+00:00
-- url     : https://prove2.me/theorems/787e3720-16d9-435a-9e23-09b4f57e542f
-- title:
--   Definitions for On the semisimplicity of cyclotomic Baruer algebras, II
-- statement:
--   The objects the formalized statements of *On the semisimplicity of cyclotomic Baruer algebras, II* (arXiv:math/0702633) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BrauerRel`: Exactly relations (a)--(q), PDF p.3, including both equalities in (k) and (o). Every index is guarded; no extra free generators are present.
--   - `CyclotomicBrauer`: The cyclotomic Brauer algebra over an arbitrary commutative unital ring, using the generators-and-relations definition on PDF p.3.
--   - `brauerQuotientMap`: Canonical quotient map for the presentation, PDF p.3.
--   - `brauerGenerator`: Canonical image of any valid source generator, PDF p.3.
--   - `brauerT`: Canonical t_(i+1), with auxiliary zero outside its range, PDF p.3.
--   - `HasSplitWedderburn`: Finite split semisimplicity in the sense of PDF p.2: existence of an algebra isomorphism to a finite product of full matrix algebras over F. The sizes are positive; a supplied decomposition is never a hypothesis.
-- source:
--   On the semisimplicity of cyclotomic Baruer algebras, II, arXiv:math/0702633v1, https://arxiv.org/abs/math/0702633v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P16

/-!
Rui--Xu, arXiv:math/0702633v1, PDF pp.2--3,14--15.
The algebra below uses the complete presentation (a)--(q) on PDF p.3.
Generator indices in Lean are zero based. Parameters are indexed by ZMod m,
so the source convention delta_m = delta_0 is built into the parameter type.
The deferred cellular and diagram constructions are recorded in HARD.md;
no arbitrary forms, modules or decomposition data stand in for those objects.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P72

universe u v

/- The accepted BMWLetter is reused only as a free symbol type: its s and e
slots are indexed by Fin (n-1), and its x slot by Fin n. Here the x slot denotes
the source's t symbol. The imported freeS/freeE/freeX have no relations; the
Brauer quotient below imposes exactly the relations on PDF p.3. No affine BMW
quotient, skein relation, or source theorem from that module is used. -/
open QAlgorithms.Papers.Independent.Renew46.P16 (BMWLetter freeS freeE freeX)

/-- Exactly relations (a)--(q), PDF p.3, including both equalities in (k)
and (o). Every index is guarded; no extra free generators are present. -/
inductive BrauerRel (R : Type u) [CommRing R] (m n : ℕ) (delta : ZMod m → R) :
    FreeAlgebra R (BMWLetter n) → FreeAlgebra R (BMWLetter n) → Prop
  | a (i : ℕ) (hi : i + 1 < n) :
      BrauerRel R m n delta (freeS R n i ^ 2) (1)
  | b (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n)
      (hfar : i + 1 < j ∨ j + 1 < i) :
      BrauerRel R m n delta (freeS R n i * freeS R n j) (freeS R n j * freeS R n i)
  | c (i : ℕ) (hi : i + 2 < n) :
      BrauerRel R m n delta (freeS R n i * freeS R n (i + 1) * freeS R n i) (freeS R n (i + 1) * freeS R n i * freeS R n (i + 1))
  | d (i j : ℕ) (hi : i + 1 < n) (hj : j < n) (hji : j ≠ i) (hji1 : j ≠ i + 1) :
      BrauerRel R m n delta (freeS R n i * freeX R n j) (freeX R n j * freeS R n i)
  | e (i : ℕ) (hi : i + 1 < n) :
      BrauerRel R m n delta (freeE R n i ^ 2) (algebraMap R (FreeAlgebra R (BMWLetter n)) (delta 0) * freeE R n i)
  | f (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n)
      (hfar : i + 1 < j ∨ j + 1 < i) :
      BrauerRel R m n delta (freeS R n i * freeE R n j) (freeE R n j * freeS R n i)
  | g (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n)
      (hfar : i + 1 < j ∨ j + 1 < i) :
      BrauerRel R m n delta (freeE R n i * freeE R n j) (freeE R n j * freeE R n i)
  | h (i j : ℕ) (hi : i + 1 < n) (hj : j < n) (hji : j ≠ i) (hji1 : j ≠ i + 1) :
      BrauerRel R m n delta (freeE R n i * freeX R n j) (freeX R n j * freeE R n i)
  | i (i j : ℕ) (hi : i < n) (hj : j < n) :
      BrauerRel R m n delta (freeX R n i * freeX R n j) (freeX R n j * freeX R n i)
  | j (i : ℕ) (hi : i + 1 < n) :
      BrauerRel R m n delta (freeS R n i * freeX R n i) (freeX R n (i + 1) * freeS R n i)
  | kLeft (i : ℕ) (hi : i + 1 < n) :
      BrauerRel R m n delta (freeE R n i * freeS R n i) (freeE R n i)
  | kRight (i : ℕ) (hi : i + 1 < n) :
      BrauerRel R m n delta (freeS R n i * freeE R n i) (freeE R n i)
  | l (i : ℕ) (hi : i + 2 < n) :
      BrauerRel R m n delta (freeS R n i * freeE R n (i + 1) * freeE R n i) (freeS R n (i + 1) * freeE R n i)
  | m (i : ℕ) (hi : i + 2 < n) :
      BrauerRel R m n delta (freeE R n (i + 1) * freeE R n i * freeS R n (i + 1)) (freeE R n (i + 1) * freeS R n i)
  | n (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n)
      (hnear : i + 1 = j ∨ j + 1 = i) :
      BrauerRel R m n delta (freeE R n i * freeE R n j * freeE R n i) (freeE R n i)
  | oLeft (i : ℕ) (hi : i + 1 < n) :
      BrauerRel R m n delta (freeE R n i * freeX R n i * freeX R n (i + 1)) (freeE R n i)
  | oRight (i : ℕ) (hi : i + 1 < n) :
      BrauerRel R m n delta (freeX R n i * freeX R n (i + 1) * freeE R n i) (freeE R n i)
  | p (i a : ℕ) (hi : i + 1 < n) (ha : 1 ≤ a) (ham : a < m) :
      BrauerRel R m n delta (freeE R n i * freeX R n i ^ a * freeE R n i) (algebraMap R (FreeAlgebra R (BMWLetter n)) (delta (a : ZMod m)) * freeE R n i)
  | q (i : ℕ) (hi : i < n) :
      BrauerRel R m n delta (freeX R n i ^ m) (1)

/-- The cyclotomic Brauer algebra over an arbitrary commutative unital ring,
using the generators-and-relations definition on PDF p.3. -/
abbrev CyclotomicBrauer (R : Type u) [CommRing R] (m n : ℕ) (delta : ZMod m → R) :=
  RingQuot (BrauerRel R m n delta)

/-- Canonical quotient map for the presentation, PDF p.3. -/
def brauerQuotientMap (R : Type u) [CommRing R] (m n : ℕ) (delta : ZMod m → R) :
    FreeAlgebra R (BMWLetter n) →ₐ[R] CyclotomicBrauer R m n delta :=
  RingQuot.mkAlgHom R (BrauerRel R m n delta)

/-- Canonical image of any valid source generator, PDF p.3. -/
def brauerGenerator (R : Type u) [CommRing R] (m n : ℕ) (delta : ZMod m → R)
    (g : BMWLetter n) : CyclotomicBrauer R m n delta :=
  brauerQuotientMap R m n delta (FreeAlgebra.ι R g)

/-- Canonical t_(i+1), with auxiliary zero outside its range, PDF p.3. -/
def brauerT (R : Type u) [CommRing R] (m n : ℕ) (delta : ZMod m → R) (i : ℕ) :
    CyclotomicBrauer R m n delta :=
  brauerQuotientMap R m n delta (freeX R n i)

/-- Finite split semisimplicity in the sense of PDF p.2: existence of an
algebra isomorphism to a finite product of full matrix algebras over F.
The sizes are positive; a supplied decomposition is never a hypothesis. -/
def HasSplitWedderburn (F : Type u) [Field F] (A : Type v) [Ring A] [Algebra F A] : Prop :=
  ∃ r : ℕ, ∃ d : Fin r → ℕ, (∀ i, 0 < d i) ∧
    Nonempty (A ≃ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F))

/-- Sanity: at one strand the presentation has no crossing or cap-cup. -/
example (R : Type u) [CommRing R] :
    freeS R 1 0 = 0 ∧ freeE R 1 0 = 0 := by
  simp [freeS, freeE]

/-- Sanity: at one strand the t generator is present, including t_n. -/
example (R : Type u) [CommRing R] :
    freeX R 1 0 = FreeAlgebra.ι R (BMWLetter.x (0 : Fin 1)) := by
  simp [freeX]

/-- Sanity: the sole one-strand generator has the exact cyclic relation. -/
example (R : Type u) [CommRing R] (m : ℕ) (delta : ZMod m → R) :
    brauerT R m 1 delta 0 ^ m = 1 := by
  have h := RingQuot.mkAlgHom_rel R
    (BrauerRel.q (R := R) (m := m) (n := 1) (delta := delta) 0 (by decide))
  simpa only [brauerT, brauerQuotientMap, map_pow, map_one] using h

/-- Sanity: a single positive matrix block satisfies the split predicate. -/
example (F : Type u) [Field F] :
    HasSplitWedderburn F (Fin 1 → Matrix (Fin 1) (Fin 1) F) := by
  exact ⟨1, (fun _ => 1), (fun _ => Nat.zero_lt_succ 0), ⟨AlgEquiv.refl⟩⟩

end QAlgorithms.Papers.Independent.Intake100.P72


