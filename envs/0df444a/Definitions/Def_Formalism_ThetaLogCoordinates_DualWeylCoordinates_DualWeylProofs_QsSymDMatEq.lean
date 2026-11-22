-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:35.799547+00:00
-- url     : https://prove2.me/theorems/b4cb2cc3-62ec-44c9-a793-6ed18400084b
-- title:
--   Qs Sym DMat Eq
-- statement:
--   Definitions and structural lemmas for Qs Sym DMat Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsSymDMatEq.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
def qs_cnt {ι : Type*} [Fintype ι] (a : ι → Fin n) (x : Fin n) : ℕ := (univ.filter fun c => a c = x).card
def qs_SM {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A) (b : ℕ) : Matrix (SymIdx n b) (SymIdx n b) A :=
  fun α β => MvPolynomial.coeff (symMono α) (∏ m : Fin n, (∑ a : Fin n, MvPolynomial.C (G a m) * X a) ^ (β.1 m : ℕ))
lemma qs_sum_cnt {ι : Type*} [Fintype ι] (a : ι → Fin n) : ∑ x, qs_cnt a x = Fintype.card ι := by
  classical
  simp only [qs_cnt]
  rw [← Finset.card_eq_sum_card_fiberwise (f := a) (s := univ) (t := univ) (fun _ _ => by simp)]
  simp
def qs_mon {ι : Type*} [Fintype ι] {b : ℕ} (hb : Fintype.card ι = b) (m : ι → Fin n) : SymIdx n b :=
  ⟨fun x => ⟨qs_cnt m x, by
    have := qs_sum_cnt m
    have h2 : qs_cnt m x ≤ ∑ x, qs_cnt m x := Finset.single_le_sum (f := qs_cnt m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    omega⟩, by simpa using (qs_sum_cnt m).trans hb⟩
def qs_gC (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord ℤ n) :=
  Matrix.of fun a b => algebraMap _ (GLCoord ℤ n) (genMat ℤ n a b)
def qs_gI (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord ℤ n) := Matrix.of fun a b => ginvC n a b
end Formalism.InvariantFactorPaths.ColumnFamilies


