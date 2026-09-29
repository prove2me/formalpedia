-- Prove2me | Definitions.Def_mme_dwz_cw_square_fine_central_channels
-- name    : mme_dwz_cw_square_fine_central_channels
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T03:45:57.061143+00:00
-- url     : https://prove2.me/theorems/33ac5ccc-5804-40b7-bbc0-ae8172ec00fb
-- title:
--   Fine source labels for the central 022 and 202 constituents of the CW square
-- statement:
--   For the central constituents of the square of the Coppersmith–Winograd tensor, this interface records the exact source-basis channels rather than only their total dimension. The 022 constituent has two exceptional one-dimensional channels and one channel for each ordered pair in $[q]^2$; the 202 constituent uses the same channel coordinate after rotating tensor modes. The interface gives the corresponding canonical CW-square basis pair in each of the three modes and the matching standard matrix-multiplication basis vectors.
--
--   Thus the common channel set has size
--
--   $$
--   q^2+2,
--   $$
--
--   with an explicit equivalence to the standard finite coordinate set. These labels support source-faithful zeroing arguments for tensor powers, where retaining a prescribed word must refer to its actual CW coordinates rather than to an arbitrary subspace of the same dimension.
--
--   **Formalization Note** The definitions use the public canonical five-grading of the CW square and distinguish the source order “left, middle, right” from the router order “two exceptional channels, then ordered pairs.”
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 (PDF pp. 59–60 / printed pp. 58–59) and Appendix A, proof of Lemma 4.6(c) (PDF pp. 82–83 / printed pp. 81–82), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_CW_square_canonical_grading

namespace MME.DWZFineChannel

universe u

set_option autoImplicit false

/-- The two one-dimensional outer channels and the `q^2` middle channels of
the CW-square 022 constituent, in source order `left | middle | right`. -/
def Fine022Channel (q : ℕ) :=
  Fin 1 ⊕ ((Fin q × Fin q) ⊕ Fin 1)

/-- The same channel labels viewed in the 202 mode rotation. -/
abbrev Fine202Channel (q : ℕ) := Fine022Channel q

/-- Reorder source channels into the router order `two specials | q^2`. -/
def fine022ToCentralSum (q : ℕ) :
    Fine022Channel q ≃ (Fin 2 ⊕ (Fin q × Fin q)) where
  toFun
    | Sum.inl _ => Sum.inl 0
    | Sum.inr (Sum.inl ij) => Sum.inr ij
    | Sum.inr (Sum.inr _) => Sum.inl 1
  invFun
    | Sum.inl k => if k = 0 then Sum.inl 0 else Sum.inr (Sum.inr 0)
    | Sum.inr ij => Sum.inr (Sum.inl ij)
  left_inv c := by
    rcases c with a | c
    · fin_cases a
      rfl
    · rcases c with ij | a
      · rfl
      · fin_cases a
        rfl
  right_inv c := by
    rcases c with k | ij
    · fin_cases k <;> simp
    · simp

/-- The exact finite MM coordinate used by both the 022 and 202 routers. -/
noncomputable def fine022ChannelEquiv (q : ℕ) :
    Fine022Channel q ≃ Fin (q ^ 2 + 2) :=
  (fine022ToCentralSum q).trans <|
    (Equiv.sumCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans <|
      finSumFinEquiv.trans (finCongr (by simp [pow_two, Nat.add_comm]))

noncomputable def fine202ChannelEquiv (q : ℕ) :
    Fine202Channel q ≃ Fin (q ^ 2 + 2) :=
  fine022ChannelEquiv q

def cwO (q : ℕ) : Fin (q + 2) := ⟨0, by omega⟩
def cwM (q : ℕ) (i : Fin q) : Fin (q + 2) := ⟨i.val + 1, by omega⟩
def cwT (q : ℕ) : Fin (q + 2) := ⟨q + 1, by omega⟩

/-- Exact canonical CW-square basis-pair labels of every 022 channel. -/
def fine022SourcePair (q : ℕ) (c : Fine022Channel q) :
    Fin 3 → Fin (q + 2) × Fin (q + 2)
  | ⟨0, _⟩ => (cwO q, cwO q)
  | ⟨1, _⟩ =>
      match c with
      | Sum.inl _ => (cwO q, cwT q)
      | Sum.inr (Sum.inl ij) => (cwM q ij.1, cwM q ij.2)
      | Sum.inr (Sum.inr _) => (cwT q, cwO q)
  | ⟨2, _⟩ =>
      match c with
      | Sum.inl _ => (cwT q, cwO q)
      | Sum.inr (Sum.inl ij) => (cwM q ij.1, cwM q ij.2)
      | Sum.inr (Sum.inr _) => (cwO q, cwT q)

/-- The 202 rotation of the same exact canonical basis-pair labels. -/
def fine202SourcePair (q : ℕ) (c : Fine202Channel q) :
    Fin 3 → Fin (q + 2) × Fin (q + 2)
  | ⟨0, _⟩ =>
      match c with
      | Sum.inl _ => (cwO q, cwT q)
      | Sum.inr (Sum.inl ij) => (cwM q ij.1, cwM q ij.2)
      | Sum.inr (Sum.inr _) => (cwT q, cwO q)
  | ⟨1, _⟩ => (cwO q, cwO q)
  | ⟨2, _⟩ =>
      match c with
      | Sum.inl _ => (cwT q, cwO q)
      | Sum.inr (Sum.inl ij) => (cwM q ij.1, cwM q ij.2)
      | Sum.inr (Sum.inr _) => (cwO q, cwT q)

/-- Standard 022 matrix-multiplication basis vectors indexed by the shared
channel coordinate. -/
noncomputable def fine022MMVec
    (K : Type u) [Field K] (q : ℕ) (k : Fin (q ^ 2 + 2)) :
    ∀ s : Fin 3, (MMObj K 1 1 (q ^ 2 + 2)).V s
  | ⟨0, _⟩ =>
      (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)
  | ⟨1, _⟩ =>
      (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin (q ^ 2 + 2) → K)
  | ⟨2, _⟩ =>
      (Pi.single (k, (0 : Fin 1)) 1 : Fin (q ^ 2 + 2) × Fin 1 → K)

/-- Standard 202 matrix-multiplication basis vectors indexed by that same
channel coordinate. -/
noncomputable def fine202MMVec
    (K : Type u) [Field K] (q : ℕ) (k : Fin (q ^ 2 + 2)) :
    ∀ s : Fin 3, (MMObj K (q ^ 2 + 2) 1 1).V s
  | ⟨0, _⟩ =>
      (Pi.single (k, (0 : Fin 1)) 1 : Fin (q ^ 2 + 2) × Fin 1 → K)
  | ⟨1, _⟩ =>
      (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)
  | ⟨2, _⟩ =>
      (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin (q ^ 2 + 2) → K)

end MME.DWZFineChannel


