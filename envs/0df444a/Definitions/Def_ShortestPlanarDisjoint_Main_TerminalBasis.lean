-- Prove2me | Definitions.Def_ShortestPlanarDisjoint_Main_TerminalBasis
-- name    : ShortestPlanarDisjoint_Main_TerminalBasis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:22.623034+00:00
-- url     : https://prove2.me/theorems/d6dfa674-0794-44de-836b-6bb0e462689b
-- title:
--   Stack basis, admissible caps and addition programs
-- statement:
--   For a word sigma in {x,y}^h, scan its positions from left to right, matching each y to the most recent unmatched x when one exists. Let C(sigma) be these caps and U(sigma) the unmatched x positions. Over a commutative coefficient ring R define
--
--   $$B_\sigma=\prod_{(i,j)\in C(\sigma)}(t_i+t_j)\prod_{i\in U(\sigma)}t_i.$$
--
--   Multiaffinity means that every exponent in the polynomial support is at most one. Ordinary coefficient arrays and B-coordinate arrays define actual multivariate polynomials. An admissible cap set is a noncrossing partial matching with increasing endpoints and every interior position covered. Its uncovered positions are relabelled in increasing order. Cap insertion writes x and y at the two endpoints of each cap and the core word at uncovered positions; Delta_C is the corresponding product of binomials.
--
--   An addition program begins with the ordinary coefficient array and appends sums of two earlier registers. Its output wires select the converted coordinates. Definitions assert neither a basis theorem nor a conversion bound. The lemma states all identities over every characteristic-two commutative ring, including rings of polynomials or Laurent polynomials in other variables.
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Section 5.6, Lemma 5.9, p. 27 (PDF p. 29)

import Definitions.Def_ShortestPlanarDisjoint_Main_StateSignature

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
noncomputable section

abbrev BlockWord (h : ℕ) := Fin h → Bool
abbrev BlockPolynomial (R : Type*) [CommRing R] (h : ℕ) := MvPolynomial (Fin h) R

/-- Scan x/y left to right, pairing each y with the last unmatched x. -/
def blockStack {h : ℕ} (word : BlockWord h) : List (Fin h) × Finset (Fin h × Fin h) :=
  (List.finRange h).foldl (fun state i =>
    if word i then (i :: state.1, state.2) else
      match state.1 with
      | [] => state
      | j :: rest => (rest, insert (j,i) state.2)) ([], ∅)

def blockCaps {h : ℕ} (word : BlockWord h) := (blockStack word).2

def blockBasis {R : Type*} [CommRing R] {h : ℕ} (word : BlockWord h) : BlockPolynomial R h :=
  (∏ ij ∈ blockCaps word, (MvPolynomial.X ij.1 + MvPolynomial.X ij.2)) *
    ((blockStack word).1.map (fun i => (MvPolynomial.X i : BlockPolynomial R h))).prod

def wordExponent {h : ℕ} (word : BlockWord h) : Fin h →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i => if word i then 1 else 0) (by simp)

def IsMultiaffine {R : Type*} [CommRing R] {h : ℕ} (p : BlockPolynomial R h) : Prop :=
  ∀ a ∈ p.support, ∀ i, a i ≤ 1

def ordinaryPolynomial {R : Type*} [CommRing R] {h : ℕ} (a : BlockWord h → R) : BlockPolynomial R h :=
  ∑ word, MvPolynomial.monomial (wordExponent word) (a word)

def basisPolynomial {R : Type*} [CommRing R] {h : ℕ} (a : BlockWord h → R) : BlockPolynomial R h :=
  ∑ word, MvPolynomial.C (a word) * blockBasis word

/-- Noncrossing partial matching enclosing only fully covered positions. These
are precisely the admissibility conditions preceding Lemma 5.9. -/
structure AdmissibleCaps (h : ℕ) where
  pairs : Finset (Fin h × Fin h)
  increasing : ∀ ij ∈ pairs, ij.1 < ij.2
  disjoint : ∀ ij ∈ pairs, ∀ uv ∈ pairs, ij ≠ uv →
    ij.1 ≠ uv.1 ∧ ij.1 ≠ uv.2 ∧ ij.2 ≠ uv.1 ∧ ij.2 ≠ uv.2
  noncrossing : ∀ ij ∈ pairs, ∀ uv ∈ pairs,
    ¬ (ij.1 < uv.1 ∧ uv.1 < ij.2 ∧ ij.2 < uv.2)
  enclosed : ∀ ij ∈ pairs, ∀ u, ij.1 < u → u < ij.2 →
    ∃ uv ∈ pairs, u = uv.1 ∨ u = uv.2

def AdmissibleCaps.free {h : ℕ} (C : AdmissibleCaps h) : Finset (Fin h) :=
  Finset.univ.filter fun i => ∀ ij ∈ C.pairs, i ≠ ij.1 ∧ i ≠ ij.2

def AdmissibleCaps.freePosition {h : ℕ} (C : AdmissibleCaps h) :
    Fin C.free.card ↪o Fin h := C.free.orderEmbOfFin rfl

def AdmissibleCaps.insertWord {h : ℕ} (C : AdmissibleCaps h)
    (word : BlockWord C.free.card) : BlockWord h := by
  classical
  exact fun i => if hi : i ∈ C.free then
    word ((C.free.orderIsoOfFin rfl).symm ⟨i,hi⟩)
    else decide (∃ j, (i,j) ∈ C.pairs)

def AdmissibleCaps.delta {R : Type*} [CommRing R] {h : ℕ} (C : AdmissibleCaps h) : BlockPolynomial R h :=
  ∏ ij ∈ C.pairs, (MvPolynomial.X ij.1 + MvPolynomial.X ij.2)

def AdmissibleCaps.liftCaps {h : ℕ} (C : AdmissibleCaps h)
    (word : BlockWord C.free.card) : Finset (Fin h × Fin h) :=
  (blockCaps word).image fun ij => (C.freePosition ij.1, C.freePosition ij.2)

/-- An addition-only straight-line program. The initial registers are the 2^h
ordinary coefficients, indexed by words via equivFin. Every new register is the
sum of two earlier registers. No basis inversion is an input oracle. -/
structure AdditionProgram (h : ℕ) where
  additions : List (ℕ × ℕ)
  valid : ∀ i (hi : i < additions.length),
    (additions[i]'hi).1 < Fintype.card (BlockWord h) + i ∧
    (additions[i]'hi).2 < Fintype.card (BlockWord h) + i
  output : BlockWord h → ℕ
  output_valid : ∀ word, output word < Fintype.card (BlockWord h) + additions.length

def AdditionProgram.eval {R : Type*} [CommRing R] {h : ℕ} (P : AdditionProgram h)
    (input : BlockWord h → R) : BlockWord h → R :=
  let initial := List.ofFn (fun i : Fin (Fintype.card (BlockWord h)) =>
    input ((Fintype.equivFin (BlockWord h)).symm i))
  let values := P.additions.foldl (fun values ij =>
    values ++ [values[ij.1]?.getD 0 + values[ij.2]?.getD 0]) initial
  fun word => values[P.output word]?.getD 0

end
end ShortestPlanarDisjoint.Main


