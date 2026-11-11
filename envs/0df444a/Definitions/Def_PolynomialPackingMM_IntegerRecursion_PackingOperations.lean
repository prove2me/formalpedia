-- Prove2me | Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations
-- name    : PolynomialPackingMM_IntegerRecursion_PackingOperations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:03.627211+00:00
-- url     : https://prove2.me/theorems/0d7e5649-c6b6-428d-aa0b-f4a0191cd64a
-- title:
--   Finite packing operations, amplification counts and round hypotheses
-- statement:
--   Finite task-list operations describe source zero-padding, target deletion, source addition and independent repetition. Products are isomorphic only when dimensions agree and all three monomial supports share one variable renaming. For same-left packings a common renaming acts on every task.
--
--   For $d,m\ge1$, the retained amplification count is the exact integer ceiling
--
--   $$w=\left\lceil\frac{m^{2d}}{d+1}\right\rceil=\frac{m^{2d}+d}{d+1}\quad\text{(integer division on the right).}$$
--
--   The word count is the cardinality of pairs of length-$d$ words over the two tagged alphabets $(\mathrm{Fin}\,f)\sqcup(\mathrm{Fin}\,g)$ and $(\mathrm{Fin}\,g)\sqcup(\mathrm{Fin}\,f)$, retaining exactly $d$ Full letters in total. The two round hypotheses retain both parameter triples and a source count at most $2w$. Ordinary matrix multiplication is recognized by all three supports being the constant monomial.
--
--   These are specifications and explicit finite operations; none asserts that a packing exists. **Formalization Note** All tagged letters remain distinct, even when one alphabet has size zero. Tensor units and finite empty task lists are retained.
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 10 (PDF 11), Observation 2.5; Lemma 2.10, p. 12; equation (8) and Claim 3.3, p. 14; Lemma 4.2 hypotheses, p. 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_Packing

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

noncomputable def repeatTasks (k : ℕ) (T : Tasks) : Tasks := (List.replicate k T).flatten

/-- Source matrix zero-padding changes dimensions, retaining all three monomial supports. -/
def IsSourcePadding (P Q : SelectedProduct) : Prop :=
  P.shape = Q.shape ∧ ∀ i, P.edge i ≤ Q.edge i

def TasksIsomorphic (T T' : Tasks) : Prop := List.Forall₂ SelectedProduct.Isomorphic T T'

def SourcePadding (S S' : Tasks) : Prop := List.Forall₂ IsSourcePadding S S'

noncomputable def Shape.rename (P : Shape) (π : Equiv.Perm (Fin P.numVars)) : Shape :=
  ⟨P.numVars, renameSupport π P.left, renameSupport π P.right, renameSupport π P.output⟩

/-- One common coordinate permutation for every target and source (SL clause of Lemma 2.10). -/
def CommonRenaming (T S T' S' : Tasks) : Prop :=
  ∃ (m : ℕ) (π : Equiv.Perm (Fin m)),
    (List.Forall₂ (fun P Q => P.edge = Q.edge ∧
      ∃ h : P.shape.numVars = m,
        Q.shape = P.shape.rename (h ▸ π)) T T') ∧
    (List.Forall₂ (fun P Q => P.edge = Q.edge ∧
      ∃ h : P.shape.numVars = m,
        Q.shape = P.shape.rename (h ▸ π)) S S')

noncomputable def mixedTargets (m a b : ℕ) (p q r : ℕ+) (choices : Fin m → Bool) : Tasks :=
  List.ofFn (fun i => product (if choices i then full a b else mid a b) p q r)

/-- Exactly the ceiling in equation (8); no real-number rounding or truncation is involved. -/
def amplifiedCount (d m : ℕ) : ℕ := (m ^ (2 * d) + d) / (d + 1)

def fullLetters {f g d : ℕ} (w : (Fin d → Fin f ⊕ Fin g) × (Fin d → Fin g ⊕ Fin f)) : ℕ :=
  ((List.finRange d).filter (fun i => (w.1 i).isLeft)).length +
    ((List.finRange d).filter (fun i => (w.2 i).isLeft)).length

noncomputable def balancedWordCount (f g d : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : (Fin d → Fin f ⊕ Fin g) × (Fin d → Fin g ⊕ Fin f) =>
    fullLetters w = d)).card

/-- All singleton supports are the constant monomial, regardless of the number of dummy variables. -/
def IsOrdinaryMatrixProduct (P : SelectedProduct) : Prop :=
  P.shape.left = {0} ∧ P.shape.right = {0} ∧ P.shape.output = {0}

/-- Both hypotheses of Lemma 4.2, with a bounded source count and one common exact/modulo mode. -/
def RoundHypothesis (mode : Mode) (d L L' u w : ℕ+) : Prop :=
  ∀ a : ℕ, a = (L : ℕ) ∨ a = (L' : ℕ) →
    ∃ k : ℕ, k ≤ 2 * (w : ℕ) ∧
      HasPacking mode
        (copies w (product (balanced d a L) 1 1 w))
        (copies k (product (balanced d a L') 1 1 u))

end PolynomialPackingMM.IntegerRecursion


