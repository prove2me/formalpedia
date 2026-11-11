-- Prove2me | Definitions.Def_CapacitatedKMedianFPT_Main_RandomSets
-- name    : CapacitatedKMedianFPT_Main_RandomSets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:24.44123+00:00
-- url     : https://prove2.me/theorems/c3147762-f600-4591-a768-da24a82a5998
-- title:
--   Independent random subsets, the random set R_L of a tuple of lists, and the procedure Fix
-- statement:
--   Objects of §5 for a finite ground set.
--
--   1. A distribution $D$ over subsets of $G$ is a mass function $D(X)\ge0$ with total mass $1$ and support among subsets of $G$; $\mathbb E[|X|]=\sum_XD(X)|X|$ and $\Pr[x\in X]=\sum_{X\ni x}D(X)$.
--   2. For independent $X_i\sim D_i$ ($i\in[k]$),
--   $$\mathbb E[v(X_1\cup\dots\cup X_k)]=\sum_{X_1,\dots,X_k}\Bigl(\prod_iD_i(X_i)\Bigr)v\Bigl(\bigcup_iX_i\Bigr).$$
--   3. For lists $L_1,\dots,L_k$ (multisets, repetitions allowed) and $\eta\in[0,1]$: every occurrence of an element of $L_i$ is put in $R_i$ independently with probability $\eta$, duplicates are removed, and $R_L=\bigcup_iR_i$. $\mathbb E[v(R_L)]$ is the corresponding finite sum over inclusion patterns.
--   4. **Fix** (Algorithm 4) returns $(x_1,\dots,x_k)\in L_1\times\dots\times L_k$ maximizing $v(\{x_1,\dots,x_k\})$; $x$ is an output of Fix if it is such a maximizer (ties broken arbitrarily).
--
--   These are the objects of Lemma 7 and Corollary 1.
--
--   **Formalization Note** Probabilities are real mass functions and expectations finite sums, so all expectations are finite.
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 16, definition of R_i, R_L and (5.1); p. 16, Lemma 7; p. 17, Algorithm 4 (Fix); p. 18, Corollary 1

import Mathlib

set_option autoImplicit false

/-!
# Independent random subsets, the random set `R_L` of a tuple of lists, and the procedure Fix

Anand–Huang–Jaiswal–Kumar–Lee–Yadav, STOC 2027 submission #1646, §5, p. 16–18 (Lemma 7,
Algorithm 4, Corollary 1).
-/

namespace CapacitatedKMedianFPT.Main

open scoped BigOperators

noncomputable section

variable {α : Type} [Fintype α] [DecidableEq α]

/-- `D` is a probability distribution over subsets of `G`, given by its mass function. -/
def IsSubsetLaw (D : Finset α → ℝ) (G : Finset α) : Prop :=
  (∀ X, 0 ≤ D X) ∧ ∑ X, D X = 1 ∧ ∀ X, D X ≠ 0 → X ⊆ G

/-- `E[|X|]` for `X ∼ D`. -/
def expectedCard (D : Finset α → ℝ) : ℝ := ∑ X, D X * (X.card : ℝ)

/-- `Pr[x ∈ X]` for `X ∼ D`. -/
def inclusionProb (D : Finset α → ℝ) (x : α) : ℝ := ∑ X, if x ∈ X then D X else 0

/-- `E[v(X_1 ∪ ⋯ ∪ X_k)]` for independent `X_i ∼ D_i` (product of the laws). -/
def expectedUnionValue {k : ℕ} (D : Fin k → Finset α → ℝ) (v : Finset α → ℝ) : ℝ :=
  ∑ X : Fin k → Finset α, (∏ i, D i (X i)) * v (Finset.univ.biUnion X)

/-- For an inclusion pattern `b` of the occurrences of the lists `L_i`, the set
`R_L = ⋃_i R_i` of included elements (duplicates removed). -/
def occurrenceSet {k : ℕ} (L : Fin k → List α) (b : (i : Fin k) → Fin (L i).length → Bool) :
    Finset α :=
  Finset.univ.biUnion
    (fun i => (Finset.univ.filter (fun j => b i j = true)).image (fun j => (L i).get j))

/-- Probability of the inclusion pattern `b` when every occurrence is included independently with
probability `η`. -/
def occurrenceWeight (η : ℝ) {k : ℕ} (L : Fin k → List α)
    (b : (i : Fin k) → Fin (L i).length → Bool) : ℝ :=
  ∏ i, ∏ j, (if b i j = true then η else 1 - η)

/-- `E[v(R_L)]` (p. 16): each occurrence of an element of `L_i` is put in `R_i` independently with
probability `η`, duplicates are removed, and `R_L = ⋃_i R_i`. -/
def expectedRandomValue (v : Finset α → ℝ) (η : ℝ) {k : ℕ} (L : Fin k → List α) : ℝ :=
  ∑ b : (i : Fin k) → Fin (L i).length → Bool, occurrenceWeight η L b * v (occurrenceSet L b)

/-- Algorithm 4: `x = (x_1, …, x_k)` is an output of `Fix(L_1, …, L_k)`, i.e. a choice of one
entry from every list maximizing `v({x_1, …, x_k})` (any tie-breaking). -/
def IsFixOutput (v : Finset α → ℝ) {k : ℕ} (L : Fin k → List α) (x : Fin k → α) : Prop :=
  (∃ j : (i : Fin k) → Fin (L i).length, ∀ i, x i = (L i).get (j i)) ∧
    ∀ j : (i : Fin k) → Fin (L i).length,
      v (Finset.univ.image (fun i => (L i).get (j i))) ≤ v (Finset.univ.image x)

end

end CapacitatedKMedianFPT.Main


