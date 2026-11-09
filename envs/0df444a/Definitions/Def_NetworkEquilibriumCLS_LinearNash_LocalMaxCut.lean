-- Prove2me | Definitions.Def_NetworkEquilibriumCLS_LinearNash_LocalMaxCut
-- name    : NetworkEquilibriumCLS_LinearNash_LocalMaxCut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:37.201471+00:00
-- url     : https://prove2.me/theorems/848a9cfb-33ea-4ea2-8a2d-c2ac471aa1d5
-- title:
--   Weighted local MAX CUT and its negative-cut polynomial
-- statement:
--   A weighted simple undirected graph is represented by its upper-triangular natural edge weights. A zero entry denotes no edge, so every present edge has a positive integer weight. Lower-triangular and diagonal input entries are ignored. A cut b partitions the vertices into two unrestricted parts and has weight
--
--   $$C(b)=\sum_{q<r,\ b_q\ne b_r}w_{qr}.$$
--
--   Local optimality means that no single vertex switch increases this weight. Inputs are explicit binary matrix codes and answers are bit vectors. The associated integer square-free quadratic is exactly
--
--   $$h(b)=-\sum_{q<r}w_{qr}(b_q+b_r-2b_qb_r).$$
--
--   The linear and quadratic coefficients are computed from the graph, rather than assumed to have a representation property. PLS membership and completeness use the published LocalOpt canonical problem and the same totality, verification, runtime and all-answer reduction interfaces as the CLS definition. This supplies the external local-search background used by Lemma 3.2.
-- source:
--   Schäffer and Yannakakis, Simple Local Search Problems that are Hard to Solve, SIAM J. Comput. 20(1), 56–87 (1991), Definition 2.8, p.61, and Corollary 5.12 (MAX CUT clause), p.83, https://doi.org/10.1137/0220004; submission p.9 (PDF 10), proof of Lemma 3.2.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_BooleanSearch

open Finset

noncomputable section

namespace NetworkEquilibriumCLS.LinearNash

/-- Positive integer weights on present edges; zero upper-triangular entries denote nonedges.
Schäffer–Yannakakis, Definition 2.8, printed p.61. -/
def cutValue {n : ℕ} (w : Fin n → Fin n → ℕ) (b : Fin n → Bool) : ℕ :=
  ∑ i, ∑ j ∈ univ.filter (i < ·), if b i ≠ b j then w i j else 0

def LocalMaxCut {n : ℕ} (w : Fin n → Fin n → ℕ) (b : Fin n → Bool) : Prop :=
  ∀ q, cutValue w (Function.update b q (!(b q))) ≤ cutValue w b

def encCut {n : ℕ} (w : Fin n → Fin n → ℕ) : List Bool :=
  encNat n ++ encList (encList encNat) (List.ofFn fun i => List.ofFn (w i))

def maxcutSearch : SearchProblem where
  valid x := ∃ n, ∃ w : Fin n → Fin n → ℕ, encCut w = x
  answer x y := ∃ n, ∃ w : Fin n → Fin n → ℕ, encCut w = x ∧
    ∃ b : Fin n → Bool, y = List.ofFn b ∧ LocalMaxCut w b

/-- The actual negative-cut polynomial used in the proof of Lemma 3.2, p.9 (PDF 10). -/
def cutPolynomial {n : ℕ} (w : Fin n → Fin n → ℕ) : BooleanPolynomial n where
  beta q := -(∑ r ∈ univ.filter (· ≠ q),
    if q < r then (w q r : ℤ) else (w r q : ℤ))
  weight q r := 2 * (w q r : ℤ)

def InPLS (S : SearchProblem) : Prop := InTFNP S ∧ SearchReduces S ConstrSOSP.LocalOpt

def PLSComplete (S : SearchProblem) : Prop :=
  InPLS S ∧ ∀ R, InPLS R → SearchReduces R S

end NetworkEquilibriumCLS.LinearNash


