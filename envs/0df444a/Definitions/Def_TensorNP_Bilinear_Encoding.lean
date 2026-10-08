-- Prove2me | Definitions.Def_TensorNP_Bilinear_Encoding
-- name    : TensorNP_Bilinear_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:13.469428+00:00
-- url     : https://prove2.me/theorems/7d45aba5-a4aa-4e21-a7f3-887a83fdcaa2
-- title:
--   Binary code of rational tensors and the language of tensor bilinear feasibility (Problem 3.1)
-- statement:
--   Instances are written in binary over the four-letter alphabet $\{0, 1, -, \#\}$ of the published definition `ProjSchedTW.Complexity.Encoding`, in which every number is written in binary and terminated by a separator.
--
--   1. The graph code and the language **3-COLORABILITY** (codes of graphs that admit a proper 3-coloring), and the code of a rational number $q$ (its reduced numerator, a signed integer, followed by its denominator), are those of the shared definition `TensorNP.Eigen.Defs` (`graphCode`, `threeColLang`, `encRat`).
--   2. A rational tensor $\mathcal A \in \mathbb Q^{l\times m\times n}$ is coded by $l, m, n$ followed by its entries $a_{ijk}$ in lexicographic order of $(i,j,k)$. Since every number code ends in a separator, the code determines $l, m, n$ and $\mathcal A$.
--   3. **Tensor bilinear feasibility over $F$** is the language of the codes of rational tensors $\mathcal A$ for which the system (9) of Problem 3.1, with the entries of $\mathcal A$ read in $F$, has a solution with $\mathbf u \in F^l$, $\mathbf v \in F^m$, $\mathbf w \in F^n$ all nonzero.
--
--   These are the source and target languages of the reduction of Theorem 3.7.
--
--   **Formalization Note** A language is a set of words over `BSym` (`CookPvsNP.Lang`). A 3-coloring is Mathlib's `SimpleGraph.Colorable 3`. A rational number is `q.num` and `q.den` of Mathlib's normalized `ℚ`. A word that is not the code of an instance belongs to neither target language.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:15, Problem 3.1; p. 0:17, Theorem 3.7; p. 0:7, §1.4 (input size in bits)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_TensorNP_Bilinear_Feasibility
import Definitions.Def_TensorNP_Eigen_Defs

namespace TensorNP.Bilinear

open CookPvsNP ProjSchedTW.Complexity

/-! # Binary codes and the languages of Theorem 3.7 (Hillar–Lim, p. 0:17) -/

open Classical in

/-- The code of a rational tensor `A ∈ ℚ^{l×m×n}`: `l`, `m`, `n`, then the entries `a_{ijk}` in
lexicographic order of `(i, j, k)`. Every number code ends in a separator, so the code
determines `l, m, n` and `A`. -/
def tensorCode {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℚ) : List BSym :=
  encNats [l, m, n] ++
    (List.ofFn fun i => (List.ofFn fun j => (List.ofFn fun k => TensorNP.Eigen.encRat (A i j k)).flatten).flatten).flatten

/-- TENSOR BILINEAR FEASIBILITY over the field `F` (Problem 3.1): the codes of the rational
tensors `A ∈ ℚ^{l×m×n}` for which the system (9), with `A`'s entries read in `F`, has a solution
with `u ∈ F^l`, `v ∈ F^m`, `w ∈ F^n` all nonzero. -/
def tbfLang (F : Type*) [Field F] : Lang BSym :=
  { w | ∃ (l m n : ℕ) (A : Fin l → Fin m → Fin n → ℚ),
      TBF (fun i j k => (A i j k : F)) ∧ w = tensorCode A }

end TensorNP.Bilinear


