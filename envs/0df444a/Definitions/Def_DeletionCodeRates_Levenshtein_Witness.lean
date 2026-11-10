-- Prove2me | Definitions.Def_DeletionCodeRates_Levenshtein_Witness
-- name    : DeletionCodeRates_Levenshtein_Witness
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:20:34.505097+00:00
-- url     : https://prove2.me/theorems/d696f711-c201-45e9-83d0-d40c845d6568
-- title:
--   Leftmost embeddings, locally restricted common witnesses and the count $M_1(n,d;r)$
-- statement:
--   * **Leftmost embedding** (§4.1). For a witness $\boldsymbol w$ and a word $\boldsymbol c$ with $\boldsymbol w\preceq\boldsymbol c$, the leftmost embedding matches each successive symbol of $\boldsymbol w$ at its earliest available position after the preceding match, so that $\boldsymbol c=B_0\,w_1\,B_1\,w_2\cdots B_{\ell-1}\,w_\ell\,B_\ell$. `leftmostGaps w c` is `some` $[|B_0|,|B_1|,\dots,|B_{\ell-1}|]$ (entry $j$ is the gap before the match of $w_{j+1}$; the final suffix $B_\ell$ is not recorded), or `none` when $\boldsymbol w\not\preceq\boldsymbol c$.
--   * **Locally restricted common witness** (Lemma 11). For words $\boldsymbol c_1,\dots,\boldsymbol c_k$, `IsLocallyRestricted w c` says: $w_1=0$; $\boldsymbol w$ is a subsequence of every $\boldsymbol c_i$ and $w_1$ is matched at position 1 of every $\boldsymbol c_i$ (the first gap is empty); and before every subsequent match ($w_{j+1}$, $1\le j<|\boldsymbol w|$) at least one of the $k$ gaps is empty. There is no condition on the suffixes after the last match.
--   * $M_1(n,d;r)$ (p. 13, `M1 n d r`) is the number of triples $(\boldsymbol w,\boldsymbol c_1,\boldsymbol c_2)$ with $\boldsymbol c_1,\boldsymbol c_2\in\mathcal U(n,r)$ (ordered, possibly equal), $|\boldsymbol w|=n-d$, $w_1=0$ and the leftmost embeddings having at least one empty gap before every subsequent match.
--
--   **Formalization Note.** `M1 4 1 2 = 7`, the paper's example on p. 14, and `M1 7 2 4 = 584`, both by `#eval`.
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), §4.1, pp. 11–12 (PDF 13–14); definition of M_1(n, d; r), p. 13 (PDF 15)

import Mathlib
import Definitions.Def_DeletionCodeRates_Levenshtein_RunEnsemble

set_option autoImplicit false

namespace DeletionCodeRates.Levenshtein

/-! # Leftmost embeddings, locally restricted common witnesses and the count `M_1(n, d; r)`

Kiah, Wei, Zeng, arXiv:2609.21395 (PDF sha256 bc43cfa2…), §4.1, printed pp. 11–12 (PDF 13–14),
and the definition of `M_1(n, d; r)` before Theorem 13, printed p. 13 (PDF 15). -/

/-- The gaps of the leftmost embedding of `w` into `c` (§4.1, p. 11): the leftmost embedding
matches each successive symbol of `w` at its earliest available position after the preceding
match, writing `c = B₀ w₁ B₁ w₂ ⋯ B_{ℓ-1} w_ℓ B_ℓ`. The result is `some [|B₀|, |B₁|, …, |B_{ℓ-1}|]`
(entry `j` is the length of the gap before the match of `w_{j+1}`, zero-based; the final suffix
`B_ℓ` is not recorded), or `none` if `w` is not a subsequence of `c`. -/
def leftmostGaps {α : Type*} [DecidableEq α] : List α → List α → Option (List ℕ)
  | [], _ => some []
  | _ :: _, [] => none
  | a :: w, b :: c =>
      if a = b then (leftmostGaps w c).map (fun g => 0 :: g)
      else (leftmostGaps (a :: w) c).map (fun g => (g.headD 0 + 1) :: g.tail)

/-- A locally restricted common witness of the words `c 0, …, c (k-1)` (§4.1, Lemma 11):
`w` starts with `0` (`w₁ = 0`); `w` is a subsequence of every `c i` and its first symbol is
matched at position 1 of every `c i` (the first leftmost-embedding gap is empty); and before
every subsequent match (the match of `w_{j+1}`, `1 ≤ j < |w|`, zero-based gap index `j`) at least
one of the `k` leftmost-embedding gaps is empty. There is no condition on the suffixes after the
last match. -/
def IsLocallyRestricted {k : ℕ} (w : List (Fin 2)) (c : Fin k → List (Fin 2)) : Prop :=
  w.head? = some 0 ∧
  (∀ i, (leftmostGaps w (c i)).bind List.head? = some 0) ∧
  ∀ j : Fin w.length, 1 ≤ j.val →
    ∃ i, (leftmostGaps w (c i)).bind (fun g => g[j.val]?) = some 0

instance {k : ℕ} (w : List (Fin 2)) (c : Fin k → List (Fin 2)) :
    Decidable (IsLocallyRestricted w c) := by
  unfold IsLocallyRestricted; infer_instance

/-- `M_1(n, d; r)` (p. 13): the number of triples `(w, c₁, c₂)` with `c₁, c₂ ∈ U(n, r)` (ordered,
possibly equal), `|w| = n - d`, `w₁ = 0`, `w` a common subsequence whose leftmost embeddings in
`c₁` and `c₂` have at least one empty gap before every subsequent match. -/
def M1 (n d r : ℕ) : ℕ :=
  ((binWords (n - d) ×ˢ (U n r ×ˢ U n r)).filter
    (fun t => IsLocallyRestricted t.1 ![t.2.1, t.2.2])).card

end DeletionCodeRates.Levenshtein


