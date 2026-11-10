-- Prove2me | Definitions.Def_DeletionCodeRates_Levenshtein_RunEnsemble
-- name    : DeletionCodeRates_Levenshtein_RunEnsemble
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:19:48.528538+00:00
-- url     : https://prove2.me/theorems/9a32d130-fbcb-428c-94cf-298136e01a9e
-- title:
--   Runs, the run-restricted ensemble $\mathcal U(n,r)$ and the bad-pair event $E_{\{1,2\}}$
-- statement:
--   Binary words are lists over `Fin 2`.
--
--   * $\mathrm{runs}(\boldsymbol c)$ is the number of maximal blocks of equal symbols ($0$ for the empty word).
--   * (20): $\mathcal U(n,r)=\{\boldsymbol c\in\{0,1\}^n: c_1=0,\ \mathrm{runs}(\boldsymbol c)=r\}$ (`U n r`; the paper uses $1\le r\le n$, and outside that range the same formula is empty).
--   * `IsCommonSubseq v c`: $\boldsymbol v$ is a subsequence of every word of the tuple $\boldsymbol c$.
--   * The bad event of §4.1 for two independent uniform samples $\boldsymbol C_1,\boldsymbol C_2$ from $\mathcal U(n,r)$ is $E_{\{1,2\}}=\{\mathrm{LCS}(\boldsymbol C_1,\boldsymbol C_2)\ge n-d\}$. `badPairs n d r` is the set of ordered pairs in $\mathcal U(n,r)^2$ with a common subsequence of length $\ge n-d$, and $\Pr(E_{\{1,2\}})$ is `probBadPair n d r` $=|\texttt{badPairs}|/|\mathcal U(n,r)|^2$.
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), §4.1, (20) and the event E_{1,2}, p. 11 (PDF 13)

import Mathlib

set_option autoImplicit false

namespace DeletionCodeRates.Levenshtein

/-! # Runs, the run-restricted ensemble `U(n, r)`, longest common subsequences and the bad pairs

Kiah, Wei, Zeng, arXiv:2609.21395 (PDF sha256 bc43cfa2…), §4.1, (20) and the bad event
`E_{1,2}`, printed p. 11 (PDF 13). Binary words are `List (Fin 2)`. -/

/-- `runs(c)`, the number of maximal blocks of equal symbols of `c` (`0` for the empty word). -/
def runs {α : Type*} [DecidableEq α] : List α → ℕ
  | [] => 0
  | [_] => 1
  | a :: b :: l => (if a = b then 0 else 1) + runs (b :: l)

/-- All binary words of length `n`. -/
def binWords (n : ℕ) : Finset (List (Fin 2)) :=
  (Finset.univ : Finset (Fin n → Fin 2)).image List.ofFn

/-- (20): `U(n, r) = {c ∈ {0,1}^n : c₁ = 0, runs(c) = r}` (the paper uses it for `1 ≤ r ≤ n`;
outside that range the same formula gives the empty set). -/
def U (n r : ℕ) : Finset (List (Fin 2)) :=
  (binWords n).filter (fun c => c.head? = some 0 ∧ runs c = r)

/-- `v` is a common subsequence of the words `c 0, …, c (k-1)`. -/
def IsCommonSubseq {α : Type*} {k : ℕ} (v : List α) (c : Fin k → List α) : Prop :=
  ∀ i, List.Sublist v (c i)

open Classical in
/-- The bad pairs `(c₁, c₂) ∈ U(n, r)²` of §4.1: `LCS(c₁, c₂) ≥ n - d`, i.e. `c₁` and `c₂` have
a common subsequence of length at least `n - d`. With `C₁, C₂` independent uniform samples
from `U(n, r)`, `Pr(E_{1,2}) = |badPairs n d r| / |U(n, r)|²`. -/
noncomputable def badPairs (n d r : ℕ) : Finset (List (Fin 2) × List (Fin 2)) :=
  (U n r ×ˢ U n r).filter
    (fun p => ∃ v : List (Fin 2), n - d ≤ v.length ∧ List.Sublist v p.1 ∧
      List.Sublist v p.2)

/-- `Pr(E_{1,2})` for two independent uniform samples from `U(n, r)` (the event
`LCS(C₁, C₂) ≥ n - d`), as the fraction of bad ordered pairs. -/
noncomputable def probBadPair (n d r : ℕ) : ℝ :=
  ((badPairs n d r).card : ℝ) / ((U n r).card : ℝ) ^ 2

end DeletionCodeRates.Levenshtein


