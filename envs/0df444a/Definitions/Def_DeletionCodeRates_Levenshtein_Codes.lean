-- Prove2me | Definitions.Def_DeletionCodeRates_Levenshtein_Codes
-- name    : DeletionCodeRates_Levenshtein_Codes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:19:44.112736+00:00
-- url     : https://prove2.me/theorems/b4fc61cd-f9a9-460d-aaf0-0fca42fc1ba9
-- title:
--   Insertion–deletion balls, list decodability (Definition 2) and the supremal asymptotic rate $\mathcal R^{(L)}_q(\gamma,\delta)$
-- statement:
--   Words over $\Sigma_q=\{0,\dots,q-1\}$ are finite lists over `Fin q`; $\boldsymbol u\preceq\boldsymbol v$ (subsequence, $\boldsymbol u=\boldsymbol v$ allowed) is `List.Sublist`.
--
--   * **Insertion–deletion ball** (§2). $B(\boldsymbol u;a,b)$ is the set of words obtainable from $\boldsymbol u$ by at most $a$ insertions and at most $b$ deletions. Deleting first and then inserting, $\boldsymbol w\in B(\boldsymbol u;a,b)$ iff some common subsequence $\boldsymbol v$ of $\boldsymbol u$ and $\boldsymbol w$ has $|\boldsymbol u|\le|\boldsymbol v|+b$ and $|\boldsymbol w|\le|\boldsymbol v|+a$ (`InsDelBall u a b`).
--   * **Definition 2.** A code $\mathcal C\subseteq\Sigma_q^n$ is $(a,b;L)$-list-decodable if for every received word $\boldsymbol w$ (of any length), $|\{\boldsymbol c\in\mathcal C:\boldsymbol w\in B(\boldsymbol c;a,b)\}|\le L$ (`IsListDecodable C a b L`). `IsBlockCode C n` says every codeword has length $n$.
--   * **Achievable rate.** $R$ is achievable for $(\gamma,\delta,L)$ over $\Sigma_q$ (`IsAchievableRate q γ δ L R`) if for every $\varepsilon>0$ and all sufficiently large $n$ there is a $(\lfloor\gamma n\rfloor,\lfloor\delta n\rfloor;L)$-list-decodable $\mathcal C_n\subseteq\Sigma_q^n$ with $|\mathcal C_n|\ge q^{n(R-\varepsilon)}$, i.e. of rate $n^{-1}\log_q|\mathcal C_n|\ge R-\varepsilon$ (such a code is nonempty).
--   * $\mathcal R^{(L)}_q(\gamma,\delta)$ (`supRate q γ δ L`) is the supremum of the nonnegative achievable rates, and $\mathcal R^{(L)}_{q,\mathrm{del}}(\delta)=\mathcal R^{(L)}_q(0,\delta)$ (`supRateDel q δ L`).
--
--   **Formalization Note.** The paper says "the supremum of achievable asymptotic rates" without spelling out the rate notion. The reading here requires codes for *all* sufficiently large $n$ (equivalently, a family with $\liminf_n n^{-1}\log_q|\mathcal C_n|\ge R$), which is the stronger reading for a lower bound and the one Lemma 8 delivers. For $q\ge2$ and $L\ge1$ the set of achievable rates contains $0$ (singleton codes) and is bounded above by $1$ ($|\mathcal C_n|\le q^n$, $q\ge2$), so the real supremum is genuine.
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), §2 and Definition 2, pp. 5–6 (PDF 7–8)

import Mathlib

set_option autoImplicit false

namespace DeletionCodeRates.Levenshtein

/-! # Insertion–deletion balls, list decodability and supremal asymptotic rates

Kiah, Wei, Zeng, *Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable
Insertion–Deletion Codes*, arXiv:2609.21395 (PDF sha256 bc43cfa2…), §2 and Definition 2,
printed pp. 5–6 (PDF 7–8).

Words over `Σ_q = {0, …, q-1}` are `List (Fin q)`; `List.Sublist u v` is `u ⪯ v`. -/

/-- The insertion–deletion error ball `B(u; a, b)` (§2, p. 5): `w ∈ B(u; a, b)` iff `w` is
obtainable from `u` by at most `a` insertions and at most `b` deletions, i.e. (deleting first,
then inserting) some common subsequence `v` of `u` and `w` has `|u| - |v| ≤ b` and
`|w| - |v| ≤ a`. -/
def InsDelBall {α : Type*} (u : List α) (a b : ℕ) : Set (List α) :=
  {w | ∃ v : List α, List.Sublist v u ∧ List.Sublist v w ∧
    u.length ≤ v.length + b ∧ w.length ≤ v.length + a}

open Classical in
/-- Definition 2 (p. 5). A code `C ⊆ Σ_q^n` is `(a, b; L)`-list-decodable if every received word
`w` lies in the balls `B(c; a, b)` of at most `L` codewords `c ∈ C`. -/
def IsListDecodable {q : ℕ} (C : Finset (List (Fin q))) (a b L : ℕ) : Prop :=
  ∀ w : List (Fin q), (C.filter (fun c => w ∈ InsDelBall c a b)).card ≤ L

/-- A code of block length `n` over `Σ_q`: every codeword has length `n`. -/
def IsBlockCode {q : ℕ} (C : Finset (List (Fin q))) (n : ℕ) : Prop :=
  ∀ c ∈ C, c.length = n

/-- `R` is an achievable asymptotic rate for `(γ, δ, L)`-insdel list decoding over `Σ_q` (§2, p. 6):
for every `ε > 0` and all sufficiently large `n` there is a code `C_n ⊆ Σ_q^n` that is
`(⌊γn⌋, ⌊δn⌋; L)`-list-decodable with `|C_n| ≥ q^{n(R - ε)}`, i.e. of rate
`n⁻¹ log_q |C_n| ≥ R - ε` for `q ≥ 2` (such a code is nonempty). The paper uses
`γ, δ ≥ 0` and `L ≥ 1`; values outside the rate domain are only total extensions. -/
def IsAchievableRate (q : ℕ) (γ δ : ℝ) (L : ℕ) (R : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, ∃ C : Finset (List (Fin q)),
    IsBlockCode C n ∧ IsListDecodable C ⌊γ * n⌋₊ ⌊δ * n⌋₊ L ∧
      (q : ℝ) ^ ((n : ℝ) * (R - ε)) ≤ (C.card : ℝ)

/-- `R^{(L)}_q(γ, δ)`, the supremum of the achievable asymptotic rates (§2, p. 6). The set of
nonnegative achievable rates contains `0` for `q ≥ 2`, `L ≥ 1` (singleton codes) and is bounded
above by `1` (since `|C_n| ≤ q^n`), so this real supremum is genuine on the paper's domain. -/
noncomputable def supRate (q : ℕ) (γ δ : ℝ) (L : ℕ) : ℝ :=
  sSup {R : ℝ | 0 ≤ R ∧ IsAchievableRate q γ δ L R}

/-- `R^{(L)}_{q,del}(δ) = R^{(L)}_q(0, δ)`, the supremal rate for pure deletions (§2, p. 6). -/
noncomputable def supRateDel (q : ℕ) (δ : ℝ) (L : ℕ) : ℝ :=
  supRate q 0 δ L

end DeletionCodeRates.Levenshtein


