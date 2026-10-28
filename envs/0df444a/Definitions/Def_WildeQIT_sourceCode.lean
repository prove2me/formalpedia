-- Prove2me | Definitions.Def_WildeQIT_sourceCode
-- name    : WildeQIT_sourceCode
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T07:28:58.820608+00:00
-- url     : https://prove2.me/theorems/74a20034-9d83-4e0c-ad03-aa4b09ffb813
-- title:
--   Source codes, error probability and achievable compression rates (§14.4, for Theorem 14.4.1)
-- statement:
--   The notions behind Theorem 14.4.1 (Shannon compression), reconstructed from Wilde §14.4 (they are not roster items). An $(n,R)$ **source code** for the i.i.d. source $p_X$ consists of an encoder $E:\mathcal{X}^n\to\{1,\dots,M\}$ with $M\le 2^{nR}$ codewords and a decoder $D:\{1,\dots,M\}\to\mathcal{X}^n$. Its **error probability** is $\Pr\{D(E(X^n))\ne X^n\}$. A rate $R$ is **achievable** for $X$ if for every $\varepsilon\in(0,1)$, $\delta>0$ and all sufficiently large $n$ there is an $(n,R+\delta)$ code with error probability at most $\varepsilon$.
--
--   **Formalization Note.** `SourceCode α n M` bundles `enc : (Fin n → α) → Fin M` and `dec : Fin M → (Fin n → α)`; `SourceCode.errorProb p c = ∑ x, if c.dec (c.enc x) = x then 0 else (p.iid n).prob x`; `IsAchievableSourceRate p R` quantifies `∀ ε ∈ (0,1), ∀ δ > 0, ∃ N, ∀ n ≥ N, ∃ M ≤ 2^{n(R+δ)}, ∃ c, errorProb ≤ ε` (real exponent, `Real.rpow`).
-- source:
--   Wilde, Quantum Information Theory 2nd ed. (Cambridge 2017; arXiv:1106.1445v8), Theorem 14.4.1, §Application: Data Compression (roster-items.csv line 25241); the notions '(n,R) source code', 'error probability' and 'achievable rate' from the prose of §14.4 preceding it.

import Definitions.Def_WildeQIT_iid
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §14.4 (Application: Data compression), the
notions used by Theorem 14.4.1 (Shannon compression): an `(n, R)` source code for the i.i.d.
source `p_X` maps each sequence `xⁿ` to one of at most `2^{nR}` codewords and decodes back; its
error probability is `Pr{ D(E(Xⁿ)) ≠ Xⁿ }`; a rate `R` is achievable if for every `ε ∈ (0,1)`,
`δ > 0` and all sufficiently large `n` there is an `(n, R + δ)` code with error probability at
most `ε`.
-/

namespace WildeQIT

/-- A source code of block length `n` with `M` codewords: an encoder into `Fin M` and a decoder. -/
structure SourceCode (α : Type) (n M : ℕ) where
  /-- The encoder `E : 𝒳ⁿ → {1, …, M}`. -/
  enc : (Fin n → α) → Fin M
  /-- The decoder `D : {1, …, M} → 𝒳ⁿ`. -/
  dec : Fin M → (Fin n → α)

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The error probability `Pr{ D(E(Xⁿ)) ≠ Xⁿ }` of a source code under the i.i.d. source `p`. -/
noncomputable def SourceCode.errorProb {n M : ℕ} (p : FinDist α) (c : SourceCode α n M) : ℝ :=
  ∑ x, if c.dec (c.enc x) = x then 0 else (p.iid n).prob x

/-- A rate `R` is achievable for the source `p`: for every `ε ∈ (0,1)` and `δ > 0`, for all
sufficiently large `n` there is a source code with at most `2^{n(R+δ)}` codewords and error
probability at most `ε`. -/
def IsAchievableSourceRate (p : FinDist α) (R : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N,
    ∃ M : ℕ, (M : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (R + δ)) ∧ ∃ c : SourceCode α n M, c.errorProb p ≤ ε

end WildeQIT


