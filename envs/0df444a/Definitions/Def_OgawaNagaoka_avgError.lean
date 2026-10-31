-- Prove2me | Definitions.Def_OgawaNagaoka_avgError
-- name    : OgawaNagaoka_avgError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:22:43.259585+00:00
-- url     : https://prove2.me/theorems/22049fc1-4fa2-41f9-952e-406937303331
-- title:
--   Average error probability $\mathrm{Pe}(\mathcal C,X)$
-- statement:
--   For a code with codebook $\mathcal C=\{u_1,\dots,u_M\}\subset\mathcal X^n$ and decoder $X=\{X_0,X_1,\dots,X_M\}$ (a quantum measurement on $H^{\otimes n}$, $X_0$ being the evasion outcome), the average error probability under uniformly distributed messages is
--
--   $$
--   \mathrm{Pe}(\mathcal C,X)=1-\frac1M\sum_{k=1}^M\mathrm{Tr}\,\rho_{u_k}X_k .
--   $$
--
--   It is the quantity bounded from below in Lemma 1, Theorem 1 and the strong converse.
--
--   **Formalization Note** The codebook is `c : Fin M → (Fin n → A)`, so codewords may repeat; the decoder is indexed by `Option (Fin M)`, with `none` the evasion outcome. $\mathrm{Tr}\,\rho X$ is the real part of the trace (`QAlgorithms.effectProb`). At $M=0$ the value is $1$ (Lean's $1/0=0$). Statements assume the decoder is a POVM.
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_HolevoCQ_wordState

open QAlgorithms

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, p.2: the average error probability of a code `(C, X)` with
codebook `C = {u₁, …, u_M}` and decoder `X = {X₀, X₁, …, X_M}`,
`Pe(C, X) = 1 − (1/M) Σ_{k=1}^M Tr ρ_{u_k} X_k`.

**Formalization Note.** The codebook is `c : Fin M → (Fin n → A)` (codewords may repeat). The
decoder is indexed by `Option (Fin M)`: `some k` is `X_k` and `none` is the evasion outcome `X₀`,
which does not enter `Pe`; the statements that use `avgError` assume `X` is a POVM
(`QAlgorithms.IsPOVM X`: every `X_k ⪰ 0` and `Σ_k X_k = I`). `Tr ρ X` is the real part of the trace
(`QAlgorithms.effectProb X ρ = Re Tr(X ρ)`, equal to `Tr ρ X` by cyclicity). At `M = 0` the value is
`1` (`1/0 = 0` in Lean). -/
noncomputable def avgError {A D : Type} [Fintype D] [DecidableEq D] (ρ : A → Matrix D D ℂ)
    {n M : ℕ} (c : Fin M → (Fin n → A))
    (X : Option (Fin M) → Matrix (Fin n → D) (Fin n → D) ℂ) : ℝ :=
  1 - (1 / (M : ℝ)) * ∑ k : Fin M, effectProb (X (some k)) (HolevoCQ.wordState ρ n (c k))

end OgawaNagaoka


