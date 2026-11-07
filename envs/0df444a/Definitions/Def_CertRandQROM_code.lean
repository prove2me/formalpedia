-- Prove2me | Definitions.Def_CertRandQROM_code
-- name    : CertRandQROM_code
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:57.108603+00:00
-- url     : https://prove2.me/theorems/8425ecdc-3ddc-41f9-ab09-0894fbd04fe8
-- title:
--   The code family $C_\lambda=\mathrm{FRS}_{\mathbb F_{q(\lambda)},\gamma(\lambda),m(\lambda),k(\lambda)}$ of §5.2
-- statement:
--   For a security parameter $\lambda$ (logarithms base $2$), §5.2 chooses
--
--   $$
--   q=2^{2\lfloor\log\lambda\rfloor},\quad m=2^{\lfloor\log\lambda\rfloor}+1,\quad N=q-1,\quad n=\frac{N}{m}=2^{\lfloor\log\lambda\rfloor}-1,\quad k=\Big\lfloor\frac{N}{10\sqrt n}\Big\rfloor ,
--   $$
--
--   a generator $\gamma$ of $\mathbb F_q^*$, and sets $C_\lambda=\mathrm{FRS}_{\mathbb F_q,\gamma,m,k}$: the folded Reed–Solomon code whose codewords are $\big((f(\gamma^{jm+1}),\dots,f(\gamma^{jm+m}))\big)_{j=0}^{n-1}$ for the polynomials $f$ of degree at most $k$. It is a code of length $n$ over the alphabet $\Sigma_\lambda=\mathbb F_q^m$. The oracle of Construction 6.2 has input set $[n]\times\Sigma_\lambda$.
--
--   This is the code whose list recoverability (Lemma 5.2) drives the min-entropy proof.
--
--   **Formalization Note** `mPar`, `NPar`, `nPar`, `kPar` are $m,N,n,k$; `Alph F l` is $\Sigma_\lambda$ and `Dom F l` is $[n]\times\Sigma_\lambda$. The field `F l` and the generator `γ l` are parameters: the statements assume $|F_\lambda|=2^{2\lfloor\log_2\lambda\rfloor}$ and that $\gamma_\lambda$ has order $|F_\lambda|-1$ for $\lambda\ge2$. The code is the published `TFNPRom.foldedRS`, which evaluates at $\gamma^{jm},\dots,\gamma^{jm+m-1}$; the sanity file proves it equals the page's code for every $\gamma\ne0$, and that $n=2^{\lfloor\log_2\lambda\rfloor}-1$, $N=nm$ and $0<k<N$ for $\lambda\ge16$. For $\lambda<2$ the paper's construction is undefined and the Lean values do not matter in any asymptotic statement.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), §5.1 Folded Reed–Solomon Codes and §5.2 Construction, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_TFNPRom_foldedRS

namespace CertRandQROM

/-- The folding parameter `m(λ) = 2^{⌊log λ⌋} + 1` of §5.2, p.23 (Coladangelo et al.,
arXiv:2608.31112, sha256 b75095a2…); `log` is base 2. -/
def mPar (l : ℕ) : ℕ := 2 ^ Nat.log 2 l + 1

/-- `N(λ) = q(λ) − 1` (§5.2, p.23), for a field family `F` with `|F λ| = q(λ)`. -/
def NPar (F : ℕ → Type) [∀ l, Fintype (F l)] (l : ℕ) : ℕ := Fintype.card (F l) - 1

/-- The code length `n(λ) = N(λ)/m(λ)` (§5.2, p.23); it equals `2^{⌊log λ⌋} − 1` when
`|F λ| = 2^{2⌊log λ⌋}` and `λ ≥ 2` (proved in the sanity file). -/
def nPar (F : ℕ → Type) [∀ l, Fintype (F l)] (l : ℕ) : ℕ := NPar F l / mPar l

/-- The degree parameter `k(λ) = ⌊R(λ) N(λ)⌋` with rate `R(λ) = 1/(10√n(λ))` (§5.2, p.23). -/
noncomputable def kPar (F : ℕ → Type) [∀ l, Fintype (F l)] (l : ℕ) : ℕ :=
  ⌊(NPar F l : ℝ) / (10 * Real.sqrt (nPar F l))⌋₊

/-- The alphabet `Σ_λ = F_{q(λ)}^{m(λ)}`. -/
abbrev Alph (F : ℕ → Type) (l : ℕ) : Type := Fin (mPar l) → F l

/-- The oracle's input set `[n] × Σ_λ` (0-based `[n]`). -/
abbrev Dom (F : ℕ → Type) [∀ l, Fintype (F l)] (l : ℕ) : Type := Fin (nPar F l) × Alph F l

/-- **The code family `{C_λ}` of §5.2, p.23**: `C_λ = FRS_{F_{q(λ)}, γ(λ), m(λ), k(λ)}`, a subset of
`Σ_λ^{n(λ)}`, written with the published folded Reed–Solomon code `TFNPRom.foldedRS`.

**Formalization Note** The field `F λ` and the generator `γ λ` are parameters; the statements
assume `|F λ| = 2^{2⌊log₂ λ⌋}` and `orderOf (γ λ) = |F λ| − 1` for `λ ≥ 2` (the paper:
`q(λ) = 2^{2⌊log λ⌋}`, `γ(λ)` an arbitrary generator of `F_q^*`). `TFNPRom.foldedRS` evaluates
at `γ^0, …, γ^{N−1}`, the page's FRS at `γ^1, …, γ^N`; the two codes are equal as sets for every
`γ ≠ 0` (proved in the sanity file). For `λ < 2` the paper's construction is undefined and the
Lean values are irrelevant to every asymptotic statement. -/
noncomputable def code (F : ℕ → Type) [∀ l, Field (F l)] [∀ l, Fintype (F l)]
    [∀ l, DecidableEq (F l)] (γ : ∀ l, F l) (l : ℕ) : Finset (Fin (nPar F l) → Alph F l) :=
  TFNPRom.foldedRS (γ l) (mPar l) (kPar F l)

end CertRandQROM


