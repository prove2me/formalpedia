-- Prove2me | Definitions.Def_LaconicBarrier_SecureAgainst
-- name    : LaconicBarrier_SecureAgainst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:06.119206+00:00
-- url     : https://prove2.me/theorems/bc35e1e8-f951-4c0e-aca3-799a27c84341
-- title:
--   $\Gamma$-security against a class of algorithms
-- statement:
--   Let $D$ be a probabilistic algorithm taking $1^\lambda$ and an auxiliary input, with sets $\mathrm{Aux}_{\lambda,n}$ of allowed auxiliary inputs, and let $\Pr[D(1^\lambda, \mathrm{aux}) \text{ wins}]$ be its winning probability against the challenger of $(\mathcal C, c)$ run at its target parameter. The game is **$\Gamma$-secure against $D$** if for every sequence $\{(n_\lambda, \mathrm{aux}_\lambda)\}$ with $n_\lambda \le p(\lambda)$ and $\mathrm{aux}_\lambda \in \mathrm{Aux}_{\lambda, n_\lambda}$ the family $\{D(1^\lambda, \mathrm{aux}_\lambda)\}$ does not $\Gamma'$-break $(\mathcal C, c)$, where $\Gamma'(\lambda) = \Gamma(\lambda, n_\lambda)$.
--
--   **Formalization Note** The sequence must satisfy its constraints only for all sufficiently large $\lambda$. Breaking is an infinitely-often property, so this is the paper's notion whenever every allowed set is nonempty (as for the honest-prover reduction), and it does not become vacuous when an allowed set is empty for small $\lambda$.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.14, p.21

import Mathlib
import Definitions.Def_LaconicBarrier_Game
import Definitions.Def_LaconicBarrier_Breaks

namespace LaconicBarrier

/-- **Γ-security against a class** (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256
1af78662…), Definition 4.14, p.21). `winP λ aux` is the probability that the algorithm `D(1^λ, aux)`
wins the challenger of `(C, c)` (run at its target parameter), and `Aux λ n` is the set of allowed
auxiliary inputs at `(λ, n)`. The game is Γ-secure against `D` if, for every sequence
`{(n_λ, aux_λ)}` with `n_λ ≤ p(λ)` and `aux_λ ∈ Aux_{λ, n_λ}`, the family `{D(1^λ, aux_λ)}` does not
Γ′-break `(C, c)`, where `Γ′(λ) = Γ(λ, n_λ)`.

**Formalization Note** The sequence is required to satisfy the constraints only for all sufficiently
large `λ`: breaking is an infinitely-often property, so this is the paper's condition whenever every
`Aux_{λ,n}` is nonempty (as for the honest-prover reduction), and it does not become vacuous when the
allowed set is empty for small `λ`. -/
def SecureAgainst {α : Type} (G : Game) (winP : ℕ → α → ℝ) (Aux : ℕ → ℕ → Set α) (p : ℕ → ℕ)
    (Γ : ℕ → ℕ → ℕ) : Prop :=
  ∀ (ns : ℕ → ℕ) (aux : ℕ → α),
    (∀ᶠ lam : ℕ in Filter.atTop, ns lam ≤ p lam ∧ aux lam ∈ Aux lam (ns lam)) →
      ¬ Breaks (fun lam => Γ lam (ns lam)) (fun lam => max 0 (winP lam (aux lam) - G.c))

end LaconicBarrier


