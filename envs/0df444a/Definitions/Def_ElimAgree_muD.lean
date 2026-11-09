-- Prove2me | Definitions.Def_ElimAgree_muD
-- name    : ElimAgree_muD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:32.702392+00:00
-- url     : https://prove2.me/theorems/f2e873c1-272b-4217-9642-d83941f8d77e
-- title:
--   The hard laws $\mu_D$, $\mu_I$, $\lambda=\mu_D^{\otimes r}$ and $\mu_\sigma$
-- statement:
--   Let $\ell\ge1$ and $N=4\ell-1$. Let $\mu_D$ be the uniform law on pairs of disjoint $\ell$-subsets of $[N]$, and $\mu_I$ the uniform law on pairs of $\ell$-subsets meeting in exactly one element. For $r$ instances let $\lambda=\mu_D^{\otimes r}$, a law on pairs $(X,Y)$ of $r$-tuples of subsets of $[N]$:
--   $$\lambda(X,Y)=\prod_{i=1}^r\mu_D(x_i,y_i).$$
--   For $\sigma\in\{D,I\}^k$ let $\mu_\sigma=\bigotimes_i\mu_{\sigma_i}$.
--
--   These are Razborov-type distributions; Theorem 3.6 compares $\mu_I^{\otimes r}$ with $\lambda$ on every rectangle.
--
--   **Formalization Note** Both parties' inputs range over all tuples of subsets of $[N]$, and the laws vanish off tuples of $\ell$-subsets. $\{D,I\}$ is `Bool` with `true` $=D$.
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), §3.3, p.9 (PDF p.11); Corollary 3.7, p.10 (PDF p.12)

import Mathlib

namespace ElimAgree

/-- Subsets of `[N] = Fin N` with `N = 4ℓ − 1` (Ben Daniel, *Can Many Instances Be Cheaper Than
One? The Price of Agreement in Elimination*, manuscript, STOC 2027 submission, §3.3, p.9).

**Formalization Note.** Used only with `1 ≤ ℓ`, where `4ℓ − 1` has no truncation. -/
abbrev Nset (ℓ : ℕ) : Type := Finset (Fin (4 * ℓ - 1))

/-- Pairs of disjoint `ℓ`-subsets of `[N]`. -/
def dPairs (ℓ : ℕ) : Finset (Nset ℓ × Nset ℓ) :=
  Finset.univ.filter (fun p => p.1.card = ℓ ∧ p.2.card = ℓ ∧ Disjoint p.1 p.2)

/-- Pairs of `ℓ`-subsets of `[N]` meeting in exactly one element. -/
def iPairs (ℓ : ℕ) : Finset (Nset ℓ × Nset ℓ) :=
  Finset.univ.filter (fun p => p.1.card = ℓ ∧ p.2.card = ℓ ∧ (p.1 ∩ p.2).card = 1)

/-- `µ_D` (§3.3, p.9): the uniform law on pairs of disjoint `ℓ`-subsets of `[N]`. -/
noncomputable def muD (ℓ : ℕ) : Nset ℓ × Nset ℓ → ℝ :=
  fun p => if p ∈ dPairs ℓ then 1 / ((dPairs ℓ).card : ℝ) else 0

/-- `µ_I` (§3.3, p.9): the uniform law on pairs of `ℓ`-subsets of `[N]` meeting in exactly one
element. -/
noncomputable def muI (ℓ : ℕ) : Nset ℓ × Nset ℓ → ℝ :=
  fun p => if p ∈ iPairs ℓ then 1 / ((iPairs ℓ).card : ℝ) else 0

/-- The product `⊗_i µ_i` of laws on pairs, as a law on pairs of `r`-tuples
`(X, Y) = ((x_1, …, x_r), (y_1, …, y_r))`: `(⊗µ)(X, Y) = Π_i µ_i(x_i, y_i)`. -/
def pairProd {r : ℕ} {S : Type} (μ : Fin r → S × S → ℝ) : (Fin r → S) × (Fin r → S) → ℝ :=
  fun p => ∏ i, μ i (p.1 i, p.2 i)

/-- `λ = µ_D^{⊗r}` (§3.3, p.9). -/
noncomputable def lamD (ℓ r : ℕ) : (Fin r → Nset ℓ) × (Fin r → Nset ℓ) → ℝ :=
  pairProd (fun _ : Fin r => muD ℓ)

/-- `µ_I^{⊗r}` (Theorem 3.6, p.9). -/
noncomputable def muIpow (ℓ r : ℕ) : (Fin r → Nset ℓ) × (Fin r → Nset ℓ) → ℝ :=
  pairProd (fun _ : Fin r => muI ℓ)

/-- `µ_σ = ⊗_i µ_{σ_i}` for `σ ∈ {D, I}^k` (Corollary 3.7, p.10).

**Formalization Note.** `{D, I}` is `Bool` with `true = D` and `false = I`, matching
`DISJ = 1 = true` in the proof of Theorem 3.8. -/
noncomputable def muSigma (ℓ : ℕ) {k : ℕ} (σ : Fin k → Bool) :
    (Fin k → Nset ℓ) × (Fin k → Nset ℓ) → ℝ :=
  pairProd (fun i => if σ i then muD ℓ else muI ℓ)

end ElimAgree


