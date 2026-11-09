-- Prove2me | Definitions.Def_SharpConsist_ConsistentAlg_Valid
-- name    : SharpConsist_ConsistentAlg_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:32.308828+00:00
-- url     : https://prove2.me/theorems/2922dd17-52d5-4fd4-b940-3e805e2a1654
-- title:
--   Capacity, recourse and measurability on every instance
-- statement:
--   An algorithm on the stream $1,\dots,n,r$ is **valid for capacity $k$ and recourse $C$** if, for every model instance $f$ on $X\cup\{r\}$ (normalized, monotone, submodular) and every seed $\omega$,
--   $$|S^-(\omega)|\le k,\qquad |S^+(\omega)|\le k,\qquad |S^+(\omega)\,\triangle\,S^-(\omega)|\le C,$$
--   and the output after the final arrival is a random variable: $\{\omega: S^+(\omega)=s\}$ is measurable for every $s\subseteq X\cup\{r\}$.
--
--   The measurability clause is what the paper's $\mathbb E f(S_t)$ presupposes; it makes $\omega\mapsto f(S^+(\omega))$ a bounded random variable, so its integral is its expectation.
--
--   **Formalization Note.** A model instance is the published `PolyContract.IsRankFunction`: $f(\emptyset)=0$, $f(A)\le f(B)$ for $A\subseteq B$, and $f(S\cup T)+f(S\cap T)\le f(S)+f(T)$ — a normalized monotone submodular function (the lattice inequality is equivalent to the paper's diminishing-returns form on a finite ground set; nonnegativity follows). The bounds are imposed only on $(n+1)$-element instances in the order $1,\dots,n,r$ and only at the times $n$ and $n+1$, which admits more algorithms than the paper's model (which imposes them at every time and on all instances of the relevant sizes). No measurability is required of the pre-arrival rule.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §1, p.1; Theorem 5.1, p.12

import Mathlib
import Definitions.Def_PolyContract_IsRankFunction
import Definitions.Def_SharpConsist_ConsistentAlg

universe u

namespace SharpConsist

/-- **Capacity, recourse and measurability on every model instance.** Fu–Zhang–Tao,
arXiv:2609.09986 (held version, sha256 874ec76c…), §1, p.1 (`|S_t| ≤ k`, `|S_t △ S_{t−1}| ≤ C`,
`E[f(S_t)]`); Theorem 5.1, p.12 ("at most C symmetric changes there, on every model instance with
n + 1 elements and every random outcome").

`alg.Valid k C` says: on every normalized monotone submodular objective `f` on `X ∪ {r}` and every
seed `ω`, the output before the final arrival has at most `k` elements, the output after it has at most
`k` elements, and the two differ in at most `C` elements (symmetric difference); and the output after
the final arrival is a random variable: `{ω | S⁺(ω) = s}` is measurable for every `s`.

**Formalization Note.** A model instance is `PolyContract.IsRankFunction f` (published): `f ∅ = 0`,
`A ⊆ B → f A ≤ f B` and `f (S ∪ T) + f (S ∩ T) ≤ f S + f T`, i.e. a normalized monotone submodular
function on the finite ground set (lattice form, equivalent to the paper's marginal forms;
nonnegativity follows). The measurability clause is what the paper's `E f(S_t)` presupposes; without it
the Bochner integral of a non-measurable integrand is `0` and every bound on an expectation would be
trivial. Nothing else is assumed: no measurability of `pre`, no bound on queries after `r`. The
conditions are imposed only on `(n+1)`-element instances in the order `1, …, n, r` and only at the
times `n` and `n + 1`, which allows more algorithms than the paper's model. -/
def ConsistentAlg.Valid {n Q : ℕ} {Ω : Type u} [MeasurableSpace Ω] (alg : ConsistentAlg n Q Ω)
    (k C : ℕ) : Prop :=
  ∀ f : Finset (Fin (n + 1)) → ℝ, PolyContract.IsRankFunction f →
    (∀ ω : Ω, (alg.preOut ω f).card ≤ k ∧ (alg.post ω f).card ≤ k ∧
      (symmDiff (alg.post ω f) (embedX (alg.preOut ω f))).card ≤ C) ∧
    ∀ s : Finset (Fin (n + 1)), MeasurableSet {ω : Ω | alg.post ω f = s}

end SharpConsist


