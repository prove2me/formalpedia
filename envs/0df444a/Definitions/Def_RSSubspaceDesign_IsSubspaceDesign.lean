-- Prove2me | Definitions.Def_RSSubspaceDesign_IsSubspaceDesign
-- name    : RSSubspaceDesign_IsSubspaceDesign
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:23:03.582608+00:00
-- url     : https://prove2.me/theorems/41366926-05ec-470c-a962-a7e289d0c8d5
-- title:
--   Definition 2.1 — $\tau$-subspace-design codes
-- statement:
--   Let $E$ be a field, $\Sigma$ an $E$-vector space, and $C\subseteq\Sigma^n$ an $E$-linear code. For $\tau:\mathbb Z_{\ge1}\to\mathbb R$, the code $C$ is a **$\tau$-subspace-design code over $E$** if for every integer $r\ge1$ and every $E$-linear subspace $A\subseteq C$ of dimension at most $r$,
--   $$\frac{1}{n}\sum_{i=1}^n\dim_E A_i\;\le\;\dim_E(A)\cdot\tau(r),\qquad A_i=\{a\in A: a_i=0\}.$$
--
--   On average over a random coordinate, setting that coordinate to zero shrinks every low-dimensional subspace of the code by a factor $\tau$. For $r=1$ it is a bound on the number of zeros of a nonzero codeword, i.e. on the distance. Subspace-design codes are list-decodable close to the generalized Singleton bound.
--
--   **Formalization Note** The paper requires $\tau$ to be nondecreasing with values in $[0,1]$; this precondition is not part of the predicate (any $\tau:\mathbb N\to\mathbb R$ is allowed, its value at $0$ is unused), and the explicit $\tau$ of every theorem here satisfies it. The alphabet $\Sigma$ is any $E$-module (the paper's $\Sigma=K^s$ is a special case). "Dimension at most $r$" is finite dimension with $\dim\le r$. Coordinates are indexed by $\{0,\dots,n-1\}$.
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Definition 2.1, pp.10–11 (PDF pp.12–13)

import Mathlib

namespace RSSubspaceDesign

/-- **Definition 2.1 (Subspace-design codes).** Alrabiah–Goyal–Guruswami, *Explicit Reed-Solomon
Subspace Designs: Optimal List and Line Decoding*, arXiv:2610.36215 (held version, sha256
cf26424b…f36206), Definition 2.1, pp.10–11.

Let `E` be a field and `Σ` (written `V`) an `E`-vector space. An `E`-linear code `C ⊆ Σⁿ` is a
`τ`-subspace-design code over `E` if for every integer `r ≥ 1` and every `E`-linear subspace
`A ⊆ C` of dimension at most `r`,
`(∑ᵢ dim_E Aᵢ) / n ≤ dim_E(A) · τ(r)`, where `Aᵢ = {a ∈ A | aᵢ = 0}`.

**Formalization Note.** Coordinates are `Fin n` (0-based). `Aᵢ` is `A ⊓ ker (proj i)`. The paper
takes `Σ = Kˢ`; here `Σ` is any `E`-module (a `Kˢ` alphabet is the special case). The paper's
precondition on `τ` ("nondecreasing, `ℤ≥1 → [0, 1]`") is **not** bundled: `τ : ℕ → ℝ` is arbitrary
and its value at `0` is never used. Where the predicate is a conclusion, the explicit `τ` is checked
to have these properties separately. "Dimension at most `r`" is `FiniteDimensional` plus
`finrank ≤ r` (Mathlib's `finrank` is `0` on infinite-dimensional spaces). -/
def IsSubspaceDesign (E : Type*) {V : Type*} [Field E] [AddCommGroup V] [Module E V] {n : ℕ}
    (C : Submodule E (Fin n → V)) (τ : ℕ → ℝ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ A : Submodule E (Fin n → V), A ≤ C → FiniteDimensional E A →
    Module.finrank E A ≤ r →
    (∑ i : Fin n, (Module.finrank E ↥(A ⊓ LinearMap.ker (LinearMap.proj i)) : ℝ)) / n ≤
      (Module.finrank E A : ℝ) * τ r

end RSSubspaceDesign


