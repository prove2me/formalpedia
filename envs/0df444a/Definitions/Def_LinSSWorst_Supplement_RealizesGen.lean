-- Prove2me | Definitions.Def_LinSSWorst_Supplement_RealizesGen
-- name    : LinSSWorst_Supplement_RealizesGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:43:00.956915+00:00
-- url     : https://prove2.me/theorems/20b52ac4-2d19-4824-a795-3a41ed2cb25b
-- title:
--   General secret-sharing schemes, their realization of an access structure, and total share size (Definition A.2)
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ be an access structure. A **secret-sharing scheme** with domain of secrets $S$ is a map
--   $$\Pi : S\times R\to S_1\times\cdots\times S_n,$$
--   where $R$ is a finite set of random strings and $S_j$ is the domain of shares of party $P_j$. For a coalition $x\in\{0,1\}^n$, the **view** $\Pi_x(s;r)$ is the restriction of $\Pi(s;r)$ to the entries $j$ with $x_j=1$. The scheme **realizes** $f$ if:
--   1. **Correctness.** For every $x$ with $f(x)=1$ there is a function $\mathrm{Recon}_x$ with $\mathrm{Recon}_x(\Pi_x(s;r))=s$ for every secret $s$ and every random string $r$.
--   2. **Privacy.** For every $x$ with $f(x)=0$ and all secrets $s,s'$, the distributions of $\Pi_x(s;r)$ and $\Pi_x(s';r)$, for $r$ uniform on $R$, are identical.
--
--   The **total share size** of the scheme is $\sum_{j=1}^n\log_2|S_j|$ bits.
--
--   No linearity or other structure is required of $\Pi$; these are the schemes of the non-linear Theorem 1.5.
--
--   **Formalization Note** $\Pi$ is a curried function `scheme s r`; $R$ is a nonempty finite type (so that its uniform distribution exists) and each $S_j$ is a finite type `σ j`. Privacy is equality of push-forwards of `PMF.uniformOfFintype R`. The theorems take $S=$ `Bool` (one-bit secrets).
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Definition A.2, p.29

import Mathlib
import Definitions.Def_LinSSWorst_Realizes

namespace LinSSWorst.Supplement

/-- The **view** `Π_x(s; r)` of a coalition `x` for a general secret-sharing scheme (Definition A.2,
p.29), from O. Nir, *Resolving the Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027
submission, version of 2026-11-02, sha256 5521cfdb…): the restriction of a share tuple
`(sh_j)_{j ∈ [n]} ∈ S_1 × ⋯ × S_n` to its `I_x`-entries `(sh_j)_{j : x_j = 1}`.

**Formalization Note.** Party `j`'s domain of shares `S_j` is the type `σ j`; the view is indexed by the
subtype `{j // x j = true}` of the parties of the coalition. -/
def viewGen {n : ℕ} {σ : Fin n → Type*} (x : Fin n → Bool) (sh : (i : Fin n) → σ i) :
    (j : {j : Fin n // x j = true}) → σ j.1 :=
  fun j => sh j.1

/-- A general (not necessarily linear) **secret-sharing scheme realizes** an access structure `f`
(Definition A.2, p.29). The scheme is a map `Π : S × R → S_1 × ⋯ × S_n`, `R` a finite set of random
strings; it realizes `f` if
* (correctness) for every `x` with `f(x) = 1` there is a reconstruction function `Recon_x` of the
  coalition's shares with `Recon_x(Π_x(s; r)) = s` for every secret `s` and every random string `r`;
* (privacy) for every `x` with `f(x) = 0` and all secrets `s, s'`, the distributions of `Π_x(s; r)` and
  `Π_x(s'; r)` for `r` uniform on `R` are identical.

**Formalization Note.** `Π` is the curried function `scheme`, `Π(s; r) = scheme s r`. The domain of secrets `S` and the domain of
shares `σ j` are arbitrary types; the theorems of this mission take `S = Bool` (one-bit secrets, so
`|S| = 2 ≥ 2`). `R` must be a nonempty finite type so that the uniform law `PMF.uniformOfFintype R`
exists; privacy is equality of the push-forwards (`PMF.map`) of that law, not of their supports.
`Recon_x` is an arbitrary function. Nothing is assumed about `Π` (no linearity). -/
def RealizesGen {n : ℕ} (f : (Fin n → Bool) → Bool) {S R : Type*} [Fintype R] [Nonempty R]
    {σ : Fin n → Type*} (scheme : S → R → (i : Fin n) → σ i) : Prop :=
  (∀ x : Fin n → Bool, f x = true →
    ∃ recon : ((j : {j : Fin n // x j = true}) → σ j.1) → S,
      ∀ (s : S) (r : R), recon (viewGen x (scheme s r)) = s) ∧
  (∀ x : Fin n → Bool, f x = false → ∀ s s' : S,
    (PMF.uniformOfFintype R).map (fun r => viewGen x (scheme s r)) =
      (PMF.uniformOfFintype R).map (fun r => viewGen x (scheme s' r)))

/-- The **total share size** `Σ_{j=1}^n log₂ |S_j|` of a secret-sharing scheme with domains of shares
`S_j = σ j` (Definition A.2, p.29), in bits.

**Formalization Note.** Logarithms are base two (§2.1). The size counts the declared share domains
`σ j`, not the image of the scheme. -/
noncomputable def totalShareSize {n : ℕ} (σ : Fin n → Type*) [∀ i, Fintype (σ i)] : ℝ :=
  ∑ i, Real.logb 2 (Fintype.card (σ i))

end LinSSWorst.Supplement


