-- Prove2me | Definitions.Def_LinSSWorst_Realizes
-- name    : LinSSWorst_Realizes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:49.061039+00:00
-- url     : https://prove2.me/theorems/7e587dbf-35d8-427b-bdbd-0f871ec70281
-- title:
--   Access structures, views, and linear schemes that realize them (Definitions A.1–A.3)
-- statement:
--   Let $n\ge 0$ and let parties $P_1,\dots,P_n$ be given. A string $x\in\{0,1\}^n$ represents the coalition $I_x=\{P_i : x_i=1\}$. Strings are ordered coordinatewise ($x\le y$ iff $x_i\le y_i$ for every $i$). An **$n$-party access structure** is a monotone function $f:\{0,1\}^n\to\{0,1\}$ with $f(0^n)=0$; $I_x$ is authorized if $f(x)=1$ and unauthorized if $f(x)=0$.
--
--   A **linear secret-sharing scheme** over a finite field $F$ is an $F$-linear map
--   $$\Pi : F\times F^{\ell_r}\to F^{\ell_1}\times\cdots\times F^{\ell_n},\qquad (s,r)\mapsto \Pi(s;r),$$
--   which sends a secret $s\in F$ and a random string $r\in F^{\ell_r}$ to the shares of the $n$ parties, party $P_i$ receiving $\ell_i$ field elements. The **view** $\Pi_x(s;r)$ of a coalition $x$ is the restriction of $\Pi(s;r)$ to the shares of the parties with $x_i=1$. The scheme **realizes** $f$ if:
--   1. **Correctness.** For every $x$ with $f(x)=1$ there is a reconstruction function $\mathrm{Recon}_x$ with $\mathrm{Recon}_x(\Pi_x(s;r))=s$ for every secret $s$ and every random string $r$.
--   2. **Privacy.** For every $x$ with $f(x)=0$ and all secrets $s,s'$, the distributions of $\Pi_x(s;r)$ and $\Pi_x(s';r)$, for $r$ uniform on $F^{\ell_r}$, are identical.
--
--   These are the objects of the main theorem: an access structure, a linear scheme, and the realization requirements.
--
--   **Formalization Note** Coalitions are functions `Fin n → Bool` with the pointwise order (`false ≤ true`), and $0^n$ is `⊥`. Each party's share is a vector indexed by a finite type `σ i` and the randomness is indexed by a finite type `ρ`; Definition A.3's scheme is the case `ρ = Fin ℓr`, `σ i = Fin (ℓ i)`. Privacy is equality of the push-forwards of the uniform PMF on the random strings. The reconstruction function is arbitrary, not required to be linear.
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Definitions A.1, A.2, A.3, p.29; monotonicity, §2.1, p.11

import Mathlib

namespace LinSSWorst

/-- **Access structure** (Definition A.1, p.29, and the order of §2.1, p.11), from O. Nir,
*Resolving the Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027 submission,
version of 2026-11-02, sha256 5521cfdb…). An `n`-party access structure is a monotone function
`f : {0,1}ⁿ → {0,1}` with `f(0ⁿ) = 0`.

**Formalization Note.** A coalition `x ∈ {0,1}ⁿ` is a function `x : Fin n → Bool` (`x j = true` iff
party `j` is in the coalition `I_x`). `Monotone f` uses the pointwise order on `Fin n → Bool` with
`false ≤ true`, which is §2.1's `x ≤ y` iff `x_i ≤ y_i` for every `i`. `⊥` is the all-`false`
string `0ⁿ`. -/
def IsAccessStructure {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  Monotone f ∧ f ⊥ = false

/-- The **view** `Π_x(s; r)` of a coalition `x` (Definition A.2, p.29): the restriction of a share
vector `(sh_j)_{j ∈ [n]}` to its `I_x`-entries `(sh_j)_{j : x_j = 1}`.

**Formalization Note.** Party `j` holds a vector of field elements indexed by a type `σ j`
(for a linear scheme of Definition A.3, `σ j = Fin ℓ_j`). The view is indexed by the subtype
`{j // x j = true}` of the parties of the coalition. -/
def view {F : Type*} {n : ℕ} {σ : Fin n → Type*} (x : Fin n → Bool)
    (sh : (i : Fin n) → σ i → F) : (j : {j : Fin n // x j = true}) → σ j.1 → F :=
  fun j => sh j.1

/-- **Correctness** of a linear secret-sharing scheme for `f` (Definition A.2, p.29): for every
coalition `x` with `f(x) = 1` there is a reconstruction function `Recon_x` of the coalition's
shares with `Recon_x(Π_x(s; r)) = s` for every secret `s` and every random string `r`.

**Formalization Note.** The scheme is an `F`-linear map from secret-and-randomness `F × (ρ → F)`
to the share vectors `(i : Fin n) → σ i → F`. `Recon_x` is an arbitrary function (Definition
A.2 does not ask it to be linear); it is chosen after `x` and before `s` and `r`. -/
def Correct {F : Type*} [Field F] {n : ℕ} (f : (Fin n → Bool) → Bool) {ρ : Type*}
    {σ : Fin n → Type*} (scheme : (F × (ρ → F)) →ₗ[F] ((i : Fin n) → σ i → F)) : Prop :=
  ∀ x : Fin n → Bool, f x = true →
    ∃ recon : ((j : {j : Fin n // x j = true}) → σ j.1 → F) → F,
      ∀ (s : F) (r : ρ → F), recon (view x (scheme (s, r))) = s

/-- **Privacy** of a linear secret-sharing scheme for `f` (Definition A.2, p.29): for every
coalition `x` with `f(x) = 0` and every pair of secrets `s, s'`, the distributions of `Π_x(s; r)`
and `Π_x(s'; r)` are identical, where `r` is drawn uniformly from the finite set of random strings.

**Formalization Note.** The set of random strings is `ρ → F` (for Definition A.3, `ρ = Fin ℓ_r`,
i.e. `F^{ℓ_r}`), finite because `ρ` and `F` are. "The distribution of `Π_x(s; r)`" is the
push-forward (`PMF.map`) of the uniform law `PMF.uniformOfFintype` on `ρ → F`; privacy is equality
of these two laws, not of their supports. -/
def Private {F : Type*} [Field F] [Fintype F] {n : ℕ} (f : (Fin n → Bool) → Bool) {ρ : Type*}
    [Fintype ρ] [DecidableEq ρ] {σ : Fin n → Type*}
    (scheme : (F × (ρ → F)) →ₗ[F] ((i : Fin n) → σ i → F)) : Prop :=
  ∀ x : Fin n → Bool, f x = false → ∀ s s' : F,
    (PMF.uniformOfFintype (ρ → F)).map (fun r => view x (scheme (s, r))) =
      (PMF.uniformOfFintype (ρ → F)).map (fun r => view x (scheme (s', r)))

/-- A linear secret-sharing scheme **realizes** `f` (Definitions A.2, A.3, p.29) if it is correct
and private for `f`.

**Formalization Note.** Definition A.3's linear scheme over `F` with parameters `ℓ_r, ℓ_1, …, ℓ_n`
is the instance `ρ = Fin ℓ_r`, `σ i = Fin ℓ_i`: `F × (Fin ℓ_r → F)` is `F^{1+ℓ_r}` and
`(i : Fin n) → Fin ℓ_i → F` is `F^{ℓ_1+⋯+ℓ_n}`, both up to the canonical linear equivalence. The
predicate is stated for arbitrary finite index types so that a construction can be written on its
natural index types (subsets of parties). The domain of secrets is `S = F`, so `|S| ≥ 2` holds for
every field. -/
def Realizes {F : Type*} [Field F] [Fintype F] {n : ℕ} (f : (Fin n → Bool) → Bool) {ρ : Type*}
    [Fintype ρ] [DecidableEq ρ] {σ : Fin n → Type*}
    (scheme : (F × (ρ → F)) →ₗ[F] ((i : Fin n) → σ i → F)) : Prop :=
  Correct f scheme ∧ Private f scheme

end LinSSWorst


