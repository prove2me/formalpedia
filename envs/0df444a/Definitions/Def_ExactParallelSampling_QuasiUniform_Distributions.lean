-- Prove2me | Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions
-- name    : ExactParallelSampling_QuasiUniform_Distributions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:49:13.121853+00:00
-- url     : https://prove2.me/theorems/ee8ea0c6-2076-4265-9d79-d3d38b47ca90
-- title:
--   Distributions on a finite product, supports, quasi-uniformity, independent sets and level functions
-- statement:
--   The objects of §2 (pp. 12–15) and Definition 4.4 (p. 22). A distribution $\mu$ on $\Sigma^E=\prod_{j\in E}\Sigma_j$ over a finite set $E$ of coordinates is given by its mass function $p$ on all assignments $x:E\to\alpha$, where the finite alphabet $\alpha$ contains every $\Sigma_j$ (assignments outside $\prod\Sigma_j$ have mass $0$); `IsDist p` says the masses are non-negative and sum to $1$.
--
--   - **Counting oracle.** `count p S y` $=\Pr[X_S=y_S]$ for $S\subseteq E$ and a pinning $y$ (only its values on $S$ matter); an inconsistent pinning returns $0$.
--   - **Marginals and supports.** `marg p S` is the law of $X_S$ on restrictions $z:S\to\alpha$; `supp p S` $=\Omega_S=\{z:\Pr[X_S=z]>0\}$ and `suppCard p S` $=|\Omega_S|$.
--   - **Quasi-uniformity (Definition 2.3).** $\mu$ is quasi-uniform if for **every** $S\subseteq E$, including $S=E$, $\Pr[X_S=z]=1/|\Omega_S|$ for all $z\in\Omega_S$.
--   - **Singleton supports and conditional support sizes.** $\Omega_j=\{a:\Pr[X_j=a]>0\}$ (`singleSupp`), $s_j=|\Omega_j|$ (`s`), and $s_S(j)=|\Omega_{S+j}|/|\Omega_S|$ as a real number (`condSize`); `condSizeNat` is the same quotient with natural-number division, equal to it whenever the division is exact (in particular for quasi-uniform $\mu$, by Lemma 2.4(b)).
--   - **Conditional laws.** `condLaw p K y` is the law of $X_{E\setminus K}$ given $X_K=y$, namely $w\mapsto \Pr[X=(y,w)]/\Pr[X_K=y]$, used at consistent $y$.
--   - **Independence (Definition 2.7).** $F$ is independent (`IsIndep p F`) if $(X_j)_{j\in F}$ are mutually independent: $\Pr[X_F=y_F]=\prod_{j\in F}\Pr[X_j=y_j]$ for all $y$. A circuit of a family $I$ is an inclusion-minimal set outside $I$ (`IsCircuit`); `circuitsIn I S` lists the circuits contained in $S$.
--   - **Level functions (Definition 4.4).** $\lambda:\mathbb N\to\mathbb N$ with $\lambda(1)=0$, $\lambda(s)\ge1$ for $s\ge2$, and $\lambda(s_{K'}(j))\le\lambda(s_K(j))-1$ whenever $K\subseteq K'$, $j\notin K'$ and $s_{K'}(j)<s_K(j)$ (written $\lambda(s_{K'}(j))+1\le\lambda(s_K(j))$). The level is $D_\lambda(\mu)=\max_j\lambda(s_j)$, $0$ for an empty maximum.
--   - **Derived oracles (Lemma 2.1).** For the law $\nu$ of $X_A$ given $X_K=y$: `condCount p K y T z` $=\Pr[X_{K\cup T}=(y,z)]/\Pr[X_K=y]$, its singleton supports `condSingleSupp`, its independent sets `IsCondIndep`, and its level `condLevel` $=\max_{j\in A}\lambda(s^\nu_j)$.
--
--   `singletonQueries` is the fixed batch of all singleton counting queries, and `supportsFromAnswers` decodes the supports from those answers alone.
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, §2 (Definitions 2.3, 2.7, Lemma 2.1) and Definition 4.4, p. 12–15, 22; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-! # Distributions on a finite product, supports, quasi-uniformity, independent sets

Shen, Li, Shi and Li (2026), *Exact Parallel Sampling without Maximal Independent Sets*,
§2 (pp. 12–15) and Definition 4.4 (p. 22).

A distribution `μ` on `Σ^E = ∏_{j ∈ E} Σ_j` is represented by its probability mass function
`p : (E → α) → ℝ` on all assignments `x : E → α`, where `E` is a finite set of coordinates and `α`
a finite alphabet containing every `Σ_j` (assignments outside `∏ Σ_j` get probability `0`). A pinning
`(S, y)` of `S ⊆ E` is given by a full assignment `y : E → α` of which only the values on `S` matter,
or by a restriction `z : ↥S → α`. Probabilities are exact real numbers. -/

variable {E α : Type*} [Fintype E] [Fintype α]

/-- `p` is a probability distribution on `α^E`: non-negative masses summing to `1`
(so its support is nonempty). -/
def IsDist (p : (E → α) → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- The counting oracle (§2.1): the answer `Pr[X_S = y_S]` to the query `(S, y)`; only the values
of `y` on `S` matter. It is defined at every pinning (an inconsistent one returns `0`). -/
def count (p : (E → α) → ℝ) (S : Finset E) (y : E → α) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : E → α => ∀ j ∈ S, x j = y j), p x

/-- The law of `X_S` (the marginal on `S`), as a mass function on restrictions `z : ↥S → α`. -/
def marg (p : (E → α) → ℝ) (S : Finset E) : (↥S → α) → ℝ :=
  fun z => ∑ x ∈ Finset.univ.filter (fun x : E → α => S.restrict x = z), p x

/-- The support `Ω_S = {y ∈ Σ^S : Pr[X_S = y] > 0}` of `X_S` (§2.3). -/
def supp (p : (E → α) → ℝ) (S : Finset E) : Finset (↥S → α) :=
  Finset.univ.filter (fun z => 0 < marg p S z)

/-- `|Ω_S|`. -/
def suppCard (p : (E → α) → ℝ) (S : Finset E) : ℕ :=
  (supp p S).card

/-- Definition 2.3: `μ` is quasi-uniform if for **every** `S ⊆ E` (including `S = E`) the law of
`X_S` is uniform on its support: `Pr[X_S = y] = 1/|Ω_S|` for every `y ∈ Ω_S`. -/
def IsQuasiUniform (p : (E → α) → ℝ) : Prop :=
  IsDist p ∧ ∀ (S : Finset E), ∀ z ∈ supp p S, marg p S z = 1 / (suppCard p S : ℝ)

/-- The singleton support `Ω_j = {a : Pr[X_j = a] > 0}`, read off the `|α|` answers `Pr[X_j = a]`. -/
def singleSupp (p : (E → α) → ℝ) (j : E) : Finset α :=
  Finset.univ.filter (fun a => 0 < count p {j} (fun _ => a))

/-- `s_j = |Ω_j|`. -/
def s (p : (E → α) → ℝ) (j : E) : ℕ :=
  (singleSupp p j).card

/-- The conditional support size `s_S(j) = |Ω_{S+j}| / |Ω_S|` (§2.3), as a real number (it is a
positive integer for quasi-uniform `μ` by Lemma 2.4(b), which is a theorem, not part of the
definition). -/
def condSize (p : (E → α) → ℝ) (S : Finset E) (j : E) : ℝ :=
  (suppCard p (insert j S) : ℝ) / (suppCard p S : ℝ)

/-- `s_S(j)` as a natural number, `|Ω_{S+j}| / |Ω_S|` with natural-number division; it equals
`condSize` whenever the division is exact, in particular for quasi-uniform `μ`. Used only where the
source applies an integer-valued function (a level function) to `s_S(j)`. -/
def condSizeNat (p : (E → α) → ℝ) (S : Finset E) (j : E) : ℕ :=
  suppCard p (insert j S) / suppCard p S

/-- Glue a pinning `y` of `K` and an assignment `w` of the remaining coordinates into a full
assignment. -/
def glue (K : Finset E) (y : ↥K → α) (w : {j // j ∉ K} → α) : E → α :=
  fun j => if h : j ∈ K then y ⟨j, h⟩ else w ⟨j, h⟩

/-- The conditional law of `X_{E∖K}` given `X_K = y` (used only at consistent pinnings, where
`Pr[X_K = y] > 0`): `w ↦ Pr[X = (y, w)] / Pr[X_K = y]`. -/
def condLaw (p : (E → α) → ℝ) (K : Finset E) (y : ↥K → α) : ({j // j ∉ K} → α) → ℝ :=
  fun w => p (glue K y w) / marg p K y

/-- Definition 2.7: `F ⊆ E` is independent for `μ` if the variables `(X_j)_{j ∈ F}` are mutually
independent: `Pr[X_F = y_F] = ∏_{j ∈ F} Pr[X_j = y_j]` for every `y`. -/
def IsIndep (p : (E → α) → ℝ) (F : Finset E) : Prop :=
  ∀ y : E → α, count p F y = ∏ j ∈ F, count p {j} y

/-- A circuit of a family `I` of sets: an inclusion-minimal set not in `I`. -/
def IsCircuit (I : Finset E → Prop) (C : Finset E) : Prop :=
  ¬ I C ∧ ∀ D, D ⊂ C → I D

/-- The family of all circuits of `I` contained in `S`. -/
def circuitsIn (I : Finset E → Prop) (S : Finset E) : Finset (Finset E) :=
  S.powerset.filter (fun C => IsCircuit I C)

/-- Definition 4.4: a level function for `μ` is `λ : ℕ → ℕ` (used on positive integers) with
`λ(1) = 0`, `λ(s) ≥ 1` for `s ≥ 2`, and such that every strict drop of a conditional support size
lowers it: for `K ⊆ K' ⊆ E` and `j ∉ K'` with `s_{K'}(j) < s_K(j)`,
`λ(s_{K'}(j)) ≤ λ(s_K(j)) − 1` (written without natural-number subtraction). -/
def IsLevelFunction (p : (E → α) → ℝ) (lam : ℕ → ℕ) : Prop :=
  lam 1 = 0 ∧ (∀ t, 2 ≤ t → 1 ≤ lam t) ∧
    ∀ K K' : Finset E, K ⊆ K' → ∀ j, j ∉ K' → condSize p K' j < condSize p K j →
      lam (condSizeNat p K' j) + 1 ≤ lam (condSizeNat p K j)

/-- The level `D_λ(μ) = max_{j ∈ E} λ(s_j)` (an empty maximum is `0`). -/
def level (p : (E → α) → ℝ) (lam : ℕ → ℕ) : ℕ :=
  Finset.univ.sup (fun j => lam (s p j))

/-! ## Laws of `X_A` given `X_K = y`, through the oracle of `μ` (Lemma 2.1)

Every distribution in the sampler's recursion is the law of `X_A` given `X_K = y` for disjoint
`A, K ⊆ E` (p. 12, p. 21). Its counting oracle is simulated by the oracle of `μ`:
`(T, z) ↦ Pr[X_{K ∪ T} = (y, z)] / Pr[X_K = y]`. -/

/-- Overwrite the pinning `y` by `z` outside `K`: the full assignment equal to `y` on `K` and to `z`
elsewhere. -/
def pinWith (K : Finset E) (y z : E → α) : E → α :=
  fun j => if j ∈ K then y j else z j

/-- The derived counting oracle of the law of `X_A` given `X_K = y` (Lemma 2.1), at the query
`(T, z)` with `T ⊆ A`. -/
def condCount (p : (E → α) → ℝ) (K : Finset E) (y : E → α) (T : Finset E) (z : E → α) : ℝ :=
  count p (K ∪ T) (pinWith K y z) / count p K y

/-- The singleton support of `X_j` under the law of `X_A` given `X_K = y`. -/
def condSingleSupp (p : (E → α) → ℝ) (K : Finset E) (y : E → α) (j : E) : Finset α :=
  Finset.univ.filter (fun a => 0 < condCount p K y {j} (fun _ => a))

/-- Independence of `F` for the law of `X_A` given `X_K = y` (Definition 2.7 for that law). -/
def IsCondIndep (p : (E → α) → ℝ) (K : Finset E) (y : E → α) (F : Finset E) : Prop :=
  ∀ z : E → α, condCount p K y F z = ∏ j ∈ F, condCount p K y {j} z

/-- The level `D_λ(ν) = max_{j ∈ A} λ(s^ν_j)` of the law `ν` of `X_A` given `X_K = y`. -/
def condLevel (p : (E → α) → ℝ) (lam : ℕ → ℕ) (A K : Finset E) (y : E → α) : ℕ :=
  A.sup (fun j => lam (condSingleSupp p K y j).card)

/-- The single nonadaptive batch of singleton counting queries used to learn all supports. -/
def singletonQueries : Finset (Finset E × (E → α)) :=
  (Finset.univ : Finset (E × α)).image (fun ja => ({ja.1}, fun _ => ja.2))

/-- Recover singleton supports from the answers to that one batch, without access to `p`. -/
def supportsFromAnswers (ans : (Finset E × (E → α)) → ℝ) (j : E) : Finset α :=
  Finset.univ.filter (fun a => 0 < ans ({j}, fun _ => a))

end ExactParallelSampling.QuasiUniform


