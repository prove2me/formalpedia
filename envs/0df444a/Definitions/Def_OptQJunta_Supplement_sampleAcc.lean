-- Prove2me | Definitions.Def_OptQJunta_Supplement_sampleAcc
-- name    : OptQJunta_Supplement_sampleAcc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:11:51.451263+00:00
-- url     : https://prove2.me/theorems/46c8585b-2748-4c3c-8fa6-d521cfcab16e
-- title:
--   Distributions, independent-sample testers $\mathbb E_{Y\sim p^{\otimes t}}[F(Y)]$, Problem 3.1 on a finite ground set, $|\mathrm{supp}(p)|$ and $\mathrm{mass}_s(p)$
-- statement:
--   For a finite set $\mathcal X$, a **probability distribution** $p\in\Delta(\mathcal X)$ is a function $p:\mathcal X\to\mathbb R$ with $p\ge0$ and $\sum_x p(x)=1$. A **$t$-sample tester** is described by its acceptance rule $F:\mathcal X^t\to[0,1]$, the probability (over private randomness) that it accepts after seeing the samples $y$; its acceptance probability on $p$ is
--
--   $$
--   \mathbb E_{Y\sim p^{\otimes t}}[F(Y)]=\sum_{y\in\mathcal X^t}\Big(\prod_{j=1}^t p(y_j)\Big)F(y).
--   $$
--
--   **Problem 3.1** (Union Size Testing) on a finite ground set $\Omega$, with $k\ge1$ and $0<\delta\le1$, concerns a distribution $\mathcal D$ on $2^\Omega$ and $X\sim\mathcal D$:
--
--   1. (YES) some $T\subseteq\Omega$ with $|T|\le k$ has $\Pr[X\subseteq T]=1$;
--   2. (NO) every $T\subseteq\Omega$ with $|T|\le k$ has $\Pr[X\not\subseteq T]\ge\delta$.
--
--   For a distribution $p$ on a finite set, $\mathrm{supp}(p)=\{j:p(j)>0\}$, and
--
--   $$
--   \mathrm{mass}_s(p)=\max_{S:\,|S|\le s}p(S)
--   $$
--
--   is the largest mass carried by at most $s$ labels. Problem 3.12 (Support Size Testing) asks to distinguish $|\mathrm{supp}(p)|\le s$ from $\mathrm{mass}_s(p)\le1-\delta$.
--
--   These objects state the sample-model results (Theorems 3.2, 3.14) and the classicalization identity (Theorem 5.11).
--
--   **Formalization Note** §2.5.4 shows that every tester requesting at most $t$ samples, adaptively and with private randomness, has acceptance probability of the displayed form for some $F$ independent of $p$. $\mathcal D$ is a function on `Finset Ω`; the YES condition is that it vanishes off the subsets of $T$. The maximum defining $\mathrm{mass}_s$ is a `Finset.sup'` over a family that always contains $\varnothing$.
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), §2.1, p.12 (Δ(𝒳), supp); §2.5.4, p.23 (independent samples); Problem 3.1, p.26; §3.2 and Problem 3.12, p.35 (mass_s)

import Mathlib

namespace OptQJunta.Supplement

/-- A probability distribution on a finite set `𝒳` (Bao, Gao, Yao, *Optimal Quantum Junta Testing*,
preprint, version of November 3, 2026, sha256 a97d09a4…, §2.1, p.12: "`Δ(𝒳)` denotes the set of
probability distributions on `𝒳`"): a nonnegative function `p : 𝒳 → ℝ` with total mass `1`. -/
def IsDist {X : Type} [Fintype X] (p : X → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- A `t`-sample acceptance rule (Bao–Gao–Yao preprint, version of November 3, 2026, sha256
a97d09a4…, §2.5.4, p.23): `F(y) ∈ [0, 1]` is the acceptance probability, over the tester's private
randomness, when the samples are `y ∈ 𝒳^t`. -/
def IsTestFn {X : Type} {t : ℕ} (F : (Fin t → X) → ℝ) : Prop :=
  ∀ y, 0 ≤ F y ∧ F y ≤ 1

/-- The acceptance probability `E_{Y ∼ p^{⊗t}}[F(Y)] = Σ_{y ∈ 𝒳^t} (Π_j p(y_j)) F(y)` of the
`t`-sample tester `F` on the distribution `p` (Bao–Gao–Yao preprint, version of November 3, 2026,
sha256 a97d09a4…, §2.5.4, p.23: "the acceptance probability is `E_{Y∼p^{⊗t}}[F(Y)]`").

**Formalization Note** §2.5.4 shows that every tester requesting at most `t` independent samples
(adaptively, with private randomness) has acceptance probability of exactly this form for an `F`
that does not depend on `p`; so quantifying over `F` with `IsTestFn F` is the paper's sample model.
A tester requesting fewer samples ignores the rest. -/
noncomputable def sampleAcc {X : Type} [Fintype X] {t : ℕ} (F : (Fin t → X) → ℝ) (p : X → ℝ) : ℝ :=
  ∑ y : Fin t → X, (∏ j, p (y j)) * F y

/-- **Problem 3.1** (Union Size Testing; Bao–Gao–Yao preprint, version of November 3, 2026, sha256
a97d09a4…, p.26) on a finite ground set `Ω`, YES case: there is `T ⊆ Ω` with `|T| ≤ k` and
`Pr_{X∼𝒟}[X ⊆ T] = 1`.

**Formalization Note** The distribution `𝒟` on `2^Ω` is `D : Finset Ω → ℝ`; for a probability
distribution, `Pr[X ⊆ T] = 1` is: `D` vanishes on every `X ⊄ T`. This is the published
`OptQJunta.UnionYes` with the ground set `Fin n` replaced by an arbitrary finite type. -/
def UnionYesOn {Ω : Type} [Fintype Ω] (D : Finset Ω → ℝ) (k : ℕ) : Prop :=
  ∃ T : Finset Ω, T.card ≤ k ∧ ∀ X : Finset Ω, ¬ X ⊆ T → D X = 0

/-- **Problem 3.1** (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, p.26) on a
finite ground set `Ω`, NO case: every `T ⊆ Ω` with `|T| ≤ k` has uncovered probability
`Pr_{X∼𝒟}[X ⊈ T] ≥ δ`. -/
def UnionNoOn {Ω : Type} [Fintype Ω] [DecidableEq Ω] (D : Finset Ω → ℝ) (k : ℕ) (δ : ℝ) : Prop :=
  ∀ T : Finset Ω, T.card ≤ k → δ ≤ ∑ X ∈ Finset.univ.filter (fun X => ¬ X ⊆ T), D X

/-- The support size `|supp(p)| = |{j : p(j) > 0}|` of a distribution `p` on a finite set
(Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, §2.1, p.12). -/
noncomputable def supportCard {X : Type} [Fintype X] (p : X → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => 0 < p j).card

/-- `mass_s(p) = max_{S ⊆ 𝒳, |S| ≤ s} p(S)`, the largest probability mass carried by at most `s`
labels (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, §3.2, p.35).

**Formalization Note** The maximum ranges over a finite family that always contains `S = ∅`, so it
is a `Finset.sup'` over a nonempty finset. -/
noncomputable def massS {X : Type} [Fintype X] (p : X → ℝ) (s : ℕ) : ℝ := by
  classical
  exact (Finset.univ.filter fun S : Finset X => S.card ≤ s).sup'
    ⟨∅, by simp⟩ fun S => ∑ j ∈ S, p j

end OptQJunta.Supplement


