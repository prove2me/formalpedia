-- Prove2me | Definitions.Def_MultiwayCut_CKR
-- name    : MultiwayCut_CKR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:08.304318+00:00
-- url     : https://prove2.me/theorems/22acf3d9-4742-401c-8c09-f5f7b2a5dd62
-- title:
--   The CKR algorithm (Algorithm 2) and its separation probability
-- statement:
--   **Algorithm 2 (CKR)** (§2.3, p.4). Choose $r\sim\mathrm{Unif}[0,1]$ and a uniformly random permutation $\sigma$ of $\{1,\dots,k\}$. For $i=1$ to $k-1$, every unassigned point $\mathbf u$ with $u_{\sigma(i)}\ge r$ is assigned to $\sigma(i)$; finally all unassigned points are assigned to $\sigma(k)$. The input points may lie anywhere in $[0,1]^k$.
--
--   The probability of an event $E(r,\sigma)$ is
--   $$\Pr[E]=\frac1{k!}\sum_{\sigma}\lambda\bigl(\{r\in[0,1]: E(r,\sigma)\}\bigr),$$
--   with $\lambda$ the Lebesgue measure, and the **separation probability** $\mathrm{sep}_{\mathrm{CKR}}(\mathbf u,\mathbf v)$ is the probability that $\mathbf u$ and $\mathbf v$ are assigned to different terminals. It is the CKR half of Algorithm 3.
--
--   **Formalization Note** 0-based: the loop index $i=1,\dots,k-1$ is $m=0,\dots,k-2$ and $\sigma(k)$ is `σ (k-1)`; a point goes to $\sigma(m)$ for the first $m$ with $r\le u_{\sigma(m)}$ (non-strict, as printed). The product of the uniform laws of $r$ and $\sigma$ is written as the average over $\sigma$ because Mathlib has no measurable structure on permutations; $\lambda$ is the Lebesgue outer measure.
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, §2.3, p.4, Algorithm 2

import Mathlib

open MeasureTheory

namespace MultiwayCut

/-- **CKR labeling** (Algorithm 2), Buchbinder, Schwartz & Weizman, *Simplex Transformations
and the Multiway Cut Problem*, manuscript of Nov. 1, 2016, §2.3, p.4: given the threshold `r`
and the order `σ`, for `i = 1` to `k − 1` every unassigned `u` with `u_{σ(i)} ≥ r` is assigned
to `σ(i)`; all unassigned vertices are finally assigned to `σ(k)`.

**Formalization Note.** Terminals and coordinates are `Fin k`, 0-based: the loop index `i`
becomes `m = i − 1 < k − 1` and `σ(k)` becomes `σ (k − 1)`. A point is assigned at the first
loop index `m` with `r ≤ u (σ m)` (the paper's non-strict "`≥ r`"). The label of a point does not
depend on the other points, so the algorithm is a function of `(r, σ, u)`. -/
noncomputable def ckr {k : ℕ} [NeZero k] (r : ℝ) (σ : Equiv.Perm (Fin k)) (u : Fin k → ℝ) :
    Fin k :=
  let S : Finset (Fin k) := Finset.univ.filter fun m => m.val < k - 1 ∧ r ≤ u (σ m)
  if h : S.Nonempty then σ (S.min' h) else σ ⟨k - 1, Nat.sub_one_lt (NeZero.ne k)⟩

/-- **Probability of an event of the CKR randomness** (Algorithm 2, step 1, p.4):
`r ∼ Unif[0, 1]` and `σ` a uniform random permutation, independent; the probability of an event
`E r σ` is `(1 / k!) Σ_σ λ({r ∈ [0, 1] | E r σ})`.

**Formalization Note.** This is the product of the uniform law on `[0, 1]` and the uniform
law on `Equiv.Perm (Fin k)`, written as the average over `σ` (Mathlib has no measurable
structure on permutations). `λ` is the Lebesgue outer measure, so no measurability side
condition is needed. The denominator `Fintype.card (Equiv.Perm (Fin k))` is `k!`. -/
noncomputable def ckrProb {k : ℕ} (E : ℝ → Equiv.Perm (Fin k) → Prop) : ℝ :=
  (∑ σ : Equiv.Perm (Fin k), (volume {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ E r σ}).toReal) /
    (Fintype.card (Equiv.Perm (Fin k)) : ℝ)

/-- **Separation probability of the CKR algorithm** (§2.3, p.4): the probability that `u` and
`v` are assigned to different terminals by Algorithm 2. -/
noncomputable def sepCKR {k : ℕ} [NeZero k] (u v : Fin k → ℝ) : ℝ :=
  ckrProb fun r σ => ckr r σ u ≠ ckr r σ v

end MultiwayCut


