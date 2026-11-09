-- Prove2me | Definitions.Def_PerturbedWF_Algorithm
-- name    : PerturbedWF_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:42:32.833202+00:00
-- url     : https://prove2.me/theorems/50f0ddd5-4f24-470a-abb6-ed1936017240
-- title:
--   The perturbed work function algorithm with $v=Aq$, $q$ uniform on $[-1,1]^m$ (Algorithm 3.1, §4.1)
-- statement:
--   Let $A_1,\dots,A_n\in\mathbb R^m$ be vectors, one per point, and $A\in\mathbb R^{n\times m}$ the matrix with rows $A_i$. The algorithm samples $q$ uniformly from the cube $[-1,1]^m$ once, sets $v=Aq$ (so $v_i=\langle A_i,q\rangle$), starts at $X_0=x_0$, and whenever $F_t$ is requested moves to
--   $$X_t\in\arg\max_{x\in\mathcal C}\{\langle v,x\rangle-W_t(x)\}.$$
--   The only randomness is the choice of $q$ at time $0$.
--
--   A **run** is any such sequence of choices, made for every $q$ in the cube; ties may be broken arbitrarily, even differently for different $q$.
--
--   **Formalization Note.** `matVec A q` is $Aq$; `cubeLaw m` is the uniform law on $[-1,1]^m$ (Lebesgue measure conditioned on the cube). `IsAlgRun d x₀ F A N X` says $X_0(q)=x_0$ for all $q$ and, for $1\le t\le N$ and $q$ in the cube, $X_t(q)$ maximizes $\langle Aq,x\rangle-W_t(x)$ over the simplex. §4.1 takes the maximum over $\mathrm{supp}(W_t)$; by Lemma 2.3 every such maximizer is a maximizer over the simplex, so every run of §4.1 is a run here. No tie-breaking rule and no measurability in $q$ is imposed.
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Algorithm 3.1, p.8 (PDF p.9); §3.4, p.9 (PDF p.10); §4.1 'Algorithm', p.12 (PDF p.13)

import Mathlib
import Definitions.Def_PerturbedWF_MetricAllocation

namespace PerturbedWF

/-!
# The perturbed work function algorithm for metric allocation (§4.1)

C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…), Algorithm 3.1, p.8 (PDF p.9); §3.4, p.9; §4.1
"Algorithm", p.12 (PDF p.13).

Given vectors `A_i ∈ ℝ^m` (one per point `i`), sample `q` uniformly from `[−1, 1]^m`, set
`v = Aq`, start at `X_0 = x₀`, and at every time `t` move to a maximizer `X_t` of
`⟨v, x⟩ − W_t(x)`.

**Formalization Note.**
* `matVec A q` is `Aq`, `(Aq)_i = ∑_k A i k * q k`, with `A : ι → Fin m → ℝ` (row `i` is `A i`).
* `cubeLaw m` is the uniform probability law on `[−1, 1]^m`, the Lebesgue measure conditioned on
  the cube `Set.Icc (-1) 1` (in the product order, the product of the intervals).
* A run is a function `X : ℕ → (Fin m → ℝ) → (ι → ℝ)`, `X t q` the configuration at time `t` for
  the draw `q`. `IsAlgRun` requires `X 0 q = x₀` for every `q` and, for `1 ≤ t ≤ N` and every
  `q` in the cube, that `X t q` maximize `⟨Aq, x⟩ − W_t(x)` over the whole simplex. §4.1 takes
  the maximum over `supp(W_t)`; by Lemma 2.3 every maximizer over `supp(W_t)` is a maximizer over
  the simplex, so the runs allowed here include all runs of §4.1. No tie-breaking rule and no
  measurability in `q` is imposed.
-/

/-- `Aq`: the vector `i ↦ ∑_k A i k * q k`. -/
def matVec {ι : Type} {m : ℕ} (A : ι → Fin m → ℝ) (q : Fin m → ℝ) : ι → ℝ :=
  fun i => ∑ k, A i k * q k

/-- The uniform distribution on the cube `[−1, 1]^m`. -/
noncomputable def cubeLaw (m : ℕ) : MeasureTheory.Measure (Fin m → ℝ) :=
  ProbabilityTheory.cond MeasureTheory.volume (Set.Icc (-1) 1)

/-- `X` is a run of the §4.1 algorithm with vectors `A` on the requests `(r, f)` up to time `N`:
`X_0 = x₀`, and for `1 ≤ t ≤ N` and every `q ∈ [−1, 1]^m`, `X_t(q)` maximizes
`⟨Aq, x⟩ − W_t(x)` over the simplex. -/
def IsAlgRun {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (d : ι → ι → ℝ) (x₀ : ι → ℝ)
    (F : ℕ → (ι → ℝ) → ℝ) (A : ι → Fin m → ℝ) (N : ℕ)
    (X : ℕ → (Fin m → ℝ) → (ι → ℝ)) : Prop :=
  (∀ q, X 0 q = x₀) ∧
    ∀ t ∈ Finset.Icc 1 N, ∀ q ∈ Set.Icc (-1 : Fin m → ℝ) 1, X t q ∈ simplex ι ∧
      ∀ y ∈ simplex ι, dot (matVec A q) y - workFn d x₀ F t y ≤
        dot (matVec A q) (X t q) - workFn d x₀ F t (X t q)

end PerturbedWF


