-- Prove2me | Definitions.Def_MultiChoiceSecretary_Alg_Setting
-- name    : MultiChoiceSecretary_Alg_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:41.159011+00:00
-- url     : https://prove2.me/theorems/f8b216af-30e8-42e9-9505-df635df66f93
-- title:
--   §1–§2, PDF pp. 1–2 — random-order k-choice model, the recursive algorithm, v, modified value, the split (Y, Z) and q
-- statement:
--   This file fixes the model and the algorithm of Kleinberg's multiple-choice secretary problem, together with the auxiliary quantities of the proof sketch of Theorem 2.1.
--
--   **The model.** A finite set $S$ of $n$ distinct non-negative real numbers is revealed one element at a time in a uniformly random order. An arrival order is a permutation $\pi$ of $\{0,\dots,n-1\}$; at time $t$ the element with rank $\pi(t)$ (in increasing order) arrives, and its value is written $x_t$. Averages over the order are $\frac{1}{n!}\sum_\pi$, the published uniform average.
--
--   **The $k$ largest elements.** For $j \ge 0$, $T_j(S)$ denotes the $j$ largest elements of $S$ (all of $S$ when $j \ge n$) and $\operatorname{top}_j(S)$ their sum; $T = T_k(S)$ and $v = \operatorname{top}_k(S)$. The **modified value** of a set $A \subseteq S$ is the sum of its elements that lie in $T$.
--
--   **The algorithm.** On an arrival sequence $x_0,\dots,x_{n-1}$ and a budget $k$, the algorithm $\mathcal A_k$ outputs a random set of selected positions:
--
--   1. If $k = 1$: the classical secretary rule — observe the first $\lfloor n/e\rfloor$ arrivals, then select the first later arrival exceeding all earlier ones, if there is one.
--   2. If $k \ge 2$: draw $m \sim B(n, 1/2)$, the number of heads in $n$ fair coin tosses. Run $\mathcal A_{\ell}$, $\ell = \lfloor k/2\rfloor$, on the first $m$ arrivals (it draws its own binomial at the next level). Let $y_1 \ge y_2 \ge \dots$ be the first $m$ values in decreasing order. After the $m$-th arrival, select every arrival exceeding $y_\ell$, in arrival order, until $k$ items have been selected in total (the items selected among the first $m$ count towards $k$) or the sequence ends.
--
--   The pair (selection among the first $m$, selection after the $m$-th) is also exposed, as the stage distribution.
--
--   **Expected values.** The expected value of the algorithm is the expectation, over the uniform order and over every binomial draw at every level of the recursion, of the sum of the selected values. The expected phase-2 modified value is the same expectation of the modified value of the elements selected after the $m$-th arrival.
--
--   **The split.** For the proof sketch, $Y$ is the set of the first $m$ values and $Z = S \setminus Y$, with the order uniform and $m \sim B(n,1/2)$ independent; an expectation of a function of $Y$ is written $\mathbb E_{\mathrm{split}}[f(Y)]$. Finally $q$ counts the elements of $Z$ that exceed $y_\ell$, the $\ell$-th largest element of $Y$.
--
--   These are the objects of Theorem 2.1 and of every claim in its proof sketch.
--
--   **Formalization Note.** Positions are $0$-based. A selection is a `Finset (Fin n)` and the algorithm is a `PMF` over selections, defined by well-founded recursion on $k$; at $k = 0$ it selects nothing, for totality only. The paper does not say what $y_\ell$ is when $m < \ell$; here it is $-\infty$ (Lean `none`): every arrival after the $m$-th is then selected until the cap, and correspondingly $q = |Z|$ when $|Y| < \ell$. Under the other reading (select nothing) Theorem 2.1 fails for $n \ll k$. The binomial is Mathlib's `PMF.binomial (1/2)`, which puts mass $\binom{n}{i}2^{-n}$ on $i$; the classical rule and the uniform average are the published definition `SecretaryWD.DiscUpper.ClassicalSecretary`, with $\lfloor n/e\rfloor$ computed as `Nat.floor (n / Real.exp 1)`.
-- source:
--   Kleinberg, A multiple-choice secretary algorithm with applications to online auctions, SODA 2005, PDF pp. 1–2, §1 (model) and §2 Algorithm (algorithm; proof sketch of Theorem 2.1 for T, modified value, Y, Z, q)

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_ClassicalSecretary

namespace MultiChoiceSecretary.Alg

open SecretaryWD.DiscUpper

/-! ### The random-order model (§1, PDF p. 1) -/

/-- The arrival sequence of the finite set `S` under the arrival order `π`: at (0-based) time `t`
the element `S.orderEmbOfFin rfl (π t)` arrives, i.e. the `π t`-th smallest element of `S`.
Averaging over `π` with `uniformAvg` gives the uniformly random order. -/
noncomputable def arrivals (S : Finset ℝ) (π : Equiv.Perm (Fin S.card)) : Fin S.card → ℝ :=
  fun t => S.orderEmbOfFin rfl (π t)

/-- `topK S j`: the `j` largest elements of `S` (all of `S` when `j ≥ |S|`). -/
noncomputable def topK (S : Finset ℝ) (j : ℕ) : Finset ℝ :=
  ((S.sort (· ≥ ·)).take j).toFinset

/-- `topSum S j`: the sum of the `j` largest elements of `S`; `v = topSum S k`. -/
noncomputable def topSum (S : Finset ℝ) (j : ℕ) : ℝ :=
  ((S.sort (· ≥ ·)).take j).sum

/-- The modified value of a set `A ⊆ S`: the sum of its elements that lie in `T = topK S k`
(an element of `S \ T` has modified value zero). -/
noncomputable def modVal (S : Finset ℝ) (k : ℕ) (A : Finset ℝ) : ℝ :=
  ∑ x ∈ A ∩ topK S k, x

/-! ### The recursive algorithm (§2, PDF p. 2) -/

/-- The values seen in the first `m` arrivals (times `t < m`), sorted from largest to smallest
(with multiplicity): `y₁ ≥ y₂ ≥ …`. -/
noncomputable def prefixSorted {n : ℕ} (x : Fin n → ℝ) (m : ℕ) : List ℝ :=
  ((Finset.univ.filter fun t : Fin n => t.val < m).val.map x).sort (· ≥ ·)

/-- The threshold `y_ℓ`: the `ℓ`-th largest (1-based) of the first `m` arrivals, or `none`
when fewer than `ℓ` arrivals were seen (read as `y_ℓ = -∞`). Used with `1 ≤ ℓ`. -/
noncomputable def kth {n : ℕ} (x : Fin n → ℝ) (m ℓ : ℕ) : Option ℝ :=
  (prefixSorted x m)[ℓ - 1]?

/-- `exceeds thr z`: `z` exceeds the threshold. A missing threshold (`none`, i.e. `-∞`) is
exceeded by every value. -/
def exceeds : Option ℝ → ℝ → Prop
  | none, _ => True
  | some y, z => y < z

noncomputable instance (o : Option ℝ) (z : ℝ) : Decidable (exceeds o z) := by
  cases o <;> unfold exceeds <;> infer_instance

/-- Phase 2 of the algorithm for `k ≥ 2`: after the `m`-th arrival, select every arrival that
exceeds the threshold `thr`, in arrival order, until `k` items have been selected **in total**
(the phase-1 selection `S1` included) or the sequence ends. Position `t` is selected iff
`t ≥ m`, `x t` exceeds `thr`, and fewer than `k` items were selected before time `t`. -/
noncomputable def phase2 {n : ℕ} (k : ℕ) (x : Fin n → ℝ) (m : ℕ) (thr : Option ℝ)
    (S1 : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun t => m ≤ t.val ∧ exceeds thr (x t) ∧
    S1.card + (Finset.univ.filter fun t' : Fin n =>
      m ≤ t'.val ∧ t' < t ∧ exceeds thr (x t')).card < k

/-- `1/2 ≤ 1` in `ℝ≥0`, for the fair-coin binomial `B(n, 1/2)`. -/
theorem half_le_one : (1 / 2 : NNReal) ≤ 1 := by norm_num

/-- One stage of the algorithm for `k ≥ 2`, given the procedure `rec` used on the first `m`
arrivals: draw `m ~ B(n, 1/2)` (`PMF.binomial` puts mass `C(n,i)/2ⁿ` on `i`), run `rec` on the
first `m` arrivals (phase 1), then run phase 2 with threshold `y_ℓ`, `ℓ = ⌊k/2⌋`. The result is
the pair (phase-1 selection, phase-2 selection), as positions in `0, …, n-1`. -/
noncomputable def stageWith (rec : (m : ℕ) → (Fin m → ℝ) → PMF (Finset (Fin m)))
    (k n : ℕ) (x : Fin n → ℝ) : PMF (Finset (Fin n) × Finset (Fin n)) :=
  (PMF.binomial (1 / 2) half_le_one n).bind fun m =>
    (rec m.val (fun i => x (Fin.castLE m.is_le i))).map fun S1' =>
      let S1 := S1'.map (Fin.castLEEmb m.is_le)
      (S1, phase2 k x m.val (kth x m.val (k / 2)) S1)

/-- Kleinberg's recursive `k`-choice secretary algorithm on an arrival sequence `x` of length `n`,
as a probability distribution over the set of selected positions.
* `k = 0`: select nothing (not part of the paper; for totality only).
* `k = 1`: the classical secretary rule (observe `⌊n/e⌋`, then take the first arrival exceeding
  all earlier ones, if any).
* `k ≥ 2`: `m ~ B(n, 1/2)`; recursively select up to `⌊k/2⌋` among the first `m` arrivals; then
  select every later arrival exceeding `y_ℓ` until `k` items are selected in total. -/
noncomputable def alg : ℕ → (n : ℕ) → (Fin n → ℝ) → PMF (Finset (Fin n))
  | 0, _, _ => PMF.pure ∅
  | 1, n, x => PMF.pure (classicalSecretary n x).toFinset
  | k + 2, n, x =>
      (stageWith (fun m y => alg ((k + 2) / 2) m y) (k + 2) n x).map fun p => p.1 ∪ p.2
termination_by k => k
decreasing_by omega

/-- The two-phase split of the algorithm at the top level, for `k ≥ 2`: the distribution of
(phase-1 selection, phase-2 selection). Its union is `alg k n x`. -/
noncomputable def stage (k n : ℕ) (x : Fin n → ℝ) : PMF (Finset (Fin n) × Finset (Fin n)) :=
  stageWith (fun m y => alg (k / 2) m y) k n x

/-! ### Expected values -/

/-- The expected value of the elements selected by the algorithm, over the uniformly random
arrival order and all internal binomial draws. -/
noncomputable def expectedValue (S : Finset ℝ) (k : ℕ) : ℝ :=
  uniformAvg fun π =>
    ∑ s : Finset (Fin S.card), ((alg k S.card (arrivals S π)) s).toReal *
      ∑ t ∈ s, arrivals S π t

/-- The expected modified value of the elements selected in phase 2 (all of which come from the
arrivals after the `m`-th, the set `Z`), over the random order and all binomial draws. -/
noncomputable def expectedPhase2ModVal (S : Finset ℝ) (k : ℕ) : ℝ :=
  uniformAvg fun π =>
    ∑ p : Finset (Fin S.card) × Finset (Fin S.card), ((stage k S.card (arrivals S π)) p).toReal *
      ∑ t ∈ p.2, if arrivals S π t ∈ topK S k then arrivals S π t else 0

/-! ### The split `(Y, Z)` used in the proof sketch -/

/-- `Y`: the set of values of the first `m` arrivals under the order `π`. -/
noncomputable def prefixSet (S : Finset ℝ) (π : Equiv.Perm (Fin S.card)) (m : ℕ) : Finset ℝ :=
  (Finset.univ.filter fun t : Fin S.card => t.val < m).image (arrivals S π)

/-- The expectation of `f(Y)` where `Y` is the set of the first `m` arrivals, the order is uniform
and `m ~ B(n, 1/2)` independently, `n = |S|`. -/
noncomputable def splitAvg (S : Finset ℝ) (f : Finset ℝ → ℝ) : ℝ :=
  uniformAvg fun π =>
    ∑ m : Fin (S.card + 1),
      ((PMF.binomial (1 / 2) half_le_one S.card) m).toReal * f (prefixSet S π m)

/-- `q`: the number of elements of `Z = S \ Y` exceeding `y_ℓ`, the `ℓ`-th largest element of `Y`.
When `Y` has fewer than `ℓ` elements, `y_ℓ = -∞` and `q = |Z|`. Used with `1 ≤ ℓ`. -/
noncomputable def qCount (S Y : Finset ℝ) (ℓ : ℕ) : ℕ :=
  match (Y.sort (· ≥ ·))[ℓ - 1]? with
  | some y => ((S \ Y).filter fun z => y < z).card
  | none => (S \ Y).card

end MultiChoiceSecretary.Alg


