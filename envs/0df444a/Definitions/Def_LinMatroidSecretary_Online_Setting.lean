-- Prove2me | Definitions.Def_LinMatroidSecretary_Online_Setting
-- name    : LinMatroidSecretary_Online_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:59.727643+00:00
-- url     : https://prove2.me/theorems/6f5f6c7e-9ae6-44c1-940a-55a80b03c596
-- title:
--   §1, §2.1 — linear matroid of a vector family, greedy optimum OPT(Y), ordinal online policies and run probabilities
-- statement:
--   The online-representation model of the linear matroid secretary problem.
--
--   1. **Linear matroid.** Let $F$ be a field and $v:R\to F^d$ a family of vectors indexed by a finite ground set $R$. A set $I\subseteq R$ is *independent* when the family $(v_e)_{e\in I}$ is linearly independent. Two elements with the same nonzero vector are therefore dependent, and an element with $v_e=0$ is a loop. These sets satisfy the matroid axioms (the augmentation axiom is proved in the definition by comparing dimensions of spans); the resulting matroid $M_v$ has ground set $R$.
--
--   2. **Value order and greedy optimum.** The ground set carries a strict total order $<$, the *value order*: it is the weight order with ties broken by the fixed total order chosen before the arrivals, larger meaning better. For $Y\subseteq R$, $\mathrm{OPT}(Y)$ is the greedy maximum-weight basis of $M_v$ restricted to $Y$:
--   $$\mathrm{OPT}(Y)=\{e\in Y:\ v_e\notin\langle v_q: q\in Y,\ e<q\rangle\},$$
--   taken from the published definition `OrdinalMSP.Forbidden.opt` applied to $M_v$.
--
--   3. **Ordinal online policies.** A policy for $n$ arrivals with vectors in $F^d$ is a rule which, at step $t$ (the $(t+1)$-st arrival), receives the vectors of the elements observed so far in arrival order, the relative value order of these elements, and its own previous accept/reject decisions, and returns the probability $a_t$ of accepting the arriving element. It sees nothing else: not the labels of the elements, not the unseen vectors, not the weights and not the ground set. The policy is *valid* when all its outputs lie in $[0,1]$.
--
--   4. **Runs.** An arrival order is a bijection $\sigma:\{0,\dots,n-1\}\to R$ ($\sigma(t)$ arrives at step $t$). A decision vector $b\in\{0,1\}^n$ has probability
--   $$\Pr[b\mid\sigma]=\prod_{t<n}\bigl(b_t\,a_t+(1-b_t)(1-a_t)\bigr),$$
--   where $a_t$ is the policy's output on the information of step $t$. The selected set is $\mathrm{ALG}(\sigma,b)=\{\sigma(t):b_t=1\}$; the first $m$ arrivals and the elements accepted among them are $\{\sigma(t):t<m\}$ and $\{\sigma(t):t<m,\ b_t=1\}$.
--
--   5. **Probabilities.** With the arrival order uniform over the $n!$ bijections,
--   $$\Pr[A]=\frac1{n!}\sum_{\sigma}\sum_{b}\Pr[b\mid\sigma]\,\mathbf 1[A(\sigma,b)],\qquad \mathbb E[w(\mathrm{ALG})]=\frac1{n!}\sum_\sigma\sum_b \Pr[b\mid\sigma]\sum_{e\in\mathrm{ALG}(\sigma,b)}w(e).$$
--
--   These objects are used by the goal theorem and by Lemma 3.
--
--   **Formalization Note** Vectors are `Fin d → F`; the value order is a `LinearOrder` on the ground type. Randomness is behavioural (one acceptance probability per step, a function of the observed history), and every probability is an exact finite sum, so no measure theory is involved. A policy is indexed by $n$, $d$ and $F$ only, so it cannot depend on the ground type.
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), §1 (PDF p. 3, printed p. 1: model, OPT(Y), ordinal algorithms, probability-competitiveness) and §2.1 (PDF p. 7, printed p. 5)

import Mathlib
import Definitions.Def_OrdinalMSP_Forbidden_Setting

/-!
# The online-representation model of the linear matroid secretary problem

Bérczi, Dughmi, Livanos, Soto, Verdugo, *The Strong Secretary Conjecture is True for Linear
Matroids*, STOC 2027 submission #608, §1 (PDF p. 3, printed p. 1) and §2.1 (PDF p. 7).

* The linear matroid of a vector family `v : R → (Fin d → F)`: `I` is independent iff the
  family `(v e)_{e ∈ I}` is linearly independent (`LinearIndepOn F v I`).
* `OPT v Y`: the greedy optimum of `Y` under the value order (a `LinearOrder` on the ground type,
  larger = better, ties already broken), via the published `OrdinalMSP.Forbidden.opt`.
* Ordinal online policies in the online-representation model, behavioural randomness, and the
  exact finite-sum semantics of a run over a uniformly random arrival order.
-/

namespace LinMatroidSecretary.Online

open Finset

noncomputable section

section Matroid

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
variable {R : Type*} [Finite R]

/-- The independence system of the vector family `v`: `I ⊆ R` is independent iff the family
`(v e)_{e ∈ I}` (not the set of vectors) is linearly independent. It satisfies the matroid
augmentation axiom, proved here by comparing dimensions of spans. -/
def linIndepMatroid (v : R → V) : IndepMatroid R :=
  IndepMatroid.ofFinite (E := Set.univ) Set.finite_univ (fun I => LinearIndepOn F v I)
    (linearIndepOn_empty F v)
    (fun _ _ hJ hIJ => hJ.mono hIJ)
    (by
      classical
      intro I J hI hJ hlt
      by_contra hcon
      push Not at hcon
      have hsub : Set.range (fun x : J => v x) ⊆ Submodule.span F (Set.range fun x : I => v x) := by
        rintro _ ⟨⟨e, heJ⟩, rfl⟩
        by_cases heI : e ∈ I
        · exact Submodule.subset_span ⟨⟨e, heI⟩, rfl⟩
        · by_contra hnot
          refine hcon e heJ heI ((linearIndepOn_insert heI).2 ⟨hI, ?_⟩)
          rwa [Set.image_eq_range]
      have : Fintype I := Fintype.ofFinite I
      have : Fintype J := Fintype.ofFinite J
      have : Module.Finite F (Submodule.span F (Set.range fun x : I => v x)) :=
        Module.Finite.span_of_finite F (Set.finite_range _)
      have hle := Submodule.finrank_mono (Submodule.span_le.2 hsub)
      rw [finrank_span_eq_card hJ, finrank_span_eq_card hI] at hle
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
        Nat.card_eq_fintype_card] at hlt
      omega)
    (fun _ _ => Set.subset_univ _)

/-- The linear matroid represented by `v`, on the ground set `univ`. -/
def linMatroid (v : R → V) : Matroid R := (linIndepMatroid (F := F) v).matroid

end Matroid

section Opt

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- `OPT(Y)` (PDF p. 3): the greedy maximum-weight basis of the linear matroid of `v` restricted
to `Y`, with the value order `<` on `ι` (larger is better, ties broken by the fixed total order).
It is the published `OrdinalMSP.Forbidden.opt` applied to `linMatroid v`:
`OPT(Y) = {e ∈ Y : e ∉ cl{q ∈ Y : e < q}}`. -/
def OPT (F : Type*) [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (v : ι → V) (Y : Finset ι) : Finset ι :=
  OrdinalMSP.Forbidden.opt (linMatroid (F := F) v) Y

end Opt

/-! ## Ordinal online policies in the online-representation model -/

/-- An ordinal online policy for `n` arrivals whose vectors lie in `Fin d → F`. At step `t`
(0-based; the arriving element is the `(t+1)`-st) it receives
* `vs : Fin (t+1) → (Fin d → F)`, the vectors of the elements observed so far, in arrival order;
* `cmp : Fin (t+1) → Fin (t+1) → Bool`, the relative order of the observed elements
  (`cmp i j = true` iff the `i`-th arrival is ranked below the `j`-th);
* `b : Fin t → Bool`, its own previous accept/reject decisions,

and returns the probability of accepting the arriving element. Nothing else (labels, unseen
vectors, weights, the ground type) is visible to it. -/
structure Policy (n d : ℕ) (F : Type*) where
  accept : (t : ℕ) → (Fin (t + 1) → Fin d → F) → (Fin (t + 1) → Fin (t + 1) → Bool) →
    (Fin t → Bool) → ℝ

/-- The policy's outputs are probabilities. -/
def Policy.Valid {n d : ℕ} {F : Type*} (π : Policy n d F) : Prop :=
  ∀ t vs cmp b, 0 ≤ π.accept t vs cmp b ∧ π.accept t vs cmp b ≤ 1

variable {F : Type*} [Field F] {d n : ℕ} {R : Type*} [Fintype R] [LinearOrder R]

/-- The vectors observed at step `t` under arrival order `σ` (`σ j` arrives at step `j`). -/
def obsVecs (v : R → Fin d → F) (σ : Fin n ≃ R) (t : Fin n) : Fin (t.val + 1) → Fin d → F :=
  fun j => v (σ ⟨j.val, by omega⟩)

/-- The relative value order of the elements observed at step `t`. -/
def obsCmp (σ : Fin n ≃ R) (t : Fin n) : Fin (t.val + 1) → Fin (t.val + 1) → Bool :=
  fun i j => decide (σ ⟨i.val, by omega⟩ < σ ⟨j.val, by omega⟩)

/-- The decisions taken before step `t`. -/
def pastDec (b : Fin n → Bool) (t : Fin n) : Fin t.val → Bool :=
  fun j => b ⟨j.val, by omega⟩

/-- The acceptance probability the policy uses at step `t`. -/
def acceptProb (π : Policy n d F) (v : R → Fin d → F) (σ : Fin n ≃ R) (b : Fin n → Bool)
    (t : Fin n) : ℝ :=
  π.accept t.val (obsVecs v σ t) (obsCmp σ t) (pastDec b t)

/-- Probability, under arrival order `σ`, that the policy's decision vector is `b`
(behavioural randomness: `∏_t (b_t ? a_t : 1 − a_t)`). -/
def runProb (π : Policy n d F) (v : R → Fin d → F) (σ : Fin n ≃ R) (b : Fin n → Bool) : ℝ :=
  ∏ t : Fin n, if b t then acceptProb π v σ b t else 1 - acceptProb π v σ b t

/-- The selected set `ALG(σ, b) = {σ t : b t}`. -/
def alg (σ : Fin n ≃ R) (b : Fin n → Bool) : Finset R :=
  (univ.filter fun t : Fin n => b t = true).image σ

/-- The set of the first `m` arrivals. -/
def prefixSet (σ : Fin n ≃ R) (m : ℕ) : Finset R :=
  (univ.filter fun t : Fin n => t.val < m).image σ

/-- The elements accepted among the first `m` arrivals. -/
def prefixAlg (σ : Fin n ≃ R) (b : Fin n → Bool) (m : ℕ) : Finset R :=
  (univ.filter fun t : Fin n => t.val < m ∧ b t = true).image σ

/-- Probability of an event `A σ b` when the arrival order is uniform over the `n!` bijections
`Fin n ≃ R` and the decisions follow the policy:
`(1/n!) ∑_σ ∑_b runProb(σ, b) · 1[A σ b]`. -/
def prob (π : Policy n d F) (v : R → Fin d → F) (A : (Fin n ≃ R) → (Fin n → Bool) → Prop) : ℝ := by
  classical
  exact ((n.factorial : ℝ))⁻¹ * ∑ σ : Fin n ≃ R, ∑ b : Fin n → Bool,
    if A σ b then runProb π v σ b else 0

/-- `P[e ∈ ALG]`. -/
def selProb (π : Policy n d F) (v : R → Fin d → F) (e : R) : ℝ :=
  prob π v fun σ b => e ∈ alg σ b

/-- `E[w(ALG)]`. -/
def expWeight (π : Policy n d F) (v : R → Fin d → F) (w : R → ℝ) : ℝ := by
  classical
  exact ((n.factorial : ℝ))⁻¹ * ∑ σ : Fin n ≃ R, ∑ b : Fin n → Bool,
    runProb π v σ b * ∑ e ∈ alg σ b, w e

end

end LinMatroidSecretary.Online


