-- Prove2me | Definitions.Def_OffPolicyDRL_CrossFit_Estimator
-- name    : OffPolicyDRL_CrossFit_Estimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:14.516758+00:00
-- url     : https://prove2.me/theorems/7b4469ca-7751-41da-862d-ad1c7094c722
-- title:
--   Cross-fitted DRL estimator ρ̂_DRL(M3) of Eq. (4): two folds, learners fitted on the opposite fold, L² errors ‖ŵ^[j] − w‖₂, ‖q̂^[j] − q‖₂
-- statement:
--   Let $O_0,O_1,\dots$ be a sequence of observations $(s,a,r,s')$, and let $n$ be the sample size. Split the indices $\{0,\dots,n-1\}$ into two folds: fold $0$ is $\{i<\lfloor n/2\rfloor\}$ and fold $1$ is $\{\lfloor n/2\rfloor\le i<n\}$.
--
--   **Nuisance learners** are maps that, for each fold $j\in\{0,1\}$ and each $n$, take the data of fold $j$ to an estimate $\hat w^{[j]}$ of $w$ and an estimate $\hat q^{[j]}$ of $q$. They are **measurable** when $(\text{data},s)\mapsto\hat w^{[j]}(s)$ and $(\text{data},(s,a))\mapsto\hat q^{[j]}(s,a)$ are jointly measurable.
--
--   The **cross-fitted estimator** (Eq. (4)) is
--   $$\hat\rho_{\rm DRL}(\mathcal M_3)=\frac1n\sum_{i=0}^{n-1}\psi\big(s^{\langle i\rangle},a^{\langle i\rangle},r^{\langle i\rangle},s'^{\langle i\rangle};\hat w^{\langle i\rangle},\hat q^{\langle i\rangle}\big).$$
--   Here $\hat w^{\langle i\rangle},\hat q^{\langle i\rangle}$ are the estimates fitted on the fold **not** containing $i$, and $\psi$ is the estimating function of the model.
--
--   The random $L^2$ errors are $\|\hat w^{[j]}-w\|_2=\big(\int(\hat w^{[j]}-w)^2\,dp^{(0)}_{\pi_b}\big)^{1/2}$ and $\|\hat q^{[j]}-q\|_2=\big(\int(\hat q^{[j]}-q)^2\,d(p^{(0)}_{\pi_b}\otimes\pi_b)\big)^{1/2}$, as on p. 23 ("defined on the offline data").
--
--   **Formalization Note** The paper splits the sample "into two even folds"; here the split is deterministic, at $\lfloor n/2\rfloor$. For an i.i.d. sample this has the same law as a random even partition. Cross-fitting is built into the types: the learner for fold $j$ is a function of fold $j$'s observations only. For $n\le1$ a fold is empty, a degenerate case that is irrelevant asymptotically.
-- source:
--   Kallus & Uehara, Efficiently Breaking the Curse of Horizon in Off-Policy Evaluation with Double Reinforcement Learning, arXiv:1909.05850v6, Eq. (4) and the following paragraph, p. 22; L² errors, p. 23

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace OffPolicyDRL.CrossFit

/-- Number of observations in fold `j` of a sample of size `n`: fold `0` is `{i < ⌊n/2⌋}` and
fold `1` is `{⌊n/2⌋ ≤ i < n}`. -/
def foldSize (j : Fin 2) (n : ℕ) : ℕ := if j = 0 then n / 2 else n - n / 2

/-- The `k`-th observation index of fold `j`. -/
def foldIdx (j : Fin 2) (n : ℕ) (k : Fin (foldSize j n)) : ℕ := (if j = 0 then 0 else n / 2) + k

/-- The fold containing observation `i` of a sample of size `n`. -/
def foldOf (n i : ℕ) : Fin 2 := if i < n / 2 then 0 else 1

/-- Nuisance learners: for each fold `j` and sample size `n`, a map from the data of fold `j`
to an estimate `ŵ^{[j]}` of `w` and an estimate `q̂^{[j]}` of `q`. -/
structure Learners (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] where
  /-- the `w`-learner fitted on fold `j` -/
  W : (j : Fin 2) → (n : ℕ) → (Fin (foldSize j n) → S × A × ℝ × S) → S → ℝ
  /-- the `q`-learner fitted on fold `j` -/
  Qh : (j : Fin 2) → (n : ℕ) → (Fin (foldSize j n) → S × A × ℝ × S) → S × A → ℝ

namespace Learners

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The learners are jointly measurable in (fold data, argument). -/
structure IsMeasurable (L : Learners S A) : Prop where
  W : ∀ j n, Measurable (Function.uncurry (L.W j n))
  Qh : ∀ j n, Measurable (Function.uncurry (L.Qh j n))

end Learners

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] {Ω : Type*}

/-- The data of fold `j` of the first `n` observations of the sample `O`. -/
def foldData (O : ℕ → Ω → S × A × ℝ × S) (j : Fin 2) (n : ℕ) (ω : Ω) :
    Fin (foldSize j n) → S × A × ℝ × S :=
  fun k => O (foldIdx j n k) ω

/-- `ŵ^{[j]}`: the `w`-estimate fitted on fold `j` only. -/
def what (L : Learners S A) (O : ℕ → Ω → S × A × ℝ × S) (j : Fin 2) (n : ℕ) (ω : Ω) : S → ℝ :=
  L.W j n (foldData O j n ω)

/-- `q̂^{[j]}`: the `q`-estimate fitted on fold `j` only. -/
def qhat (L : Learners S A) (O : ℕ → Ω → S × A × ℝ × S) (j : Fin 2) (n : ℕ) (ω : Ω) :
    S × A → ℝ :=
  L.Qh j n (foldData O j n ω)

/-- The cross-fitted estimator `ρ̂_DRL(M3) = n⁻¹ ∑_i ψ(s⟨i⟩, a⟨i⟩, r⟨i⟩, s′⟨i⟩; ŵ⟨i⟩, q̂⟨i⟩)` of
Eq. (4), where `ŵ⟨i⟩, q̂⟨i⟩` are fitted on the fold not containing `i`. -/
noncomputable def estimate [MeasurableSpace.CountablyGenerated A] (M : Model S A)
    (L : Learners S A) (O : ℕ → Ω → S × A × ℝ × S) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    M.ψ (what L O (1 - foldOf n i) n ω) (qhat L O (1 - foldOf n i) n ω) (O i ω)

/-- The `L²(p^{(0)}_{πb})` error `‖ŵ^{[j]} - w‖₂` (a random variable). -/
noncomputable def errW (M : Model S A) (L : Learners S A) (O : ℕ → Ω → S × A × ℝ × S)
    (j : Fin 2) (n : ℕ) (ω : Ω) : ℝ :=
  M.normS (fun s => what L O j n ω s - M.w s)

/-- The `L²(p^{(0)}_{πb} ⊗ πb)` error `‖q̂^{[j]} - q‖₂` (a random variable). -/
noncomputable def errQ (M : Model S A) (L : Learners S A) (O : ℕ → Ω → S × A × ℝ × S)
    (j : Fin 2) (n : ℕ) (ω : Ω) : ℝ :=
  M.normSA (fun x => qhat L O j n ω x - M.q x)

end OffPolicyDRL.CrossFit


