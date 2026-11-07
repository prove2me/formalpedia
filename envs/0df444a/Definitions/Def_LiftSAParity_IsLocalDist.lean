-- Prove2me | Definitions.Def_LiftSAParity_IsLocalDist
-- name    : LiftSAParity_IsLocalDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:14.228182+00:00
-- url     : https://prove2.me/theorems/edec10b7-06ac-4585-8f8b-cce0aa251b78
-- title:
--   $d$-local distribution for a CNF formula
-- statement:
--   Let $\varphi$ be a CNF formula over the variables $V$ and $d\in\mathbb N$. A **$d$-local distribution** for $\varphi$ is a family $\mathcal D=\{D_I\}$, one probability distribution $D_I$ on $\{0,1\}^I$ for every $I\subseteq V$ with $|I|\le d$, such that
--
--   1. no assignment in the support of $D_I$ falsifies a clause of $\varphi$ whose variables all lie in $I$;
--   2. the distributions are consistent: for all $I,K$ with $|I|,|K|\le d$, the marginals of $D_I$ and $D_K$ on $I\cap K$ are equal.
--
--   Local distributions are the dual objects of low-degree Sherali–Adams refutations, and in the lifting argument they supply the joint law of the gadget outputs on the selected blocks.
--
--   **Formalization Note** The family is a function $D(I,\sigma)$ giving the probability of $\sigma\in\{0,1\}^I$ under $D_I$. For $|I|\le d$ it must be nonnegative with total mass $1$; its values for $|I|>d$ are unconstrained.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §1.1, p.4, conditions (1)–(2)

import Mathlib
import Definitions.Def_LiftSAParity_CNF

namespace LiftSAParity

/-- The restriction of a partial assignment `σ` on `I` to the subset `I ∩ K`. -/
def restrictInter {V : Type*} [DecidableEq V] {I : Finset V} (K : Finset V) (σ : I → Bool) :
    ↥(I ∩ K) → Bool :=
  fun x => σ ⟨x.1, (Finset.mem_inter.1 x.2).1⟩

/-- **d-local distribution** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to
Unary Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §1.1, p.4): "A d-local
distribution for φ is a family of distributions D = {D_I}, one on {0, 1}^I for every I ⊆ [n] with
|I| ≤ d, such that (1) no assignment in the support of D_I falsifies a clause of φ whose variables
all lie in I; and (2) the distributions are consistent: for all I, J with |I|, |J| ≤ d, the
marginals of D_I and D_J on I ∩ J are equal."

`D I σ` is the probability of the partial assignment `σ : I → Bool` under `D_I`. The three clauses
are: each `D_I` with `|I| ≤ d` is a probability distribution (nonnegative, total mass 1); (1) the
clause condition; (2) for `|I|, |K| ≤ d`, the push-forwards of `D_I` and `D_K` to `I ∩ K` agree.

**Formalization Note** The values `D I` for `|I| > d` are unconstrained (the family is only
indexed by `|I| ≤ d` in the paper). An assignment `σ` on `I ⊇ vars(C)` falsifies `C` when every
literal `(v, b) ∈ C` has `σ v ≠ b`. -/
def IsLocalDist {V : Type*} [DecidableEq V] (φ : CNF V) (d : ℕ)
    (D : (I : Finset V) → (I → Bool) → ℝ) : Prop :=
  (∀ I : Finset V, I.card ≤ d → (∀ σ, 0 ≤ D I σ) ∧ ∑ σ, D I σ = 1) ∧
  (∀ I : Finset V, I.card ≤ d → ∀ σ : I → Bool, 0 < D I σ → ∀ C ∈ φ, clauseVars C ⊆ I →
      ¬ ∀ l ∈ C, ∀ h : l.1 ∈ I, σ ⟨l.1, h⟩ ≠ l.2) ∧
  (∀ I K : Finset V, I.card ≤ d → K.card ≤ d → ∀ τ : ↥(I ∩ K) → Bool,
      ∑ σ ∈ Finset.univ.filter (fun σ : I → Bool => restrictInter K σ = τ), D I σ =
        ∑ σ ∈ Finset.univ.filter
          (fun σ : K → Bool => (fun x : ↥(I ∩ K) => σ ⟨x.1, (Finset.mem_inter.1 x.2).2⟩) = τ),
          D K σ)

end LiftSAParity


