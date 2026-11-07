-- Prove2me | Definitions.Def_LipStableCA_emd
-- name    : LipStableCA_emd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:12.25098+00:00
-- url     : https://prove2.me/theorems/ccd88c9f-fbc9-4919-8829-ec5a50da69ee
-- title:
--   Allocation laws, couplings, the earth mover distance, expected welfare and marginals
-- statement:
--   A law is a probability mass function on the finite set $\mathcal A$. A coupling of laws $\mu,\nu$ is a nonnegative mass function on $\mathcal A\times\mathcal A$ with marginals $\mu$ and $\nu$. The earth mover distance is
--   $$\mathrm{EMD}(\mu,\nu)=\min_{\gamma\in\Gamma(\mu,\nu)}\mathbb E_{(S,T)\sim\gamma}\bigl[\|X(S)-X(T)\|_1\bigr].$$
--   The expected welfare of a law $\lambda$ at $v$ is $W_v(\lambda)=\mathbb E_{S\sim\lambda}[\sum_iv_i(S_i)]$, and its marginals are $\mathbb E_{S\sim\lambda}[X(S)]$.
--
--   **Formalization Note.** The minimum is written as an infimum of the set of costs. For laws this set is nonempty, bounded below and contains its infimum.
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Def. 2.5, p.8; Def. 2.2, p.7

import Definitions.Def_LipStableCA_Alloc

open ComplementFreeCA.CFRounding

namespace LipStableCA

variable {n m : ℕ}

/-- A distribution on allocations, `∆(A)` of §2, as a real mass function on the finite set `A`. -/
def IsLaw (P : Alloc n m → ℝ) : Prop :=
  (∀ T, 0 ≤ P T) ∧ ∑ T, P T = 1

/-- The set `Γ(µ, ν)` of couplings, Definition 2.5, p.8: nonnegative masses on pairs whose marginals
are `µ` and `ν`. -/
def IsCoupling (μ ν : Alloc n m → ℝ) (γ : Alloc n m × Alloc n m → ℝ) : Prop :=
  (∀ p, 0 ≤ γ p) ∧ (∀ S, ∑ T, γ (S, T) = μ S) ∧ (∀ T, ∑ S, γ (S, T) = ν T)

/-- The expected cost `E_{(S,T)∼γ} ‖X(S) − X(T)‖₁` of a coupling, Definition 2.5, p.8. -/
noncomputable def couplingCost (γ : Alloc n m × Alloc n m → ℝ) : ℝ :=
  ∑ p, γ p * l1Dist p.1 p.2

/-- The earth mover distance, Definition 2.5, p.8: `EMD(µ, ν) = min_{γ ∈ Γ(µ,ν)} E_γ ‖X(S) − X(T)‖₁`.
**Formalization Note.** Written as `sInf` of the set of costs. For laws `µ`, `ν` this set is nonempty
(the product coupling), bounded below by `0`, and contains its infimum (couplings form a compact
polytope), so `emd` is the book's `min`; the workspace sanity file proves this. On masses that are not
laws the set may be empty, and every statement below uses `emd` on laws only. -/
noncomputable def emd (μ ν : Alloc n m → ℝ) : ℝ :=
  sInf {c | ∃ γ, IsCoupling μ ν γ ∧ c = couplingCost γ}

/-- The expected welfare `W_v(λ) = E_{S∼λ}[W_v(S)]` of a law, Definition 2.9, p.9, and `SW(v)` of
Definition 2.2, p.7, for `λ = P_v`. -/
noncomputable def expectedWelfare (v : Profile n m) (P : Alloc n m → ℝ) : ℝ :=
  ∑ T, P T * welfare v T.1

/-- The allocation marginal `A_ij = E_{S∼µ}[X(S)ᵢⱼ]`, Definition 2.2, p.7, and Lemma 2.8(1), p.8. -/
noncomputable def marginal (P : Alloc n m → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  ∑ T, P T * incidence T i j

end LipStableCA


