-- Prove2me | Definitions.Def_KMPMixing_Supplement_parallelKMP
-- name    : KMPMixing_Supplement_parallelKMP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:52:46.004893+00:00
-- url     : https://prove2.me/theorems/19ff5096-129e-4ad1-8a13-6716717db18f
-- title:
--   The parallel KMP chain $M^{(t,d)}_{\mathrm{PKMP}}$ and the partition resampling chain $M^{(t,d)}$ with $\pi$
-- statement:
--   Let $d\ge2$ be even and $t\ge1$, and let $\Delta=\{R\in\mathbb N^d:\sum_jR_j=t\}$.
--
--   1. The **parallel KMP chain** on $\Delta$ samples a uniformly random perfect matching $\mathcal M$ of $[d]$ and, for every pair $\{i,j\}\in\mathcal M$ independently, resamples $(R_i,R_j)$ uniformly from $\{(x,y)\in\mathbb N^2:x+y=R_i+R_j\}$. Its transition matrix is
--   $$
--   M_{\mathrm{PKMP}}(r,r')=\mathbb E_{\mathcal M}\prod_{\{i,j\}\in\mathcal M}\frac{\mathbb 1[r'_i+r'_j=r_i+r_j]}{r_i+r_j+1}.
--   $$
--   2. $Y_{t,d}$ is the set of partitions of $t$ with at most $d$ parts. For $r\in\Delta$, $r\in\Xi_\lambda$ means that $r$ has type $\lambda$: sorting $r$ non-increasingly and deleting zeros gives $\lambda$.
--   3. The **partition resampling chain** on $Y_{t,d}$ pads $\lambda$ with zeros to $r_\lambda\in\Delta$, performs one parallel-KMP step and returns the type of the result:
--   $$
--   M(\lambda,\lambda')=\sum_{r'\in\Xi_{\lambda'}}M_{\mathrm{PKMP}}(r_\lambda,r').
--   $$
--   4. Its stationary distribution (Lemma 6.11) is
--   $$
--   \pi(\lambda)=\frac{|\Xi_{\lambda,d}|}{\binom{t+d-1}{d-1}}.
--   $$
--
--   These two chains carry the classical mixing bound behind the convergence of the parallel Kac twirl.
--
--   **Formalization Note** $\Delta$ is the base mission's `KMPMixing.State d t`. A partition $\lambda$ is encoded by its zero-padded vector $r_\lambda$, a non-increasing vector of $\Delta$ (`PartitionState d t`); this is a bijection with $Y_{t,d}$. "Type $\lambda$" is stated as "some rearrangement of the coordinates of $r$ equals $r_\lambda$". The binomial uses natural-number subtraction, which is the paper's value for $d\ge1$.
-- source:
--   Chen, Liu, Qin, Schulman, Song, Yao, Zhao, A Tale of Two Walks: From Kac to KMP and Back, arXiv:2609.38044 (sha256 6a9abdd4…), Definition 6.9, p.45 (PDF p.47); Lemma 6.11, p.48 (PDF p.50); Definition 6.13 and Lemma 6.14, p.50 (PDF p.52); partitions and Eq. (6), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_KMPMixing_kmpChain
import Definitions.Def_KMPMixing_Supplement_perfectMatching

namespace KMPMixing.Supplement

open MarkovMixing KMPMixing

/-- The transition matrix `M^{(t,d)}_PKMP` of the **parallel KMP chain** on
`Δ = {R ∈ ℕ^d : Σ_j R_j = t}` (arXiv:2609.38044, Definition 6.13, p.50 (PDF p.52)): sample a
uniformly random perfect matching `M` of `[d]`; for every pair `{i, j} ∈ M` independently,
resample `(R_i, R_j)` uniformly from `{(x, y) ∈ ℕ² : x + y = R_i + R_j}`. Hence
`M_PKMP(r, r') = E_M ∏_{{i,j} ∈ M} 𝟙[r'_i + r'_j = r_i + r_j] / (r_i + r_j + 1)`.

**Formalization Note** `Δ` is the base mission's `KMPMixing.State d t`. The matching is a
fixed-point-free involution `σ` (`PerfectMatching d`), averaged uniformly, and each pair is the
index `i` with `i < σ i`. Every coordinate lies in exactly one pair, so the product determines
the whole of `r'`. For odd `d` there is no perfect matching and the matrix is `0`; every
statement assumes `d` even. -/
noncomputable def pkmpChain (d t : ℕ) : Matrix (State d t) (State d t) ℝ :=
  fun r r' => ((Fintype.card (PerfectMatching d) : ℝ))⁻¹ *
    ∑ σ : PerfectMatching d, ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i),
      (if r'.1 i + r'.1 (σ.1 i) = r.1 i + r.1 (σ.1 i) then
        1 / (((r.1 i + r.1 (σ.1 i) : ℕ) : ℝ) + 1) else 0)

/-- The state space `Y_{t,d}` of the **partition resampling chain**: partitions of `t` with at
most `d` parts (arXiv:2609.38044, §2 "Partitions", p.13 (PDF p.15); Definition 6.9, p.45
(PDF p.47)).

**Formalization Note** A partition `λ = (λ₁ ≥ ⋯ ≥ λ_s > 0)` with `s ≤ d` is encoded by its
zero-padded vector `r_λ = (λ₁, …, λ_s, 0, …, 0) ∈ Δ`, i.e. a non-increasing vector of
`State d t`; this is a bijection onto `Y_{t,d}`, and `λ.1` is the vector `R` of step 1 of
Definition 6.9. -/
abbrev PartitionState (d t : ℕ) := {r : State d t // Antitone r.1}

/-- `r ∈ Ξ_λ`: the multiplicity vector `r ∈ Δ` has type `λ` (`r↓ = λ`), i.e. sorting `r`
non-increasingly and dropping zeros gives `λ` (arXiv:2609.38044, Eq. (6), p.13 (PDF p.15)).

**Formalization Note** Stated as: some rearrangement of the coordinates of `r` is the padded
vector of `λ`. -/
def HasType {d t : ℕ} (r : State d t) (lam : PartitionState d t) : Prop :=
  ∃ τ : Equiv.Perm (Fin d), r.1 ∘ τ = lam.1.1

open Classical in
/-- The transition matrix `M^{(t,d)}` of the **partition resampling chain** on `Y_{t,d}`
(arXiv:2609.38044, Definition 6.9, p.45 (PDF p.47)): pad `λ` with zeros to `R ∈ ℕ^d`, perform one
parallel-KMP step from `R` (uniform perfect matching, every pair resampled uniformly and
independently with its sum kept), and return the type `R'↓`. Hence
`M(λ, λ') = Σ_{r' ∈ Ξ_{λ'}} M_PKMP(r_λ, r')`.

**Formalization Note** The paper also writes `M` for other matrices; here it is this chain. -/
noncomputable def partitionChain (d t : ℕ) :
    Matrix (PartitionState d t) (PartitionState d t) ℝ :=
  fun lam₀ lam₁ => ∑ r' : State d t, if HasType r' lam₁ then pkmpChain d t lam₀.1 r' else 0

open Classical in
/-- The stationary distribution `π(λ) = |Ξ_{λ,d}| / C(t + d − 1, d − 1)` of the partition
resampling chain (arXiv:2609.38044, Lemma 6.11, p.48 (PDF p.50)), where
`Ξ_{λ,d} = {r ∈ Δ : r↓ = λ}`.

**Formalization Note** `t + d − 1` and `d − 1` are natural-number subtractions, the paper's
values for `d ≥ 1`; every statement assumes `d ≥ 2`. -/
noncomputable def partitionStationary (d t : ℕ) : PartitionState d t → ℝ :=
  fun lam₀ => ((Finset.univ.filter fun r : State d t => HasType r lam₀).card : ℝ) /
    ((t + d - 1).choose (d - 1) : ℝ)

end KMPMixing.Supplement


