-- Prove2me | Definitions.Def_TransvectionMixing_dS
-- name    : TransvectionMixing_dS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:20.856451+00:00
-- url     : https://prove2.me/theorems/98c974c0-20d0-4e7b-8ca6-6f436419f7ec
-- title:
--   Entry laws $\mathcal L_X(X_t|_{\mathcal S})$, $K_{\sigma,\mathcal S}(X,\cdot)$, $\pi_{\mathcal S}$ and the distances $d_{\mathcal S}(t)$, $d^\sigma_{\mathcal S}(X)$
-- statement:
--   Let $\mathbb F_q$ be a finite field, $X\in \mathrm{SL}_n(\mathbb F_q)$ an initial state and $\mathcal S\subseteq[n]\times[n]$ a set of observed entries.
--
--   1. For a skeleton $\sigma$ of length $t$, the **skeleton-conditional entry law** $K_{\sigma,\mathcal S}(X,\cdot)$ is the law of $X_t|_{\mathcal S}=(W(\sigma,a)X)|_{\mathcal S}$ for independent uniform coefficients $a\in\mathbb F_q^t$.
--   2. The **entry law** $\mathcal L_X(X_t|_{\mathcal S})$ averages $K_{\sigma,\mathcal S}(X,\cdot)$ over a uniform skeleton of length $t$ (each step an independent uniform pair of distinct rows).
--   3. The **stationary marginal** $\pi_{\mathcal S}=\pi|_{\mathcal S}$ is the law of $M|_{\mathcal S}$ for $M$ uniform on $\mathrm{SL}_n(\mathbb F_q)$; $\mathrm{Unif}(\mathbb F_q^{\mathcal S})$ is the product-uniform law.
--   4. The distances are
--   $$
--   d_{\mathcal S}(t)=\sup_{X\in\mathrm{SL}_n(\mathbb F_q)}\bigl\|\mathcal L_X(X_t|_{\mathcal S})-\pi_{\mathcal S}\bigr\|_{TV},\qquad
--   d^\sigma_{\mathcal S}(X)=\bigl\|K_{\sigma,\mathcal S}(X,\cdot)-\pi_{\mathcal S}\bigr\|_{TV},
--   $$
--   and $\Pr_{\sigma:|\sigma|=t}[d^\sigma_{\mathcal S}(X)>\varepsilon]$ is the probability over a uniform skeleton of length $t$.
--
--   The two guarantees of the main theorem are $d_{\mathcal S}(t)\le\varepsilon$ and $\sup_X\Pr_{\sigma:|\sigma|=t}[d^\sigma_{\mathcal S}(X)>\varepsilon]\le\varepsilon$.
--
--   **Formalization Note** Laws are normalized counts. Total variation is the published `MarkovMixing.tvDist`, $\max_A|\mu(A)-\nu(A)|$, which equals $\tfrac12\sum|\mu-\nu|$ on probability vectors. The supremum over $X$ ranges over the finite nonempty group $\mathrm{SL}_n(\mathbb F_q)$.
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), §1.1, eq. (1), pp.3–4 (d_S, K_σ, d^σ_S, π_S); eq. (3), p.4; §3.1, p.9 (Unif(𝔽_q^S))

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_TransvectionMixing_walkMat

namespace TransvectionMixing

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- The skeleton-conditional entry law `K_{σ,𝒮}(X, ·)`: the law of `X_t|_𝒮` for the walk
started at `X`, given the skeleton `σ`, with independent uniform coefficients
(Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices
over Large Fields*, manuscript sha256 217f833f…, §1.1, pp.3–4):
`K_{σ,𝒮}(X, y) = #{a ∈ 𝔽_q^t : (walk(σ,a)·X)|_𝒮 = y} / q^t`. -/
noncomputable def skelLaw {t : ℕ} (σ : Skel n t) (X : Matrix.SpecialLinearGroup (Fin n) F)
    (S : Finset (Fin n × Fin n)) : (↥S → F) → ℝ :=
  fun y => prob (fun a : Fin t → F => restrictEntries S (walkMat σ a * X.1) = y)

/-- The entry law `ℒ_X(X_t|_𝒮)` of the walk started at `X` after `t` steps, averaged over
uniform skeletons and coefficients (manuscript sha256 217f833f…, §1.1, eq. (1), p.3). -/
noncomputable def entryLaw (t : ℕ) (X : Matrix.SpecialLinearGroup (Fin n) F)
    (S : Finset (Fin n × Fin n)) : (↥S → F) → ℝ :=
  fun y => (∑ σ : Skel n t, skelLaw F σ X S y) / (Fintype.card (Skel n t) : ℝ)

/-- The stationary entry marginal `π_𝒮 = π|_𝒮`, the law of `M|_𝒮` for `M` uniform on
`SLₙ(𝔽_q)` (manuscript sha256 217f833f…, §1.1, p.3). It is not the product-uniform law on
`𝔽_q^𝒮`. -/
noncomputable def piS (S : Finset (Fin n × Fin n)) : (↥S → F) → ℝ :=
  fun y => prob (fun M : Matrix.SpecialLinearGroup (Fin n) F => restrictEntries S M.1 = y)

/-- The product-uniform law `Unif(𝔽_q^𝒮)` on the requested entries (manuscript sha256
217f833f…, §3.1, p.9 and proof of Theorem 1.1, p.31). -/
noncomputable def unifEntries (S : Finset (Fin n × Fin n)) : (↥S → F) → ℝ :=
  fun _ => 1 / (Fintype.card (↥S → F) : ℝ)

/-- `d_𝒮(t) = sup_{X ∈ SLₙ(𝔽_q)} ‖ℒ_X(X_t|_𝒮) − π_𝒮‖_TV` (manuscript sha256 217f833f…,
eq. (1), p.3), with the published total variation distance `MarkovMixing.tvDist`
(`max_A |μ(A) − ν(A)|`, which equals `½∑|μ − ν|` on probability vectors). -/
noncomputable def dS (S : Finset (Fin n × Fin n)) (t : ℕ) : ℝ :=
  ⨆ X : Matrix.SpecialLinearGroup (Fin n) F, MarkovMixing.tvDist (entryLaw F t X S) (piS F S)

/-- `d^σ_𝒮(X) = ‖K_{σ,𝒮}(X, ·) − π_𝒮‖_TV` (manuscript sha256 217f833f…, p.3). -/
noncomputable def dSigma {t : ℕ} (σ : Skel n t) (X : Matrix.SpecialLinearGroup (Fin n) F)
    (S : Finset (Fin n × Fin n)) : ℝ :=
  MarkovMixing.tvDist (skelLaw F σ X S) (piS F S)

/-- `Pr_{σ : |σ| = t}[d^σ_𝒮(X) > ε]` for a uniform skeleton of length `t` (manuscript sha256
217f833f…, eq. (3), p.4). The conditional guarantee of (3) is `sup_X skelBadProb ≤ ε`. -/
noncomputable def skelBadProb (S : Finset (Fin n × Fin n)) (t : ℕ)
    (X : Matrix.SpecialLinearGroup (Fin n) F) (ε : ℝ) : ℝ :=
  prob (fun σ : Skel n t => ε < dSigma F σ X S)

end TransvectionMixing


