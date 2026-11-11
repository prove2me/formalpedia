-- Prove2me | Definitions.Def_PetzMix_HasExtInfluence
-- name    : PetzMix_HasExtInfluence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:12:45.284198+00:00
-- url     : https://prove2.me/theorems/bf6294c0-69bf-459d-992d-c5a02c04a0cb
-- title:
--   Local oscillation $\delta_i$, Lipschitz constant $\|A\|_L$, exterior influence decay function and $a_\eta$
-- statement:
--   For an operator $A$ on the chain and a site $i$, the **oscillation** at $i$ is
--   $$
--   \delta_i(A)=2\inf_{K\in\mathcal A_{i^c}}\|A-K\|,
--   $$
--   the infimum over operators acting trivially on site $i$, with $\|\cdot\|$ the operator norm. The **Lipschitz constant** is $\|A\|_L=\max_{i\in\Lambda_n}\delta_i(A)$.
--
--   Fix a block length $\ell$. The block updates have **exterior influence decay function** $\eta:\mathbb N\to[0,\infty)$ if for every block $B\in\mathcal B_{n,\ell}$, every site $i\notin B$ and every observable $A=A^\dagger$,
--   $$
--   \delta_i\big(\Phi_B^\dagger(A)\big)\le\delta_i(A)+\eta\big(\operatorname{dist}(i,B)\big)\,\|A\|_L ,
--   $$
--   where $\Phi_B^\dagger$ is the Hilbert–Schmidt adjoint of the Petz update of $\sigma_\beta$. Finally
--   $$
--   a_\eta=2\sum_{r=1}^\infty\eta(r).
--   $$
--
--   These are the quantities through which the dynamical part of the argument (Section 3) is phrased.
--
--   **Formalization Note** The infimum defining $\delta_i$ is over a nonempty set bounded below, so the real infimum is exact; $\|A\|_L$ is a finite maximum. A real series that diverges has `tsum` equal to $0$, so every theorem using $a_\eta$ also assumes that $\sum_{r\ge1}\eta(r)$ converges. The adjoint is the public `QDSGibbs.heisAdj`.
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Definition 2.2, (22)–(23), p.13; Definition 3.1, (40)–(41), p.16

import Mathlib
import Definitions.Def_PetzMix_heatBathGen
import Definitions.Def_QDSGibbs_IsChannel

open scoped Matrix ComplexOrder

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- The **oscillation** of an operator at site `i` (Kim, arXiv:2610.01190 (held copy sha256
38ff48d0…), Definition 2.2, (22), p.13): `δ_i(A) = 2 inf_{K ∈ A_{i^c}} ‖A − K‖`, the infimum over
the operators acting trivially on site `i`, `‖·‖` the operator norm.

**Formalization Note** The infimum is a real `⨅` over the nonempty set `{K : SupportedOn (Λn ∖ {i}) K}`
(it contains `K = 0`) of values bounded below by `0`, so it is the true infimum. `δ_i` is defined for
every operator; the paper applies it to observables. -/
noncomputable def osc {n d : ℕ} (i : Fin n) (A : ChainOp n d) : ℝ :=
  2 * ⨅ K : {K : ChainOp n d // SupportedOn (Finset.univ.erase i) K}, opNorm (A - K.1)

/-- The **Lipschitz constant** `‖A‖_L = max_{i ∈ Λn} δ_i(A)` (arXiv:2610.01190, Definition 2.2,
(23), p.13).

**Formalization Note** A supremum of finitely many reals, i.e. the maximum for `n ≥ 1`. -/
noncomputable def lip {n d : ℕ} (A : ChainOp n d) : ℝ :=
  ⨆ i : Fin n, osc i A

/-- The block updates have **exterior influence decay function** `η` (arXiv:2610.01190,
Definition 3.1, (40), p.16): `η : ℕ → [0, ∞)` and, for every block `B ∈ B_{n,ℓ}`, every site
`i ∉ B` and every observable `A`,
`δ_i(Φ_B†(A)) ≤ δ_i(A) + η(dist(i, B)) ‖A‖_L`.

**Formalization Note** `B_{n,ℓ}` is `{cycBlock ℓ s : s : Fin n}` (the theorems assume `1 ≤ ℓ < n`,
p.16); `Φ_B` is the Petz update of `σ_β = gibbs β (Σ_j h j)`; the Heisenberg adjoint `Φ_B†` of (37)
is the public `QDSGibbs.heisAdj`. Observables are Hermitian operators (the paper's usage, "observable
A = A†", p.16). -/
def HasExtInfluence {n d : ℕ} (β : ℝ) (h : Fin n → ChainOp n d) (ℓ : ℕ) (η : ℕ → ℝ) : Prop :=
  (∀ r, 0 ≤ η r) ∧
  ∀ s : Fin n, ∀ i : Fin n, i ∉ cycBlock ℓ s → ∀ A : ChainOp n d, A.IsHermitian →
    osc i (heisAdj (petzUpdate (gibbs β (∑ j, h j)) (cycBlock ℓ s)) A) ≤
      osc i A + η (setDist i (cycBlock ℓ s)) * lip A

/-- The constant `a_η = 2 Σ_{r=1}^∞ η(r)` of a decay function (arXiv:2610.01190, Definition 3.1,
(41), p.16).

**Formalization Note** A real `tsum` is `0` for a non-summable sequence, so every statement that uses
`aEta η` also assumes `Summable (fun r => η (r + 1))` (the paper's "summable", `a_η < ∞`). The
term `η 0` is not included. -/
noncomputable def aEta (η : ℕ → ℝ) : ℝ :=
  2 * ∑' r : ℕ, η (r + 1)

end PetzMix


