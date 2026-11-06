-- Prove2me | Definitions.Def_FeedbackSwitching_CSet
-- name    : FeedbackSwitching_CSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:27.822702+00:00
-- url     : https://prove2.me/theorems/c160ba45-eb19-475f-9f08-c8b6ebea857e
-- title:
--   Comparison assignments $\mathcal C(v)$ (Definition 3) and optimal solutions of the LP (19)
-- statement:
--   Fix a tournament and a positive probability vector $v$ (the anchor). $\mathcal C(v)$ is the set of pairs $((Q_s)_{s\in[K]},\rho)$ of $K\times K$ matrices and a vector $\rho\in\mathbb R^K$ with
--   $$
--   Q_s\mathbf 1=0,\quad (Q_s)_{ir}\le0\ (i\ne r),\quad (Q_s)_{ir}=0\ \text{unless}\ i,r\in\overline N^+(s),\quad \sum_sQ_s=C_v,
--   $$
--   and, for all $s,i$, $(Q_s)_{ii}\le\rho_s$, $v_i(Q_s)_{ii}\le v_s\rho_i$, $v\le\rho\le1$ (Eqs. (16)–(17)). $\sum_s\rho_s$ is the **total source weight**. An **optimal assignment** minimizes the total source weight over $\mathcal C(v)$: the linear program (19). Also $v_{\min}=\min_iv_i$.
--
--   The support constraint makes each $Q_s\ell$ computable from the comparisons observed at $s$.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Definition 3, Eqs. (16)–(17), (19), pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_FeedbackSwitching_IsTournament
import Definitions.Def_FeedbackSwitching_centering
open Matrix

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

**Comparison assignment** `C(v)` (Definition 3, Eqs. (16)–(17), pp.19–20 = PDF pp.21–22), for
the tournament `A` and the anchor `v`: pairs `((Q_s)_{s∈[K]}, ρ)` of `K × K` matrices and a
vector `ρ ∈ ℝ^K` with
`Q_s 1 = 0`, `(Q_s)_{ir} ≤ 0 (i ≠ r)`, `(Q_s)_{ir} = 0 unless i, r ∈ N⁺(s)`, `∑_s Q_s = C_v`,
and, for all `s, i`, `(Q_s)_{ii} ≤ ρ_s`, `v_i (Q_s)_{ii} ≤ v_s ρ_i`, `v ≤ ρ ≤ 1`. -/
def CSet {K : ℕ} (A : Fin K → Fin K → Prop) (v : Fin K → ℝ) :
    Set ((Fin K → Matrix (Fin K) (Fin K) ℝ) × (Fin K → ℝ)) :=
  {z | (∀ s, z.1 s *ᵥ (fun _ => (1 : ℝ)) = 0) ∧
    (∀ s i r, i ≠ r → z.1 s i r ≤ 0) ∧
    (∀ s i r, z.1 s i r ≠ 0 → closedOut A s i ∧ closedOut A s r) ∧
    ∑ s, z.1 s = centering v ∧
    (∀ s i, z.1 s i i ≤ z.2 s) ∧
    (∀ s i, v i * z.1 s i i ≤ v s * z.2 i) ∧
    ∀ i, v i ≤ z.2 i ∧ z.2 i ≤ 1}

/-- An optimal solution of the linear program (19), p.20: minimize the total source weight
`∑_s ρ_s` over `C(v)`. -/
def IsOptimalAssignment {K : ℕ} (A : Fin K → Fin K → Prop) (v : Fin K → ℝ)
    (z : (Fin K → Matrix (Fin K) (Fin K) ℝ) × (Fin K → ℝ)) : Prop :=
  z ∈ CSet A v ∧ ∀ z' ∈ CSet A v, ∑ s, z.2 s ≤ ∑ s, z'.2 s

/-- `v_min = min_i v_i` (Lemma 6). `⨅` over the finite type `Fin K` is the minimum when `K ≥ 1`. -/
noncomputable def vmin {K : ℕ} (v : Fin K → ℝ) : ℝ :=
  ⨅ i, v i

end FeedbackSwitching


