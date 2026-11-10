-- Prove2me | Definitions.Def_BilatMatch_massLagrangian
-- name    : BilatMatch_massLagrangian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:20.477572+00:00
-- url     : https://prove2.me/theorems/c471f74e-fa88-4eaa-a520-4c6777025dc8
-- title:
--   Trade-mass polytope $P(q)$ and typewise Lagrangian $L_{\alpha,\ell}$
-- statement:
--   Fix buyer values $v_1<\dots<v_n$. A finitely supported buyer prior on them is $\sum_\ell w_\ell\delta_{v_\ell}$. For $q\in[0,1]$,
--   $$P(q)=\{\mu\in[0,q]^n:\ \mu_1\le\dots\le\mu_n\},$$
--   and for a seller-side cost function $C_\alpha$,
--   $$L_{\alpha,\ell}(\mu)=(1+\alpha)v_\ell\mu_\ell-C_\alpha(\mu_\ell)-\alpha\sum_{t<\ell}(v_{t+1}-v_t)\mu_t .$$
--
--   **Formalization Note** Indices start at $0$.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), §3.2, p.11 (pdf p.13)

import Mathlib

open MeasureTheory

namespace BilatMatch

/-!
# Trade-mass vectors and the typewise Lagrangian in mass coordinates

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), §3.2, p.11 (pdf p.13).

**Formalization Note** A finitely supported buyer prior is given by strictly increasing values
`v : Fin n → ℝ` (the paper's `v_1 < ⋯ < v_n`, indices shifted to start at `0`) and positive
probabilities `w : Fin n → ℝ`; `finiteLaw v w = ∑_ℓ w_ℓ δ_{v_ℓ}`.
-/

/-- The finitely supported prior `∑_ℓ w_ℓ δ_{v_ℓ}`. -/
noncomputable def finiteLaw {n : ℕ} (v : Fin n → ℝ) (w : Fin n → ℝ) : Measure ℝ :=
  ∑ ℓ, ENNReal.ofReal (w ℓ) • Measure.dirac (v ℓ)

/-- `P(q) = {µ ∈ [0, q]^n : µ_1 ≤ ⋯ ≤ µ_n}` (p.11). -/
def massPolytope (n : ℕ) (q : ℝ) : Set (Fin n → ℝ) :=
  {m | (∀ ℓ, 0 ≤ m ℓ ∧ m ℓ ≤ q) ∧ Monotone m}

/-- `v_{t+1}` for `t < n − 1` (and `v_t` at the last index, where it is never used below). -/
def nextVal {n : ℕ} (v : Fin n → ℝ) (t : Fin n) : ℝ :=
  if h : t.val + 1 < n then v ⟨t.val + 1, h⟩ else v t

/-- `L_{α,ℓ}(µ) = (1+α) v_ℓ µ_ℓ − C_α(µ_ℓ) − α ∑_{t<ℓ} (v_{t+1} − v_t) µ_t` (p.11), with the
seller-side cost `C = C_α`. -/
noncomputable def massLagrangian (α : ℝ) {n : ℕ} (v : Fin n → ℝ) (C : ℝ → ℝ) (m : Fin n → ℝ)
    (ℓ : Fin n) : ℝ :=
  (1 + α) * v ℓ * m ℓ - C (m ℓ) - α * ∑ t ∈ Finset.univ.filter (· < ℓ), (nextVal v t - v t) * m t

end BilatMatch


