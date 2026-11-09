-- Prove2me | Definitions.Def_RandomQueryXOR_uniformOn
-- name    : RandomQueryXOR_uniformOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:54:05.348776+00:00
-- url     : https://prove2.me/theorems/850c5833-8332-46c1-b27b-c7c05a629afa
-- title:
--   Uniform distributions on finite subsets and products of independent distributions
-- statement:
--   For a nonempty finite set $\alpha$, the **uniform distribution** gives every element probability $1/|\alpha|$ (the published `ShallowShadows.ShadowNorm.uniformDist`). For a nonempty subset $s\subseteq\alpha$, the uniform distribution on $s$ gives probability $1/|s|$ to each element of $s$ and $0$ elsewhere. For distributions $p_1,\dots,p_k$ on a finite set $Q$, the **product distribution** on $Q^k$ is
--   $$
--   (p_1\otimes\dots\otimes p_k)(q_1,\dots,q_k)=\prod_{a=1}^{k} p_a(q_a),
--   $$
--   the law of a vector with independent coordinates $q_a\sim p_a$.
--
--   These are the uniform random choices of the paper: the indices of the random query model, the gate-keeper bits, the inputs $\alpha,\beta,\rho_a,\theta_a$ of the two-bit parity game, the special index $h$ and the public coins of the embedding protocols, and the independent private randomness of the players.
--
--   **Formalization Note** Distributions are the published `WildeQIT.FinDist` (finite alphabets, as in the paper's Appendix A).
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, §3.1, p.13 (PDF p.15); §4.1, p.15 (PDF p.17); Definition 4.5, p.18 (PDF p.20); protocol π_L, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_WildeQIT_FinDist

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT

/-- The uniform distribution on a nonempty finite subset `s ⊆ α`: probability `1/|s|` on `s`
and `0` off `s` (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query
Model*, arXiv:2611.04353: the special index `h` of protocol π_L, p.19 = PDF p.21, is uniform on
the sensitive zeros of `x⋆_f`).

**Formalization Note** Distributions are the published finite-alphabet distributions
`WildeQIT.FinDist` (the paper's Appendix A works on finite sets, Definition A.2, p.58). The
uniform distribution on a whole finite type is the published
`ShallowShadows.ShadowNorm.uniformDist`. -/
noncomputable def uniformOn {α : Type} [Fintype α] [DecidableEq α] (s : Finset α)
    (hs : s.Nonempty) : FinDist α where
  prob a := if a ∈ s then (s.card : ℝ)⁻¹ else 0
  nonneg a := by split_ifs <;> positivity
  sum_eq_one := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hs.card_pos.ne')

/-- The product of `k` independent distributions `p 0, …, p (k-1)` on the same finite set `Q`:
the law of a vector `(q_0, …, q_{k-1})` with independent coordinates `q_a ∼ p a` (the private
randomness of the `k` players of the two-bit parity game, arXiv:2611.04353, p.18 = PDF p.20). -/
noncomputable def piDist {k : ℕ} {Q : Type} [Fintype Q] (p : Fin k → FinDist Q) :
    FinDist (Fin k → Q) where
  prob q := ∏ a, (p a).prob (q a)
  nonneg q := Finset.prod_nonneg fun a _ => (p a).nonneg (q a)
  sum_eq_one := by
    rw [← Fintype.prod_sum (fun a x => (p a).prob x)]
    exact Finset.prod_eq_one fun a _ => (p a).sum_eq_one

end RandomQueryXOR


