-- Prove2me | Definitions.Def_SelectiveDPT_rate
-- name    : SelectiveDPT_rate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:43.253537+00:00
-- url     : https://prove2.me/theorems/dd6de1d2-36ac-4bfe-9e86-84d09080fb28
-- title:
--   Per-query progress rate $c(\Gamma)$
-- statement:
--   For a positive-definite $|D|\times|D|$ matrix $\Gamma$ on a domain $D \subseteq X^\iota$, the **progress rate** is
--   $$c(\Gamma) = \max_{i \in \iota,\ p \in \mathbb Z_d} \big\|O_{i,p}^\dagger\,\Gamma^{1/2}\,O_{i,p}\,\Gamma^{-1/2}\big\|^2 ,$$
--   with $\|\cdot\|$ the spectral norm. It bounds the factor by which the progress measure $\mathrm{Tr}[\Gamma\rho_I]$ can grow in one query, and it is the base of the logarithm in the multiplicative adversary bound.
--
--   **Formalization Note** The maximum is over the finite set of pairs $(i,p)$ and is $0$ for an empty index set. The equality with $\max_{i,p,\rho}\mathrm{Tr}[\Gamma O_{i,p}^\dagger\rho O_{i,p}]/\mathrm{Tr}[\Gamma\rho]$ is Remark 2.13.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Propositions 2.12 and 2.14, pp.16–17 (c)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_SelectiveDPT_oracleOn
import Definitions.Def_SelectiveDPT_matSqrt

namespace SelectiveDPT

open QAlgorithms

/-- The per-query progress rate of a multiplicative adversary matrix `Γ`
(arXiv:2609.26678, Propositions 2.12 and 2.14, pp.16–17):
`c(Γ) = max_{i,p} ‖O_{i,p}† Γ^{1/2} O_{i,p} Γ^{−1/2}‖²`, the maximum over query indices `i` and
phases `p ∈ Z_d`, with `‖·‖` the spectral norm.

**Formalization Note.** The maximum is a real `⨆` over the finite type `ι × Z_d`; for an empty
index type it is `0`. The equality with the paper's other expression
`max_{i,p,ρ} Tr[Γ O_{i,p}† ρ O_{i,p}] / Tr[Γ ρ]` is Remark 2.13 (a theorem, not a definition). -/
noncomputable def rate {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} [NeZero d]
    (D : Finset (ι → ZMod d)) (Γ : Matrix D D ℂ) : ℝ :=
  ⨆ q : ι × ZMod d,
    specNorm ((oracleOn D q.1 q.2).conjTranspose * matSqrt Γ * oracleOn D q.1 q.2 *
      matInvSqrt Γ) ^ 2

end SelectiveDPT


