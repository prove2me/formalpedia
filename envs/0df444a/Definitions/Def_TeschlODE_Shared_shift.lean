-- Prove2me | Definitions.Def_TeschlODE_Shared_shift
-- name    : TeschlODE_Shared_shift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:11:55.139932+00:00
-- url     : https://prove2.me/theorems/aad9cd6e-301f-429e-b9e3-59df0b2fa5a5
-- title:
--   The shift map $\sigma$ on $\Sigma_N$ (11.29)
-- statement:
--   Let $\Sigma_N = \{0, 1, \dots, N-1\}^{\mathbb{N}_0}$ be the space of one-sided sequences in $N$ symbols (11.27). The **shift map** is
--   $$\sigma : \Sigma_N \to \Sigma_N, \qquad (x_0, x_1, x_2, \dots) \mapsto (x_1, x_2, \dots).$$
--
--   This one definition serves chunk 09-interval-maps (Theorem 11.5, p. 301; Lemmas 11.8 and 11.9, p. 303) and chunk 11-horseshoe (Theorem 11.5, p. 301; Lemmas 11.8 and 11.9, p. 303).
--
--   **Formalization Note.** A sequence is a function $\mathbb{N} \to \mathrm{Fin}\,N$ and $\sigma(x)_n = x_{n+1}$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 300, §11.4, and p. 303, §11.5, Eq. (11.29)

import Mathlib

namespace TeschlODE.Shared

/-- Teschl, §11.4, p. 300 and §11.5, p. 303, (11.29): the shift map on the sequence space
`Σ_N = {0, …, N − 1}^{ℕ₀}` (11.27), `σ(x₀, x₁, …) = (x₁, x₂, …)`. Sequences are functions
`ℕ → Fin N`, indexed from `0`. -/
def shift {N : ℕ} (x : ℕ → Fin N) : ℕ → Fin N :=
  fun n => x (n + 1)

end TeschlODE.Shared


