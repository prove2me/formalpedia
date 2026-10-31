-- Prove2me | Definitions.Def_RobustToDynamics_specRadius
-- name    : RobustToDynamics_specRadius
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:16.979525+00:00
-- url     : https://prove2.me/theorems/1b6a79df-a654-4165-a63e-bd58f03c1801
-- title:
--   Spectral radius $\rho(G)$ of a real square matrix (complex spectrum)
-- statement:
--   For a real $n\times n$ matrix $G$, the **spectral radius** is
--   $$
--   \rho(G)=\max\{|\lambda_1|,\dots,|\lambda_n|\},
--   $$
--   where $\lambda_1,\dots,\lambda_n$ are the real or complex eigenvalues of $G$.
--
--   The hypotheses $\rho(G)<1$ and $\rho(G)\le\rho^*$ of Theorem 2.7 are stated with this quantity.
--
--   **Formalization Note** $\rho(G)$ is the supremum of $|z|$ over the spectrum of $G$ viewed as a complex matrix. Taking the spectrum over $\mathbb C$ matters: a rotation has no real eigenvalue. For $n\ge1$ the spectrum is finite and nonempty, so the supremum is the maximum; for $n=0$ the value is $0$.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, §2.1, p.10 (spectral radius)

import Mathlib

namespace RobustToDynamics

/-- **Spectral radius of a real square matrix.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, §2.1, p.10: "the spectral
radius ρ(G) of an n × n matrix G is given by ρ(G) = max{|λ1|, . . . , |λn|}, where λ1, . . . , λn
are the (real or complex) eigenvalues of G."

`specRadius G` is the supremum of `|λ|` over the **complex** spectrum of `G` (the eigenvalues of
the complexified matrix).

**Formalization Note.** The spectrum is taken over `ℂ` (`spectrum ℂ` of `G.map (algebraMap ℝ ℂ)`),
not over `ℝ`: a real spectrum misses the complex eigenvalues, e.g. of a rotation. For `n ≥ 1` the
complex spectrum is finite and nonempty, so the supremum is the paper's maximum. For `n = 0` the
spectrum is empty and the value is `0`. -/
noncomputable def specRadius {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup ((fun z : ℂ => ‖z‖) '' spectrum ℂ (G.map (algebraMap ℝ ℂ)))

end RobustToDynamics


