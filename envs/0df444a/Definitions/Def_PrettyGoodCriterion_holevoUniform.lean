-- Prove2me | Definitions.Def_PrettyGoodCriterion_holevoUniform
-- name    : PrettyGoodCriterion_holevoUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:16.371149+00:00
-- url     : https://prove2.me/theorems/2c723eb0-5909-4b0c-99c0-dc39e4e787a4
-- title:
--   Holevo information $\chi(\sigma_0,\sigma_1)$ of the uniform binary ensemble
-- statement:
--   For a density matrix $\varrho$ the **von Neumann entropy** is $S(\varrho):=-\operatorname{Tr}(\varrho\log_2\varrho)$, and the **Holevo information** of a finite ensemble $\mathcal E=\{(\pi_x,\sigma_x):x\in\mathcal X\}$ with average state $\bar\sigma=\sum_x\pi_x\sigma_x$ is
--   $$\chi(\mathcal E):=S(\bar\sigma)-\sum_{x\in\mathcal X}\pi_xS(\sigma_x).\qquad(13)$$
--   For two density matrices $\sigma_0,\sigma_1$ with the uniform prior,
--   $$\chi(\sigma_0,\sigma_1):=\chi\big(\{(\tfrac12,\sigma_0),(\tfrac12,\sigma_1)\}\big)=S\Big(\frac{\sigma_0+\sigma_1}{2}\Big)-\frac{S(\sigma_0)+S(\sigma_1)}{2}.$$
--
--   For a binary-input output-symmetric classical–quantum channel $b\mapsto\sigma_b$, $\chi(\sigma_0,\sigma_1)$ is the classical capacity of the channel (the paper's Proposition 6); it is the upper bound on code rates in the main theorem.
--
--   **Formalization Note** $\chi(\mathcal E)$ is the published `HolevoCQ.holevoChi` (states first, prior second), whose entropy `QAlgorithms.vnEntropy` is $-\operatorname{Re}\operatorname{Tr}(\varrho\log_2\varrho)$ computed by the continuous functional calculus with $0\log0=0$: the paper's base-2 entropy.
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Definition 2.1, p.14 (PDF 16) (entropy, base 2); Definition 2.5, equation (13), p.16 (PDF 18)

import Mathlib
import Definitions.Def_HolevoCQ_holevoChi

namespace PrettyGoodCriterion

/-- `χ(σ₀, σ₁) := χ({(1/2, σ₀), (1/2, σ₁)})`, the Holevo information of the uniform binary
ensemble, Alrabiah–Guruswami, *Binary code rate bounds via classical–quantum channels*,
arXiv:2608.09347 (held version), Definition 2.5, equation (13), p.16 (PDF 18). Explicitly
`χ(σ₀, σ₁) = S((σ₀ + σ₁)/2) − (S(σ₀) + S(σ₁))/2` with `S(ϱ) = −Tr(ϱ log₂ ϱ)` (Definition 2.1,
p.14, base 2).

**Formalization Note.** The Holevo information `χ(ℰ) = S(σ̄) − ∑ π_x S(σ_x)` is the published
`HolevoCQ.holevoChi`, whose entropy `QAlgorithms.vnEntropy` is `−Re Tr(ϱ log₂ ϱ)` computed by the
continuous functional calculus (`0 log 0 = 0`), the paper's base-2 convention. -/
noncomputable def holevoUniform {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Fin 2 → Matrix ι ι ℂ) : ℝ :=
  HolevoCQ.holevoChi σ (fun _ : Fin 2 => (1 / 2 : ℝ))

end PrettyGoodCriterion


