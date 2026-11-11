-- Prove2me | Definitions.Def_PelagicFF_minEntropyDeficiency
-- name    : PelagicFF_minEntropyDeficiency
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:43.761042+00:00
-- url     : https://prove2.me/theorems/32d17612-b351-49ed-b1d3-ed4832e17e11
-- title:
--   Entropy in bits and the min-entropy deficiency $D_\infty(X)$
-- statement:
--   For a random variable $X$ on a finite set with mass function $p_X$, its **entropy** (in bits) is
--   $$H(X)=\sum_x p_X(x)\log_2\frac1{p_X(x)}.$$
--
--   For a $\{-1,1\}^s$-valued random variable $X$, its **min-entropy deficiency** is
--   $$D_\infty(X)=\log_2\Big(2^s\max_{x\in\{-1,1\}^s}\Pr[X=x]\Big)=s-H_\infty(X).$$
--
--   $D_\infty$ measures how far $X$ is from uniform; the lower bound of Theorem 4.2 tracks it along transcripts.
--
--   **Formalization Note** $\{-1,1\}^s$ is `ι → Bool` for a finite coordinate type `ι` with $s=|\iota|$ (bit $b$ stands for `sign b`). $H$ is the published `FuchsVdGraaf.entropy` (base 2, $0\log0=0$) of the law.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §2.3, pp.15–16, Definition 2.2

import Mathlib
import Definitions.Def_FuchsVdGraaf_entropy

namespace PelagicFF

/-- The Shannon entropy in bits `H(X) = ∑ₓ p_X(x) log₂(1/p_X(x))` of a law on a finite type
(arXiv:2610.05585, held version, sha256 4564aef3…, §2.3, p.15), via the published
`FuchsVdGraaf.entropy` (base 2, `0 log 0 = 0`). -/
noncomputable def lawEntropy {α : Type} [Fintype α] (μ : PMF α) : ℝ :=
  FuchsVdGraaf.entropy (fun a => (μ a).toReal)

/-- **Definition 2.2 (Min-entropy deficiency).** For a `{−1,1}^s`-valued random variable `X` with
law `μ`, `D∞(X) = log₂(2^s · maxₓ Pr[X = x]) = s − H∞(X)`.

arXiv:2610.05585 (held version, sha256 4564aef3…), Definition 2.2, p.16.

**Formalization Note.** `{−1,1}^s` is `ι → Bool` for a finite coordinate type `ι` with
`s = card ι` (bit `b` stands for `sign b`); the coordinates may be `Fin s` or, for truth tables,
`{0,1}ⁿ = Fin n → Bool`. The maximum is a `Finset.sup'` over the nonempty finite type. -/
noncomputable def minEntropyDeficiency {ι : Type} [Fintype ι] [DecidableEq ι] (μ : PMF (ι → Bool)) : ℝ :=
  Real.logb 2 (2 ^ Fintype.card ι * Finset.univ.sup' Finset.univ_nonempty (fun x => (μ x).toReal))

end PelagicFF


