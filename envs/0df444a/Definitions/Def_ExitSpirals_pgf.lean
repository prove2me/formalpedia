-- Prove2me | Definitions.Def_ExitSpirals_pgf
-- name    : ExitSpirals_pgf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:18.790343+00:00
-- url     : https://prove2.me/theorems/2c80f92e-eaa3-4c1a-93c1-a92f6b9df211
-- title:
--   Generating function $H$ and the smallest root of $f=H(1-s+sf)$
-- statement:
--   For a sequence $q=(q_j)_{j\ge0}$ the **probability generating function** is $H(z)=\sum_j q_jz^j$. For $s\in[0,1]$ let
--   $$f(s)=\min\{u\in[0,1]:\ u=H(1-s+s\,u)\}.$$
--   When $q$ is the offspring law of a branching process, $1-s+su$ is the generating function argument after each child is kept independently with probability $s$, and $f(s)$ is the extinction probability (Lemma 4) of the exploration in the network thinned to a fraction $s$ of its nodes.
--
--   **Formalization Note** $f(s)$ is defined as the infimum of the solution set in $[0,1]$. For a probability sequence $q$ the set contains $1$ and is bounded below by $0$, and $H$ is continuous on $[0,1]$, so the infimum is attained.
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), Appendix A.4.3, p.50 (H(z), Lemma 4); Remark 1, p.52; proof of Proposition 4 and Lemma 8, p.53 (H(f, x) = H(1 − x + x f))

import Mathlib

namespace ExitSpirals

/-- **Probability generating function** `H(z) = Σ_j q_j z^j` of a sequence `q` on `ℕ`.
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Appendix A.4.3,
p.50 ("H(z) := Σ_k p⁺_k z^k"), Remark 1, p.52. -/
noncomputable def pgf (q : ℕ → ℝ) (z : ℝ) : ℝ := ∑' j : ℕ, q j * z ^ j

/-- **Extinction probability of the thinned branching process**: the smallest solution `f ∈ [0,1]`
of `f = H(f, s) = H(1 − s + s f)` (Lemma 8, p.53: "Let f(x) denote the smallest solution
f = H(f, x)", with `Ĥ(z, x) = H(1 − x + x z)` from the proof of Proposition 4, p.53).
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814.

**Formalization Note.** Defined as `sInf` of the solution set in `[0, 1]`. For a probability
sequence `q` and `s ∈ [0, 1]` the set contains `1` (since `H(1) = 1`) and is bounded below by `0`,
so the infimum is a genuine infimum; it is attained because `H` is continuous on `[0, 1]`. -/
noncomputable def smallestRoot (q : ℕ → ℝ) (s : ℝ) : ℝ :=
  sInf {u : ℝ | u ∈ Set.Icc (0 : ℝ) 1 ∧ u = pgf q (1 - s + s * u)}

end ExitSpirals


