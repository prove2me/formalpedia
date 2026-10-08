-- Prove2me | Definitions.Def_RegevLWE_SubsetSum_Basic
-- name    : RegevLWE_SubsetSum_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:58.352139+00:00
-- url     : https://prove2.me/theorems/b414025f-9a69-4966-ae33-e042849f5089
-- title:
--   Proof of Claim 5.3 and p. 34:14 — subset sums Σ b_i g_i, the distribution P_g, its statistical distance from uniform, and the average over g ∈ G^l
-- statement:
--   Let $G$ be a finite abelian group, written additively, let $l \ge 0$ be an integer, and let $g = (g_1, \dots, g_l) \in G^l$.
--
--   1. **Subset sums.** For $b = (b_1, \dots, b_l) \in \{0,1\}^l$, the sum of the subset of $g_1, \dots, g_l$ selected by $b$ is $\sum_i b_i g_i \in G$. The empty subset ($b = 0$) gives $0$.
--   2. **The distribution $P_g$** (proof of Claim 5.3, p. 34:36) of the sum of a uniformly random subset of $g_1, \dots, g_l$:
--   $$P_g(h) = \frac{1}{2^l}\,\bigl|\{\, b \in \{0,1\}^l \mid \textstyle\sum_i b_i g_i = h \,\}\bigr|, \qquad h \in G.$$
--   3. **Statistical distance from uniform.** The discrete form of the statistical distance of p. 34:14,
--   $$\Delta(g) = \sum_{h \in G} \Bigl| P_g(h) - \frac{1}{|G|} \Bigr|,$$
--   the distance between $P_g$ and the uniform distribution on $G$. There is no factor $\tfrac12$: the distance ranges in $[0,2]$.
--   4. **Average over a uniform $g$.** For a real function $F$ on $G^l$, $\mathrm{Exp}_g[F(g)] = |G|^{-l}\sum_{g \in G^l} F(g)$, the expectation over a uniform choice of $g_1, \dots, g_l \in G$ (all $|G|^l$ tuples, repetitions allowed).
--
--   These are the objects of Claim 5.3, a special case of the leftover hash lemma used in the security proof of Regev's public-key cryptosystem.
--
--   **Formalization Note** $\{0,1\}^l$ is encoded as `Fin l → Bool`, with $b_i = 1$ read as `b i = true`; `subsetSum g b` is $\sum_i b_i g_i$, `P g h` is $P_g(h)$, `statDistUniform g` is $\Delta(g)$ and `expectG F` is $\mathrm{Exp}_g[F(g)]$. All probabilities are exact finite averages, real-valued; no measure theory is involved.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:36, proof of Claim 5.3 (definition of P_g); p. 34:14 (statistical distance, discrete form)

import Mathlib

namespace RegevLWE.SubsetSum

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {l : ℕ}

/-- The subset sum `∑ᵢ bᵢ gᵢ` of `g = (g₁, …, g_l)` selected by `b ∈ {0,1}^l`, with `{0,1}`
encoded as `Bool` (`bᵢ = true` means `gᵢ` is in the subset). Regev, J. ACM 2009, p. 34:36,
proof of Claim 5.3. The empty subset (`b` constantly `false`) gives `0`. -/
def subsetSum (g : Fin l → G) (b : Fin l → Bool) : G :=
  ∑ i, if b i then g i else 0

/-- The distribution `P_g` of the sum of a uniformly random subset of `g₁, …, g_l`:
`P_g(h) = (1/2^l) · |{b ∈ {0,1}^l | ∑ᵢ bᵢ gᵢ = h}|` (p. 34:36, proof of Claim 5.3). -/
noncomputable def P (g : Fin l → G) (h : G) : ℝ :=
  ((univ.filter fun b : Fin l → Bool => subsetSum g b = h).card : ℝ) / 2 ^ l

/-- The statistical distance between `P_g` and the uniform distribution on `G`,
`∑_{h ∈ G} |P_g(h) − 1/|G||` — the discrete form of the statistical distance of p. 34:14, with
**no** factor `1/2` (range `[0, 2]`). -/
noncomputable def statDistUniform (g : Fin l → G) : ℝ :=
  ∑ h, |P g h - 1 / (Fintype.card G : ℝ)|

/-- The expectation `Exp_g[F(g)]` over a uniform choice of `g₁, …, g_l ∈ G`, that is, over all
`|G|^l` tuples `g : Fin l → G` (with repetition): `(1/|G|^l) ∑_g F(g)`. -/
noncomputable def expectG (F : (Fin l → G) → ℝ) : ℝ :=
  (∑ g, F g) / (Fintype.card G : ℝ) ^ l

end RegevLWE.SubsetSum


