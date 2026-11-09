-- Prove2me | Definitions.Def_StochMatchPoly_edgeLaw
-- name    : StochMatchPoly_edgeLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:19:00.638582+00:00
-- url     : https://prove2.me/theorems/19bc5be5-fd89-4bae-9728-72dda2225bff
-- title:
--   The random subgraph with independent edges: probabilities and expectations
-- statement:
--   Let $E$ be a finite set of edges and let $q_e\in[0,1]$ be a survival probability for each $e\in E$. The **random subgraph** $G(\omega)$ keeps each edge $e\in E$ independently with probability $q_e$, so a realization $S\subseteq E$ has probability
--
--   $$\Pr[G(\omega)=S]=\prod_{e\in S}q_e\prod_{e\in E\setminus S}(1-q_e).$$
--
--   For a function $f$ of the realized edge set, $\mathbb E f(G(\omega))=\sum_{S\subseteq E}\Pr[G(\omega)=S]\,f(S)$. For $R$ independent realizations $S_1,\dots,S_R$ of the same random subgraph, the joint law is the product of $R$ copies. The model $G_p$ of the paper is the constant probability $q_e=p$.
--
--   This is the probability space of the whole mission: the goal's $\mathbb E\,\mu(G_p)$ and the independent samples of Algorithm 1, and in Lemma 3.1 a random subgraph whose edge probabilities need not be equal.
--
--   **Formalization Note** Only the values of $q$ on $E$ are used. At $p=1$ the law is the point mass at $E$. Expectations are finite weighted sums over subsets of $E$ (`expect`, `sampleExpect`); no measure theory is involved.
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), §1 p.1 (PDF p.2); Lemma 3.1, p.4 (PDF p.5); §4.1 p.9 (PDF p.10)

import Mathlib
import Definitions.Def_StochMatchPoly_mu

open Classical

namespace StochMatchPoly

/-! # The random subgraph with independent edges, and its expectations

S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), §1 p.1 ("let Gp be an (unknown) random subgraph of G retaining every edge
independently with probability p ∈ (0, 1]"), Lemma 3.1 p.4 ("a random subgraph of a finite graph
G = (V, E), with independent edge indicators; their probabilities need not be equal") and §4.1
p.9 ("A subscript p denotes independent edge survival with probability p").

**Formalization Note.** Every probability in these statements, except the vertex perturbations of
§3.2–3.3, lives on the finite set of subsets of the edge set `E`. Edge `e ∈ E` survives with
probability `q e`; the realization `S ⊆ E` has probability
`∏_{e ∈ E} (if e ∈ S then q e else 1 − q e)`, the product (independent) law. `Gp` is the constant
`q = fun _ => p`. Expectations are finite weighted sums over `E.powerset`. For `q` with values in
`[0, 1]` on `E` the weights are nonnegative and sum to `1` (checked in the mission's sanity file).
At `p = 1` the law is the point mass at `S = E`. Only the values of `q` on `E` matter. -/

variable {V : Type*}

/-- The probability of the realization `S ⊆ E` when every edge `e ∈ E` survives independently
with probability `q e`. -/
noncomputable def edgeWeight (q : Sym2 V → ℝ) (E S : Finset (Sym2 V)) : ℝ :=
  ∏ e ∈ E, if e ∈ S then q e else 1 - q e

/-- The expectation `E f(G(ω))` of a function of the realized edge set, under independent edge
survival with probabilities `q` on the edges of `E`. -/
noncomputable def expect (q : Sym2 V → ℝ) (E : Finset (Sym2 V)) (f : Finset (Sym2 V) → ℝ) : ℝ :=
  ∑ S ∈ E.powerset, edgeWeight q E S * f S

/-- The expectation of a function of `R` independent realizations `S 0, …, S (R − 1)` of the same
random subgraph (each `S i ⊆ E`, edges surviving independently with probabilities `q`). -/
noncomputable def sampleExpect (q : Sym2 V → ℝ) (E : Finset (Sym2 V)) (R : ℕ)
    (g : (Fin R → Finset (Sym2 V)) → ℝ) : ℝ :=
  ∑ S ∈ Fintype.piFinset (fun _ : Fin R => E.powerset), (∏ i, edgeWeight q E (S i)) * g S

end StochMatchPoly


