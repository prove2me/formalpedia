-- Prove2me | Definitions.Def_SharpConsist_Supplement_optAt
-- name    : SharpConsist_Supplement_optAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:20:36.304778+00:00
-- url     : https://prove2.me/theorems/fb14c029-6019-4e79-8de7-067b2522bd01
-- title:
--   The available optimum $\mathrm{OPT}_k(X_t)$ at time $t$
-- statement:
--   For a set function $F$ on finite sets of arrival indices, a capacity $k$ and a time $t$, the **available optimum** is
--   $$\mathrm{OPT}_k(X_t)=\max\{F(O): O\subseteq X_t,\ |O|\le k\},\qquad X_t=\{0,\dots,t-1\}.$$
--   With $F$ the objective $f$ this is the paper's $\mathrm{OPT}_k(X_t)$; with $F=u$ another set function it is $\mathrm{OPT}_k(u,X_t)$ (p.25).
--
--   **Formalization Note** The maximum is the published `SharpConsist.OPTk` over subsets of `Fin t`, mapped into $\mathbb N$; the feasible family contains $\emptyset$, so the maximum always exists.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §1.1, p.2; §8, p.25

import Mathlib
import Definitions.Def_SharpConsist_OPTk

namespace SharpConsist.Supplement

/-- **The available optimum at time `t`**, `OPT_k(X_t) = max {F(O) : O ⊆ X_t, |O| ≤ k}`.
Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §1.1, p.2 ("Let OPTk(Xt) = max{f(O) : O ⊆ Xt, |O| ≤ k} denote the available
optimum"); `OPT_k(u, Z)` on p.25.

**Formalization Note.** `X_t = {0, …, t − 1}` (arrival indices, see `natFn`). The maximum is the
published `SharpConsist.OPTk` on the finite type `Fin t`, applied to `F` read on the images of
subsets of `Fin t` in `ℕ`; the feasible family contains `∅`, so no junk value arises. -/
noncomputable def optAt (k : ℕ) (F : Finset ℕ → ℝ) (t : ℕ) : ℝ :=
  SharpConsist.OPTk k (fun S : Finset (Fin t) => F (S.map Fin.valEmbedding))

end SharpConsist.Supplement


