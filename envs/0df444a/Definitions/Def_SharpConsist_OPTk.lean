-- Prove2me | Definitions.Def_SharpConsist_OPTk
-- name    : SharpConsist_OPTk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:33.557724+00:00
-- url     : https://prove2.me/theorems/dcebe606-6e6a-4ca9-aca5-34b853debcab
-- title:
--   The available optimum $\mathrm{OPT}_k$
-- statement:
--   For a set function $f$ on a finite ground set $V$ and a capacity $k\in\mathbb N$, the **available optimum** is
--   $$\mathrm{OPT}_k=\max\{f(O): O\subseteq V,\ |O|\le k\}.$$
--   The family of feasible sets is nonempty (it contains $\emptyset$), so the maximum always exists. Applied after the final arrival, $V=X\cup\{r\}$ and $\mathrm{OPT}_k$ is the paper's $\mathrm{OPT}_k(X\cup\{r\})$.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §1.1, p.2

import Mathlib

namespace SharpConsist

/-- The **available optimum** `OPT_k = max {f(O) : |O| ≤ k}` over the whole (finite) ground set.
Fu–Zhang–Tao, arXiv:2609.09986 (held version, sha256 874ec76c…), §1.1, p.2
("Let OPTk(Xt) = max{f(O) : O ⊆ Xt, |O| ≤ k} denote the available optimum").

**Formalization Note.** The ground set is the type `α`, so `OPTk k f` is `OPT_k(X_t)` for `X_t = α`.
The maximum is a `Finset.sup'` over the subsets of size at most `k`, a nonempty family (it contains `∅`),
so no junk value arises. -/
noncomputable def OPTk {α : Type} [Fintype α] [DecidableEq α] (k : ℕ) (f : Finset α → ℝ) : ℝ :=
  (Finset.univ.filter (fun O : Finset α => O.card ≤ k)).sup' ⟨∅, by simp⟩ f

end SharpConsist


