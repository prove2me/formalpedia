-- Prove2me | Definitions.Def_TermCycDich_bidim
-- name    : TermCycDich_bidim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:08.714202+00:00
-- url     : https://prove2.me/theorems/e6a16639-3f1e-4c05-97f8-e044111c3b30
-- title:
--   Bidimensionality $\mathrm{bidim}(G,R)$
-- statement:
--   The **bidimensionality** $\mathrm{bidim}(G,R)$ of an annotated graph is the largest integer $k$ such that $(G,R)$ contains the all-red $(k\times k)$-grid $(\Gamma_k, V(\Gamma_k))$ as a red-minor; if $R=\emptyset$ it is $0$.
--
--   Red-minor-closed classes excluding an annotated planar graph are exactly those of bounded bidimensionality; Theorems 1.2, 1.3 and 8.1 are parameterized by it.
--
--   **Formalization Note** The maximum is taken over $k \le |G|$ (`Nat.findGreatest`). This is the paper's maximum: a red model of $\Gamma_k$ has $k^2$ disjoint nonempty branch sets, so $k \le k^2 \le |G|$. For $R=\emptyset$ no $k \ge 1$ qualifies, giving $0$.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 2.1, p.16 (PDF 18)

import Mathlib
import Definitions.Def_TermCycDich_HasRedGrid

namespace TermCycDich

open Classical in
/-- The **bidimensionality** `bidim(G, R)`: the largest `k` such that `(G, R)` contains the
all-red `(k × k)`-grid as a red-minor; `0` if `R = ∅`.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 2.1, p.16 (PDF 18): "The bidimensionality of an annotated graph (G, R), denoted
by bidim(G, R), is the largest integer k such that there exists (Γ_k, V(Γ_k)) as a red-minor in
(G, R) where Γ_k denotes the (k × k)-grid. If R = ∅, then we set bidim(G, R) = 0."

**Formalization Note** `Nat.findGreatest` over `k ≤ |G|`. This is the paper's maximum: a red
model of `Γ_k` has `k²` pairwise disjoint nonempty branch sets, so `k ≤ k² ≤ |G|`, and `k = 0`
always qualifies. For `R = ∅` no `k ≥ 1` qualifies (branch sets need a red vertex), giving `0` as
the paper sets. Decidability is classical. -/
noncomputable def bidim {V : Type} [Fintype V] (G : SimpleGraph V) (R : Set V) : ℕ :=
  Nat.findGreatest (fun k => HasRedGrid G R k) (Fintype.card V)

end TermCycDich


