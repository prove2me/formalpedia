-- Prove2me | Definitions.Def_NashOrTriangle_FatLE
-- name    : NashOrTriangle_FatLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:47.169177+00:00
-- url     : https://prove2.me/theorems/3b142078-a5ff-4a15-9011-782009afd71b
-- title:
--   Fat-shattering bound $\mathrm{fat}(H,r)\le N$
-- statement:
--   For a game $H$, $\mathrm{fat}(H, r)$ is the larger of the fat-shattering dimensions, with separation $r$, of its two payoff classes: the rows viewed as functions on columns, and the columns viewed as functions on rows. At a shattered point with threshold $z$ a low label means payoff at most $z$ and a high label means payoff at least $z + r$. This predicate expresses
--   $$
--   \mathrm{fat}(H, r) \le N .
--   $$
--
--   **Formalization Note** It uses the published fat-shattering dimension `BartlettNN.Margin.fat` at scale $r/2$: Bartlett's condition $(h(x_i) - r_i)\,b_i \ge r/2$ with threshold $r_i$ is the paper's "low $\le z$, high $\ge z + r$" with $z = r_i - r/2$. The dimension takes values in $\mathbb N \cup \{\infty\}$.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Appendix C.2, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering

namespace NashOrTriangle

/-- `fat(H, r) ≤ N`: both payoff classes of the game — the rows viewed as functions on columns
and the columns viewed as functions on rows — have fat-shattering dimension at most `N` with
separation `r` ("at a shattered point with threshold z, a low label means payoff at most z and a
high label means payoff at least z + r").

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Appendix C.2, printed p. 25 (PDF p. 26).

**Formalization Note** Uses the published `BartlettNN.Margin.fat` (values in `ℕ∞`) at scale
`r / 2`: Bartlett's condition `(h(xᵢ) − rᵢ) bᵢ ≥ r/2` with threshold `rᵢ` is the paper's
"low ≤ z, high ≥ z + r" with `z = rᵢ − r/2`. "The larger of the two dimensions is `≤ N`" is
the conjunction of the two bounds. -/
def FatLE {A B : Type*} (M : A → B → ℚ) (r : ℝ) (N : ℕ) : Prop :=
  BartlettNN.Margin.fat (Set.range fun a : A => fun b : B => (M a b : ℝ)) (r / 2) ≤ (N : ℕ∞) ∧
  BartlettNN.Margin.fat (Set.range fun b : B => fun a : A => (M a b : ℝ)) (r / 2) ≤ (N : ℕ∞)

end NashOrTriangle


