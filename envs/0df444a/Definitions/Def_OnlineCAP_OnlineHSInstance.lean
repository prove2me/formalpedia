-- Prove2me | Definitions.Def_OnlineCAP_OnlineHSInstance
-- name    : OnlineCAP_OnlineHSInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:30.307646+00:00
-- url     : https://prove2.me/theorems/866021f0-e5ef-408a-bcb1-129b0c427d6f
-- title:
--   Instance of online weighted hitting set
-- statement:
--   An **instance of online (weighted) hitting set** consists of
--
--   1. a finite **ground set** $G\subseteq U$ of purchasable elements;
--   2. a **cost** $c(e)\in\mathbb R$ of each element;
--   3. a predicate saying which requests are **admissible** (the family $\mathcal F$ of Problem 2.4);
--   4. for every request $r$, the set $\mathrm{cov}(r)\subseteq U$ of elements that **hit** it.
--
--   A request list $(r_1,\dots,r_t)$ is **valid** if every $r_i$ is admissible and is hit by at least one element of $G$, so that a feasible solution exists (Problem 2.4 takes $\mathcal F$ to consist of non-empty sets).
--
--   Both the connectivity-augmentation problem (requests are cuts, elements are links) and the TL-rectangle hitting set problem (requests are planar shapes, elements are points) are instances.
--
--   **Formalization Note** Nonnegativity of costs is a hypothesis of each theorem.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Problem 2.4, p.9

import Mathlib

namespace OnlineCAP

/-- **An instance of online (weighted) hitting set.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Problem 2.4, p.9 (PDF p.9):
"Initially, we are given a set system (U, F) where U is a universe of N elements with non-negative
costs c : U → R≥0 and F is a family of non-empty subsets of U. A sequence of requests Rt ∈ F
arrive online."

An instance consists of a finite **ground set** `G` of elements that may be bought, a **cost**
`c e` of each element, a predicate `ok r` saying which requests may arrive, and for each request
`r` the set `cov r` of elements that hit it.

**Formalization Note.** Requests are kept abstract (`Req`) so that a request can be a cut of a
graph (connectivity augmentation, Problem 2.1) or a planar shape (Problem 1.9); the hitting
elements of a request `r` are `cov r ∩ G`. Nonnegativity of the costs is a hypothesis of each
theorem, not part of the structure. -/
structure OnlineHSInstance (U Req : Type) where
  /-- the ground set of purchasable elements -/
  G : Finset U
  /-- the cost of each element -/
  c : U → ℝ
  /-- the admissible requests -/
  ok : Req → Prop
  /-- the elements hitting a request -/
  cov : Req → Set U

/-- **Valid request list.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Problem 2.4, p.9 ("F is a family of non-empty subsets"): a
request list is valid if every request is admissible and is hit by at least one element of the
ground set, so that a feasible solution exists. -/
def OnlineHSInstance.Valid {U Req : Type} (I : OnlineHSInstance U Req) (s : List Req) : Prop :=
  ∀ r ∈ s, I.ok r ∧ ∃ e ∈ I.G, e ∈ I.cov r

end OnlineCAP


