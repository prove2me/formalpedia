-- Prove2me | Definitions.Def_Disjunctive_ConvexHull_LiftedPolyhedron
-- name    : Disjunctive_ConvexHull_LiftedPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:09:41.221991+00:00
-- url     : https://prove2.me/theorems/eba00bda-6302-4e07-81e1-3145c44cda5f
-- title:
--   The lifted polyhedron $(2.1)$/$(2.1)_Q$ and its projections
-- statement:
--   This definition introduces the higher-dimensional "lifted" polyhedron whose projection is the
--   subject of Theorem 2.1, together with its projection operation and its integer-restricted
--   variant used in Theorem 2.4.
--
--   For a set $S \subseteq \mathbb{R}^n \times \beta$ (for any auxiliary space $\beta$), the
--   **$x$-projection** is $\mathrm{Proj}_x(S) := \{x \in \mathbb{R}^n : \exists\, y \in \beta,\
--   (x,y) \in S\}$.
--
--   Given the data of the previous definition, and a subset $Q_{\mathrm{idx}} \subseteq Q$ (taken
--   to be $Q^*$ for the system labeled $(2.1)$, or all of $Q$ for the variant $(2.1)_Q$), the
--   **lifted polyhedron** is the set of tuples $\big(x, \{y^h\}_{h \in Q}, \{y^h_0\}_{h \in Q}\big)$
--   with
--
--   $$
--   x = \sum_{h \in Q} y^h, \qquad A_h y^h - b_h y^h_0 \ge 0,\ \ y^h_0 \ge 0 \quad (h \in
--   Q_{\mathrm{idx}}), \qquad \sum_{h \in Q} y^h_0 = 1,
--   $$
--
--   together with $y^h = 0$, $y^h_0 = 0$ for every $h \notin Q_{\mathrm{idx}}$. Finally, the
--   **integer-restricted** lifted set keeps only those tuples with every $y^h_0 \in \{0,1\}$.
--
--   **Formalization Note.** The book quantifies its lifted vectors "$(y^h, y^h_0) \in
--   \mathbb{R}^{n+1}$, $h \in Q^*$" — i.e. only over the feasible indices. This definition instead
--   ranges the vectors over *all* of $Q$ and forces the components outside $Q_{\mathrm{idx}}$ to
--   zero; since the constraints and the sums are unaffected by appending zero terms, this is an
--   equivalent, Finset/decidability-free encoding of the same object (documented in
--   `MODERATION_NOTES.md`). The same definition serves both the $(2.1)$ system (via
--   $Q_{\mathrm{idx}} = Q^*$) and the $(2.1)_Q$ variant (via $Q_{\mathrm{idx}} = Q$) that Theorem
--   2.3 compares.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 19-21, 23, Section 2.1

import Mathlib

namespace Disjunctive.ConvexHull

/-- The projection of a subset of `(Fin n → ℝ) × β` onto its `x`-component (Balas §2.1, p. 19,
`X(P) := {x ∈ ℝⁿ : ∃ vectors (y^h,y^h_0), h ∈ Q*, such that (x,{y^h,y^h_0}) ∈ P}`, and p. 20,
`Proj_x(S) := {x ∈ ℝⁿ : ∃ u ∈ ℝᵖ, (x,u) ∈ S}`). -/
def ProjX {n : ℕ} {β : Type*} (S : Set ((Fin n → ℝ) × β)) : Set (Fin n → ℝ) :=
  {x | ∃ y : β, (x, y) ∈ S}

/-- The lifted system `(2.1)` (Balas §2.1, p. 19, Theorem 2.1), or its variant `(2.1)_Q`
(p. 21) when `Qidx` is taken to be all of `Q` rather than `Q*`: the set of
`(x, {y^h}_{h}, {y^h_0}_{h})` with `x = Σ_h y^h`, `A_h y^h - b_h y^h_0 ≥ 0` and `y^h_0 ≥ 0` for
`h ∈ Qidx`, `y^h = 0` and `y^h_0 = 0` for `h ∉ Qidx` (the padding convention for "vectors indexed
by `Qidx`" — see the mission's `MODERATION_NOTES.md`), and `Σ_h y^h_0 = 1`. -/
def LiftedPolyhedron {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) (Qidx : Set Q) :
    Set ((Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) :=
  {p | p.1 = ∑ h, p.2.1 h ∧
        (∀ h ∈ Qidx, 0 ≤ (A h).mulVec (p.2.1 h) - p.2.2 h • (b h) ∧ 0 ≤ p.2.2 h) ∧
        (∀ h, h ∉ Qidx → p.2.1 h = 0 ∧ p.2.2 h = 0) ∧
        ∑ h, p.2.2 h = 1}

/-- The integer-restricted lifted set `P^I_Q` (Balas §2.1.2, p. 23, right before Theorem 2.4):
the points of a lifted polyhedron whose `y^h_0` components are all `0` or `1`. -/
def IntegerRestricted {n : ℕ} {Q : Type*}
    (S : Set ((Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ)))) :
    Set ((Fin n → ℝ) × ((Q → Fin n → ℝ) × (Q → ℝ))) :=
  {p ∈ S | ∀ h, p.2.2 h = 0 ∨ p.2.2 h = 1}

end Disjunctive.ConvexHull


