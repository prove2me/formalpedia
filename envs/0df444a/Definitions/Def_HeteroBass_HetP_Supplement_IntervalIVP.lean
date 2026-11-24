-- Prove2me | Definitions.Def_HeteroBass_HetP_Supplement_IntervalIVP
-- name    : HeteroBass_HetP_Supplement_IntervalIVP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:28:12.58489+00:00
-- url     : https://prove2.me/theorems/eeeb7a8d-f2db-4fe4-9572-88c8bf3ca1f0
-- title:
--   (46) — finite interval coordinates, master-equation RHS and initial-value predicate
-- statement:
--   For each anchor $j$, retain the proper intervals $0\le m+n\le M-2$, and use a single shared coordinate $s_M$ for every full interval. Thus there are $M(M-1)/2$ proper coordinates for each anchor, together with the shared full coordinate. Let $u^j_{m,n}(t)$ and $u_M(t)$ denote their values. Write $L=Q_{j-m-1,j-m}$ and $R=Q_{j+n+1,j+n}$. For $M\ge3$, the **interval initial-value system** is
--
--   $$\begin{aligned}
--   (u^j_{m,n})'&=-\left(\sum_{i\in U^j_{m,n}}p_i+L+R\right)u^j_{m,n}
--    +L u^j_{m+1,n}+R u^j_{m,n+1},\\
--   u_M'&=-\left(\sum_i p_i\right)u_M,\qquad u_c(0)=1\quad\hbox{for every coordinate }c.
--   \end{aligned}$$
--
--   Every extension to length $M$ uses $u_M$. For $M=2$, the only proper intervals are singletons; set $R=0$ in this display so that the coincident peer edge is counted once, as required by p. 19 and the two-node equations (23). The missing superscript $j$ on the printed left-extension term of (46a) is restored, consistently with Appendix K. The predicate `SolvesCircleIVP` asserts precisely these equations and initial data for a proposed family $u$. The separate `circleObservation` is the family measured from the published process, not a chosen solution of the equations.
--
--   **Formalization Note** `CircleCoord M` is a finite option type: `none` is the all-node coordinate, while a proper coordinate stores its anchor and bounded pair $(m,n)$. All full intervals map to `none`. The coordinate accessor is used only at length at most $M$; its arbitrary extension beyond that range also returns `none`. Derivatives are taken within $[0,\infty)$, including the right derivative at zero. Uniqueness is asserted only on this time domain, without imposing any condition on a candidate family's negative-time values. Repeated eigenvalues are allowed.
-- source:
--   Fibich & Golan, Diffusion of new products with heterogeneous consumers, arXiv:2102.05926v3, Lemma 12, (46), pp. 18–19; Appendix K, p. 34; Appendix L, (82), pp. 34–35

import Mathlib
import Definitions.Def_HeteroBass_HetP_Supplement_Circle

namespace HeteroBass.HetP.Supplement

/-- Each anchor has all proper intervals; `none` is the single shared all-node coordinate. -/
abbrev CircleCoord (M : ℕ) :=
  Option (Fin M × {mn : Fin M × Fin M // mn.1.val + mn.2.val + 1 < M})

/-- Every full interval is the shared `none` coordinate; proper intervals retain their anchor. -/
def intervalCoord {M : ℕ} (j : Fin M) (m n : ℕ) : CircleCoord M :=
  if h : m + n + 1 < M then
    some (j, ⟨(⟨m, by omega⟩, ⟨n, by omega⟩), h⟩)
  else none

/-- Generator observations indexed by the finite interval coordinates. -/
noncomputable def circleObservation {M : ℕ} (p : Fin M → ℝ)
    (Q : Fin M → Fin M → ℝ) (t : ℝ) (c : CircleCoord M) : ℝ :=
  match c with
  | none => subsetNonadoption p Q Finset.univ t
  | some (j, mn) => intervalNonadoption p Q j mn.val.1.val mn.val.2.val t

/-- RHS of (46), restoring the left extension's anchor j.
At M=2 the coincident peer edge appears once, per the p.19 network convention. -/
noncomputable def circleRHS {M : ℕ} (p : Fin M → ℝ)
    (Q : Fin M → Fin M → ℝ) (x : CircleCoord M → ℝ) (c : CircleCoord M) : ℝ :=
  match c with
  | none => -(∑ i, p i) * x none
  | some (j, mn) =>
    let m := mn.val.1.val;
    let n := mn.val.2.val;
    let left := Q (cyclicShift j (-((m : ℤ) + 1))) (cyclicShift j (-(m : ℤ)));
    let right := if M = 2 then 0 else
      Q (cyclicShift j ((n : ℤ) + 1)) (cyclicShift j (n : ℤ));
    -( (∑ i ∈ intervalSet j m n, p i) + left + right) * x c
      + left * x (intervalCoord j (m + 1) n)
      + right * x (intervalCoord j m (n + 1))

/-- All equations and initial data of (46) on physical time t ≥ 0.
The derivative at time zero is taken within the nonnegative half-line. -/
def SolvesCircleIVP {M : ℕ} (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ)
    (u : ℝ → CircleCoord M → ℝ) : Prop :=
  (∀ c, u 0 c = 1) ∧
    ∀ t, 0 ≤ t → ∀ c,
      HasDerivWithinAt (fun s => u s c) (circleRHS p Q (u t) c) (Set.Ici 0) t

end HeteroBass.HetP.Supplement


