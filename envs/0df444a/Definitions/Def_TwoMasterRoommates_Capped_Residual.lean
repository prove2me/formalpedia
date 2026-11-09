-- Prove2me | Definitions.Def_TwoMasterRoommates_Capped_Residual
-- name    : TwoMasterRoommates_Capped_Residual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:46:35.432106+00:00
-- url     : https://prove2.me/theorems/d9b65281-3605-4f86-8822-59f80ca3638c
-- title:
--   Positive intervals, residual deadlines, and integer Hall corrections
-- statement:
--   For a mandatory kernel, an active $u$ is bad when $r(u)<r(Mu)$. Its oriented positive edge $(u,v)$ has half-open interval $[r(u),r(v))$. A permitted positive edge passes its endpoint type and cap tests. Equal-rank active edges are represented once, in identity order.
--
--   Families $F,L$ are admissible when positive intervals and all chosen endpoints are disjoint, equal-rank edges lie outside strict positive interiors and pass their caps, and all remaining actives are marked. The residual token population removes token endpoints of $F$; the residual active population removes endpoints of $F\cup L$. Write
--
--   $$d_0(w)=\min\{c(w),r(w)\},\qquad d_F(w)=\begin{cases}\min\{c(w),\alpha\},&\alpha<r(w)<\beta\text{ for }[\alpha,\beta)\in F,\\d_0(w),&\text{otherwise}.\end{cases}$$
--
--   The definition uses finite minima, with empty minimum $+\infty$, so it has a value for every family; the disjointness hypothesis makes the relevant interval unique. Residual assignment means a bijection from the remaining tokens to remaining actives respecting these deadlines.
--
--   The integer correction $\Delta_e(t)$ is exactly equation (4), with $\epsilon_e=1$ for an active partner and zero for a token partner. For that formula alone $d_0(s)=r(s)$ on tokens. These objects state the exact residual criterion and locality identities without assuming their conclusions.
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), pp. 9–10 (PDF pp. 10–11), §§A.1–A.2, equations (3)–(5)

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Kernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

noncomputable def endpoints {ι : Type} [DecidableEq ι] (F : Finset (ι × ι)) : Finset ι :=
  F.biUnion fun e => {e.1, e.2}

def PositiveEdge {ι R : Type} [LinearOrder R] (K : Kernel ι R) (e : ι × ι) : Prop :=
  K.kind e.1 = .active ∧ K.r e.1 < K.r e.2 ∧
  (K.r e.2 : WithTop R) ≤ K.c e.1 ∧
  ((K.kind e.2 = .active ∧ (K.r e.1 : WithTop R) ≤ K.c e.2) ∨
    (K.kind e.2 = .token ∧ K.marked e.1 = true))

def Bad {ι R : Type} [LinearOrder R] (K : Kernel ι R) (M : ι → ι) (u : ι) : Prop :=
  K.kind u = .active ∧ K.r u < K.r (M u)

noncomputable def positiveEdges {ι R : Type} [Fintype ι] [DecidableEq ι] [LinearOrder R]
    (K : Kernel ι R) (M : ι → ι) : Finset (ι × ι) := by
  classical
  exact (Finset.univ.filter fun u => Bad K M u).image fun u => (u, M u)

noncomputable def equalEdges {ι R : Type} [Fintype ι] [LinearOrder ι] [LinearOrder R]
    (K : Kernel ι R) (M : ι → ι) : Finset (ι × ι) := by
  classical
  exact (Finset.univ.filter fun u => K.kind u = .active ∧ K.kind (M u) = .active ∧
    u < M u ∧ K.r u = K.r (M u)).image fun u => (u, M u)

noncomputable def d0 {ι R : Type} [LinearOrder R] (K : Kernel ι R) (w : ι) : WithTop R :=
  if K.kind w = .active then min (K.c w) (K.r w) else (K.r w : WithTop R)

noncomputable def dF {ι R : Type} [DecidableEq ι] [LinearOrder R]
    (K : Kernel ι R) (F : Finset (ι × ι)) (w : ι) : WithTop R := by
  classical
  exact min (d0 K w) (F.inf fun e =>
    if K.r e.1 < K.r w ∧ K.r w < K.r e.2 then (K.r e.1 : WithTop R) else ⊤)

noncomputable def residualActives {ι R : Type} [Fintype ι] [DecidableEq ι] [LinearOrder R]
    (K : Kernel ι R) (F L : Finset (ι × ι)) : Finset ι := by
  classical
  exact (Finset.univ.filter fun v => K.kind v = .active) \ endpoints (F ∪ L)

noncomputable def residualTokens {ι R : Type} [Fintype ι] [DecidableEq ι] [LinearOrder R]
    (K : Kernel ι R) (F : Finset (ι × ι)) : Finset ι := by
  classical
  exact (Finset.univ.filter fun v => K.kind v = .token) \ endpoints F

noncomputable def AdmissibleFamilies {ι R : Type} [Fintype ι] [LinearOrder ι] [LinearOrder R]
    (K : Kernel ι R) (F L : Finset (ι × ι)) : Prop :=
  (∀ e ∈ F, PositiveEdge K e) ∧
  (F : Set (ι × ι)).Pairwise (fun e f => Disjoint (Set.Ico (K.r e.1) (K.r e.2))
    (Set.Ico (K.r f.1) (K.r f.2))) ∧
  (∀ e ∈ L, e.1 < e.2 ∧ K.kind e.1 = .active ∧ K.kind e.2 = .active ∧
    K.r e.1 = K.r e.2 ∧ (K.r e.2 : WithTop R) ≤ K.c e.1 ∧
    (K.r e.1 : WithTop R) ≤ K.c e.2) ∧
  (∀ e ∈ F ∪ L, e.1 ≠ e.2) ∧
  ((F ∪ L : Finset (ι × ι)) : Set (ι × ι)).Pairwise
    (fun e f => Disjoint ({e.1, e.2} : Set ι) {f.1, f.2}) ∧
  (∀ e ∈ F, ∀ w ∈ endpoints L, ¬ (K.r e.1 < K.r w ∧ K.r w < K.r e.2)) ∧
  ∀ w ∈ residualActives K F L, K.marked w = true

noncomputable def ResidualAssignment {ι R : Type} [Fintype ι] [DecidableEq ι] [LinearOrder R]
    (K : Kernel ι R) (F L : Finset (ι × ι)) : Prop :=
  ∃ σ : {s // s ∈ residualTokens K F} ≃ {w // w ∈ residualActives K F L},
    ∀ s, (K.r s.val : WithTop R) ≤ dF K F (σ s).val

noncomputable def correction {ι R : Type} [Fintype ι] [DecidableEq ι] [LinearOrder R]
    (K : Kernel ι R) (e : ι × ι) (t : R) : ℤ := by
  classical
  let ε : ℤ := if K.kind e.2 = .active then 1 else 0
  exact (if K.r e.1 ≤ t then 1 else 0) + ε * (if d0 K e.2 ≤ (t : WithTop R) then 1 else 0) -
    (1 - ε) * (if K.r e.2 ≤ t then 1 else 0) -
    ∑ w ∈ Finset.univ.filter (fun w => K.kind w = .active ∧ K.r e.1 < K.r w ∧ K.r w < K.r e.2),
      (if min (K.c w) (K.r e.1) ≤ (t : WithTop R) ∧ (t : WithTop R) < d0 K w then 1 else 0)

end TwoMasterRoommates.Capped


