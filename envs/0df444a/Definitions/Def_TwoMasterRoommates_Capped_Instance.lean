-- Prove2me | Definitions.Def_TwoMasterRoommates_Capped_Instance
-- name    : TwoMasterRoommates_Capped_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:27:09.358577+00:00
-- url     : https://prove2.me/theorems/cc085fca-6ac6-4451-81b3-07ec12ddf46e
-- title:
--   Whole weak masters, personal caps, perfect matchings, and weak stability
-- statement:
--   Let $V=\{0,\ldots,n-1\}$ be a finite identity population, partitioned into observer classes $A$ and $B$. Two whole rank maps $a,b:V\to R$ take values in a linearly ordered set, with smaller ranks preferred. Observer $v$ uses $r_v=a$ in $A$ and $r_v=b$ in $B$. The self entry is retained in both whole maps but cannot be a partner. The personal cap $\kappa_v$ is finite or $+\infty$.
--
--   A perfect matching $M:V\to V$ is an involution without fixed points. Its attained quality is $Q_v=r_v(Mv)$. Distinct $u,v$ block exactly when
--
--   $$r_u(v)<Q_u\quad\text{and}\quad r_v(u)<Q_v.$$
--
--   A solution is a perfect matching with $Q_v\le\kappa_v$ for every identity and no blocker. Caps never remove pairs from the blocking test. The comparison-presentation predicate preserves the classes, both strict master comparisons, and every candidate's cap acceptance. Swapping the instance exchanges observer classes and the two masters.
--
--   This is the common model used throughout the mission. Empty populations and either empty observer class are allowed.
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 4 (PDF p. 5), §3, equations (1); p. 12 (PDF p. 13), Appendix B, equation (7)

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

/-- Whole weak masters, observer classes, and personal upper caps (§3, Appendix B). -/
structure Instance (R : Type) [LinearOrder R] (n : ℕ) where
  isA : Fin n → Bool
  a : Fin n → R
  b : Fin n → R
  κ : Fin n → WithTop R

def Instance.r {R : Type} [LinearOrder R] {n : ℕ} (I : Instance R n)
    (v x : Fin n) : R := if I.isA v then I.a x else I.b x

def IsPerfectMatching {α : Type} (M : α → α) : Prop :=
  Function.Involutive M ∧ ∀ v, M v ≠ v

def Q {R : Type} [LinearOrder R] {n : ℕ} (I : Instance R n)
    (M : Fin n → Fin n) (v : Fin n) : R := I.r v (M v)

def Blocks {R : Type} [LinearOrder R] {n : ℕ} (I : Instance R n)
    (M : Fin n → Fin n) (u v : Fin n) : Prop :=
  u ≠ v ∧ I.r u v < Q I M u ∧ I.r v u < Q I M v

def IsSolution {R : Type} [LinearOrder R] {n : ℕ} (I : Instance R n)
    (M : Fin n → Fin n) : Prop :=
  IsPerfectMatching M ∧ (∀ v, (↑(Q I M v) : WithTop R) ≤ I.κ v) ∧
    ∀ u v, ¬ Blocks I M u v

def SameComparisons {R : Type} [LinearOrder R] {n : ℕ}
    (I : Instance R n) (J : Instance ℤ n) : Prop :=
  I.isA = J.isA ∧
  (∀ x y, I.a x < I.a y ↔ J.a x < J.a y) ∧
  (∀ x y, I.b x < I.b y ↔ J.b x < J.b y) ∧
  (∀ v x, (I.r v x : WithTop R) ≤ I.κ v ↔ (J.r v x : WithTop ℤ) ≤ J.κ v)

def Instance.swap {R : Type} [LinearOrder R] {n : ℕ} (I : Instance R n) : Instance R n :=
  ⟨fun v => !(I.isA v), I.b, I.a, I.κ⟩

end TwoMasterRoommates.Capped


