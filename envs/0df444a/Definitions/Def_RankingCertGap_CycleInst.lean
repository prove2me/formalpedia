-- Prove2me | Definitions.Def_RankingCertGap_CycleInst
-- name    : RankingCertGap_CycleInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:49:17.105186+00:00
-- url     : https://prove2.me/theorems/918e8f71-afac-4596-844b-63d3946fd7f3
-- title:
--   Cycles with an arrival order: peaks, path blocks, chain lengths and postponed peaks
-- statement:
--   A **cycle** has $n$ offline and $n$ online nodes, with $N(j_r)=\{i_r,i_{r+1}\}$ and indices taken modulo $n$. Here $r$ is the position on the cycle and $t_r$ the position of $j_r$ in the arrival order. The node $j_r$ is a **peak** if $t_r>t_{r-1}$ and $t_r>t_{r+1}$.
--
--   Removing the peaks leaves alternating path blocks. A block is described by its minimum-time online node $j_q$ (a local minimum of $t$) and by the numbers $a$, $b$ of arm extensions on its two sides: arrival times increase away from $j_q$, up to the next peak on each side. Its online nodes are $j_{q-a},\dots,j_{q+b}$ and its offline nodes $i_{q-a},\dots,i_{q+b+1}$. The endpoints $i_{q-a}$ and $i_{q+b+1}$ have **chain lengths** $a+2$ and $b+2$.
--
--   An order $t'$ **postpones the peaks** of $t$ when it keeps the relative order of the nonpeaks, keeps the relative order of the peaks, and places every nonpeak before every peak.
--
--   **Formalization Note** In the arrival-ordered encoding, the online vertex with arrival position $a$ is $j_{t^{-1}(a)}$, so $j_r$ is the vertex $t(r)$. Offline vertices are labelled by cycle position. Positions are $0$-based where the page is $1$-based.
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), §10.1, p.35; Lemma 23, p.36; App. J.1, p.77

import Mathlib
import Definitions.Def_RankingCertGap_Inst

namespace RankingCertGap

variable {n : ℕ}

/-- A cycle with `n` offline and `n` online nodes. Xu, arXiv:2610.17545 (held file sha256
75896dd9…), §10.1, p.35: "`N_C(j_r) = {i_r, i_{r+1}}` and indices interpreted modulo `n`. Here `r`
specifies position on the cycle, not arrival order. Let `t_r` be the position of `j_r` in the
prescribed arrival order."

**Formalization Note.** `t : Equiv.Perm (Fin n)` is `r ↦ t_r`, and `finRotate n` is `r ↦ r + 1`
modulo `n`. In the arrival-ordered encoding of `Inst`, the online vertex with arrival position `a`
is `j_{t⁻¹ a}`, so `j_r` is the online vertex `t r`. Offline vertices are labelled by their cycle
position. Positions are `0`-based where the page is `1`-based. -/
def cycleInst (t : Equiv.Perm (Fin n)) : Inst n n where
  N a := {t.symm a, finRotate n (t.symm a)}

/-- "We call `j_r` a peak if `t_r > t_{r−1}` and `t_r > t_{r+1}`" (p.35). -/
def IsPeak (t : Equiv.Perm (Fin n)) (r : Fin n) : Prop :=
  t ((finRotate n).symm r) < t r ∧ t (finRotate n r) < t r

/-- `j_q` is a local minimum of the arrival times. These are the minimum-time online nodes of the
blocks (p.36, App. J.1, p.77). -/
def IsValley (t : Equiv.Perm (Fin n)) (q : Fin n) : Prop :=
  t q < t ((finRotate n).symm q) ∧ t q < t (finRotate n q)

/-- The block with minimum arrival `j_q`, left arm of `a` extensions and right arm of `b` extensions:
arrival times increase along both arms away from `j_q`, and each arm runs up to the next peak. The
online nodes of the block are `j_{q−a}, …, j_{q+b}`. -/
structure IsBlock (t : Equiv.Perm (Fin n)) (q : Fin n) (a b : ℕ) : Prop where
  rightArm : ∀ k ≤ b, t ((finRotate n)^[k] q) < t ((finRotate n)^[k + 1] q)
  rightPeak : IsPeak t ((finRotate n)^[b + 1] q)
  leftArm : ∀ k ≤ a, t ((finRotate n).symm^[k] q) < t ((finRotate n).symm^[k + 1] q)
  leftPeak : IsPeak t ((finRotate n).symm^[a + 1] q)

/-- The online nodes `j_{q−a}, …, j_{q+b}` of a block. -/
def blockOnline (q : Fin n) (a b : ℕ) : Finset (Fin n) :=
  (Finset.range (a + 1)).image (fun k => (finRotate n).symm^[k] q) ∪
    (Finset.range (b + 1)).image (fun k => (finRotate n)^[k] q)

/-- The offline nodes `i_{q−a}, …, i_{q+b+1}` of a block. -/
def blockOffline (q : Fin n) (a b : ℕ) : Finset (Fin n) :=
  (Finset.range (a + 1)).image (fun k => (finRotate n).symm^[k] q) ∪
    (Finset.range (b + 2)).image (fun k => (finRotate n)^[k] q)

/-- The endpoint `i_{q−a}` at the end of the left arm. Its chain length is `a + 2`: it is reached
after `a = r − 2` arm extensions from the minimum arrival (p.36). -/
def leftEndpoint (q : Fin n) (a : ℕ) : Fin n := (finRotate n).symm^[a] q

/-- The endpoint `i_{q+b+1}` at the end of the right arm. Its chain length is `b + 2`. -/
def rightEndpoint (q : Fin n) (b : ℕ) : Fin n := (finRotate n)^[b + 1] q

/-- `t'` is `t` with all peak arrivals postponed to the end: the relative order of the nonpeaks is
kept and every nonpeak precedes every peak (p.36; App. J.1, p.77: "We may postpone all of them to
the end, preserving the order of the remaining arrivals").

**Formalization Note.** The page does not fix the relative order of the postponed peaks, so this
predicate leaves it free: every order of the peaks at the end is a postponement. -/
def IsPostponement (t t' : Equiv.Perm (Fin n)) : Prop :=
  (∀ r r', ¬ IsPeak t r → ¬ IsPeak t r' → (t r < t r' ↔ t' r < t' r')) ∧
    (∀ r r', ¬ IsPeak t r → IsPeak t r' → t' r < t' r')

open Classical in
/-- The number of nonpeak online nodes: the length of the prefix "immediately before the postponed
peaks" (p.36). -/
noncomputable def nonpeakCount (t : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun r => ¬ IsPeak t r).card

end RankingCertGap


