-- Prove2me | Definitions.Def_ChoresTIE197_Main_Nomination
-- name    : ChoresTIE197_Main_Nomination
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T02:17:06.013969+00:00
-- url     : https://prove2.me/theorems/65c83d74-cc89-40ce-a3f8-0e746af4928e
-- title:
--   Public residual blocks, safety and Mechanism 2
-- statement:
--   For every agent, remove her $k$ publicly tie-broken largest chores, then split the residual descending order into blocks of size $n-k$. The nomination count $l(e)$ counts all agents nominating $e$. Safety requires either a singleton bundle or avoidance of all nominations together with at most one chore from each residual block.
--
--   Mechanism 2 pads with forced zero chores, samples a uniform $(n-k)$-element agent subset, and constructs the chore-to-tagged-block graph for those agents. It chooses a uniform member of its operational right-saturating matching decomposition. The remaining chores go to unselected agents by a uniform bijection, realized here by a uniform permutation and public ordered agent list. Dummies are then removed. No safety, marginal or approximation guarantee is assumed in the law's definition.
--
--   Both graph vertex enumerations use increasing public orders, including lexicographic orders on tagged products, rather than an arbitrary classical bijection.
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), §3.2, Mechanism 2, printed p.10, PDF p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Rounding

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

def block {n m : ℕ} (c : Profile n m) (k : ℕ) (i : Fin n) (r : ℕ) : Finset (Fin m) :=
  univ.filter (fun e => k + r * (n-k) ≤ rank (c i) e ∧ rank (c i) e < k + (r+1)*(n-k))

def nominations {n m : ℕ} (c : Profile n m) (k : ℕ) (e : Fin m) : ℕ :=
  (univ.filter (fun i => e ∈ top (c i) k)).card

def Safe {n m : ℕ} (c : Profile n m) (k : ℕ) (A : Allocation n m) : Prop :=
  ∀ i, (bundle A i).card ≤ 1 ∨
    (Disjoint (bundle A i) (top (c i) k) ∧ ∀ r, ((bundle A i) ∩ block c k i r).card ≤ 1)

def nominationDraw {n m : ℕ} [NeZero n] (k b : ℕ) (c : Profile n m)
    (S : Finset (Fin n)) : Law n m :=
  letI : LinearOrder (Fin n × Fin m) := inferInstanceAs (LinearOrder (Fin n ×ₗ Fin m))
  let R := {v : Fin n × Fin m // v.1 ∈ S ∧ v.2.val < b}
  let ρ := orderedFinEquiv R
  letI : LinearOrder (Fin m × R) := inferInstanceAs (LinearOrder (Fin m ×ₗ R))
  let ε := orderedFinEquiv (Fin m × R)
  let left := fun e => (ε.symm e).1
  let right := fun e => ρ (ε.symm e).2
  let E := univ.filter (fun e =>
    (ε.symm e).1 ∈ block c k (ε.symm e).2.val.1 (ε.symm e).2.val.2.val)
  let parts := decomposition left right (n-k) E
  (uniformChoice (range (n-k)) 0).bind (fun t =>
    let W := parts[t]?.getD ∅
    let matched := W.image left
    let U := univ \ matched
    let agents := (univ \ S).sort (· ≤ ·)
    (PMF.uniformOfFintype (Equiv.Perm (Fin m))).map (fun π e =>
      if h : ∃ f ∈ W, left f = e then
        let f := firstBy (W.filter (fun f => left f = e)) (fun f => f.val) (Classical.choose h)
        (ρ.symm (right f)).val.1
      else
        let pos := (U.filter (fun f => (π.symm f).val < (π.symm e).val)).card
        agents[pos]?.getD 0))

def nominationPadded {n m : ℕ} [NeZero n] (k : ℕ) : Mechanism n m := fun c =>
  let b := (m-k)/(n-k)
  (uniformChoice (univ.powerset.filter (fun S : Finset (Fin n) => S.card = n-k)) ∅).bind
    (nominationDraw k b c)

/-- Padding is fixed from n,m,k before collecting any report. -/
def nominationPadding (n m k : ℕ) : ℕ := k + (m/(n-k)+1)*(n-k) - m

def mechanism2 {n m : ℕ} [NeZero n] (k : ℕ) : Mechanism n m := fun c =>
  (nominationPadded k (pad (nominationPadding n m k) c)).map unpad

end ChoresTIE197.Main


