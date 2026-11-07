-- Prove2me | Definitions.Def_PopRAM_WeightCreation
-- name    : PopRAM_WeightCreation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:14.750975+00:00
-- url     : https://prove2.me/theorems/cc9decb5-df9e-43fd-a941-b546ad36d3c6
-- title:
--   WeightCreation$(w)$: rules (1)–(3) as a mini-protocol
-- statement:
--   The protocol creates the **weights** $P_0,\dots,P_{w-2}$, disjoint sets with $|P_k|=2^k$. The leader $\ell_0$, at its first interaction with a free agent $\phi$, becomes $\ell_1$ and gives that agent the delegation state $p^*(w-2)$. Then, with the active agent as initiator,
--   $$p^*(k)+\phi\to p^*(k-1)+p_k(k)\ (k>1),\qquad p^*(1)+\phi\to p_0(0)+p_1(1),\qquad p_k(i)+\phi\to p_k(i-1)+p_k(i-1)\ (i>0).$$
--   An agent in $p_k(i)$ holds mass $2^i$ of weight $P_k$; $P_k$ is the set of agents in $p_k(0)$ at the end. All other pairs are unchanged ($X$ denotes an inert agent).
--
--   `wcDone` is the absence of the anomaly condition of p.21: the leader has delegated and no agent is in a state $p^*(\cdot)$ or $p_k(i)$ with $i>0$. `weightStates w` is the set of states $p^*(k)$, $1\le k\le w-2$, and $p_k(i)$, $0\le i\le k\le w-2$.
--
--   **Formalization Note** The delegation applies in both orientations ("in its first interaction with a free agent"); rules (1)–(3) initiator first, as printed and as the proof of Lemma 3 counts them.
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), MC+ Weight Creation, rules (1)–(3), p.21 (PDF p.22)

import Mathlib

set_option autoImplicit false

namespace PopRAM

/-! # WeightCreation(w) as a mini-protocol (rules (1)–(3))

Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM Simulation by Population Protocols*,
arXiv:2611.06178 (held version, sha256 f13223b3…), "MC+ Weight Creation", p.21 (PDF p.22): "In its
first interaction with a free agent, the leader delegates the creation of all weights by assigning
that agent state p∗(w − 2)", and

    p∗(k) + φ → p∗(k − 1) + p_k(k),  for k > 1,   (1)
    p∗(1) + φ → p₀(0) + p₁(1),                    (2)
    p_k(i) + φ → p_k(i − 1) + p_k(i − 1),  for i > 0.   (3)

**Formalization Note** `lead0` is the leader before delegation, `lead1` after; `free` is `φ`; `X`
is any other agent (inert). Rules (1)–(3) are applied with the active agent as initiator, as
printed (the proof of Lemma 3 conditions on "a specified active agent being selected as
initiator"). The delegation applies in both orientations ("its first interaction with a free
agent"). Every other pair is unchanged. `weightStates w` is the set of states `p∗(k)`,
`1 ≤ k ≤ w − 2`, and `p_k(i)`, `0 ≤ i ≤ k ≤ w − 2`. `wcDone` is the absence of the anomaly
condition of p.21: the leader has delegated, and no agent is in a state `p∗(·)` or `p_k(i)` with
`i > 0`. -/

/-- States of WeightCreation. -/
inductive WCState where
  | lead0
  | lead1
  | free
  | pstar (k : ℕ)
  | p (k i : ℕ)
  | X
  deriving DecidableEq

/-- The transition function of WeightCreation(w). -/
def wcδ (w : ℕ) : WCState → WCState → WCState × WCState
  | .lead0, .free => (.lead1, .pstar (w - 2))
  | .free, .lead0 => (.pstar (w - 2), .lead1)
  | .pstar k, .free =>
      if 1 < k then (.pstar (k - 1), .p k k)
      else if k = 1 then (.p 0 0, .p 1 1)
      else (.pstar k, .free)
  | .p k i, .free => if 0 < i then (.p k (i - 1), .p k (i - 1)) else (.p k i, .free)
  | a, b => (a, b)

/-- Weight creation has finished without anomaly. -/
def wcDone {n : ℕ} : Set (Fin n → WCState) :=
  {c | (∃ b, c b = .lead1) ∧ ∀ b, (∀ k, c b ≠ .pstar k) ∧ ∀ k i, c b = .p k i → i = 0}

/-- The weight states `p∗(k)` (`1 ≤ k ≤ w − 2`) and `p_k(i)` (`0 ≤ i ≤ k ≤ w − 2`). -/
def weightStates (w : ℕ) : Finset WCState :=
  (Finset.Icc 1 (w - 2)).image WCState.pstar ∪
    (((Finset.range (w - 1)) ×ˢ (Finset.range (w - 1))).filter (fun ki => ki.2 ≤ ki.1)).image
      (fun ki => WCState.p ki.1 ki.2)

end PopRAM


