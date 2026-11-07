-- Prove2me | Definitions.Def_IntroDelayAMDP_LayeredSpace
-- name    : IntroDelayAMDP_LayeredSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:42:38.773322+00:00
-- url     : https://prove2.me/theorems/871789c3-d171-4260-a682-1662a34c12dd
-- title:
--   Layered state space of an episodic AMDP
-- statement:
--   A **layered state space** with horizon $H$ on a set $\mathcal S$ of non-terminal states is a map assigning to each state $s$ its layer $h(s)\in\{0,\dots,H-1\}$, together with an initial state $s_0$ such that the layer $\mathcal S_0$ equals $\{s_0\}$. The number of non-terminal states is $S=|\mathcal S|$.
--
--   This is the state space of Definition 1.1 and Section 2.1. All other objects of the mission are built on it.
--
--   **Formalization Note** The extra layer $\mathcal S_H$ of terminal states is not modelled: a pair of layer $H-1$ has no successor, and value functions vanish beyond the last layer. The paper itself merges $\mathcal S_H$ into one state, which affects neither $q_k$ nor $B_k$ (p.30).
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Definition 1.1, p.3; Section 2.1, p.12

import Mathlib

namespace IntroDelayAMDP

/-- **Layered state space of an episodic AMDP** (Definition 1.1, p.3; Section 2.1, p.12).
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Section 2.1, printed p.12: "the state space is layered as `S = S₀ ∪ S₁ ∪ · · · ∪ S_{H−1}`,
where `S_h ∩ S_{h′} = ∅` for any `h ≠ h′`, the first layer `S₀ = {s₀}` only contains the initial
state `s₀`, and transitions only happen from one layer to the next one … where `S_H` is an extra
layer of terminal states".

`St` is the set of **non-terminal** states; `layer s ∈ {0, …, H−1}` is the layer of `s`, `s0` is
the initial state, and `S₀ = {s₀}`.

**Formalization Note.** There is no terminal layer `S_H`: a layer-`(H−1)` pair has no successor,
and value functions vanish beyond the last layer, which is the convention `V = 0` on `S_H` of
Eq. (12). The paper itself merges `S_H` into one state, "which affects neither `q_k` nor `B_k`"
(p.30). The number of non-terminal states is `S = Fintype.card St`. Layers are 0-based as on
the page. -/
structure LayeredSpace (St : Type) (H : ℕ) where
  /-- the layer `h` with `s ∈ S_h` -/
  layer : St → ℕ
  /-- the initial state `s₀` -/
  s0 : St
  layer_lt : ∀ s, layer s < H
  layer_s0 : layer s0 = 0
  layer_zero : ∀ s, layer s = 0 → s = s0

end IntroDelayAMDP


