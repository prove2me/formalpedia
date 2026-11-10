-- Prove2me | Definitions.Def_BinaryTwoWayErasure_Optimal_Channel
-- name    : BinaryTwoWayErasure_Optimal_Channel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T17:44:47.565978+00:00
-- url     : https://prove2.me/theorems/22eb0028-1dec-40b7-bbf0-d95951c23359
-- title:
--   Finite words and fixed-schedule binary erasure protocols
-- statement:
--   Alice holds an arbitrary binary word $x$ of length $n$; Bob has no private input. A deterministic protocol fixes a length $T$, a speaking order $p\in\{A,B\}^T$, local message functions, and Bob's output function. A local view records the party's own sent bits and its received symbols in chronological order. Channel deliveries are bits or the erasure symbol $\bot$. An adversary chooses a subset $\mathrm{Adv}\subseteq[T]$ of channel uses in either direction. Execution recursively evaluates each sender on its own view and delivers $\bot$ exactly at the masked positions. The sender's view records its sent bit regardless of erasure.
--
--   Resilience at fraction $\rho$ means
--   $$
--   \forall x\in\{0,1\}^n\ \forall\mathrm{Adv}\subseteq[T],\qquad
--   |\mathrm{Adv}|\le\rho T\ \Longrightarrow\ g(\pi_B)=x.
--   $$
--   The additional single-party evaluation permits arbitrary received histories for the worst-case runtime specification. This interface is reusable for deterministic communication over a shared adversarial erasure budget. Indices use $\operatorname{Fin}(T)$, corresponding to source positions $1,\ldots,T$ by adding one.
-- source:
--   Klim Efremenko, Gillat Kol, Sergey Komech, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1142 (October 2026), §3, printed p.6 / PDF p.8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1142.pdf

import Mathlib

namespace BinaryTwoWayErasure.Optimal

/-- Finite words use zero-based indices; source position i+1 is index i. -/
abbrev Bits (n : ℕ) := Fin n → Bool
abbrev Received := Option Bool

inductive Party where
  | alice | bob
  deriving DecidableEq, Repr

/-- Local events distinguish one's own sent bit from a channel delivery. -/
inductive Event where
  | sent (b : Bool)
  | received (s : Received)
  deriving DecidableEq, Repr

structure Protocol (n : ℕ) where
  length : ℕ
  schedule : Fin length → Party
  alice : Bits n → List Received → Bool
  bob : List Received → Bool
  output : List Received → Bits n

structure Views where
  alice : List Received := []
  bob : List Received := []
  aliceEvents : List Event := []
  bobEvents : List Event := []

/-- Neither sender learns whether its transmission was erased. -/
def channelTurn {n : ℕ} (P : Protocol n) (x : Bits n) (mask : Finset (Fin P.length))
    (t : Fin P.length) (v : Views) : Views :=
  match P.schedule t with
  | .alice =>
      let b := P.alice x v.alice
      let s := if t ∈ mask then none else some b
      ⟨v.alice ++ [some b], v.bob ++ [s],
        v.aliceEvents ++ [.sent b], v.bobEvents ++ [.received s]⟩
  | .bob =>
      let b := P.bob v.bob
      let s := if t ∈ mask then none else some b
      ⟨v.alice ++ [s], v.bob ++ [some b],
        v.aliceEvents ++ [.received s], v.bobEvents ++ [.sent b]⟩

def executeProtocol {n : ℕ} (P : Protocol n) (x : Bits n)
    (mask : Finset (Fin P.length)) : Views :=
  (List.finRange P.length).foldl (fun v t => channelTurn P x mask t v) {}

def Resilient {n : ℕ} (P : Protocol n) (ρ : ℝ) : Prop :=
  ∀ (x : Bits n) (mask : Finset (Fin P.length)),
    (mask.card : ℝ) ≤ ρ * P.length → P.output (executeProtocol P x mask).bob = x

/-- A single party's possible history under arbitrary incoming symbols, including
histories that no joint honest execution can produce. -/
def localHistory {n : ℕ} (P : Protocol n) (who : Party) (x : Bits n)
    (incoming : Fin P.length → Received) : List Received × List Event :=
  (List.finRange P.length).foldl (fun v t =>
    if P.schedule t = who then
      let b := match who with
        | .alice => P.alice x v.1
        | .bob => P.bob v.1
      (v.1 ++ [some b], v.2 ++ [.sent b])
    else (v.1 ++ [incoming t], v.2 ++ [.received (incoming t)])) ([], [])

end BinaryTwoWayErasure.Optimal


