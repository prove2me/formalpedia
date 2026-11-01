-- Prove2me | Definitions.Def_WildeQIT_EntManip_IsLOCC
-- name    : WildeQIT_EntManip_IsLOCC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:07.202013+00:00
-- url     : https://prove2.me/theorems/cea5e46b-52ba-4387-a908-6184499c0ab3
-- title:
--   LOCC channel: a finite composition of one-way LOCC rounds
-- statement:
--   A map $\Lambda:\mathcal L(\mathcal H_A\otimes\mathcal H_B)\to\mathcal L(\mathcal H_{A'}\otimes\mathcal H_{B'})$ between finite-dimensional bipartite systems is an **LOCC channel** (local operations and classical communication) when it is a finite composition
--
--   $$
--   \Lambda = \Lambda_r\circ\cdots\circ\Lambda_2\circ\Lambda_1 ,\qquad r\ge1,
--   $$
--
--   of one-way rounds, each either from Alice to Bob, $\sum_x\mathcal F^x_A\otimes\mathcal G^x_B$ (19.21), or from Bob to Alice (the same with $A$ and $B$ switched). The intermediate systems of Alice and Bob may be any finite-dimensional spaces.
--
--   LOCC channels are the operations allowed in entanglement manipulation; they map separable states to separable states.
--
--   **Formalization Note** `IsLOCC` is an inductive predicate: the two kinds of rounds are LOCC, and the composition of two LOCC channels is LOCC. Systems are indexed by finite types in `Type`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §19.2, p. 538

import Mathlib
import Definitions.Def_WildeQIT_EntManip_IsOneWayLOCCAB
import Definitions.Def_WildeQIT_EntManip_IsOneWayLOCCBA

namespace WildeQIT.EntManip

/-- **LOCC channel** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
§19.2, p. 538): "An LOCC channel consists of a finite number of compositions of the following":
1. a one-way round from Alice to Bob, `∑_x F^x_A ⊗ G^x_B` (19.21) (`IsOneWayLOCCAB`);
2. a one-way round from Bob to Alice, the same with the `A` and `B` labels switched
   (`IsOneWayLOCCBA`).

`IsLOCC Λ` for `Λ : L(H_A ⊗ H_B) → L(H_{A'} ⊗ H_{B'})` is the least predicate containing both
kinds of round and closed under composition `Λ₂ ∘ Λ₁`; the intermediate systems of a composition
are arbitrary finite-dimensional spaces of Alice and of Bob.

**Formalization Note** Finite dimensions throughout (finite index types in `Type`). A
derivation of `IsLOCC Λ` is a finite composition tree of rounds, i.e. a finite number of
compositions, at least one. -/
inductive IsLOCC : {a b a' b' : Type} →
    (Matrix (a × b) (a × b) ℂ → Matrix (a' × b') (a' × b') ℂ) → Prop
  /-- A one-way round from Alice to Bob, (19.21). -/
  | oneWayAB {a b a' b' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      [Fintype a'] [Fintype b']
      {Λ : Matrix (a × b) (a × b) ℂ → Matrix (a' × b') (a' × b') ℂ}
      (h : IsOneWayLOCCAB Λ) : IsLOCC Λ
  /-- A one-way round from Bob to Alice, (19.21) with `A` and `B` switched. -/
  | oneWayBA {a b a' b' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      [Fintype a'] [Fintype b']
      {Λ : Matrix (a × b) (a × b) ℂ → Matrix (a' × b') (a' × b') ℂ}
      (h : IsOneWayLOCCBA Λ) : IsLOCC Λ
  /-- The composition of two LOCC channels. -/
  | comp {a b a' b' a'' b'' : Type}
      {Λ₁ : Matrix (a × b) (a × b) ℂ → Matrix (a' × b') (a' × b') ℂ}
      {Λ₂ : Matrix (a' × b') (a' × b') ℂ → Matrix (a'' × b'') (a'' × b'') ℂ}
      (h₁ : IsLOCC Λ₁) (h₂ : IsLOCC Λ₂) : IsLOCC (Λ₂ ∘ Λ₁)

end WildeQIT.EntManip


