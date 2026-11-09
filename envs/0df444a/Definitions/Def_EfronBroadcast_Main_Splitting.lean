-- Prove2me | Definitions.Def_EfronBroadcast_Main_Splitting
-- name    : EfronBroadcast_Main_Splitting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:50.316925+00:00
-- url     : https://prove2.me/theorems/1c41e9c1-1c39-4b22-affd-031c0cc9f98f
-- title:
--   Independent SPLIT input and output specifications
-- statement:
--   Let $q$ be the receiver, $A\subseteq[n]$ its initial values, $P$ its sender set with a fixed tie order, and $W_p\subseteq[n]$ the values held by sender $p$. A duplicate-free list represents the ordered set $P$. Every correct sender must satisfy
--
--   $$
--   |P|\le |W_p|-|A|,
--   $$
--
--   where subtraction is in the integers. Outputs are indices $j_p\in[n]\cup\{\bot\}$. If $q$ is correct, the independent output specification requires
--
--   $$
--   j_p=j_{p'}\ne\bot\ \Longrightarrow\ p=p',\qquad
--   j_p\ne\bot\ \Longrightarrow\ j_p\notin A,
--   $$
--
--   and every correct sender $p$ must have $j_p\ne\bot$ and $j_p\in W_p\setminus A$. These predicates describe the task without assuming any properties of Bisect or imposing truthfulness on faulty reports. They are shared by its invariant and security statements.
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 8, PDF p. 9, Definition 3; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_FaultModel
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- The input inequality is in integers, as in Definition 3, not truncated subtraction. -/
def SplitInput {n : ℕ} (a : Corruptions n) (A : Finset (Fin n))
    (P : List (Party n)) (W : Party n → Finset (Fin n)) : Prop :=
  P.Nodup ∧ ∀ p ∈ P, IsCorrect a p → (P.length : ℤ) ≤ (W p).card - (A.card : ℤ)

/-- The independent SPLIT output specification. `none` represents bottom. -/
def SplitOutput {n : ℕ} (a : Corruptions n) (q : Party n)
    (A : Finset (Fin n)) (P : List (Party n)) (W : Party n → Finset (Fin n))
    (j : Party n → Option (Fin n)) : Prop :=
  IsCorrect a q →
    (∀ p ∈ P, ∀ v, j p = some v → v ∉ A) ∧
    (∀ p ∈ P, ∀ p' ∈ P, ∀ v, j p = some v → j p' = some v → p = p') ∧
    (∀ p ∈ P, IsCorrect a p → ∃ v, j p = some v ∧ v ∈ W p ∧ v ∉ A)


end EfronBroadcast.Main


