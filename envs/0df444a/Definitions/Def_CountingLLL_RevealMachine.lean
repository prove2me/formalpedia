-- Prove2me | Definitions.Def_CountingLLL_RevealMachine
-- name    : CountingLLL_RevealMachine
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T09:43:27.346694+00:00
-- url     : https://prove2.me/theorems/a784fd74-f924-46a5-93b6-c0fd4e2b74fa
-- title:
--   Deterministic machine with finite reveal bookkeeping
-- statement:
--   A deterministic small-step machine may query at most one coordinate of a fixed input array in each step. Its extended state records both the program state and the finite set of coordinates read so far. This generic interface is intended for proving nonanticipation; a concrete encoding of ReciprocalTest into it is a separate task.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
set_option autoImplicit false

/-! Deterministic bookkeeping for a machine that reads at most one array
coordinate per atomic step. It records the finite set of coordinates actually
read. Connecting a specific program, such as ReciprocalTest, to this generic
interface is a separate verification task. -/
namespace CountingLLL.RevealMachine

structure Program (σ ι α : Type*) where
  query : σ → Option ι
  read : σ → α → σ
  silent : σ → σ

variable {σ ι α : Type*} [DecidableEq ι]

def step (P : Program σ ι α) (ω : ι → α) (c : σ × Finset ι) : σ × Finset ι :=
  match P.query c.1 with
  | none => (P.silent c.1, c.2)
  | some i => (P.read c.1 (ω i), insert i c.2)

def run (P : Program σ ι α) (ω : ι → α) (initial : σ) (n : ℕ) : σ × Finset ι :=
  (step P ω)^[n] (initial, ∅)
end CountingLLL.RevealMachine


