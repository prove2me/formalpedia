-- Prove2me | Definitions.Def_BBBV_RandomPermutation_Chain
-- name    : BBBV_RandomPermutation_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:22.219686+00:00
-- url     : https://prove2.me/theorems/94fc115d-2797-4a82-9723-98583390ad8b
-- title:
--   Proof of Theorem 3.6 — transposition chain of random permutation oracles
-- statement:
--   Let $\pi_0$ be uniform among permutations of length-$n$ binary strings and set $x_0=\pi_0^{-1}(1^n)$. Independently choose $x_1,\ldots,x_{T+1}$ uniformly. Define the chain by
--
--   $$\pi_{i+1}=\pi_i\circ(x_i\ x_{i+1}).$$
--
--   The chain is the family of permutation oracles compared in the proof of Theorem 3.6. The language test at $1^n$ asks whether the first bit of $\pi_i^{-1}(1^n)$ is $1$. A hybrid run uses $\pi_i$ for the oracle operation of step $i$. An average is the uniform finite average over all choices of $\pi_0,x_1,\ldots,x_{T+1}$.
--
--   **Formalization Note** This sample space has the same joint law as the paper's construction, which first chooses $x_0$ uniformly and then chooses $\pi_0$ uniformly subject to $\pi_0(x_0)=1^n$. The string $x_i$ is set to $1^n$ beyond index $T+1$ so its Lean function is total; all theorems use indices at most $T+1$.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, pp. 10–11, proof of Theorem 3.6

import Mathlib
import Definitions.Def_BBBV_RandomPermutation_QueryModel

namespace BBBV.RandomPermutation

def firstBit {n : ℕ} (hn : 0 < n) (s : BBBV.RandomOracle.Str n) : ZMod 2 := s ⟨0, hn⟩

abbrev Ω (n T : ℕ) := Equiv.Perm (BBBV.RandomOracle.Str n) × (Fin (T + 1) → BBBV.RandomOracle.Str n)

def x {n T : ℕ} (ω : Ω n T) : ℕ → BBBV.RandomOracle.Str n
  | 0 => ω.1.symm (BBBV.RandomOracle.ones n)
  | i + 1 => if h : i < T + 1 then ω.2 ⟨i, h⟩ else BBBV.RandomOracle.ones n

def piChain {n T : ℕ} (ω : Ω n T) : ℕ → Equiv.Perm (BBBV.RandomOracle.Str n) :=
  Nat.rec ω.1 (fun i π => π * Equiv.swap (x ω i) (x ω (i + 1)))

def hybrid {n T : ℕ} (ω : Ω n T) : Fin T → BBBV.RandomOracle.Str n → BBBV.RandomOracle.Str n :=
  fun i => piChain ω i

noncomputable def avg {n T : ℕ} (f : Ω n T → ℝ) : ℝ :=
  (∑ ω : Ω n T, f ω) / (Fintype.card (Ω n T) : ℝ)

end BBBV.RandomPermutation


