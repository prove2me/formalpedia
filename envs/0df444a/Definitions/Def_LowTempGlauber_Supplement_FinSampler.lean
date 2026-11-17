-- Prove2me | Definitions.Def_LowTempGlauber_Supplement_FinSampler
-- name    : LowTempGlauber_Supplement_FinSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:26:25.549673+00:00
-- url     : https://prove2.me/theorems/1a1b209c-e102-4e84-8aff-7dbd9db93cc8
-- title:
--   Conditional and push-forward laws; the samplers' input and output on graphs with vertex set $\{0,\dots,n-1\}$
-- statement:
--   This module fixes the probabilistic and machine conventions shared by Theorems 2 and 3.
--
--   For a finite set $\Omega$, a function $\pi:\Omega\to\mathbb R$ and a predicate $p$, the **conditional law** is
--   $$\pi(x\mid p)=\frac{\pi(x)\,\mathbf 1\{p(x)\}}{\sum_{y:\,p(y)}\pi(y)},$$
--   equal to $0$ off $p$. For a map $f:\Omega\to\Omega'$ the **push-forward** $f_\#\pi(b)=\sum_{a:\,f(a)=b}\pi(a)$ is the law of $f(X)$ for $X\sim\pi$.
--
--   The full-distribution samplers run on the published unit-cost real RAM with fair coins (the `SubsetConvFPRAS` machine, both value oracles set to $0$). On a graph $G$ with vertex set $\{0,\dots,n-1\}$ and degree $d$, the input is: integer cell $0$ holds $n$, cell $1$ holds $d$, and cell $2+dv+j$ ($j<d$) holds the $j$-th neighbour of $v$ in increasing order; all other integer cells hold $0$; the real cells hold the model parameters; all bitmaps are empty. The output is bitmap $0$ of a halted run. The **output law** after $B$ steps gives a set $S$ the fraction of the $2^B$ coin sequences of length $B$ on which the run has halted with bitmap $0$ equal to $S$.
--
--   These conventions are the vertex-set-$\{0,\dots,n-1\}$ analogue of the published input encoding of Theorem 1, whose vertex set is bipartite.
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Theorem 2, p.4, and Theorem 3, part 2, p.5 (the full-distribution algorithms)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_Machine

open Classical

namespace LowTempGlauber.Supplement

/-!
# Conditional laws, push-forward laws, and the samplers' input on `Fin n` graphs

A. Galanis, D. Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission manuscript dated 3 November 2026 (held version, sha256 c41a38ff…7533d), Theorem 2 (p.4,
"there is an algorithm that, for any `β > 0`, outputs in time `Õ(n²)` an `ε`-sample from the full
distribution `π_G`") and Theorem 3, part 2 (p.5).

The graphs of Theorems 2, 3 and 21 are `d`-regular graphs on the vertex set `Fin n` (`G ∼ G_{n,d}`,
p.5). The machine is the published `SubsetConvFPRAS` real RAM (unit cost per instruction, rational
literals in `Admissible` programs, fair coins, integer memory, bitmaps over a ground set `Fin N`),
used with both value oracles `0`, as in the published goal `LowTempGlauber.theorem_1`.

**Formalization Note.**
* `condLaw π p` is `π(· | p)`, and `0` off `p` (`0` everywhere if `π(p) = 0`); `pushLaw π f` is the law
  of `f(X)` for `X ∼ π`.
* Input (`graphInts`, `initState`): integer cell `0` holds `n`, cell `1` holds `d`, cell `2 + d·v + j`
  (`j < d`) holds the `j`-th neighbour of `v` in increasing order; all other integer cells hold `0`.
  The real cells hold the model parameters (given as `reals`); bitmaps are empty.
* Output (`outLaw`): the program halts and the sample is bitmap `0`. `outLaw P s₀ B S` is the fraction
  of the `2^B` coin tapes of length `B` on which the run of `B` steps from `s₀` has halted with bitmap
  `0` equal to `S`.
-/

/-- The conditional law `π(· | p)`; `0` off `p`. -/
noncomputable def condLaw {α : Type*} [Fintype α] (π : α → ℝ) (p : α → Prop) (x : α) : ℝ :=
  if p x then π x / ∑ y ∈ Finset.univ.filter p, π y else 0

/-- The law of `f(X)` for `X ∼ π`. -/
noncomputable def pushLaw {α β : Type*} [Fintype α] (π : α → ℝ) (f : α → β) (b : β) : ℝ :=
  ∑ a, if f a = b then π a else 0

/-- The neighbours of `v` in increasing order. -/
noncomputable def nbrList {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : List (Fin n) :=
  (Finset.univ.filter (G.Adj v)).sort (· ≤ ·)

/-- The integer input: `n`, `d`, then the sorted adjacency lists (`d` entries per vertex). -/
noncomputable def graphInts (n d : ℕ) (G : SimpleGraph (Fin n)) : ℤ → ℤ := fun i =>
  if i = 0 then (n : ℤ)
  else if i = 1 then (d : ℤ)
  else if h : 2 ≤ i ∧ (i - 2).toNat < d * n then
    (((nbrList G ⟨(i - 2).toNat / d, Nat.div_lt_of_lt_mul h.2⟩)[(i - 2).toNat % d]?
      |>.map (fun x : Fin n => ((x : ℕ) : ℤ))).getD 0)
  else 0

/-- The initial state on ground set `Fin N`: the graph input and the real parameters `reals`. -/
noncomputable def initState (N n d : ℕ) (G : SimpleGraph (Fin n)) (reals : ℤ → ℝ) :
    SubsetConvFPRAS.State N :=
  SubsetConvFPRAS.mkInit (graphInts n d G) (fun _ => ∅) reals

/-- The output law of `P` run for `B` steps from `s₀`: the probability, over `B` fair coins, that it
has halted with bitmap `0` equal to `S`. -/
noncomputable def outLaw {N : ℕ} (P : SubsetConvFPRAS.Program) (s₀ : SubsetConvFPRAS.State N)
    (B : ℕ) (S : Finset (Fin N)) : ℝ :=
  (SubsetConvFPRAS.tapeCount P (fun _ => 0) (fun _ => 0) s₀ B
      (fun st => st.output.isSome ∧ st.bitmap 0 = S) : ℝ) / 2 ^ B

end LowTempGlauber.Supplement


