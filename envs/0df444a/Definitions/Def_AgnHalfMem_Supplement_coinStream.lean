-- Prove2me | Definitions.Def_AgnHalfMem_Supplement_coinStream
-- name    : AgnHalfMem_Supplement_coinStream
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:55:49.869499+00:00
-- url     : https://prove2.me/theorems/691e64c7-25b6-496b-9eb6-f46095fceaac
-- title:
--   Private-coin streaming algorithms — the coin law, the stream with coins, and the output classifier
-- statement:
--   A **private-coin streaming algorithm** with memory states $S$ and $T$ samples is a deterministic layered branching program (Definition B.1 of the paper, the base mission's `BP`) that at step $t$ reads the labelled sample $(x_t,y_t)\sim D$ together with a fresh coin $u_t\sim\mathrm{Unif}[0,1]$, independent of everything else. Formally, the program is fed i.i.d. copies of $((x,u),y)$, where $(x,y)\sim D$ and $u\sim\mathrm{Unif}[0,1]$ independently; this law is called the **coin stream** of $D$. When the computation path reaches a leaf, the algorithm outputs that leaf's label, a classifier $x\mapsto\tilde h(x)$ on $\mathbb R^d$ (read with the coin coordinate set to $0$).
--
--   The algorithm uses $b$ bits of memory when $|S|\le2^b$. Since the program is deterministic, any random choice it keeps (for example the random stopping index $J$ of the paper's Algorithm 1) has to be stored in its state, which is how the paper counts memory in its upper bounds.
--
--   **Formalization Note** This model is used for the existence results (Theorems 5.1 and 5.2), where a free public random seed would make the claims weaker than printed. One real coin per step supplies any finite number of random bits.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), App. A.2, pp.25–28 (Algorithm 1, memory count including J); App. B, p.28 (Definitions B.1, B.2)

import Mathlib
import Definitions.Def_AgnHalfMem_BP

open MeasureTheory

namespace AgnHalfMem

namespace Supplement

/-- **The private coin law `Unif[0, 1]`.** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for
Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), App. A.2, pp.25–28 (Algorithm 1 "Choose J uniformly at random"; "storing the
randomly chosen index J […] requires O(log N) bits"). `coinLaw` is Lebesgue measure restricted
to `[0, 1]`, a probability measure. -/
noncomputable def coinLaw : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc 0 1)

/-- **The stream seen by a private-coin algorithm.** For a distribution `D` on `X × {−1, 1}`,
`coinStream D` is the law of `((x, u), y)` where `(x, y) ∼ D` and `u ∼ Unif[0, 1]` is an
independent fresh coin: the image of `D ⊗ Unif[0, 1]` under `((x, y), u) ↦ ((x, u), y)`.

A **private-coin streaming algorithm** with memory states `S` and `T` samples is a deterministic
Definition B.1 branching program `b : BP S (X × ℝ) T` (base mission, p.28) that reads at step `t`
the sample `(xₜ, yₜ)` together with its own coin `uₜ`; any random choice the algorithm keeps (such
as Algorithm 1's index `J`) must therefore be stored in its state, and `b` uses `β` bits of
memory when `Fintype.card S ≤ 2^β`.

**Formalization Note.** Randomness is private and counted in memory, unlike the base mission's
public-seed `StreamAlg`; one real coin per step supplies any finite number of random bits. -/
noncomputable def coinStream {X : Type*} [MeasurableSpace X] (D : Measure (X × Bool)) :
    Measure ((X × ℝ) × Bool) :=
  (D.prod coinLaw).map (fun q : (X × Bool) × ℝ => ((q.1.1, q.2), q.1.2))

/-- **The classifier output by a private-coin algorithm.** Definition B.2, p.28: "The program
outputs the label h̃_v of the leaf v reached by the computation-path." For a private-coin program
`b` and a stream `s`, `pcOutput b s x` is the label of the leaf reached, evaluated at the
feature `x` (and the coin coordinate `0`, which the output does not need). -/
noncomputable def pcOutput {X S : Type*} {T : ℕ} (b : BP S (X × ℝ) T)
    (s : Fin T → (X × ℝ) × Bool) : X → Bool :=
  fun x => b.output s (x, 0)

end Supplement

end AgnHalfMem


