-- Prove2me | Definitions.Def_Ironclad_Decomposition
-- name    : Ironclad_Decomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:24:44.448247+00:00
-- url     : https://prove2.me/theorems/5490af30-8053-47e9-b589-b42ed5cf951d
-- title:
--   Greedy decomposition into the patterns $\sigma_1,\dots,\sigma_4$, the states $S_0,S_1,S_2$, the counts $\#_L$ and $\alpha_L$
-- statement:
--   Fix the network delay $\Delta\ge1$. A characteristic string $x\in\{0,h,H\}^{\mathbb N}$ is decomposed greedily, from its first nonzero symbol, into the four **characteristic patterns** of Definition 3.1:
--
--   1. $\sigma_1=\{h\}\|\{0\}^k$ with $k<\Delta$ and $\sigma_2=\{h\}\|\{0\}^k$ with $k\ge\Delta$: an $h$ followed by the zeros up to the next nonzero symbol;
--   2. $\sigma_3=\{H\}\|\{0,h\}^k$ with $k<\Delta$: an $H$ followed by the symbols up to the next $H$, when that $H$ comes within the next $\Delta$ slots;
--   3. $\sigma_4=\{H\}\|\{0,h\}^\Delta\|\{0\}^*$: an $H$ with no other $H$ in the next $\Delta$ slots, followed by those $\Delta$ slots and then by the zeros up to the next nonzero symbol.
--
--   Each pattern starts where the previous one ends. The **state** $X_k\in\{S_0,S_1,S_2\}$ of the embedded chain before the $k$-th pattern is $X_0=S_0$, and after a pattern the chain is in $S_0$ (after $\sigma_2$ or $\sigma_4$), $S_1$ (after $\sigma_1$) or $S_2$ (after $\sigma_3$).
--
--   For a period of length $L$ (the slots $0,\dots,L-1$), $\#_L(S_i\xrightarrow{\sigma}S_j)$ counts the transitions out of $S_i$ by pattern $\sigma$ whose pattern lies in the period, $\#_L(S_2\xrightarrow{\sigma_4}S_0\xrightarrow{\sigma_2}S_0)$ counts the $\sigma_2$ transitions out of $S_0$ in the period whose preceding transition was $S_2\xrightarrow{\sigma_4}S_0$, and $\#_LS_i$ counts the sojourns in $S_i$ in the period. The **minimal mining-power requirement of the period** is
--
--   $$
--   \alpha_L=\frac1L\Big[\#_L(S_0\xrightarrow{\sigma_2}S_0)-\#_L(S_2\xrightarrow{\sigma_4}S_0\xrightarrow{\sigma_2}S_0)+\theta\big(\#_L(S_0\xrightarrow{\sigma_4}S_0)+\#_L(S_1\xrightarrow{\sigma_4}S_0)\big)\Big],
--   $$
--
--   the total weight of the agreement blocks of the period divided by $L$, where regular blocks weigh $1$ and iron blocks $\theta$. The module also gives the length of the $k$-th pattern and, for a fixed slot $t$, the length of the pattern of a given type starting at $t$ (zero if none does).
--
--   These are the objects whose long-run behaviour Lemma 3.1 and Theorem 3.2 describe.
--
--   **Formalization Note** The σ₃ boundary is $k<\Delta$: Definition 3.1 prints $k\le\Delta$, but the occurrence probabilities $\mathbb P(\sigma_3)=q_H[1-(1-q_H)^\Delta]$ and $\mathbb P(\sigma_4)=q_H(1-q_H)^\Delta$ on the same page (and App. .1.1's "$Z<\Delta$") hold only for $k<\Delta$, which is also the only reading under which $\sigma_3$ and $\sigma_4$ do not overlap. The decomposition starts at the first nonzero symbol (the paper takes strings "starting with $H$ or $h$") from the initial state $S_0$ (the paper is silent; the limits do not depend on it). A transition is counted in the period of length $L$ when its pattern lies in the slots $0,\dots,L-1$, i.e. the next pattern starts at a slot $\le L$; this reproduces the paper's example $\alpha_7=\theta/7$ for Figure 4 (proved in the verification files). If no further pattern start exists (finitely many nonzero symbols, a null event) the decomposition stops and nothing more is counted. At $L=0$, $\alpha_0=0$ (division by zero).
-- source:
--   Zhang, Gong, Li, Wu & Zhang, Improving Blockchain Consistency by Assigning Weights to Random Blocks, arXiv:2107.10467v2, Definition 3.1 and the greedy decomposition, p.9; states, p.10; α_L, p.13

import Mathlib
import Definitions.Def_Ironclad_Model

namespace Ironclad

/-- The four characteristic patterns `σ₁, σ₂, σ₃, σ₄` of Definition 3.1, arXiv:2107.10467v2, p.9. -/
inductive Pat
  | s1
  | s2
  | s3
  | s4
  deriving DecidableEq, Repr

open Classical in
/-- The first slot `n ≥ s` whose symbol satisfies `p`, or `none` if there is none. -/
noncomputable def firstFrom (p : Sym → Prop) (x : ℕ → Sym) (s : ℕ) : Option ℕ :=
  if h : ∃ n, s ≤ n ∧ p (x n) then some (Nat.find h) else none

/-- One step of the greedy decomposition of Definition 3.1, arXiv:2107.10467v2, p.9, for a
pattern starting at slot `s` of the honest string `x`: the type of the pattern and the slot at
which the next pattern starts.

* `x s = h`, next nonzero symbol at `n`: the pattern is `{h}||{0}^k` with `k = n − s − 1`; it is
  `σ₁` if `k < Δ` (i.e. `n ≤ s + Δ`) and `σ₂` otherwise; the next pattern starts at `n`.
* `x s = H`, next `H` at `m ≤ s + Δ`: the pattern is `σ₃ = {H}||{0,h}^k` with `k = m − s − 1 < Δ`;
  the next pattern starts at `m`.
* `x s = H`, no `H` in the slots `s+1, …, s+Δ`: the pattern is `σ₄ = {H}||{0,h}^Δ||{0}^*`; the next
  pattern starts at the first nonzero symbol after slot `s + Δ` (the `h`s among the `Δ` slots
  after the `H` belong to the pattern).
* `x s = 0`, or the next start does not exist: `none`.

**Formalization Note** The σ₃ boundary is `k < Δ`, the reading under which the paper's
`P(σ₃) = q_H[1 − (1 − q_H)^Δ]` and `P(σ₄) = q_H(1 − q_H)^Δ` (p.9) partition the patterns that start
with `H`; Definition 3.1 prints `k ≤ Δ`. When the next start does not exist (finitely many
nonzero symbols, an event of probability zero), the decomposition stops. -/
noncomputable def step (Δ : ℕ) (x : ℕ → Sym) (s : ℕ) : Option (Pat × ℕ) :=
  match x s with
  | .zero => none
  | .h => (firstFrom (· ≠ .zero) x (s + 1)).map fun n => (if n ≤ s + Δ then .s1 else .s2, n)
  | .H =>
    match firstFrom (· = .H) x (s + 1) with
    | some m =>
      if m ≤ s + Δ then some (.s3, m)
      else (firstFrom (· ≠ .zero) x (s + Δ + 1)).map fun n => (.s4, n)
    | none => (firstFrom (· ≠ .zero) x (s + Δ + 1)).map fun n => (.s4, n)

/-- The start slot of the `k`-th pattern (from `0`) of the greedy decomposition of `x`,
arXiv:2107.10467v2, p.9: the decomposition starts at the first nonzero symbol, and each pattern
starts where the previous one ends. `none` once the decomposition has stopped. -/
noncomputable def start (Δ : ℕ) (x : ℕ → Sym) : ℕ → Option ℕ
  | 0 => firstFrom (· ≠ .zero) x 0
  | k + 1 => (start Δ x k).bind fun s => (step Δ x s).map Prod.snd

/-- The type of the `k`-th pattern (from `0`) of the decomposition of `x`. -/
noncomputable def pat (Δ : ℕ) (x : ℕ → Sym) (k : ℕ) : Option Pat :=
  (start Δ x k).bind fun s => (step Δ x s).map Prod.fst

/-- The length `|σ|` (number of slots) of the `k`-th pattern of the decomposition of `x`. -/
noncomputable def patLength (Δ : ℕ) (x : ℕ → Sym) (k : ℕ) : Option ℕ :=
  (start Δ x k).bind fun s => (start Δ x (k + 1)).map fun e => e - s

/-- The state entered after a pattern, arXiv:2107.10467v2, p.10: "State `S₀` is visited whenever
patterns `σ₂` or `σ₄` occurs [...] States `S₁` and `S₂` correspond to `σ₁` and `σ₃`". States are
`0, 1, 2 : Fin 3` for `S₀, S₁, S₂`. -/
def stateOf : Pat → Fin 3
  | .s1 => 1
  | .s2 => 0
  | .s3 => 2
  | .s4 => 0

/-- The state `X_k` of the embedded chain before the `k`-th pattern: `X₀ = S₀`, and
`X_{k+1}` is the state entered by the `k`-th pattern.

**Formalization Note** The initial state is `S₀` (the paper is silent; the limits do not depend
on it). After the decomposition has stopped the value `0` is junk. -/
noncomputable def state (Δ : ℕ) (x : ℕ → Sym) : ℕ → Fin 3
  | 0 => 0
  | k + 1 => ((pat Δ x k).map stateOf).getD 0

/-- The `k`-th pattern lies in the period of length `L`, i.e. in the slots `0, …, L − 1`: the next
pattern starts at a slot `≤ L`. -/
def EndsBy (Δ : ℕ) (x : ℕ → Sym) (k L : ℕ) : Prop :=
  ∃ e, start Δ x (k + 1) = some e ∧ e ≤ L

open Classical in
/-- `#_L(S_i −σ→ ·)`, arXiv:2107.10467v2, p.13: the number of transitions out of state `S_i` by
pattern `σ` within the period of length `L`.

**Formalization Note** A transition is counted in the period of length `L` when its pattern lies in
the slots `0, …, L − 1` (`EndsBy`). Starts are strictly increasing, so the `k`-th pattern ends after
slot `k` and only `k < L` can be counted. -/
noncomputable def cntTrans (Δ : ℕ) (x : ℕ → Sym) (L : ℕ) (i : Fin 3) (σ : Pat) : ℕ :=
  ((Finset.range L).filter fun k => EndsBy Δ x k L ∧ state Δ x k = i ∧ pat Δ x k = some σ).card

open Classical in
/-- `#_L(S₂ −σ₄→ S₀ −σ₂→ S₀)`, arXiv:2107.10467v2, p.13: the number of `σ₂` transitions out of `S₀`
within the period of length `L` whose preceding transition was `S₂ −σ₄→ S₀`. -/
noncomputable def cntTwoStep (Δ : ℕ) (x : ℕ → Sym) (L : ℕ) : ℕ :=
  ((Finset.range L).filter fun k => EndsBy Δ x (k + 1) L ∧ state Δ x k = 2 ∧
    pat Δ x k = some .s4 ∧ pat Δ x (k + 1) = some .s2).card

open Classical in
/-- `#_L S_i`, arXiv:2107.10467v2, Appendix .2.3, p.30: the number of visits to state `S_i` (the
sojourns in `S_i`) within the period of length `L`. -/
noncomputable def cntState (Δ : ℕ) (x : ℕ → Sym) (L : ℕ) (i : Fin 3) : ℕ :=
  ((Finset.range L).filter fun k => EndsBy Δ x k L ∧ state Δ x k = i).card

/-- `α_L`, arXiv:2107.10467v2, p.13: the total weight of the agreement blocks in the period of
length `L`, divided by `L`,
`α_L = (1/L)[#_L(S₀ −σ₂→ S₀) − #_L(S₂ −σ₄→ S₀ −σ₂→ S₀) + θ(#_L(S₀ −σ₄→ S₀) + #_L(S₁ −σ₄→ S₀))]`.

**Formalization Note** `#_L(S₀ −σ→ S₀)` is `cntTrans … 0 σ`, since `σ₂` and `σ₄` lead to `S₀`.
At `L = 0` the value is `0` (division by zero), which does not affect limits. -/
noncomputable def alphaL (Δ : ℕ) (θ : ℝ) (x : ℕ → Sym) (L : ℕ) : ℝ :=
  (1 / (L : ℝ)) * ((cntTrans Δ x L 0 .s2 : ℝ) - (cntTwoStep Δ x L : ℝ) +
    θ * ((cntTrans Δ x L 0 .s4 : ℝ) + (cntTrans Δ x L 1 .s4 : ℝ)))

/-- The length of the pattern of type `σ` starting at slot `t` (as a real number), and `0` if no
pattern of type `σ` starts at `t`; used for `E[|σ|]` (arXiv:2107.10467v2, p.9). -/
noncomputable def slotLen (Δ : ℕ) (x : ℕ → Sym) (t : ℕ) (σ : Pat) : ℝ :=
  match step Δ x t with
  | some (σ', e) => if σ' = σ then ((e - t : ℕ) : ℝ) else 0
  | none => 0

end Ironclad


