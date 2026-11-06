-- Prove2me | Definitions.Def_MemQueryFeas_IsNoiseAddition
-- name    : MemQueryFeas_IsNoiseAddition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:37:18.250194+00:00
-- url     : https://prove2.me/theorems/776692cb-aa69-4cf6-9cde-b5db4063c1ff
-- title:
--   NoiseAddition (Algorithm 1)
-- statement:
--   **NoiseAddition$(F,\delta)$** takes a subspace $F\in\mathrm{Gr}(k,d)$ and accuracies $\delta=(\delta^{(0)},\dots,\delta^{(N)})$, sets $F^{(N+1)}=F$ and, for $i=N,N-1,\dots,0$, samples
--   $$
--   F^{(i)}\sim\mathrm{Unif}\big(B(F^{(i+1)},\delta^{(i)})\big),
--   $$
--   returning $F^{(\le N)}=(F^{(0)},\dots,F^{(N)})$.
--
--   The predicate says that random variables $F^{(0)},\dots,F^{(N)}$ are such an output started at $F=F(G)$, with fresh randomness: for each $i$, conditionally on the input variable $G$ and on $F^{(i+1)},\dots,F^{(N)}$, the law of $F^{(i)}$ is $\mathrm{Unif}(B(c,\delta^{(i)}))$ with $c=F(G)$ if $i=N$ and $c=F^{(i+1)}$ otherwise.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Algorithm 1, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MemQueryFeas_unifBall
import Definitions.Def_MemQueryFeas_HasCondLaw

open MeasureTheory

namespace MemQueryFeas

/-- **NoiseAddition (Algorithm 1).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Algorithm 1, p.8 (PDF p.9): "Input: subspace `F`,
accuracies `δ = (δ^(0), …, δ^(N))`. Initialize `F^(N+1) ← F` and for `i = N, N − 1, …, 0` do Sample
`F^(i) ∼ Unif(B(F^(i+1), δ^(i)))`; Return `F^(≤N)`."

`IsNoiseAddition μ ν k G F δ N ch` says that `ch 0, …, ch N` is the output of NoiseAddition started
at `F(G)`: for each `i ≤ N`, conditionally on `G` and on `ch (i+1), …, ch N`, the law of `ch i` is
`Unif(B(c, δ_i))` (Haar law `ν` of `Gr(k,d)` restricted to the ball), with center `c = F(G)` if
`i = N` and `c = ch (i+1)` otherwise. The variable `G` collects everything sampled before the
procedure, so the procedure uses fresh randomness independent of it.

**Formalization Note.** Conditional laws are in the disintegration form `HasCondLaw`. The later
indices are passed as the sequence `j ↦ ch j` for `i < j ≤ N` (and `0` elsewhere). -/
def IsNoiseAddition {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ] {d : ℕ}
    (μ : Measure Ω) (ν : Measure (Op d)) (k : ℕ) (G : Ω → γ) (F : γ → Op d) (δ : ℕ → ℝ)
    (N : ℕ) (ch : ℕ → Ω → Op d) : Prop :=
  ∀ i ≤ N, HasCondLaw μ (ch i)
    (fun ω => (G ω, fun j : ℕ => if i < j ∧ j ≤ N then ch j ω else 0))
    (fun z => unifBall ν k (if i = N then F z.1 else z.2 (i + 1)) (δ i))

end MemQueryFeas


