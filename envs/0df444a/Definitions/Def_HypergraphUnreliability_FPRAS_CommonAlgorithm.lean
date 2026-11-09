-- Prove2me | Definitions.Def_HypergraphUnreliability_FPRAS_CommonAlgorithm
-- name    : HypergraphUnreliability_FPRAS_CommonAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:45.677926+00:00
-- url     : https://prove2.me/theorems/69301d67-341e-447e-b25f-a5f680eac372
-- title:
--   The common-probability finite-bit algorithm of §§7–8
-- statement:
--   For a common failure probability $p=A/B$, the algorithm of §§7–8 is as follows. Discard empty and singleton edges and repeated incidences, keeping parallel labels. Return $0$ if $n\le1$, $1$ if the input is disconnected, $0$ at $p=0$, and $1$ at $p=1$.
--
--   Otherwise, with $b$ the binary length of the written $B$, set $H_0=b+1$, $N=\binom n2$, $\eta=\varepsilon/(128Nm)$, and take $T^\prime$ from Lemma 7.1. Put
--   $$L=\Bigl\lceil\frac{128Nm^2H_0^2}{\varepsilon}\Bigr\rceil,\quad h=\frac{T^\prime}{L},\quad S=\Bigl\lceil\frac{128N}{\varepsilon^2}\Bigr\rceil.$$
--   Take the least $q\ge1$ with $2^q\ge128N[N+L(2m+2)]/\varepsilon$ and the least positive odd $r$ with $2^{-r}\le\delta$. Run the sampler at unit rates with $\Lambda=\lambda$, and return $\min\{1,p^\lambda M_*\}$ with $M_*$ the median.
--
--   Lemma 8.2 is the cost statement for this procedure.
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), §§7–8, pp. 8–12; §2, p. 4

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Instance
import Definitions.Def_HypergraphUnreliability_FPRAS_EulerSampler
import Definitions.Def_HypergraphUnreliability_FPRAS_RationalApprox

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

namespace CommonInstance

variable (x : CommonInstance)

/-- The edges kept by the preprocessing of §1.1, p. 2: repeated incidences removed, empty and
singleton edges discarded, parallel labels retained. -/
def retained : List (Finset (Fin x.graph.n)) :=
  (x.graph.edges.map List.toFinset).filter (fun e => 2 ≤ e.card)

/-- `m = |E|` after preprocessing. -/
def m : ℕ := x.retained.length

/-- The preprocessed hypergraph. -/
def H : LabeledHypergraph x.graph.n (Fin x.m) where
  inc e := x.retained.get e

/-- `N = binom(n, 2)`, as a rational number. -/
def N : ℚ := (x.graph.n.choose 2 : ℕ)

/-- `H₀ = b + 1`, with `b` the binary length of the written denominator `B` of `p` (§7, p. 8). -/
def H₀ : ℕ := Nat.size x.p.den + 1

/-- `η = ε / (128 N m)`, (7.2), p. 9. -/
def η : ℚ := x.ε.val / (128 * x.N * x.m)

/-- `T′` from Lemma 7.1 at tolerance `η`. -/
def T' : ℚ := logLower x.p.num x.p.den x.η

/-- `L = ⌈128 N m² H₀² / ε⌉`, (7.2), p. 9. -/
def L : ℕ := ⌈128 * x.N * (x.m : ℚ) ^ 2 * (x.H₀ : ℚ) ^ 2 / x.ε.val⌉₊

/-- The parameters of the common-probability sampler, (7.2), (7.3), (7.5) and (8.1): unit rates,
`Λ = λ`, `h = T′/L`, the least `q ≥ 1` with `2^q ≥ 128 N [N + L(2m+2)] / ε`,
`S = ⌈128 N / ε²⌉`, and the least positive odd `r` with `2^{-r} ≤ δ`. -/
def params : SamplerParams x.graph.n x.m where
  H := x.H
  r := fun _ => 1
  Λ := (x.H.minCutCount : ℚ)
  h := x.T' / x.L
  L := x.L
  q := bitWidth (128 * x.N * (x.N + x.L * (2 * x.m + 2)) / x.ε.val)
  S := ⌈128 * x.N / x.ε.val ^ 2⌉₊
  b := oddBatchCount x.δ.val

/-- The case in which the sampler runs, (2.2), p. 4. -/
def IsSamplingCase : Prop :=
  x.H.Standing ∧ 0 < x.p.num ∧ x.p.num < x.p.den

/-- The output of the common-probability algorithm on the random bit stream `ω`: the exact boundary
answers (§2, p. 4), and otherwise `min{1, p^λ M_*}`, (8.2), p. 11. -/
def output (ω : ℕ → Bool) : ℚ :=
  if x.graph.n ≤ 1 then 0
  else if ¬ x.H.IsConnected then 1
  else if x.p.num = 0 then 0
  else if x.p.num = x.p.den then 1
  else min 1 (x.p.val ^ x.H.minCutCount * x.params.medianOfBatches ω)

end CommonInstance

end HypergraphUnreliability.FPRAS


