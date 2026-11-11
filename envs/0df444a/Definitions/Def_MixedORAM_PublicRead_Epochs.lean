-- Prove2me | Definitions.Def_MixedORAM_PublicRead_Epochs
-- name    : MixedORAM_PublicRead_Epochs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:47:44.212375+00:00
-- url     : https://prove2.me/theorems/ef921125-cc22-4af6-92b1-f25025fbc000
-- title:
--   Dependency edges, epoch edge counts E_I and D_I, and the terminal reference experiments of §4.1 and Lemma A.6
-- statement:
--   A **dependency edge** joins two consecutive probes to the same cell (other cells may be probed in between) when the second probe is a read; it goes from the request making the first probe to the request making the read.
--
--   Fix an endpoint $e$: the prefix has $e$ requests and the terminal block follows it. An **epoch** of length $\ell$ at offset $s$ is the block of the $\ell$ requests ending $s$ requests before the end of the prefix (the paper's $[e-s-\ell+1,e-s]$); its **younger span** is the following $s$ requests of the prefix. $E_I$ counts the edges from the epoch into its younger span and $D_I$ the edges from the epoch into the terminal block.
--
--   A **terminal experiment** with request law $\delta$, endpoint set $V$, event $G_0$ and terminal law: draw $e$ uniformly from $V$, a prefix of length $e$ from the IID workload, keep it only if $G_0$ holds, append a terminal block drawn from the terminal law, and run the implementation. Expectations are conditioned on $G_0$.
--
--   The **reference experiment** of §4.1: $V=\{\lceil N/2\rceil,\dots,N-1\}$, window $\omega=\lfloor n/(128p)\rfloor$, shortest epoch length $\ell_0=\lceil C(m+1)/p\rceil$, the safe set $V_e$ of addresses not written in the last $\omega$ requests of the prefix, $G_0=\{|V_e|\ge 15n/16\}$, and the terminal block one public read of an address uniform in $V_e$.
--
--   **Formalization Note** Positions are $0$-based: the prefix occupies positions $0,\dots,e-1$ and the terminal block starts at $e$. Preprocessing probes precede every request, so they never start an edge from a request and are left out of the edge count. The conditional expectation is the ratio of the weight on $G_0$ to the probability of $G_0$.
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), pp. 9–10, §4.1; p. 18, Appendix A.4, Lemma A.6

import Mathlib
import Definitions.Def_MixedORAM_PublicRead_Workload

set_option autoImplicit false

namespace MixedORAM.PublicRead

/-- Every probe of a trace, in order, tagged with the (`0`-based) position of the request that made
it. -/
def indexedProbes {a : ℕ} (tr : ReqTrace a) : List (ℕ × Probe a) :=
  tr.zipIdx.flatMap (fun pt => pt.1.map (fun q => (pt.2, q)))

/-- The **dependency edges** of a trace (§4.1, p. 9: "A dependency edge joins two consecutive
physical probes to the same cell (potentially with probes to other cells in between) when the second
is a read"): for every read probe of a request that has an earlier request probe to the same cell,
the pair (position of the request making the latest such earlier probe, position of the request
making the read). Preprocessing precedes every request, so a read whose latest earlier probe to its
cell is a preprocessing probe has no edge from any request, and preprocessing probes are left out. -/
def depEdges {a : ℕ} (tr : ReqTrace a) : List (ℕ × ℕ) :=
  let L := indexedProbes tr
  (List.range L.length).filterMap fun j =>
    match L[j]? with
    | some (t, q) =>
        if q.isWrite then none
        else ((L.take j).reverse.find? (fun x => decide (x.2.addr = q.addr))).map (fun x => (x.1, t))
    | none => none

/-- Position `t` lies in the epoch of length `ℓ` ending `s` positions before the endpoint `e`:
`0`-based positions `e − s − ℓ, …, e − s − 1`, i.e. the paper's `1`-based positions
`[e − s − ℓ + 1, e − s]` (the prefix has `e` requests, at `0`-based positions `0, …, e − 1`). -/
abbrev inEpoch (e s ℓ t : ℕ) : Prop := t + s < e ∧ e ≤ t + s + ℓ

/-- Position `t` lies in the younger span of that epoch: `0`-based `e − s, …, e − 1` (the paper's
`[e − s + 1, e]`). -/
abbrev inYounger (e s t : ℕ) : Prop := e ≤ t + s ∧ t < e

/-- `E_I`: the number of dependency edges from the epoch `(s, ℓ)` (relative to the endpoint `e`)
into its younger requests (§4.1, p. 9). -/
def edgesE {a : ℕ} (e s ℓ : ℕ) (tr : ReqTrace a) : ℕ :=
  ((depEdges tr).filter (fun uv => decide (inEpoch e s ℓ uv.1 ∧ inYounger e s uv.2))).length

/-- `D_I`: the number of dependency edges from the epoch `(s, ℓ)` into the terminal block, i.e. the
requests after the prefix of length `e` (§4.1, p. 9). -/
def edgesD {a : ℕ} (e s ℓ : ℕ) (tr : ReqTrace a) : ℕ :=
  ((depEdges tr).filter (fun uv => decide (inEpoch e s ℓ uv.1 ∧ e ≤ uv.2))).length

/-- The probes of the terminal block: all requests after the prefix of length `e`. -/
def terminalProbes {a w : ℕ} (e : ℕ) (res : List (StepRecord a w)) : ℕ :=
  ((res.drop e).map (·.probes.length)).sum

open Classical in
/-- The unnormalized weight of a function `f` in a **terminal experiment** (§4.1, p. 9; Lemma A.6,
p. 18): draw the endpoint `e` uniformly from the finite set `V`, the prefix `u` of length `e` from
the IID workload with request law `δ`, keep only prefixes in the event `G₀ e u`, draw the terminal
block `τ` from `term e u`, and run `I` on `u ++ τ` from the initial array `A₀`. -/
noncomputable def termMass {n w m a : ℕ} (I : Impl n w m a) (A₀ : Fin n → BitVec w)
    (δ : PMF (Request n w)) (V : Finset ℕ) (G₀ : ℕ → List (Request n w) → Prop)
    (term : ℕ → List (Request n w) → PMF (List (Request n w)))
    (f : ℕ → List (Request n w) → List (StepRecord a w) → ENNReal) : ENNReal :=
  ∑ e ∈ V, (V.card : ENNReal)⁻¹ * ∑' u, iidList δ e u *
    (if G₀ e u then ∑' τ, term e u τ * ∑' res, I.exec A₀ (u ++ τ) res * f e u res else 0)

/-- The probability of `G₀` in the terminal experiment. -/
noncomputable def termProbG {n w m a : ℕ} (I : Impl n w m a) (A₀ : Fin n → BitVec w)
    (δ : PMF (Request n w)) (V : Finset ℕ) (G₀ : ℕ → List (Request n w) → Prop)
    (term : ℕ → List (Request n w) → PMF (List (Request n w))) : ENNReal :=
  termMass I A₀ δ V G₀ term (fun _ _ _ => 1)

/-- The expectation of `f` in the terminal experiment **conditioned on `G₀`**. -/
noncomputable def termExp {n w m a : ℕ} (I : Impl n w m a) (A₀ : Fin n → BitVec w)
    (δ : PMF (Request n w)) (V : Finset ℕ) (G₀ : ℕ → List (Request n w) → Prop)
    (term : ℕ → List (Request n w) → PMF (List (Request n w)))
    (f : ℕ → List (Request n w) → List (StepRecord a w) → ENNReal) : ENNReal :=
  termMass I A₀ δ V G₀ term f / termProbG I A₀ δ V G₀ term

/-! The reference experiment of §4.1 (p. 9). -/

/-- The window length `ω = ⌊n/(128p)⌋` (§4.1, p. 9). -/
noncomputable def omegaW (n : ℕ) (p : ℝ) : ℕ := ⌊(n : ℝ) / (128 * p)⌋₊

/-- The shortest epoch length `ℓ₀ = ⌈C(m + 1)/p⌉` (§4.1, p. 9). -/
noncomputable def ell0 (C : ℝ) (m : ℕ) (p : ℝ) : ℕ := ⌈C * ((m : ℝ) + 1) / p⌉₊

/-- The endpoint range `V = {⌈N/2⌉, …, N − 1}` (§4.1, p. 9). -/
def endpoints (N : ℕ) : Finset ℕ := Finset.Icc ((N + 1) / 2) (N - 1)

/-- The **safe set** `V_e`: the addresses not written in the last `ω` requests of the prefix `u`
(all of `u` if it is shorter) (§4.1, p. 9). -/
def safeSet {n w : ℕ} (ω : ℕ) (u : List (Request n w)) : Finset (Fin n) :=
  Finset.univ.filter fun x =>
    (u.drop (u.length - ω)).all (fun r => !(decide (r.op.kind = .write) && decide (r.op.addr = x)))

/-- The event `G₀ = {|V_e| ≥ 15n/16}` (§4.1, p. 9). -/
def refG0 {n w : ℕ} (ω : ℕ) (_e : ℕ) (u : List (Request n w)) : Prop :=
  15 * (n : ℝ) / 16 ≤ ((safeSet ω u).card : ℝ)

/-- The terminal of the reference experiment: one public read of an address uniform in `V_e`
(the empty block if `V_e = ∅`, which never happens under `G₀` for `n ≥ 1`). -/
noncomputable def refTerm {n w : ℕ} (ω : ℕ) (_e : ℕ) (u : List (Request n w)) :
    PMF (List (Request n w)) :=
  if h : (safeSet ω u).Nonempty then
    (PMF.uniformOfFinset (safeSet ω u) h).map (fun x => [⟨.pub, .read x⟩])
  else PMF.pure []

/-- The expectation `E_ref[f]` over the **reference terminal experiment** of §4.1 (p. 9) on the
workload `wl` with private probability `p` and horizon `N`: the endpoint `e` uniform in
`V = {⌈N/2⌉, …, N − 1}`, the prefix of length `e` from the workload conditioned on `G₀`, a terminal
public read of an address uniform in `V_e`, and the implementation's randomness. -/
noncomputable def refExp {n w m a : ℕ} [NeZero n] (I : Impl n w m a) (A₀ : Fin n → BitVec w)
    (wl : Workload) (p : ℝ) (N : ℕ)
    (f : ℕ → List (Request n w) → List (StepRecord a w) → ENNReal) : ENNReal :=
  termExp I A₀ (reqDist wl n w p) (endpoints N) (refG0 (omegaW n p)) (refTerm (omegaW n p)) f

end MixedORAM.PublicRead


