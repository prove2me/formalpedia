-- Prove2me | Definitions.Def_IIDMatchHard_Adjusted
-- name    : IIDMatchHard_Adjusted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:06:11.822199+00:00
-- url     : https://prove2.me/theorems/6388112f-2f6f-4511-83e8-eb82dc47ab08
-- title:
--   The adjusted Poisson model of $I(G,\lambda)$: blocked arrivals, Poisson values, $\widehat{\mathrm{OPT}}$, net gains, $P_e$, $Q^s_{e,d}$, $\theta_t$, $\Gamma_e$, $\Phi_G$
-- statement:
--   Fix a finite simple graph $G=(V,E)$ with $n=|V|$, $m=|E|$, and $\lambda>0$. In the **adjusted Poisson model** of $I(G,\lambda)$ (Algorithm 2), arrivals come from a Poisson process of rate $R=n+2m\lambda$, with types drawn i.i.d. with probabilities $\lambda_y/R$. The online arrivals are the $K(1)$ points in $[0,1]$. An edge arrival $f^\pm$ is **blocked**, meaning its neighbor set is empty, if some earlier arrival has an edge type $e^s$, blocked or not, with $e$ sharing an endpoint with $f$. Vertex arrivals are never blocked.
--
--   1. $\widehat M_\pi$ is the number of matches of a policy $\pi$ run in the adjusted model. The policy sees the types, not the times. $\mathbb E[\widehat M_\pi]$ is its **Poisson value**, and $\widehat{\mathrm{OPT}}=\sup_\pi\mathbb E[\widehat M_\pi]$.
--   2. For a policy $\pi$ of $I(G,\lambda)$, the **transferred** policy rejects every blocked arrival and otherwise takes the decision $\pi$ takes in $I(G,\lambda)$ (App. B.3: "In the adjusted model, π takes the same decisions as in I(G, λ), except that it rejects every blocked arrival").
--   3. $h_d(t)=\mathbb P(\mathrm{Pois}(1-t)\le d-1)$, which equals $0$, $e^{t-1}$ and $(2-t)e^{t-1}$ for $d=0,1,2$.
--   4. $X_u(t)$ is the number of vertex arrivals of $u$ among the first $K(t)$ arrivals. $D_e(t)$ is the event that one of these arrivals has an edge type of an edge incident to an endpoint of $e$. The number of blocked arrivals among $y_1,\dots,y_{K(1)}$ is also defined.
--   5. For a hypothetical arrival of type $e^s$ after $y_1,\dots,y_{K(t)}$: $P_e(t)$ is the probability that it is not blocked, event (I). $Q^s_{e,d}(t)$ is the conditional probability, given (I), that $\pi$ matches it to some $w^s$, $w\in e$, whose pair $\{w^+,w^-\}$ has $d$ free vertices, event (II).
--   6. $\theta_t(u)$ is the sign of the free vertex of $u$'s pair if exactly one is free after $\pi$ processes $y_1,\dots,y_{K(t)}$, and $+$ otherwise. For $e=(u,v)$,
--   $$\Gamma_e(t)=2h_2(t)\,\mathbf 1[\min\{X_u(t),X_v(t)\}=0]+h_1(t)\,\mathbf 1[\min\{X_u(t),X_v(t)\}=1].$$
--   7. $$\Phi_G(x)=\Big(2-\frac3e\Big)n+\Big(\frac1e+\frac9{e^2}\Big)\lambda m+\Big(\frac2e-\frac5{e^2}\Big)\lambda x.$$
--
--   These quantities express the Poisson value of a policy in Lemmas 3.3–3.9.
--
--   **Formalization Note** The law is that of `Def_IIDMatchHard_Poisson` with $R=n+2m\lambda$ and $p=\lambda_y/R$. Expectations of the nonnegative, bounded counts and of $\Gamma_e$ are lower Lebesgue integrals converted to reals. $Q^s_{e,d}(t)$ is a ratio of probabilities; $P_e(t)>0$ for $\lambda>0$. $P_e$ is computed for $e^+$, since blocking does not depend on the sign. $h_d$ is the finite Poisson sum $\sum_{j<d}e^{-(1-t)}(1-t)^j/j!$, and $e=\exp 1$.
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), §3.2, pp.6–8 (PDF pp.7–9), Algorithm 2; App. B.2, p.15; App. B.3, p.16; App. B.5, p.18; Lemma 3.6, p.9

import Definitions.Def_IIDMatchHard_CutInstance
import Definitions.Def_IIDMatchHard_Poisson

set_option autoImplicit false

namespace IIDMatchHard

open MeasureTheory ProbabilityTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **rule for blocked arrivals** of the adjusted Poisson model (§3.2, p.6 (PDF p.7); Algorithm 2, p.7):
after the history `h`, an arrival of edge type `f^±` is blocked iff some earlier arrival in `h`
has an edge type `e^s` (blocked or not) whose edge `e` shares an endpoint with `f`. Vertex
arrivals are never blocked.

**Formalization Note.** "We will block any future edge arrival with type f⁺ or f⁻ when f is an
edge that is incident to u or v; the rule applies even when e^s itself is blocked" (p.6): the
condition reads only the types of `h`, never the policy's decisions. -/
def Blocked (G : SimpleGraph V) (h : List (IType G)) : IType G → Prop
  | .vtx _ => False
  | .edge f _ => ∃ y ∈ h, ∃ (e : G.edgeSet) (s : Bool), y = .edge e s ∧
      ∃ w, w ∈ (e : Sym2 V) ∧ w ∈ (f : Sym2 V)

open Classical in
/-- The neighbor sets of the **adjusted** model (Algorithm 2, line 8, p.7): a blocked arrival has
no neighbors, every other arrival has its neighbors in `I(G, λ)`. -/
noncomputable def adjNbr (G : SimpleGraph V) (h : List (IType G)) (y : IType G) :
    Finset (V × Bool) :=
  if Blocked G h y then ∅ else cutNbr G y

/-- The law of the adjusted Poisson model of `I(G, λ)` (Algorithm 2, p.7 (PDF p.8)): a Poisson
process of rate `R = n + 2mλ`, each arrival's type drawn independently with probability
`λ_y / R`. -/
noncomputable def cutLaw (G : SimpleGraph V) (lam : ℝ) : Measure (Sample (IType G)) :=
  poissonLaw (totalRate G lam) (cutInst G lam).p

/-- `M̂_π`: the number of matches of the policy `π` run in the adjusted Poisson model, on the
`K(1)` arrivals in `[0, 1]` with the adjusted neighbor sets (the policy sees the types, not the
arrival times). Teng–Yang (sha256 f0193d92…), §3.2, p.7 (PDF p.8). -/
noncomputable def adjMatches (G : SimpleGraph V) (π : Policy (V × Bool) (IType G))
    (ω : Sample (IType G)) : ℕ :=
  numMatches (adjNbr G) π (firstTypes ω (count ω 1))

/-- The **Poisson value** `E[M̂_π]` of a policy `π` (p.7 (PDF p.8)).

**Formalization Note.** The expectation of the nonnegative count is a lower Lebesgue integral,
converted to a real number; the count is at most `2n`, so the integral is finite. -/
noncomputable def poissonValue (G : SimpleGraph V) (lam : ℝ)
    (π : Policy (V × Bool) (IType G)) : ℝ :=
  (∫⁻ ω, (adjMatches G π ω : ENNReal) ∂ cutLaw G lam).toReal

/-- `ÔPT = sup_π E[M̂_π]`, the optimal Poisson value over all online policies (p.7 (PDF p.8)),
a supremum over deterministic policies (bounded above by `2n`). -/
noncomputable def optHat (G : SimpleGraph V) (lam : ℝ) : ℝ :=
  ⨆ π : Policy (V × Bool) (IType G), poissonValue G lam π

open Classical in
/-- The **transferred** policy of a policy `π` for `I(G, λ)`, for the adjusted model: on the
history `h`, it rejects a blocked arrival, and otherwise takes the decision that `π` takes on the
same arrival in `I(G, λ)` (replaying `π` on `h` in the unadjusted model): it proposes the vertex
`π` matches there, and rejects if `π` rejects there. Teng–Yang (sha256 f0193d92…), App. B.3,
p.16 (PDF p.17): "In the adjusted model, π takes the same decisions as in I(G, λ), except that it
rejects every blocked arrival."

**Formalization Note.** This is how Lemma 3.3 runs a policy `π` "for `I(G, λ)`" in the adjusted
model; the proof of Lemma 3.3 shows these decisions are feasible there. -/
noncomputable def transfer (G : SimpleGraph V) (π : Policy (V × Bool) (IType G)) :
    Policy (V × Bool) (IType G) :=
  fun h _ y =>
    if Blocked G h y then none
    else
      match π h (matched (static (cutNbr G)) π h) y with
      | some u => if u ∈ cutNbr G y ∧ u ∉ matched (static (cutNbr G)) π h then some u else none
      | none => none

/-- `h_d(t) = P(Pois(1 − t) ≤ d − 1)`, the expected **net gain** of matching an edge arrival at
time `t` to a vertex whose pair has `d` free vertices (p.7 (PDF p.8)), written as
`∑_{j < d} e^{−(1−t)} (1 − t)^j / j!`. For `t ∈ [0, 1]` it is `0`, `e^{t−1}`, `(2 − t)e^{t−1}`
for `d = 0, 1, 2`.

**Formalization Note.** `d − 1` is never computed: the event `Pois(1 − t) ≤ d − 1` is the union of
`{Pois(1 − t) = j}` over `j < d`, empty for `d = 0`; `e^{−r} r^j / j!` is the Poisson probability
of `j` for the rate `r = 1 − t ≥ 0` (`t ≤ 1`). -/
noncomputable def hNet (d : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range d, Real.exp (-(1 - t)) * (1 - t) ^ j / (j.factorial : ℝ)

/-- `X_u(t)`: the number of vertex arrivals of type `u` among the first `K(t)` arrivals
(p.8 (PDF p.9)). -/
noncomputable def vtxCount (G : SimpleGraph V) (ω : Sample (IType G)) (t : ℝ) (u : V) : ℕ :=
  (firstTypes ω (count ω t)).count (.vtx u)

/-- `D_e(t)`: the event that some arrival among `y_1, …, y_{K(t)}` has type `f⁺` or `f⁻` for an
edge `f` incident to an endpoint of `e` (App. B.2, p.15 (PDF p.16)). -/
def blockEvent (G : SimpleGraph V) (e : Sym2 V) (t : ℝ) : Set (Sample (IType G)) :=
  {ω | ∃ k < count ω t, ∃ (f : G.edgeSet) (s : Bool), arrType ω k = .edge f s ∧
      ∃ w, w ∈ e ∧ w ∈ (f : Sym2 V)}

open Classical in
/-- The number of **blocked arrivals** among `y_1, …, y_{K(1)}` (Lemma B.2(b), p.15 (PDF p.16)):
the arrivals `k` (0-based) blocked after the history `y_1, …, y_k` of the earlier arrivals. -/
noncomputable def blockedCount (G : SimpleGraph V) (ω : Sample (IType G)) : ℕ :=
  ((List.range (count ω 1)).filter fun k => decide (Blocked G (firstTypes ω k) (arrType ω k))).length

/-- `P_e(t)`: the probability that a hypothetical arrival of edge type `e^s` following
`y_1, …, y_{K(t)}` is not blocked, event (I) of p.7 (PDF p.8).

**Formalization Note.** Blocking does not depend on the sign `s`; the definition uses `e⁺`. -/
noncomputable def probUnblocked (G : SimpleGraph V) (lam : ℝ) (e : G.edgeSet) (t : ℝ) : ℝ :=
  (cutLaw G lam {ω | ¬ Blocked G (firstTypes ω (count ω t)) (.edge e true)}).toReal

/-- The free vertices of the pair `{w⁺, w⁻}` of `w` when the matched set is `S`. -/
def pairFree (S : Finset (V × Bool)) (w : V) : Finset (V × Bool) :=
  ({(w, true), (w, false)} : Finset (V × Bool)).filter fun x => x ∉ S

/-- Event (I) ∧ (II) of p.7: a hypothetical arrival of edge type `e^s` following
`y_1, …, y_{K(t)}` is not blocked, and the policy `π` (run in the adjusted model on
`y_1, …, y_{K(t)}`) matches it to some `w^s`, `w ∈ e`, whose pair `{w⁺, w⁻}` has exactly `d`
free vertices before the match. -/
def MatchEvent (G : SimpleGraph V) (π : Policy (V × Bool) (IType G)) (e : G.edgeSet) (s : Bool)
    (d : ℕ) (t : ℝ) : Set (Sample (IType G)) :=
  {ω | ∃ x, π (firstTypes ω (count ω t)) (matched (adjNbr G) π (firstTypes ω (count ω t)))
        (.edge e s) = some x ∧
      x ∈ adjNbr G (firstTypes ω (count ω t)) (.edge e s) ∧
      x ∉ matched (adjNbr G) π (firstTypes ω (count ω t)) ∧
      (pairFree (matched (adjNbr G) π (firstTypes ω (count ω t))) x.1).card = d}

/-- `Q^s_{e,d}(t)`: the conditional probability of (II) given (I) (p.7 (PDF p.8)): the probability
of `MatchEvent` divided by `P_e(t)`.

**Formalization Note.** `P_e(t) > 0` for `λ > 0` (Lemma B.2(a)), so the division is the
conditional probability. -/
noncomputable def probMatch (G : SimpleGraph V) (lam : ℝ) (π : Policy (V × Bool) (IType G))
    (e : G.edgeSet) (s : Bool) (d : ℕ) (t : ℝ) : ℝ :=
  (cutLaw G lam (MatchEvent G π e s d t)).toReal / probUnblocked G lam e t

/-- `θ_t(u)`: if the pair of `u` has exactly one free vertex after `π` processes
`y_1, …, y_{K(t)}` in the adjusted model, the sign of this vertex; otherwise `+` (`true`).
App. B.5, p.18 (PDF p.19). -/
noncomputable def theta (G : SimpleGraph V) (π : Policy (V × Bool) (IType G))
    (ω : Sample (IType G)) (t : ℝ) (u : V) : Bool :=
  if (u, true) ∉ matched (adjNbr G) π (firstTypes ω (count ω t)) ∧
      (u, false) ∈ matched (adjNbr G) π (firstTypes ω (count ω t)) then true
  else if (u, false) ∉ matched (adjNbr G) π (firstTypes ω (count ω t)) ∧
      (u, true) ∈ matched (adjNbr G) π (firstTypes ω (count ω t)) then false
  else true

/-- `Γ_e(t) = 2h₂(t)·1[min{X_u(t), X_v(t)} = 0] + h₁(t)·1[min{X_u(t), X_v(t)} = 1]` for the edge
`e = (u, v)` (App. B.5, p.18 (PDF p.19)). -/
noncomputable def gammaE (G : SimpleGraph V) (ω : Sample (IType G)) (t : ℝ) (u v : V) : ℝ :=
  2 * hNet 2 t * (if min (vtxCount G ω t u) (vtxCount G ω t v) = 0 then 1 else 0) +
    hNet 1 t * (if min (vtxCount G ω t u) (vtxCount G ω t v) = 1 then 1 else 0)

/-- `E[Γ_e(t)]`, the expectation of the nonnegative bounded `Γ_e(t)` (as a lower Lebesgue
integral converted to a real number). -/
noncomputable def expGamma (G : SimpleGraph V) (lam : ℝ) (t : ℝ) (u v : V) : ℝ :=
  (∫⁻ ω, ENNReal.ofReal (gammaE G ω t u v) ∂ cutLaw G lam).toReal

/-- The affine function `Φ_G(x) = (2 − 3/e)n + (1/e + 9/e²)λm + (2/e − 5/e²)λx` of Lemma 3.6
(p.9 (PDF p.10)), with `n = |V|`, `m = |E|` and `e = exp 1`. -/
noncomputable def Phi (G : SimpleGraph V) (lam : ℝ) (x : ℝ) : ℝ :=
  (2 - 3 / Real.exp 1) * (Fintype.card V : ℝ) +
    (1 / Real.exp 1 + 9 / Real.exp 1 ^ 2) * lam * (numEdges G : ℝ) +
    (2 / Real.exp 1 - 5 / Real.exp 1 ^ 2) * lam * x

end IIDMatchHard


