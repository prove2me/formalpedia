-- Prove2me | Definitions.Def_PottsRapidMixing_RecordLaws
-- name    : PottsRapidMixing_RecordLaws
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:40.417628+00:00
-- url     : https://prove2.me/theorems/6ed7ebc4-e537-438b-9958-be8f257c5b8f
-- title:
--   The record laws $P$ and $Q$
-- statement:
--   Run Algorithm 1 in one of two cases. *Spin case:* for a spin law $\nu$, sample $\sigma\sim\nu$, then $H\sim\mathbb P_{\sigma,M}$, and explore $H$; set $X=\sigma$, $\rho=\mu$. *Edge case:* for an edge law $\nu$, sample $\omega\sim\nu$ and explore $\omega$; set $X=\omega$, $\rho=\phi$. $P$ is the law of the record, and $\nu_h$ is the law of $X$ given the history $h$. The law $Q$ draws the outcome of each test of $e$ after history $h$ as follows:
--
--   1. If $P(\mathcal R_j=h)>0$ and the test is good: in the spin case sample $\tau=\sigma_{V\setminus F}$ from $\nu_h$, then $\sigma_F$ from $\mu^\tau_{F^+}$, and include $e$ with probability $\mathbb P_{\sigma,M}(e\in H)$; in the edge case sample $\eta=\omega_{E\setminus E(F^+)}$ from $\nu_h$, then $\omega_{E(F^+)}$ from $\phi^\zeta_{F^+}$, where $\zeta$ is the partition of $\partial F^+$ induced by $\eta$, and record $\omega_e$.
--   2. If $P(\mathcal R_j=h)>0$ and the test is not good, the outcome has the same distribution as under $P$.
--   3. If $P(\mathcal R_j=h)=0$, the test records $(e,0)$.
--
--   `SpinSubcritical` and `EdgeSubcritical` say that a radius $R$ gives (3.1), resp. (3.6), at level $s$ on every forward tree. `ComponentTails` is the pair of conclusions (3.19), (3.20) for one law $Q$.
--
--   The law $Q$ is the intermediate process: subcritical at good tests, and close to $P$ in relative entropy.
--
--   **Formalization Note** Given $X$, distinct edges are independent and each edge is tested at most once, so $P(\mathcal R_j=h)=\sum_x\nu(x)\prod_{(e,b)\in h}\mathrm{lik}(x;e,b)$. $Q$ of a record is the product of its conditional outcome probabilities. The laws $\mu^\tau_{F^+}$ and $\phi^\zeta_{F^+}$ are stated on $F^+$ as a graph on $V$: the former conditions the Potts law of $F^+$ on the spins off $F$, the latter takes the open edges of $\eta$ as the identification graph.
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Definitions 3.6–3.7, p.18; Lemmas 3.4–3.5, pp.17–18; Lemma 3.11, p.21

import Mathlib
import Definitions.Def_PottsRapidMixing_ChainM
import Definitions.Def_PottsRapidMixing_Exploration

open scoped Classical

namespace PottsRapidMixing

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {X : Type*} [Fintype X]

/-- `P(R_j = h)`, for `X ∼ ν` and a likelihood `lik x (e, b)` of the outcome `b` of a test of `e` given
`x` (Definition 3.6, Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.18).

**Formalization Note.** Given `x`, the outcomes of distinct edges are independent and each edge is
tested at most once, so the likelihood of a history is the product over its entries. -/
noncomputable def histProb (ν : X → ℝ) (lik : X → G.edgeSet × Bool → ℝ)
    (h : List (G.edgeSet × Bool)) : ℝ :=
  ∑ x, ν x * (h.map (lik x)).prod

/-- `ν_h`, the conditional law of `X` given the history `h` (Definition 3.6, arXiv:2610.42059, p.18). -/
noncomputable def posterior (ν : X → ℝ) (lik : X → G.edgeSet × Bool → ℝ)
    (h : List (G.edgeSet × Bool)) (x : X) : ℝ :=
  ν x * (h.map (lik x)).prod / histProb ν lik h

/-- The law `Q_h` of the outcome of the next test (Definition 3.7, arXiv:2610.42059, p.18), the
probability of the outcome `b` after the history `h`, with its three cases. `inner c d x` is the
probability that the good test `d` from the state `c` succeeds, when the exterior is taken from `x`
and the interior redrawn from the reference law. -/
noncomputable def qStep (ord : ExplOrder G) (R : ℕ) (ν : X → ℝ) (lik : X → G.edgeSet × Bool → ℝ)
    (inner : Cfg G → G.Dart → X → ℝ) (h : List (G.edgeSet × Bool)) (b : Bool) : ℝ :=
  match nextDart ord (cfgOf ord h) with
  | none => 0
  | some d =>
    if 0 < histProb ν lik h then
      if IsGoodTest (cfgOf ord h).graph (cfgOf ord h).U d.fst d.snd R then
        if b = true then ∑ x, posterior ν lik h x * inner (cfgOf ord h) d x
        else 1 - ∑ x, posterior ν lik h x * inner (cfgOf ord h) d x
      else histProb ν lik (h ++ [(dartEdge d, b)]) / histProb ν lik h
    else if b = true then 0 else 1

/-- `Q(R = ρ)`: the probability of a record under Definition 3.7 (arXiv:2610.42059, p.18), the product of
the conditional outcome probabilities along it. -/
noncomputable def qRecord (ord : ExplOrder G) (R : ℕ) (ν : X → ℝ)
    (lik : X → G.edgeSet × Bool → ℝ) (inner : Cfg G → G.Dart → X → ℝ)
    (ρ : List (G.edgeSet × Bool)) : ℝ :=
  ∏ i : Fin ρ.length, qStep ord R ν lik inner (ρ.take i) (ρ.get i).2

/-- `Q(R_j = h)`: the mass under `Q` of the complete records that extend `h`. -/
noncomputable def qPrefix (ord : ExplOrder G) (R : ℕ) (ν : X → ℝ)
    (lik : X → G.edgeSet × Bool → ℝ) (inner : Cfg G → G.Dart → X → ℝ)
    (h : List (G.edgeSet × Bool)) : ℝ :=
  ∑ ρ ∈ (completeRecords ord).filter (fun ρ => h <+: ρ), qRecord ord R ν lik inner ρ

/-- Spin case of Definition 3.6: the likelihood of `(e, b)` given `σ`, namely `P_{σ,M}(e ∈ H)` for
`b = 1` and its complement for `b = 0` (arXiv:2610.42059, p.18). -/
noncomputable def spinLik {q : ℕ} (β r : ℝ) (σ : V → Fin q) (t : G.edgeSet × Bool) : ℝ :=
  if t.2 = true then inclProb β r σ t.1.1 else 1 - inclProb β r σ t.1.1

/-- Edge case of Definition 3.6: the outcome is read off `ω`. -/
noncomputable def edgeLik (ω : G.edgeSet → Bool) (t : G.edgeSet × Bool) : ℝ :=
  if ω t.1 = t.2 then 1 else 0

/-- Item 1 of Definition 3.7, spin case (arXiv:2610.42059, p.18): with `τ` the exterior of `σ'`, sample
`σ_F` from `µ^τ_{F⁺}` at inverse temperature `β` and include `e` with probability `P_{σ,M}(e ∈ H)`.

**Formalization Note.** `µ^τ_{F⁺}` is the Potts law on `F⁺` given the spins off `F`. -/
noncomputable def spinInner {q : ℕ} (R : ℕ) (β r : ℝ) (c : Cfg G) (d : G.Dart) (σ' : V → Fin q) : ℝ :=
  ∑ σ, condLaw (pottsLaw (forwardGraph c.graph (forwardRegion c.graph d.fst d.snd R)) β q)
      (forwardRegion c.graph d.fst d.snd R)ᶜ σ' σ * inclProb β r σ (dartEdge d).1

/-- The open edges of `ω'` outside `E(F⁺)`, as a graph: its connectivity is the partition `ζ` of
`∂F⁺` induced by the exterior (arXiv:2610.42059, p.18). -/
def exteriorGraph (Fp : SimpleGraph V) (ω' : G.edgeSet → Bool) : SimpleGraph V :=
  SimpleGraph.fromRel (fun a b => ∃ h : G.Adj a b, ω' ⟨s(a, b), h⟩ = true ∧ ¬ Fp.Adj a b)

/-- Item 1 of Definition 3.7, edge case (arXiv:2610.42059, p.18): with `η` the exterior of `ω'`, sample
`ω_{E(F⁺)}` from `ϕ^ζ_{F⁺}`, `ζ` the partition of `∂F⁺` induced by `η`, and record `ω_e`. -/
noncomputable def edgeInner (R : ℕ) (p q : ℝ) (c : Cfg G) (d : G.Dart) (ω' : G.edgeSet → Bool) : ℝ :=
  ∑ ω : (forwardGraph c.graph (forwardRegion c.graph d.fst d.snd R)).edgeSet → Bool,
    rcBoundary (forwardGraph c.graph (forwardRegion c.graph d.fst d.snd R)) p q
      (exteriorGraph (forwardGraph c.graph (forwardRegion c.graph d.fst d.snd R)) ω') ω *
    (if ∃ h, ω ⟨d.edge, h⟩ = true then 1 else 0)

/-- (3.1) at `s` for radius `R`, for all forward trees (arXiv:2610.42059, p.17): for every boundary
assignment `τ`, the spins on `F` drawn from `µ^τ_{F⁺}` give `P_{µ^τ_{F⁺},M}(yv ∈ H) ≤ s`, where `M` has
sprinkling level `r`. -/
def SpinSubcritical (Δ q : ℕ) (β r s : ℝ) (R : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (T : SimpleGraph W) (y v : W) (F : Finset W),
    IsForwardTree T Δ R y v F → ∀ τ : W → Fin q,
      ∑ σ, condLaw (pottsLaw T β q) Fᶜ τ σ * inclProb β r σ s(y, v) ≤ s

/-- (3.6) at `s` for radius `R`, for all forward trees (arXiv:2610.42059, p.18): for every boundary
partition `ζ` of `∂F⁺`, `ϕ^ζ_{F⁺}(ω_e = 1) ≤ s`. A partition is given by a graph `ζ` whose edges join
vertices off `F`. -/
def EdgeSubcritical (Δ : ℕ) (p q s : ℝ) (R : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (T : SimpleGraph W) (y v : W) (F : Finset W),
    IsForwardTree T Δ R y v F → ∀ ζ : SimpleGraph W, (∀ a b, ζ.Adj a b → a ∉ F ∧ b ∉ F) →
      ∑ ω : T.edgeSet → Bool, rcBoundary T p q ζ ω * (if ∃ h, ω ⟨s(y, v), h⟩ = true then 1 else 0) ≤ s

/-- The conclusions (3.19), (3.20) of Lemma 3.11 (arXiv:2610.42059, p.21) for one law `Q`: for every
history `h` with `Q(R_j = h) > 0` after which Algorithm 1 is at line 3 with `i` finished components, and
`C` the component explored next, `Q(|C| ≥ m | R_j = h) ≤ C₁ e^{−2c₀m}` for `m ≥ 1` and
`E_Q[e^{c₀|C|} 1{|C| > a} | R_j = h] ≤ C_tail e^{−c₀a}` for integers `a ≥ 0`. -/
def ComponentTails (ord : ExplOrder G) (R : ℕ) (ν : X → ℝ) (lik : X → G.edgeSet × Bool → ℝ)
    (inner : Cfg G → G.Dart → X → ℝ) (c₀ C₁ Ctail : ℝ) : Prop :=
  ∀ (h : List (G.edgeSet × Bool)) (i : ℕ), 0 < qPrefix ord R ν lik inner h → AtLine3 ord h i →
    (∀ m : ℕ, 1 ≤ m →
      (∑ ρ ∈ (completeRecords ord).filter (fun ρ => h <+: ρ ∧ m ≤ (compOf ord ρ i).card),
        qRecord ord R ν lik inner ρ) / qPrefix ord R ν lik inner h
        ≤ C₁ * Real.exp (-2 * c₀ * m)) ∧
    (∀ a : ℕ,
      (∑ ρ ∈ (completeRecords ord).filter (fun ρ => h <+: ρ ∧ a < (compOf ord ρ i).card),
        qRecord ord R ν lik inner ρ * Real.exp (c₀ * ((compOf ord ρ i).card : ℝ))) /
          qPrefix ord R ν lik inner h
        ≤ Ctail * Real.exp (-c₀ * a))

end PottsRapidMixing


