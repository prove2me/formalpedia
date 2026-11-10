-- Prove2me | Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore
-- name    : HiddenHardCoreColoring_Mixing_HardCore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:59:15.558381+00:00
-- url     : https://prove2.me/theorems/fc77d443-3b6b-4da8-96f8-3814526bc325
-- title:
--   Hard-core model with vertex activities, its Glauber dynamics, gap(H), λ_crit and the resolvent
-- statement:
--   This file fixes the hard-core objects of §3.3 (p.8) and the resolvent of §6.4 (p.21). $G=(V,E)$ is a finite simple graph and $\lambda=(\lambda_v)_{v\in V}$ vertex activities.
--
--   1. $\mathcal I$ is the set of independent sets of $G$, including $\emptyset$, and
--   $$\nu(I)=\frac1Z\prod_{v\in I}\lambda_v,\qquad Z=\sum_{I'\in\mathcal I}\prod_{v\in I'}\lambda_v .$$
--   2. $V_{\mathrm{ubl}}(I)=\{v:N(v)\cap I=\emptyset\}$ and $p_v=\lambda_v/(1+\lambda_v)$. The heat-bath update $P_v^\nu$ moves, if $v\in V_{\mathrm{ubl}}(I)$, to $I\cup\{v\}$ with probability $p_v$ and to $I\setminus\{v\}$ with probability $1-p_v$, and otherwise stays; $P^\nu=\frac1n\sum_vP_v^\nu$.
--   3. $H_v=\mathrm{Id}-P_v^\nu$, $H=\sum_vH_v=n(\mathrm{Id}-P^\nu)$, and $\operatorname{gap}(H)=n\operatorname{gap}(P^\nu)$.
--   4. $\lambda_{\mathrm{crit}}(\Delta)=(\Delta-1)^{\Delta-1}/(\Delta-2)^\Delta$, the uniqueness threshold on the infinite $\Delta$-regular tree.
--   5. For $a>0$, the resolvent $R=(\mathrm{Id}+aH)^{-1}$ on $\mathbb R^{\mathcal I}$.
--   6. The property of the function $\theta^*$ in Theorem 5: for every $\delta\in(0,1)$, $\theta^*(\delta)\in(0,1]$, and $\operatorname{gap}(P^\nu)\ge\theta^*(\delta)/n$ and $\operatorname{gap}(H)\ge\theta^*(\delta)$ for every $\Delta\ge3$, every graph on $n\ge1$ vertices of maximum degree at most $\Delta$ and all activities $0<\lambda_v\le(1-\delta)\lambda_{\mathrm{crit}}(\Delta)$.
--
--   These objects are general: the coloring argument applies them to the hidden models of each color class.
--
--   **Formalization Note** The state space of the hard-core chain is the subtype of independent sets, so its spectrum has no spurious directions. The resolvent is the matrix inverse; Fact 21 states that $\mathrm{Id}+aH$ is invertible for $a>0$ and positive activities.
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; §3.3, eqs. (4)–(5), p.8 (ν, Z, V_ubl, p_v, P^ν, H_v, H, gap(H), λ_crit, Theorem 5); §6.4, p.21 and Fact 21, p.23 (R = (Id + aH)^{-1})

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Chain

namespace HiddenHardCoreColoring.Mixing

open Finset

noncomputable section

/-!
# The hard-core model with vertex activities and its heat-bath Glauber dynamics

Xiongxin Yang, *Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via
Hidden Hard-Core Models*, STOC 2027 submission #964 (October 2026), §3.3, p.8 (eqs. (4)–(8),
`λ_crit`, Theorem 5) and §6.4 / Fact 21, pp.21, 23 (the resolvent).

`G` is a finite simple graph on `V`; `ℐ = IndSet G` is the set of all independent sets of `G`,
including `∅`; `lam : V → ℝ` are vertex activities (positive in every statement). Functions on `ℐ`
are all real functions `IndSet G → ℝ`, with the weights of `ν`.
-/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `ℐ`: the independent sets of `G`, including the empty set (§3.3, p.8). -/
abbrev IndSet : Type _ := {I : Finset V // ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w}

/-- The hard-core weight `∏_{v∈I} λ_v` (eq. (4), p.8). -/
def hcWeight (lam : V → ℝ) (I : IndSet G) : ℝ := ∏ v ∈ I.1, lam v

/-- The partition function `Z := ∑_{I∈ℐ} ∏_{v∈I} λ_v` (eq. (4), p.8). -/
def hcZ (lam : V → ℝ) : ℝ := ∑ I : IndSet G, hcWeight G lam I

/-- **The hard-core model** `ν(I) := Z⁻¹ ∏_{v∈I} λ_v` on `ℐ` (eq. (4), p.8). -/
def hcLaw (lam : V → ℝ) (I : IndSet G) : ℝ := hcWeight G lam I / hcZ G lam

/-- The unblocked vertices `V_ubl(I) := {v ∈ V : N(v) ∩ I = ∅}` (§3.3, p.8). -/
def ubl (I : IndSet G) : Finset V := univ.filter fun v => ∀ u ∈ I.1, ¬ G.Adj v u

/-- The conditional occupation probability `p_v := λ_v/(1 + λ_v)` at an unblocked vertex
(§3.3, p.8). -/
def occProb (lam : V → ℝ) (v : V) : ℝ := lam v / (1 + lam v)

/-- **The heat-bath update `P_v^ν` at `v`** (§3.3, p.8): if `v ∈ V_ubl(I)`, move to `I ∪ {v}` with
probability `p_v` and to `I ∖ {v}` with probability `1 − p_v`; otherwise stay at `I`. (When
`v ∈ I`, `I ∪ {v} = I`; when `v ∉ I`, `I ∖ {v} = I`.) -/
def hcPv (lam : V → ℝ) (v : V) : Matrix (IndSet G) (IndSet G) ℝ :=
  fun I J =>
    if v ∈ ubl G I then
      (if J.1 = insert v I.1 then occProb lam v else 0) +
        (if J.1 = I.1.erase v then 1 - occProb lam v else 0)
    else (if J = I then 1 else 0)

/-- **The Glauber dynamics** `P^ν := n⁻¹ ∑_v P_v^ν` for `ν` (§3.1, p.6, and §3.3, p.8): pick a
uniform vertex and apply its heat-bath update. -/
def hcP (lam : V → ℝ) : Matrix (IndSet G) (IndSet G) ℝ :=
  (1 / (Fintype.card V : ℝ)) • ∑ v, hcPv G lam v

/-- `H_v := Id − P_v^ν` (§3.3, p.8). -/
def hcHv (lam : V → ℝ) (v : V) : Matrix (IndSet G) (IndSet G) ℝ := 1 - hcPv G lam v

/-- `H := ∑_v H_v = n(Id − P^ν)` (§3.3, p.8). -/
def hcH (lam : V → ℝ) : Matrix (IndSet G) (IndSet G) ℝ := ∑ v, hcHv G lam v

/-- `gap(H) := n · gap(P^ν)` (§3.3, p.8), with `n = |V|` and `gap` counted with multiplicity. -/
def hcGapH (lam : V → ℝ) : ℝ := (Fintype.card V : ℝ) * gap (hcP G lam)

/-- `⟨h, g⟩_ν = ∑_I ν(I) h(I) g(I)` on functions on `ℐ`. -/
def ipNu (lam : V → ℝ) (h g : IndSet G → ℝ) : ℝ := MarkovMixing.innerPi (hcLaw G lam) h g

/-- **The resolvent** `R := (Id + aH)⁻¹` of the hidden dynamics (§6.4, p.21; Fact 21, p.23), as the
matrix inverse on `ℝ^ℐ`. (`Id + aH` is invertible for `a > 0` and positive activities; this is part
of the statement of Fact 21 in this mission. The matrix inverse is the actual inverse whenever the
matrix is invertible.) -/
def resolvent (lam : V → ℝ) (a : ℝ) : Matrix (IndSet G) (IndSet G) ℝ :=
  (1 + a • hcH G lam)⁻¹

/-- The uniqueness threshold `λ_crit(Δ) := (Δ − 1)^{Δ−1}/(Δ − 2)^Δ` of the hard-core model on the
infinite `Δ`-regular tree (§3.3, p.8). Used with `Δ ≥ 3`. -/
def lamCrit (Δ : ℕ) : ℝ := ((Δ : ℝ) - 1) ^ (Δ - 1) / ((Δ : ℝ) - 2) ^ Δ

/-- **The property of the function `θ*` of Theorem 5** (§3.3, p.8): for every `δ ∈ (0, 1)`,
`θ*(δ) ∈ (0, 1]`, and for every `Δ ≥ 3`, every graph on `n ≥ 1` vertices of maximum degree at most
`Δ`, and all activities `0 < λ_v ≤ (1 − δ) λ_crit(Δ)`, one has `gap(P^ν) ≥ θ*(δ)/n` and
`gap(H) ≥ θ*(δ)`. Theorem 5 asserts that such a function exists; Corollary 17 is stated for every
such function. -/
def IsHardCoreGapBound (θs : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 →
    0 < θs δ ∧ θs δ ≤ 1 ∧
      ∀ Δ : ℕ, 3 ≤ Δ →
        ∀ (W : Type) [Fintype W] [DecidableEq W] [Nonempty W] (H : SimpleGraph W)
          [DecidableRel H.Adj], (∀ w, H.degree w ≤ Δ) →
          ∀ lam : W → ℝ, (∀ w, 0 < lam w ∧ lam w ≤ (1 - δ) * lamCrit Δ) →
            θs δ / (Fintype.card W : ℝ) ≤ gap (hcP H lam) ∧ θs δ ≤ hcGapH H lam

end

end HiddenHardCoreColoring.Mixing


