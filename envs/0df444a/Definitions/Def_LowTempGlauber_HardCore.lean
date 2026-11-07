-- Prove2me | Definitions.Def_LowTempGlauber_HardCore
-- name    : LowTempGlauber_HardCore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:08.634385+00:00
-- url     : https://prove2.me/theorems/4cc2200a-f48c-40ee-b9a4-8d1cea98c695
-- title:
--   The hard-core model on $V^+\sqcup V^-$: $\lambda_c(d)$, activities, magnetisation, the phases $\mathcal I^\pm_G$ and $\mu^+_{G,s}$
-- statement:
--   Let $G$ be a graph on $V=V^+\sqcup V^-$ with $|V^\pm|=n$ (the vertices are $\mathrm{Fin}\,n\sqcup\mathrm{Fin}\,n$ of the published random-bipartite-graph layer, $V^+$ the left copy). A configuration $\sigma:V\to\{0,1\}$ is identified with the set of occupied vertices; it is an independent set when no edge has both ends occupied.
--
--   1. The **tree uniqueness threshold** $\lambda_c(d)=\dfrac{(d-1)^{d-1}}{(d-2)^d}$ (p.3).
--   2. The **hard-core law with activities** $(\lambda_v)_{v\in V}$: $\mu(I)\propto\prod_{v\in I}\lambda_v$ on independent sets $I$ and $0$ otherwise (Lemma 7). With a single activity $\lambda$ it is the published law $\mu_G(I)=\lambda^{|I|}/Z_G$ of p.3.
--   3. The **magnetisation** $M(I)=|I\cap V^+|-|I\cap V^-|$ (p.9).
--   4. The **phases** (p.3): $\mathcal I^+_G$ is the set of independent sets with more occupied vertices on $V^+$ than on $V^-$, i.e. $M(I)>0$, and $\mathcal I^-_G=\mathcal I_G\setminus\mathcal I^+_G$ (independent, $M(I)\le0$).
--   5. The **conditional law** $\pi(\cdot\mid S)$, and the **biased plus phase** $\mu^+_{G,s}(I)\propto(\lambda e^s)^{|I\cap V^+|}(\lambda e^{-s})^{|I\cap V^-|}$ on $\mathcal I^+_G$ (p.9); at $s=0$ it is $\mu^+_G=\mu_G(\cdot\mid\mathcal I^+_G)$.
--   6. The one-sided independent sets $V^+$ and $V^-$, the starting states $X^\pm_0$ of Glauber dynamics (p.3).
--   7. The **balanced independent sets** $\mathcal I^{\mathrm{bal}}_G(\theta)=\{I: M(I)\le\theta n\}$ (p.9).
--
--   For $\lambda>\lambda_c(d)$ the hard-core law on a random bipartite $d$-regular graph is bimodal, its two modes being concentrated on $\mathcal I^+_G$ and $\mathcal I^-_G$; these are the objects in which the mission's results are stated.
--
--   **Formalization Note** Configurations are `Vertex n → Bool`; independence is the published `MarkovMixing.IsHardcore`. $\mathcal I^+_G$ uses the strict inequality $M>0$ of p.3 (Section 6, p.32, writes $M\ge0$; p.3 is used throughout). The conditional law is $0$ off the conditioning set.
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), §1.1.1, p.3; §3, p.9; Lemma 7, p.9

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting
import Definitions.Def_mm_coupling

open Classical

namespace LowTempGlauber

/-!
# The hard-core model on a bipartite graph, its phases and the field-biased phase laws

A. Galanis, D. Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission manuscript dated 3 November 2026 (held version, sha256 c41a38ff…7533d), §1.1.1, p.3;
§3, p.9; Lemma 7, p.9; Lemma 11, p.13.

The vertex set is the published `ExpanderBIS.RandomHardCore.Vertex n = Fin n ⊕ Fin n`; the `inl`
side (`oddSide`) is `V⁺` and the `inr` side (`evenSide`) is `V⁻`, so `|V±| = n`. A configuration is
`σ : Vertex n → Bool`, `σ v = true` meaning `v` is occupied; independence is the published
`MarkovMixing.IsHardcore`, and the one-activity hard-core law `μ_G(I) = λ^{|I|}/Z_G` of p.3 is the
published `MarkovMixing.hardcoreDist G λ`.

**Formalization Note.**
* `lamC d = (d − 1)^{d−1}/(d − 2)^d`, the tree uniqueness threshold of p.3, for natural `d ≥ 3`.
* `hcLaw G act` is the hard-core law with vertex activities `act v` (Lemma 7, p.9, and (38), p.32):
  weight `∏_{v ∈ I} act v` on independent configurations, `0` otherwise, normalized.
* `mag σ = |I ∩ V⁺| − |I ∩ V⁻|` (the magnetisation `M(I)`, p.9).
* `IPlus G` is `I⁺_G` of p.3: independent sets with **strictly** more occupied vertices on `V⁺`
  (`M > 0`); `IMinus G = I_G ∖ I⁺_G` (`M ≤ 0`). (Section 6, p.32, uses `M ≥ 0`; the main text's p.3
  definition is used throughout.)
* `condLaw π p` is `π(· | p)`, and `0` off `p`. If `π(p) = 0` it is `0` everywhere.
* `fieldAct λ s` is the activity `λ e^{s}` on `V⁺` and `λ e^{−s}` on `V⁻`; `muPlus G λ s` is `μ⁺_{G,s}`
  of p.9, `μ_G` with these activities conditioned on `I⁺_G`. At `s = 0` it is `μ⁺_G` of p.3.
* `plusInit n` is the one-sided independent set `V⁺`, `minusInit n` is `V⁻`.
* `Ibal G θ σ` is `I^bal_G(θ)` of p.9: independent with `M(σ) ≤ θ n`.
-/

open ExpanderBIS.RandomHardCore

/-- The tree uniqueness threshold `λ_c(d) = (d − 1)^{d−1}/(d − 2)^d`, p.3. -/
noncomputable def lamC (d : ℕ) : ℝ :=
  ((d : ℝ) - 1) ^ (d - 1) / ((d : ℝ) - 2) ^ d

/-- The weight `∏_{v ∈ I} act v` of an independent configuration, `0` otherwise. -/
noncomputable def hcW {n : ℕ} (G : SimpleGraph (Vertex n)) (act : Vertex n → ℝ)
    (σ : Vertex n → Bool) : ℝ :=
  if MarkovMixing.IsHardcore G σ then ∏ v ∈ Finset.univ.filter (fun v => σ v = true), act v
  else 0

/-- The hard-core law with vertex activities `act` (Lemma 7, p.9). -/
noncomputable def hcLaw {n : ℕ} (G : SimpleGraph (Vertex n)) (act : Vertex n → ℝ)
    (σ : Vertex n → Bool) : ℝ :=
  hcW G act σ / ∑ τ, hcW G act τ

/-- The magnetisation `M(I) = |I ∩ V⁺| − |I ∩ V⁻|`, p.9. -/
def mag {n : ℕ} (σ : Vertex n → Bool) : ℤ :=
  ((Finset.univ.filter (fun i : Fin n => σ (Sum.inl i) = true)).card : ℤ) -
    ((Finset.univ.filter (fun j : Fin n => σ (Sum.inr j) = true)).card : ℤ)

/-- `I⁺_G`, p.3: independent sets with more occupied vertices on `V⁺` than on `V⁻`. -/
def IPlus {n : ℕ} (G : SimpleGraph (Vertex n)) (σ : Vertex n → Bool) : Prop :=
  MarkovMixing.IsHardcore G σ ∧ 0 < mag σ

/-- `I⁻_G = I_G ∖ I⁺_G`, p.3. -/
def IMinus {n : ℕ} (G : SimpleGraph (Vertex n)) (σ : Vertex n → Bool) : Prop :=
  MarkovMixing.IsHardcore G σ ∧ mag σ ≤ 0

/-- The conditional law `π(· | p)`; `0` off `p`. -/
noncomputable def condLaw {n : ℕ} (π : (Vertex n → Bool) → ℝ) (p : (Vertex n → Bool) → Prop)
    (σ : Vertex n → Bool) : ℝ :=
  if p σ then π σ / ∑ τ ∈ Finset.univ.filter p, π τ else 0

/-- The field activities: `λ e^{s}` on `V⁺`, `λ e^{−s}` on `V⁻` (p.9). -/
noncomputable def fieldAct {n : ℕ} (lam s : ℝ) : Vertex n → ℝ :=
  Sum.elim (fun _ => lam * Real.exp s) (fun _ => lam * Real.exp (-s))

/-- `μ⁺_{G,s}`, p.9: the hard-core law with activities `λ e^{±s}` conditioned on `I⁺_G`. -/
noncomputable def muPlus {n : ℕ} (G : SimpleGraph (Vertex n)) (lam s : ℝ) :
    (Vertex n → Bool) → ℝ :=
  condLaw (hcLaw G (fieldAct lam s)) (IPlus G)

/-- The one-sided independent set `V⁺` (`X⁺₀`, p.3). -/
def plusInit (n : ℕ) : Vertex n → Bool := fun v => v.isLeft

/-- The one-sided independent set `V⁻` (`X⁻₀`, p.3). -/
def minusInit (n : ℕ) : Vertex n → Bool := fun v => v.isRight

/-- `I^bal_G(θ)`, p.9: independent sets with `M(I) ≤ θ n`. -/
def Ibal {n : ℕ} (G : SimpleGraph (Vertex n)) (θ : ℝ) (σ : Vertex n → Bool) : Prop :=
  MarkovMixing.IsHardcore G σ ∧ (mag σ : ℝ) ≤ θ * n

end LowTempGlauber


