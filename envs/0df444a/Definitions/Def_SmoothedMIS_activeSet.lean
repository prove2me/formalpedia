-- Prove2me | Definitions.Def_SmoothedMIS_activeSet
-- name    : SmoothedMIS_activeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:40.281721+00:00
-- url     : https://prove2.me/theorems/a2a84189-5fee-4d4f-9fef-5e75d02103ac
-- title:
--   Steps 1–2 of Algorithm 1: high and low vertices, helpers $S$, active set $\mathcal A$, condition (1)
-- statement:
--   Fix a base graph $G$ on $n$ vertices, $\beta>0$, and the coins $\omega=(\omega_R,\omega_\kappa)$: the smoothing coins, which give the random edges $R$ and $\mathcal G=G\cup R$, and an independent coin $\kappa_{uv}$ on every pair, true with probability $\theta$ (the device of p.25, which has the same distribution as the marks of the algorithm). Then:
--   1. $V_{hi}=\{v:\deg_{\mathcal G}(v)>B\}$ and $V_{lo}=V\setminus V_{hi}$ (Definition 4.2);
--   2. a present edge $uv$ with $u\in V_{hi}$, $v\in V_{lo}$ is **marked** when $\kappa_{uv}=1$;
--   3. the candidates are $Y=\{v\in V_{lo}: v\text{ has a marked edge}\}$ and the helpers $S=\{v\in Y: v\text{ has no neighbour in }Y\}$;
--   4. the **active set** is $\mathcal A=V_{hi}\setminus N_{\mathcal G}[S]$;
--   5. **condition (1)**: $\mathcal A=\emptyset$, or all vertices of $\mathcal A$ are pairwise within distance $\ell$ in $\mathcal G$.
--
--   The **analysis law** is the product of the smoothing law with probability $p=\beta\ln n/n$ and the mark coins with probability $\theta$.
--
--   Lemmas 4.4–4.13 are statements about these sets.
--
--   **Formalization Note** Degrees are compared with $B$ as real numbers; distances are `SimpleGraph.edist` ($\infty$ between components).
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), §4.1, Definition 4.2 and Algorithm 1 lines 1–7, pp.17–18; condition (1), p.20; coins $\kappa_{uv}$, p.25 (PDF pp.19–20, 22, 27)

import Mathlib
import Definitions.Def_SmoothedMIS_IsMIS
import Definitions.Def_SmoothedMIS_coinLaw
import Definitions.Def_SmoothedMIS_smoothLaw
import Definitions.Def_SmoothedMIS_B0

open MeasureTheory

namespace SmoothedMIS

/-- The coins of the analysis: `ω.1` the smoothing coins (the random edges `R`), `ω.2` the mark
coins `κ_uv` (§4.2.1, p.25). -/
abbrev Coins (n : ℕ) := (Sym2 (Fin n) → Bool) × (Sym2 (Fin n) → Bool)

/-- The law of the analysis: smoothing coins with probability `p = β ln n/n` and, independently,
mark coins with probability `θ` (§4.2.1, p.25: "give every pair {u, v} a coin κuv equal to 1 with
probability θ, independently of each other and of all random edges … this has the same
distribution as the algorithm"). -/
noncomputable def anaLaw (n : ℕ) (β : ℝ) : Measure (Coins n) :=
  (smoothLaw n β).prod (coinLaw (Sym2 (Fin n)) (theta n β))

/-- `uv ∈ R`: a random edge, i.e. a pair that is not an edge of `G` and whose smoothing coin is
`true` (§2, p.9). -/
def Radj {n : ℕ} (G : SimpleGraph (Fin n)) (ωR : Sym2 (Fin n) → Bool) (u v : Fin n) : Prop :=
  u ≠ v ∧ ¬ G.Adj u v ∧ ωR s(u, v) = true

/-- `V_hi = {v : deg_𝒢(v) > B}` (Definition 4.2, p.17). -/
def Vhi {n : ℕ} (β : ℝ) (G : SimpleGraph (Fin n)) (ωR : Sym2 (Fin n) → Bool) : Set (Fin n) :=
  {v | Bthr n β < (deg (addSmooth G ωR) v : ℝ)}

/-- `V_lo = V \ V_hi` (Definition 4.2, p.17). -/
def Vlo {n : ℕ} (β : ℝ) (G : SimpleGraph (Fin n)) (ωR : Sym2 (Fin n) → Bool) : Set (Fin n) :=
  (Vhi β G ωR)ᶜ

/-- Step 1: the high vertex `u` marks its edge to the low vertex `v` (coin `κ_uv`). -/
def marked {n : ℕ} (β : ℝ) (G : SimpleGraph (Fin n)) (ω : Coins n) (u v : Fin n) : Prop :=
  (addSmooth G ω.1).Adj u v ∧ u ∈ Vhi β G ω.1 ∧ v ∈ Vlo β G ω.1 ∧ ω.2 s(u, v) = true

/-- The candidates `Y = {v ∈ V_lo : v has a marked incident edge}` (Algorithm 1, line 5). -/
def candidates {n : ℕ} (β : ℝ) (G : SimpleGraph (Fin n)) (ω : Coins n) : Set (Fin n) :=
  {v | v ∈ Vlo β G ω.1 ∧ ∃ u, marked β G ω u v}

/-- The helpers `S = {v ∈ Y : v has no neighbour in Y}` (Algorithm 1, line 6). -/
def helpers {n : ℕ} (β : ℝ) (G : SimpleGraph (Fin n)) (ω : Coins n) : Set (Fin n) :=
  {v | v ∈ candidates β G ω ∧ ∀ w, (addSmooth G ω.1).Adj v w → w ∉ candidates β G ω}

/-- **The active set** `𝒜 = V_hi \ N_𝒢[S]` of Algorithm 1 (Dey, Dufoulon, Moses Jr.,
Pandurangan, *Smoothed Analysis for Distributed MIS* (manuscript, sha256 dc2131db…), §4.1,
Algorithm 1 line 7, p.18), in the centralized analysis model of §4.2.

**Formalization Note** All sets of Steps 1–2 are functions of the base graph `G` and the coins
`ω = (ω_R, ω_κ)`: `𝒢 = addSmooth G ω_R`; high/low by `deg_𝒢(v) > B` compared as reals; a
present edge `uv` with `u` high and `v` low is marked iff `κ_uv = 1`, as on p.25. -/
def activeSet {n : ℕ} (β : ℝ) (G : SimpleGraph (Fin n)) (ω : Coins n) : Set (Fin n) :=
  Vhi β G ω.1 \ closedNbhd (addSmooth G ω.1) (helpers β G ω)

/-- **Condition (1)** (§4.2, p.20): `𝒜 = ∅`, or all vertices of `𝒜` are pairwise within
distance `ℓ` in `𝒢` (`SimpleGraph.edist`, `∞` between components). -/
def cond1 {n : ℕ} (β : ℝ) (G : SimpleGraph (Fin n)) (ω : Coins n) : Prop :=
  activeSet β G ω = ∅ ∨
    ∀ u ∈ activeSet β G ω, ∀ v ∈ activeSet β G ω, (addSmooth G ω.1).edist u v ≤ ell n

end SmoothedMIS


