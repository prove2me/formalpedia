-- Prove2me | Definitions.Def_RankingCertGap_CertifyingCapacity
-- name    : RankingCertGap_CertifyingCapacity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:52:13.749557+00:00
-- url     : https://prove2.me/theorems/b99a7f27-86e1-4d59-9edd-ce89f0cfec27
-- title:
--   Competitiveness $\gamma$, guarantee $\chi$, capacity $\Gamma$, tightness, the classes $\mathcal A$, $\mathcal F$, $\mathcal B^{\mathrm{on}}_{\le d}$, $\mathcal B_d$, and the profile $\tilde f^\star_2$
-- statement:
--   For a collection $\mathcal G$ of instances, the **competitiveness** of RANKING and the **worst-case edgewise guarantee** of a gain-sharing function $f$ are
--
--   $$
--   \gamma(\mathcal G):=\inf_{G\in\mathcal G,\ \mathrm{OPT}(G)>0}\frac{\mathbb E[\mathrm{RANKING}(G)]}{\mathrm{OPT}(G)},\qquad
--   \chi(f,\mathcal G):=\inf_{G\in\mathcal G,\ (i,j)\in E(G)}\Phi_G(i,j;f).
--   $$
--
--   The **certifying capacity** of a function class $\mathcal S$ is $\Gamma_{\mathcal S}(\mathcal G):=\sup_{f\in\mathcal S}\chi(f,\mathcal G)$, and the protocol is **tight** when $\Gamma_{\mathcal S}(\mathcal G)=\gamma(\mathcal G)$.
--
--   The full admissible class $\mathcal A$ consists of the Borel functions $f:[0,1]\to[0,1]$ with $f(1)=1$, and $\mathcal F\subseteq\mathcal A$ of those that are also nondecreasing and right-continuous on $[0,1)$. The instance classes are $\mathcal B^{\mathrm{on}}_{\le d}$ (online degree at most $d$) and $\mathcal B_d$ (nonempty $d$-regular). The profile $\tilde f^\star_2$ is $3/4$ on $[0,1)$ and $1$ at $1$.
--
--   **Formalization Note** Functions are $\mathbb R\to\mathbb R$ with values in $[0,1]$ everywhere: a printed $f$ extends, for instance by $0$, and scores read it only on $[0,1]$ almost surely. Infima and suprema are real $\texttt{sInf}$ and $\texttt{sSup}$; the verification file proves that for both classes the sets are nonempty and bounded.
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), eqs. (1), (4), (5), pp.2–3; Proposition 1, p.3; §1.2, p.4; eq. (12), p.5; eq. (27), p.10

import Mathlib
import Definitions.Def_RankingCertGap_Score

namespace RankingCertGap

/-- A collection of finite online bipartite matching instances. Sizes vary, so an instance is a
triple `⟨m, n, G⟩`. -/
abbrev InstClass : Type := Set (Σ m : ℕ, Σ n : ℕ, Inst m n)

/-- The competitiveness `γ(𝒢) := inf_{G ∈ 𝒢, OPT(G) > 0} E[RANKING(G)] / OPT(G)`. Xu,
arXiv:2610.17545 (held file sha256 75896dd9…), eq. (1), p.2. The set is bounded below by `0`. The
class must contain an instance of positive optimum, as the page requires; the verification file
checks this for both classes used here. -/
noncomputable def gammaC (C : InstClass) : ℝ :=
  sInf {r : ℝ | ∃ G ∈ C, 0 < G.2.2.OPT ∧ r = G.2.2.rankingValue / (G.2.2.OPT : ℝ)}

/-- The worst-case edgewise guarantee `χ(f, 𝒢) := inf_{G ∈ 𝒢, (i,j) ∈ E(G)} Φ_G(i, j; f)`. Xu,
arXiv:2610.17545 (held file sha256 75896dd9…), eq. (4), p.3. -/
noncomputable def chiC (f : ℝ → ℝ) (C : InstClass) : ℝ :=
  sInf {r : ℝ | ∃ G ∈ C, ∃ i j, G.2.2.Edge i j ∧ r = G.2.2.Phi i j f}

/-- The certifying capacity `Γ_𝔓(S)(𝒢) := sup_{f ∈ S} χ(f, 𝒢)`. Xu, arXiv:2610.17545 (held file
sha256 75896dd9…), eq. (5), p.3. -/
noncomputable def GammaC (S : Set (ℝ → ℝ)) (C : InstClass) : ℝ :=
  sSup ((fun f => chiC f C) '' S)

/-- Tightness: "its certifying capacity equals the actual competitiveness of RANKING on `𝒢`" (p.3). -/
def IsTight (S : Set (ℝ → ℝ)) (C : InstClass) : Prop := GammaC S C = gammaC C

/-- The full admissible class `𝒜 := {f : [0, 1] → [0, 1] : f is Borel measurable, f(1) = 1}`. Xu,
arXiv:2610.17545 (held file sha256 75896dd9…), Proposition 1, p.3. No monotonicity or continuity.

**Formalization Note.** A printed `f` on `[0, 1]` is extended to `ℝ` with values in `[0, 1]`, for
instance by `0`. Scores read `f` only at ranks, which lie in `[0, 1]` almost surely, and at `1`; so
the extension changes no score and `sup_{f ∈ 𝒜}` is the printed one. -/
def classA : Set (ℝ → ℝ) :=
  {f | Measurable f ∧ (∀ y, f y ∈ Set.Icc (0 : ℝ) 1) ∧ f 1 = 1}

/-- The class `ℱ := {f ∈ 𝒜 : f is nondecreasing and right-continuous on [0, 1)}`, eq. (12), p.5. -/
def classF : Set (ℝ → ℝ) :=
  {f | f ∈ classA ∧ MonotoneOn f (Set.Icc 0 1) ∧
    ∀ y ∈ Set.Ico (0 : ℝ) 1, ContinuousWithinAt f (Set.Ioi y) y}

/-- `B^on_≤d`: online degree at most `d`, offline degrees free (p.4). -/
def onDegLE (d : ℕ) : InstClass := {G | G.2.2.IsOnlineDegLE d}

/-- `B_d`: nonempty finite `d`-regular instances (p.4). -/
def regular (d : ℕ) : InstClass := {G | G.2.2.IsRegular d}

/-- The profile `f̃★₂` of eq. (27), p.10: `3/4` on `[0, 1)` and `1` at `1`.

**Formalization Note.** Values outside `[0, 1]` are irrelevant; `y > 1` gets `1`, which keeps the
extension nondecreasing and `[0, 1]`-valued. -/
noncomputable def fTilde (y : ℝ) : ℝ := if y < 1 then 3 / 4 else 1

end RankingCertGap


