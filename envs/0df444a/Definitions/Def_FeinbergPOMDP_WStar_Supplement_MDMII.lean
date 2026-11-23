-- Prove2me | Definitions.Def_FeinbergPOMDP_WStar_Supplement_MDMII
-- name    : FeinbergPOMDP_WStar_Supplement_MDMII
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:21:37.199348+00:00
-- url     : https://prove2.me/theorems/92827cb6-ca01-4d6f-91ee-ec238acc0f9c
-- title:
--   §8.3, pp. 32–34 — the MDMII observation kernel and the family 𝒫*_𝒪
-- statement:
--   Objects of the Markov decision model with incomplete information (MDMII).
--
--   1. **Observation kernel.** For the state space $\mathbb X=\mathbb Y\times\mathbb W$ of observed and unobserved coordinates, $Q(C|a,(y,w))=\mathbf 1\{y\in C\}$ for Borel $C\subseteq\mathbb Y$: the observation is the observed coordinate of the state.
--   2. **The family $\mathcal P^*_{\mathcal O}$.** For a set $\mathcal O\subseteq\mathbb W$ and a transition kernel $P$ on $\mathbb X$ given $\mathbb X\times\mathbb A$,
--   $$\mathcal P^*_{\mathcal O}=\{(x,a)\mapsto P(C\times\mathcal O|x,a):C\in\mathcal B(\mathbb Y)\},$$
--   a family of $[0,1]$-valued functions on $\mathbb X\times\mathbb A$ indexed by the Borel subsets of $\mathbb Y$.
--
--   Equicontinuity of $\mathcal P^*_{\mathcal O}$ for every nonempty open $\mathcal O$ is the hypothesis of Theorem 8.2.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, §8.3, observation kernel Q, p. 32; the family 𝒫*_𝒪, p. 34

import Mathlib

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace FeinbergPOMDP.WStar.Supplement

/-! Feinberg, Kasyanov, Zgurovsky, *Partially Observable Total-Cost Markov Decision Processes with
Weakly Continuous Transition Probabilities*, arXiv:1401.2168v2, §8.3, pp. 32–34: the Markov
decision model with incomplete information (MDMII) as a POMDP with state space `𝕏 = 𝕐 × 𝕎`, the
projection observation kernel, and the family `𝒫*_𝒪`. -/

variable {Y W A : Type*} [MeasurableSpace Y] [MeasurableSpace W] [MeasurableSpace A]

/-- The observation kernel of an MDMII (p. 32): `Q(C | a, x) = I{y ∈ C}` for `x = (y, w)`, the
Dirac measure at the observed coordinate `y` of the state (the projection of `𝕏 = 𝕐 × 𝕎` on `𝕐`). -/
noncomputable def mdmiiObs : Kernel (A × (Y × W)) Y :=
  Kernel.deterministic (fun p : A × (Y × W) => p.2.1) (measurable_fst.comp measurable_snd)

instance : IsMarkovKernel (mdmiiObs (Y := Y) (W := W) (A := A)) := by
  unfold mdmiiObs; infer_instance

/-- The family `𝒫*_𝒪 = {(x, a) ↦ P(C × 𝒪 | x, a) : C ∈ ℬ(𝕐)}` (p. 34), indexed by the Borel sets
`C ⊆ 𝕐`, as real-valued functions on `𝕏 × 𝔸` with `𝕏 = 𝕐 × 𝕎`. -/
noncomputable def PStarFamily (P : Kernel ((Y × W) × A) (Y × W)) (O : Set W) :
    {C : Set Y // MeasurableSet C} → (Y × W) × A → ℝ :=
  fun C p => (P p (C.1 ×ˢ O)).toReal

end FeinbergPOMDP.WStar.Supplement


