-- Prove2me | Definitions.Def_CausalFailureRank_Instance
-- name    : CausalFailureRank_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:31.682085+00:00
-- url     : https://prove2.me/theorems/faaa5c77-8d2b-43f7-bb92-6a7331d7680e
-- title:
--   Fixed graph and channel instance
-- statement:
--   A **fixed graph and channel instance** consists of $N$ ordered output slots, a set $U$ of $q$ one-use tools and compatibility sets $S_i\subseteq U$. For each stage $i$ it also fixes a nondegenerate prior $\pi_i$ of a binary fact $X_i$, a review price $c_i>0$, a finite alphabet with two distinct full-support review laws $P_i^0,P_i^1$, fees $f_{ir}\ge 0$ for the correction of stage $i$ with tool $r$, and a number of normal calls charged at the stage's ordinary write. Also $f_{\max}=\max f_{ir}$ over compatible pairs, or zero when there is none.
--
--   All later objects are parametrized by an instance.
--
--   **Formalization Note** Stages are 0-based and alphabets are per stage, since full support on one shared alphabet would restrict the class. $N=0$, $q=0$ and $S_i=\emptyset$ are allowed. Inputs are real rather than rational. $H_0$ of the paper is the sum of the normal calls.
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §2, pp.4–5

import Mathlib

open MeasureTheory

namespace CausalFailureRank

/-- **A fixed graph and channel instance.** Zang, Li, Jin, Xu, *Causal Failure Rank Determines
Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §2,
pp.4–5: `N` required output slots, a set `U = Fin q` of one-use tools, compatibility sets
`S i ⊆ U`; at stage `i` a binary fact with nondegenerate prior, a review price `c i > 0`, a finite
alphabet and two distinct full-support review laws `P i false`, `P i true`; fees `f i r ≥ 0`.

**Formalization Note.** Stages are 0-based. `prior i` is `π_i(1)`, the probability that the fact is
`true`, so `π_i(0) = 1 - prior i`. The alphabet is per stage, since full support on one shared
alphabet would restrict the class. `N = 0`, `q = 0` and `S i = ∅` are allowed. Inputs are real, not
rational: the rational case is an instance. `normalCalls i` counts the environment calls charged
at the ordinary write of stage `i`: §2 fixes no such count, it only lets `H₀` bound the normal
calls, so `H₀ = ∑ i, normalCalls i` (all zero bounds reviews and corrections only). -/
structure Instance (N q : ℕ) where
  /-- The compatibility set `S i`. -/
  S : Fin N → Finset (Fin q)
  /-- The review alphabet of stage `i`. -/
  α : Fin N → Type
  /-- The alphabet is finite. -/
  [fintypeα : ∀ i, Fintype (α i)]
  /-- The alphabet has decidable equality. -/
  [decEqα : ∀ i, DecidableEq (α i)]
  /-- The prior probability `π_i(1)` of the fact being `true`. -/
  prior : Fin N → ℝ
  prior_pos : ∀ i, 0 < prior i
  prior_lt_one : ∀ i, prior i < 1
  /-- The review law `P_i^x`. -/
  P : (i : Fin N) → Bool → PMF (α i)
  P_support : ∀ i x y, P i x y ≠ 0
  P_ne : ∀ i, P i false ≠ P i true
  /-- The review price `c i`. -/
  c : Fin N → ℝ
  c_pos : ∀ i, 0 < c i
  /-- The fee `f i r` of the actual correction of stage `i` with tool `r`. -/
  f : Fin N → Fin q → ℝ
  f_nonneg : ∀ i r, 0 ≤ f i r
  /-- The normal calls charged at the ordinary write of stage `i`. -/
  normalCalls : Fin N → ℕ

attribute [instance] Instance.fintypeα Instance.decEqα

/-- Review alphabets carry the discrete σ-algebra. -/
instance Instance.measurableSpaceα {N q : ℕ} (I : Instance N q) (i : Fin N) :
    MeasurableSpace (I.α i) := ⊤

instance Instance.discreteα {N q : ℕ} (I : Instance N q) (i : Fin N) :
    DiscreteMeasurableSpace (I.α i) := ⟨fun _ => trivial⟩

/-- `f_max = max f_ir` over compatible pairs, or zero when there is no compatible pair, §2, p.5. -/
noncomputable def fmax {N q : ℕ} (I : Instance N q) : ℝ :=
  let fees : Finset ℝ := Finset.univ.biUnion fun i => (I.S i).image (I.f i)
  if h : fees.Nonempty then fees.max' h else 0

end CausalFailureRank


