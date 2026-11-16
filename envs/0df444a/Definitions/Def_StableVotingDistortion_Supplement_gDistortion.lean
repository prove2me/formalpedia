-- Prove2me | Definitions.Def_StableVotingDistortion_Supplement_gDistortion
-- name    : StableVotingDistortion_Supplement_gDistortion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:55:25.755309+00:00
-- url     : https://prove2.me/theorems/4473664e-d1b4-4c67-b002-24694af28442
-- title:
--   $\mathrm{distortion}(g)$ and the class of nonconstant activations (Theorem 7)
-- statement:
--   An **activation** is a continuous, nondecreasing function $g:[0,1]\to[0,1]$; the class of Theorem 7 consists of the activations that are **not constant** on $[0,1]$ (no normalization $g(0)=0$, $g(1)=1$ is imposed).
--
--   A real number $B$ is a **distortion bound for $g$** if in every election (finitely many voters and candidates, at least one of each) every $g$-stable lottery $D$ has distortion at most $B$: for every pseudometric $d$ consistent with the election and every candidate $a$, $\mathrm{cost}_d(D)\le B\cdot\mathrm{cost}_d(a)$.
--
--   The **distortion of $g$**, the worst-case distortion of a $g$-stable lottery over all elections, is
--   $$
--   \mathrm{distortion}(g)=\inf\{B\in\mathbb R : B \text{ is a distortion bound for } g\}\in\mathbb R\cup\{\pm\infty\},
--   $$
--   equal to $+\infty$ when no real bound exists.
--
--   These objects state the optimal-activation problem of Theorem 7.
--
--   **Formalization Note** The worst case (a supremum of cost ratios) is written as the least valid bound in the extended reals, with the base mission's inequality form of a distortion bound; bounds are upward closed because costs are nonnegative.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6, p.20; Theorem 7, p.21

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_HasDistortionAtMost
import Definitions.Def_StableVotingDistortion_IsGStable

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion.Supplement

/-- `g` is a continuous, nondecreasing function `[0, 1] → [0, 1]` that is **not constant** on `[0, 1]`: the
class of activations over which Theorem 7 takes its infimum.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 7, p.21: "the infimum ranges over all
continuous, nondecreasing functions g : [0, 1] → [0, 1] that are not constant".

**Formalization Note.** No normalization `g(0) = 0`, `g(1) = 1` is imposed. -/
def IsNonconstantActivation (g : ℝ → ℝ) : Prop :=
  IsActivation g ∧ ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1, g x ≠ g y

/-- `B` bounds the distortion of `g`-stable lotteries: in every election (finite nonempty voters and
candidates), every `g`-stable lottery has distortion at most `B`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6, p.20: "Writing distortion(g) for the
worst-case distortion of a g-stable lottery over all elections"; §2, p.6 (distortion).

**Formalization Note.** Distortion of a lottery in one election is the base mission's inequality form
`HasDistortionAtMost`. -/
def IsGDistortionBound (g : ℝ → ℝ) (B : ℝ) : Prop :=
  ∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C) (D : C → ℝ),
    IsGStable g E D → HasDistortionAtMost E D B

/-- `distortion(g)`, the worst-case distortion of a `g`-stable lottery over all elections, as an extended real:
the infimum of the real bounds `B` valid for every `g`-stable lottery of every election (`+∞` if there is none).

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6, p.20: "Writing distortion(g) for the
worst-case distortion of a g-stable lottery over all elections".

**Formalization Note.** The worst case (a supremum of cost ratios) equals the least valid bound; the bounds are
upward closed since costs are nonnegative. Valued in `EReal`, so a `g` with no finite bound has distortion `⊤`. -/
noncomputable def gDistortion (g : ℝ → ℝ) : EReal :=
  sInf {x : EReal | ∃ B : ℝ, x = (B : EReal) ∧ IsGDistortionBound g B}

end StableVotingDistortion.Supplement


