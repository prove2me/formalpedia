-- Prove2me | Definitions.Def_PrivLittlestone_Alg1Spec
-- name    : PrivLittlestone_Alg1Spec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:49.594216+00:00
-- url     : https://prove2.me/theorems/04ee67d7-c48b-4476-a22c-9a3e007b2565
-- title:
--   Public inputs of Algorithm 1
-- statement:
--   The **public inputs of Algorithm 1** are: a ranked candidate system on records $Z$ and candidates $U$; the phase cap $K$; the number $m$ of samples per phase; the horizon $T$; the sampling scales $\eta, a$ of (2); the threshold $U$; the counter privacy parameter $\varepsilon_a$; a public aggregation rule $\mathrm{Agg} : U^m \to \{0,1\}^X$; a deterministic training filter $\kappa(g, z) \in Z \cup \{\bot\}$; and a fallback classifier $g_{\mathrm{fb}}$.
--
--   **Formalization Note** $\bot$ is `none`. Conditions on the parameters are hypotheses of the theorems, not fields.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §4.1, p.6, and §4.2, p.7

import Mathlib
import Definitions.Def_PrivLittlestone_RankedCandidateSystem

namespace PrivLittlestone

/-- The **public inputs of Algorithm 1** (He–He, *Private Online Learning of Littlestone Classes
and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), §4.1, p.6, and §4.2,
p.7): a ranked candidate system on records `Z` and candidates `U`, the phase cap `K`, the number
`m` of samples per phase, the public horizon `T`, the sampling scales `η, a` of (2), the threshold
`U` (here `Uth`), the counter privacy parameter `ε_a`, a public aggregation rule
`Agg : U^m → {0,1}^X`, a deterministic training filter `κ(g, z) ∈ Z ∪ {⊥}` and a fallback
classifier `g_fb`.

**Formalization Note** `⊥` is `none`. No condition is bundled: the conditions on the parameters
(`K, m ≥ 1`, `η, a, U, ε_a > 0`, (4)–(8)) are hypotheses of the theorems that use them. -/
structure Alg1Spec (X Z U : Type*) (D : ℕ) (B : ℝ) where
  /-- the ranked candidate system -/
  sys : RankedCandidateSystem Z U D B
  /-- the phase cap -/
  K : ℕ
  /-- the number of samples per phase -/
  m : ℕ
  /-- the public horizon -/
  T : ℕ
  /-- the loss scale of (2) -/
  η : ℝ
  /-- the rank scale of (2) -/
  a : ℝ
  /-- the stopping threshold `U` -/
  Uth : ℝ
  /-- the counter privacy parameter `ε_a` -/
  εa : ℝ
  /-- the public aggregation rule `Agg` -/
  agg : (Fin m → U) → X → Bool
  /-- the deterministic training filter `κ` (`none` = `⊥`) -/
  κ : (X → Bool) → X × Bool → Option Z
  /-- the public fallback classifier `g_fb` -/
  gfb : X → Bool

end PrivLittlestone


