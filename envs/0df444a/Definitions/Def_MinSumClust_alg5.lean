-- Prove2me | Definitions.Def_MinSumClust_alg5
-- name    : MinSumClust_alg5
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:46.398376+00:00
-- url     : https://prove2.me/theorems/59c18ba1-20af-4a9b-80f1-984da53842fe
-- title:
--   Algorithm 5: pre-processing into matched and residual clusters
-- statement:
--   Given $\mathcal S_1,\mathcal S_2$ and the labelings, Algorithm 5 (p.44) starts with $\mathcal S_1^{(\mathrm{match})}=\mathcal S_2^{(\mathrm{match})}=\emptyset$, $\mathcal S_1^{(\mathrm{res})}=\mathcal S_1$, $\mathcal S_2^{(\mathrm{res})}=\mathcal S_2$ and, while some $S_1\in\mathcal S_1^{(\mathrm{res})}$ has no $S_2\in\mathcal S_2^{(\mathrm{res})}$ with $\ell_L(S_2)=S_1$, moves $S_1$ to $\mathcal S_1^{(\mathrm{match})}$ and $\ell_M(S_1)$ (if $\ne\bot$) to $\mathcal S_2^{(\mathrm{match})}$. At the end $\mathcal S_2^{(\mathrm{match})}=\{\ell_M(S_1):S_1\in\mathcal S_1^{(\mathrm{match})},\ \ell_M(S_1)\ne\bot\}$ and every residual $S_1$ has a link from a residual $S_2$.
--
--   **Formalization Note** The order in which clusters are moved does not change the result: moving a cluster only shrinks $\mathcal S_2^{(\mathrm{res})}$, so every order ends at the least set $\mathcal S_1^{(\mathrm{match})}$ closed under the rule. Lean computes this set by $|\mathcal S_1|$ parallel rounds.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Algorithm 5, p.44 (PDF p.46)

import Mathlib
import Definitions.Def_MinSumClust_Bipoint

namespace MinSumClust

variable {D : Type} [Fintype D] [DecidableEq D]

/-- The partition produced by Algorithm 5: `𝒮₁^(match)`, `𝒮₂^(match)`, `𝒮₁^(res)`, `𝒮₂^(res)`. -/
structure Alg5Out (D : Type) where
  /-- `𝒮₁^(match)` -/
  match1 : Finset (Finset D)
  /-- `𝒮₂^(match)` -/
  match2 : Finset (Finset D)
  /-- `𝒮₁^(res)` -/
  res1 : Finset (Finset D)
  /-- `𝒮₂^(res)` -/
  res2 : Finset (Finset D)

/-- `{ℓ_M(S₁) : S₁ ∈ M, ℓ_M(S₁) ≠ ⊥}`. -/
def matchImage (ℓ : Labels D) (M : Finset (Finset D)) : Finset (Finset D) :=
  M.biUnion fun S => (ℓ.lM S).toFinset

/-- One parallel round of Algorithm 5: add to `M` every `S₁ ∈ 𝒮₁` that has no link from the
current `𝒮₂^(res) = 𝒮₂ \ ℓ_M(M)`. -/
def alg5Round (S₁ S₂ : Finpartition (Finset.univ : Finset D)) (ℓ : Labels D)
    (M : Finset (Finset D)) : Finset (Finset D) :=
  M ∪ S₁.parts.filter fun S => ∀ T ∈ S₂.parts \ matchImage ℓ M, ℓ.lL T ≠ some S

/-- **Algorithm 5 (Phase 1: Pre-processing)**, p.44 (PDF p.46).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Algorithm 5, p.44.

Starting from `𝒮₁^(match) = 𝒮₂^(match) = ∅`, while some `S₁ ∈ 𝒮₁^(res)` has no `S₂ ∈ 𝒮₂^(res)`
with `ℓ_L(S₂) = S₁`, move `S₁` to `𝒮₁^(match)` and `ℓ_M(S₁)` (if `≠ ⊥`) to `𝒮₂^(match)`.

**Formalization Note.** The paper does not fix which such `S₁` is moved first. The final partition
does not depend on it: moving a cluster only shrinks `𝒮₂^(res)`, so every order ends at the least
set `𝒮₁^(match)` closed under the rule. Lean computes that set by `|𝒮₁|` parallel rounds (each round
that changes the set adds a cluster of `𝒮₁`). Then `𝒮₂^(match) = ℓ_M(𝒮₁^(match)) \ {⊥}`,
`𝒮₁^(res) = 𝒮₁ \ 𝒮₁^(match)` and `𝒮₂^(res) = 𝒮₂ \ 𝒮₂^(match)`. -/
def alg5 (S₁ S₂ : Finpartition (Finset.univ : Finset D)) (ℓ : Labels D) : Alg5Out D :=
  let M := (alg5Round S₁ S₂ ℓ)^[S₁.parts.card] ∅
  ⟨M, matchImage ℓ M, S₁.parts \ M, S₂.parts \ matchImage ℓ M⟩

end MinSumClust


