-- Prove2me | Definitions.Def_MinSumClust_alg6
-- name    : MinSumClust_alg6
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:50:22.893232+00:00
-- url     : https://prove2.me/theorems/ab0fc33e-5170-4e49-ab25-43b759c0ba19
-- title:
--   Algorithm 6: opening clusters among the residual clusters
-- statement:
--   Algorithm 6 (p.46) takes the residual clusters of Algorithm 5 and the labelings, and produces opened clusters $\mathcal S_{1,O}^{(\mathrm{res})}$, $\mathcal S_{2,O}^{(\mathrm{res})}$ and a partial assignment $A'$:
--
--   1. $D^{(\mathrm{res})}=\bigcup_{S_2\in\mathcal S_2^{(\mathrm{res})}}S_2$ (26);
--   2. for each $S_1\in\mathcal S_1^{(\mathrm{res})}$ independently, $M(S_1)$ is uniform among the residual $S_2$ with $\ell_L(S_2)=S_1$; $\mathcal S_2'=\mathcal S_2^{(\mathrm{res})}\setminus\{M(S_1)\}$;
--   3. a uniformly random subset of $\mathcal S_2'$ of size $|\mathcal S_2'|-(k_2-k)$ is opened;
--   4. the clusters $S_1\in\mathcal S_1^{(\mathrm{res})}$ are processed in increasing order of size (ties broken arbitrarily). With $G$ the good clients of $S_1\cap D^{(\mathrm{res})}$ and $D_{\mathrm{settled}}$ the union of the opened residual $S_2$ so far: if $|G\cap D_{\mathrm{settled}}|<\frac13|G|$, or some unopened $S_2\in\mathcal S_2'$ has $\ell_L(S_2)=S_1$, then $S_1$ is opened and $A'(i)=S_1$ for the bad clients $i$ of every residual $S_2$ linked to $S_1$; otherwise $M(S_1)$ is opened and, if $G\ne\emptyset$, a uniform $i\in G\cap D_{\mathrm{settled}}$ is chosen and $A'(j)=C_2(i)$ for $j\in G\setminus D_{\mathrm{settled}}$.
--
--   **Formalization Note** Assigned clusters carry their side ($\mathcal S_1$ or $\mathcal S_2$), since one set can be a cluster of both solutions. "Breaking ties arbitrarily" is a ranking parameter, and the milestones hold for every ranking.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Algorithm 6, p.46 (PDF p.48); (26), p.44

import Mathlib
import Definitions.Def_MinSumClust_pexp
import Definitions.Def_MinSumClust_Bipoint
import Definitions.Def_MinSumClust_alg5

namespace MinSumClust

variable {D : Type} [Fintype D] [DecidableEq D]

/-- The state and output of Algorithm 6: the opened clusters `𝒮₁,O^(res)`, `𝒮₂,O^(res)` and the
partial assignment `A′`. An assigned value is tagged by the side of its cluster (`0` for `𝒮₁`, `1`
for `𝒮₂`), because one set can be a cluster of both solutions. -/
structure Alg6Out (D : Type) where
  /-- `𝒮₁,O^(res)` -/
  open1 : Finset (Finset D)
  /-- `𝒮₂,O^(res)` -/
  open2 : Finset (Finset D)
  /-- the partial assignment `A′` -/
  assign : D → Option (Fin 2 × Finset D)

/-- The processing order of step 4 of Algorithm 6: increasing `|S₁|`, ties broken by the ranking
`rk`. -/
noncomputable def procOrder (rk : Finset D → ℕ) (s : Finset (Finset D)) : List (Finset D) :=
  s.toList.mergeSort fun A B => decide (A.card < B.card ∨ (A.card = B.card ∧ rk A ≤ rk B))

/-- Step 4 of Algorithm 6 for one cluster `S₁` (p.46): with `G` the good residual clients of `S₁`
and `D_settled` the union of `𝒮₂,O^(res)` so far, open `S₁` if `|G ∩ D_settled| < |G|/3` or some
unopened `S₂ ∈ 𝒮₂′` links to `S₁` (and assign the bad clients of every residual `S₂` linked to `S₁`
to `S₁`); otherwise open `M(S₁)` and, if `G ≠ ∅`, send `G \ D_settled` to `C₂(i)` for a uniform
`i ∈ G ∩ D_settled`. -/
noncomputable def alg6Process (S₁ S₂ : Finpartition (Finset.univ : Finset D)) (ℓ : Labels D)
    (o5 : Alg5Out D) (Mf : Finset D → Finset D) (S₂' : Finset (Finset D)) (st : Alg6Out D)
    (S : Finset D) : PMF (Alg6Out D) :=
  let G := (S ∩ o5.res2.biUnion id).filter fun j => (S₂.part j).card ≤ (S₁.part j).card
  let Ds := st.open2.biUnion id
  if 3 * (G ∩ Ds).card < G.card ∨ ∃ T ∈ S₂' \ st.open2, ℓ.lL T = some S then
    PMF.pure
      { st with
        open1 := insert S st.open1
        assign := fun i =>
          if ∃ T ∈ o5.res2, ℓ.lL T = some S ∧ i ∈ bad S₁ S₂ T then some (0, S) else st.assign i }
  else if h : (G ∩ Ds).Nonempty then
    (PMF.uniformOfFinset (G ∩ Ds) h).map fun i =>
      { st with
        open2 := insert (Mf S) st.open2
        assign := fun j => if j ∈ G \ Ds then some (1, S₂.part i) else st.assign j }
  else
    PMF.pure { st with open2 := insert (Mf S) st.open2 }

/-- **Algorithm 6 (Phase 2: Opening clusters among the residual clusters)**, p.46 (PDF p.48).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Algorithm 6, p.46, given the labelings `ℓ` and the output
`o5` of Algorithm 5:
1. `D^(res) = ⋃_{S₂ ∈ 𝒮₂^(res)} S₂` (26);
2. for each `S₁ ∈ 𝒮₁^(res)` independently a uniform `M(S₁)` from `{S₂ ∈ 𝒮₂^(res) : ℓ_L(S₂) = S₁}`;
   `𝒮₂′ = 𝒮₂^(res) \ {M(S₁)}`;
3. a uniform subset of `𝒮₂′` of size `|𝒮₂′| − (k₂ − k)` forms `𝒮₂,O^(res)`;
4. the clusters of `𝒮₁^(res)` in increasing size (`alg6Process`).

**Formalization Note.** "Breaking ties arbitrarily" is the ranking parameter `rk`; statements
quantify over every `rk`. The independent choices of step 2 are one uniform choice from their
product (`Fintype.piFinset`). Sizes use ℕ subtraction; the paper shows `|𝒮₂′| ≥ k₂ − k`
(Observation 48, Claim 58). -/
noncomputable def alg6 (S₁ S₂ : Finpartition (Finset.univ : Finset D)) (k : ℕ)
    (rk : Finset D → ℕ) (ℓ : Labels D) (o5 : Alg5Out D) : PMF (Alg6Out D) :=
  (unifOr (Fintype.piFinset fun S : Finset D =>
      if S ∈ o5.res1 then o5.res2.filter (fun T => ℓ.lL T = some S) else {∅}) (fun _ => ∅)).bind
    fun Mf =>
      let S₂' := o5.res2 \ o5.res1.image Mf
      (unifOr (S₂'.powersetCard (S₂'.card - (S₂.parts.card - k))) ∅).bind fun T =>
        (procOrder rk o5.res1).foldlM (alg6Process S₁ S₂ ℓ o5 Mf S₂') ⟨∅, T, fun _ => none⟩

end MinSumClust


