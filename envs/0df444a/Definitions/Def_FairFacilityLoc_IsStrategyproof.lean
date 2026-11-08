-- Prove2me | Definitions.Def_FairFacilityLoc_IsStrategyproof
-- name    : FairFacilityLoc_IsStrategyproof
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:13:01.293623+00:00
-- url     : https://prove2.me/theorems/8f608868-e45a-4564-8073-f97022cf8003
-- title:
--   Definition 2.4: strategyproofness, anonymity, coordinate independence
-- statement:
--   A mechanism $M$ is
--
--   1. **strategyproof** if $\|x_i-M(x;\mathcal G)\|_2\le\|x_i-M((x_i',x_{-i});\mathcal G)\|_2$ for every group structure, profile, agent $i$ and report $x_i'$;
--   2. **anonymous** if $M(x\circ\pi;\mathcal G)=M(x;\mathcal G)$ for every group structure, profile and permutation $\pi$ of $N$ with $\{j:i\in G_j\}=\{j:\pi(i)\in G_j\}$ for every $i$;
--   3. **coordinate-independent** if $M(x;\mathcal G)_r=M(x';\mathcal G)_r$ whenever $x_{ir}=x'_{ir}$ for every $i$.
--
--   The module also defines **unanimity**, $M(z,\dots,z;\mathcal G)=z$ (Proposition 3.3).
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Definition 2.4, p.15 (PDF p.17); unanimity Proposition 3.3, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_FairFacilityLoc_Mechanism

namespace FairFacilityLoc

/-- **Strategyproofness** (Yan, Zhou, manuscript, sha256 642a1268…, Definition 2.4, p.15, PDF p.17):
`∥x_i − M(x; G)∥₂ ≤ ∥x_i − M((x′_i, x_{−i}); G)∥₂` for every group structure, profile, agent and report.

**Formalization Note.** `Function.update x i x'` is the printed `(x′_i, x_{−i})`. -/
def IsStrategyproof {d : ℕ} (M : Mechanism d) : Prop :=
  ∀ {n m : ℕ} (G : GroupStructure n m) (x : Fin n → GeoSemialgCSP.E d) (i : Fin n) (x' : GeoSemialgCSP.E d),
    ‖x i - M G x‖ ≤ ‖x i - M G (Function.update x i x')‖

/-- **Anonymity** (Definition 2.4, p.15, PDF p.17): `M(x ∘ π; G) = M(x; G)` for every permutation `π` of
the agents that preserves group memberships, that is, `{j : i ∈ G_j} = {j : π(i) ∈ G_j}` for every `i`. -/
def IsAnonymous {d : ℕ} (M : Mechanism d) : Prop :=
  ∀ {n m : ℕ} (G : GroupStructure n m) (x : Fin n → GeoSemialgCSP.E d) (π : Equiv.Perm (Fin n)),
    (∀ i j, i ∈ G.G j ↔ π i ∈ G.G j) → M G (x ∘ π) = M G x

/-- **Coordinate independence** (Definition 2.4, p.15, PDF p.17): `M(x; G)_r = M(x′; G)_r` for all profiles
with `x_{ir} = x′_{ir}` for every `i`. -/
def IsCoordinateIndependent {d : ℕ} (M : Mechanism d) : Prop :=
  ∀ {n m : ℕ} (G : GroupStructure n m) (r : Fin d) (x x' : Fin n → GeoSemialgCSP.E d),
    (∀ i, x i r = x' i r) → M G x r = M G x' r

/-- **Unanimity** (Proposition 3.3, p.18, PDF p.20): `M(z, …, z; G) = z` for every `z`. -/
def IsUnanimous {d : ℕ} (M : Mechanism d) : Prop :=
  ∀ {n m : ℕ} (G : GroupStructure n m) (z : GeoSemialgCSP.E d), M G (fun _ => z) = z

end FairFacilityLoc


