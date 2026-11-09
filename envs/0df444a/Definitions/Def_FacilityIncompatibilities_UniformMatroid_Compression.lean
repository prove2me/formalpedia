-- Prove2me | Definitions.Def_FacilityIncompatibilities_UniformMatroid_Compression
-- name    : FacilityIncompatibilities_UniformMatroid_Compression
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:32.973348+00:00
-- url     : https://prove2.me/theorems/f937ced9-be66-4afe-9d16-6aa1feb6be84
-- title:
--   §2.1 — the weight W(π), minimum-cost injections μ : O → S, the count q(π) and the tie-broken assignment π
-- statement:
--   Fix facility sets $S$, $O$ and a feasible assignment $\sigma_O:V_C\to O$. For an assignment $\pi:V_C\to S$ put
--
--   $$W(\pi)=\sum_{j\in V_C}d(\sigma_O(j),\pi(j)).$$
--
--   $\pi$ is a **$W$-minimizer** if it is a feasible assignment to $S$ with $W(\pi)\le W(\pi')$ for every feasible $\pi':V_C\to S$. A **minimum-cost injection** $\mu:O\to S$ is an injection minimizing $\sum_{o\in O}d(o,\mu(o))$ over all injections $O\to S$. For such $\mu$ let
--
--   $$q(\pi)=\big|\{j\in V_C:\pi(j)\notin\mu(O)\}\big|.$$
--
--   The **injection of §2.1** is, when $|O|<|S|$, a minimum-cost injection with $\mu(i)=i$ for every $i\in O\cap S$ (no condition when $|O|\ge|S|$). The **assignment $\pi$ of §2.1** is a $W$-minimizer which, when $|O|<|S|$, also minimizes $q$ among all $W$-minimizers. Its image is $P=\pi(V_C)$.
--
--   These are the objects of Lemmas 9, 10, 12, 13, 14 and 15.
--
--   **Formalization Note** $\mu$ is a function $F\to F$ mapping $O$ into $S$ and injective on $O$; its values off $O$ play no role. All minimizations are genuine finite minimizations stated as predicates; none presupposes a conclusion of the lemmas.
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, §1.2, printed p.4 / PDF p.5, and §2.1, printed p.5 / PDF p.6; q(π) printed p.13 / PDF p.14

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Model

namespace FacilityIncompatibilities.UniformMatroid

/-- `q(π) = |{j ∈ V_C : π(j) ∉ μ(O)}|`, the tie-breaking count of §2.1 (printed p.5; written
`q(π)` on printed p.13). -/
def outsideCount {C F : Type*} [Fintype C] [DecidableEq F] (O : Finset F) (μ : F → F)
    (π : C → F) : ℕ :=
  (Finset.univ.filter fun j => π j ∉ O.image μ).card

namespace Instance

variable {C F : Type*} (I : Instance C F)

/-- **`W(π) = ∑_{j ∈ V_C} d(σ_O(j), π(j))`** (§1.2, printed p.4, and §2.1, printed p.5). -/
def W [Fintype C] (σO π : C → F) : ℝ := ∑ j, I.fdist (σO j) (π j)

/-- `π` is a feasible assignment to `S` minimizing `W(π)` among all feasible assignments to `S`
(§2.1, printed p.5). -/
def IsWMin [Fintype C] (S : Finset F) (σO π : C → F) : Prop :=
  I.IsFeasibleAssignment S π ∧ ∀ π', I.IsFeasibleAssignment S π' → I.W σO π ≤ I.W σO π'

/-- `μ` is a **minimum-cost injection `O → S`** (§2.1, printed p.5; Lemmas 12–13, printed p.10):
`μ` maps `O` injectively into `S` and minimizes `∑_{o ∈ O} d(o, μ(o))` among all such maps.

**Formalization Note** `μ` is a function on all of `F`; only its values on `O` matter. -/
def IsMinInjection (O S : Finset F) (μ : F → F) : Prop :=
  (∀ o ∈ O, μ o ∈ S) ∧ Set.InjOn μ (O : Set F) ∧
    ∀ μ' : F → F, (∀ o ∈ O, μ' o ∈ S) → Set.InjOn μ' (O : Set F) →
      ∑ o ∈ O, I.fdist o (μ o) ≤ ∑ o ∈ O, I.fdist o (μ' o)

/-- The injection `μ` of §2.1 (printed p.5): when `|O| < |S|`, a minimum-distance injection
`O → S` with `μ(i) = i` for every `i ∈ O ∩ S`. When `|O| ≥ |S|` no condition is imposed (no
injection `O → S` is used). -/
def IsSection21Injection [DecidableEq F] (O S : Finset F) (μ : F → F) : Prop :=
  O.card < S.card → I.IsMinInjection O S μ ∧ ∀ i ∈ S ∩ O, μ i = i

/-- **The assignment `π` of §2.1** (printed p.5): a feasible assignment to `S` minimizing `W(π)`;
if `|O| < |S|`, among all such minimizers it also minimizes `q(π)`. -/
def IsTieBrokenWMin [Fintype C] [DecidableEq F] (S O : Finset F) (σO : C → F) (μ : F → F)
    (π : C → F) : Prop :=
  I.IsWMin S σO π ∧
    (O.card < S.card → ∀ π', I.IsWMin S σO π' → outsideCount O μ π ≤ outsideCount O μ π')

end Instance

/-- The image `P = π(V_C)` of an assignment, as a facility set. -/
def assignImage {C F : Type*} [Fintype C] [DecidableEq F] (π : C → F) : Finset F :=
  Finset.univ.image π

end FacilityIncompatibilities.UniformMatroid


