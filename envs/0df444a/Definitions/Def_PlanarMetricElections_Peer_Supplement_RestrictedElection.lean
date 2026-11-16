-- Prove2me | Definitions.Def_PlanarMetricElections_Peer_Supplement_RestrictedElection
-- name    : PlanarMetricElections_Peer_Supplement_RestrictedElection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:43:19.014207+00:00
-- url     : https://prove2.me/theorems/ff7a61b9-3598-4fd9-923c-fc55008f733a
-- title:
--   Restricted Euclidean election factor $\mathrm{RR}_{\ell_2}(k)$ on $\mathbb R^r$ (equation (2))
-- statement:
--   A **Euclidean election** on $\mathbb R^r$ consists of a nonempty finite set of voters $V\subseteq\mathbb R^r$ and a nonempty finite set of candidates $C\subseteq\mathbb R^r$ (the two sets may overlap) such that no voter is equidistant from two distinct candidates. Voter $v$ prefers $c$ to a nonempty coalition $S$ when $\|v-c\|_2<\|v-s\|_2$ for every $s\in S$; the challenger's payoff is
--
--   $$P(V,S,c)=\frac{|\{v\in V:\ \|v-c\|_2<\|v-s\|_2\ \text{for all } s\in S\}|}{|V|}.$$
--
--   In the restricted–restricted game both the defending coalition and the challenger are drawn from $C$, and
--
--   $$\mathrm{RR}_{\ell_2}(k)=\sup_{(V,C)}\ \inf_{\substack{S\subseteq C\\ 1\le |S|\le k}}\ \max_{c\in C} P(V,S,c),$$
--
--   the supremum ranging over all Euclidean elections on $\mathbb R^r$.
--
--   **Formalization Note** For $k\ge1$ every range is nonempty and contained in $[0,1]$, so the real `sSup`/`sInf` are the true extrema. Taking the maximum over all $c\in C$ rather than $C\setminus S$ changes nothing, because a member of $S$ captures no voter.
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Section 2 (Metric elections), p. 3 (PDF p. 4); Section 4, equation (2), pp. 6–7 (PDF pp. 7–8)

import Definitions.Def_PlanarMetricElections_Peer_Supplement_EuclideanMass

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer.Supplement

/-- A finite-candidate Euclidean metric election on `ℝ^r`: nonempty finite voters `V` and
candidates `C` (which may overlap), with no voter equidistant from two distinct candidates. -/
def IsEuclidElection {r : ℕ} (V C : Finset (Euc r)) : Prop :=
  V.Nonempty ∧ C.Nonempty ∧
    ∀ v ∈ V, ∀ a ∈ C, ∀ b ∈ C, a ≠ b → dist v a ≠ dist v b

/-- Fraction of voters strictly closer (ℓ₂) to the challenger `c` than to every member of `S`. -/
def euclidPayoff {r : ℕ} (V S : Finset (Euc r)) (c : Euc r) : ℝ :=
  ((V.filter (fun v => ∀ s ∈ S, dist v c < dist v s)).card : ℝ) / (V.card : ℝ)

/-- Best response of a challenger restricted to `C` (supremum over `c ∈ C`). -/
def restrictedWorst {r : ℕ} (V C S : Finset (Euc r)) : ℝ :=
  sSup {p : ℝ | ∃ c ∈ C, p = euclidPayoff V S c}

/-- Value of the restricted game for one election: infimum over nonempty `S ⊆ C`, `|S| ≤ k`. -/
def restrictedInstance {r : ℕ} (V C : Finset (Euc r)) (k : ℕ) : ℝ :=
  sInf {x : ℝ | ∃ S : Finset (Euc r), S ⊆ C ∧ S.Nonempty ∧ S.card ≤ k ∧
    x = restrictedWorst V C S}

/-- The factor `RR_{ℓ₂}(k)` on `ℝ^r` of equation (2): supremum over Euclidean elections. -/
def restrictedFactor (r k : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ V C : Finset (Euc r), IsEuclidElection V C ∧ x = restrictedInstance V C k}

end PlanarMetricElections.Peer.Supplement


