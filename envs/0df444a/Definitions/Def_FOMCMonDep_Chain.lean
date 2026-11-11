-- Prove2me | Definitions.Def_FOMCMonDep_Chain
-- name    : FOMCMonDep_Chain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:32.149863+00:00
-- url     : https://prove2.me/theorems/ce713d12-e533-4801-a562-810b91a8ee36
-- title:
--   Chains and their radius-$r$ width (Definition 6.2)
-- statement:
--   A **chain** in a graph $G$ is a decreasing sequence $V(G)=S_1\supseteq\dots\supseteq S_\ell=\emptyset$ of vertex sets; $\ell$ is its length. Its **radius-$r$ width** is
--   $$\max_{2\le i\le\ell}\ \max_{v\in V(G)}\ \bigl|\mathrm{Ball}^{S_i}_r(v)/\mathcal P_{S_{i-1}}\bigr|,$$
--   the largest number of parts of the atomic-type partition $\mathcal P_{S_{i-1}}$ met by a flip-metric ball $\mathrm{Ball}^{S_i}_r(v)=\bigcap\{\mathrm{Ball}^H_r(v): H \text{ an } S_i\text{-flip of } G\}$. A chain is input as $\ell$ followed by the $\ell$ sets as $0/1$ vectors.
--
--   Chains of constant length and subpolynomial width are what the companion paper computes (Theorem 6.3) and what Lemma 6.4 turns into definable construction sequences.
--
--   **Formalization Note** The pieces $\mathcal P_S$ (`oneType`), the flip-metric ball (`flipBall`) and the count of parts met (`partsHit`) are the published `MonDepMW` definitions. The maximum over an empty range ($\ell=1$) is $0$.
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), §6, p.28 (PDF 30)

import Mathlib
import Definitions.Def_MonDepMW_IsFlip
import Definitions.Def_MonDepMW_RunsWithin

set_option autoImplicit false

namespace FOMCMonDep

/-- **Chains (Definition 6.2).** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §6, p.28 (PDF 30): "A chain in a graph G is a decreasing
sequence V(G) = S1 ⊇ · · · ⊇ Sℓ = ∅ of vertex sets."

**Formalization Note.** The chain is the list `[S₁, …, S_ℓ]`; its length `ℓ` is the length of the list, at least
`1`. For `n = 0` the one-element list `[∅]` is a chain. -/
def IsChain {n : ℕ} (S : List (Finset (Fin n))) : Prop :=
  S.head? = some Finset.univ ∧ S.getLast? = some ∅ ∧ S.IsChain (fun A B => B ⊆ A)

/-- **The radius-`r` width of a chain (Definition 6.2).** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §6, p.28 (PDF 30): "Its
radius-r width, for r ∈ N, is defined as max_{2⩽i⩽ℓ} max_{v∈V(G)} |ATypes^G(Ball^{Si}_r(v)/Si−1)| =
max_{2⩽i⩽ℓ} max_{v∈V(G)} |Ball^{Si}_r(v)/𝒫_{Si−1}|, where Ball^S_r(v) is defined above via S-flips and 𝒫_S is the
partition into atomic types over S."

**Formalization Note.** With the published `MonDepMW` pieces: `𝒫_S` is `oneType G S`, `Ball^S_r(v)` is
`flipBall G (oneType G S) r v` (the intersection of the radius-`r` balls of `v` over all `𝒫_S`-flips), and
`|X/𝒫|` is `partsHit 𝒫 X`. List index `i − 1` is the paper's `S_i`. The maximum over an empty range (`ℓ = 1`) is
`0`. -/
noncomputable def chainWidth {n : ℕ} (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))) (r : ℕ) : ℕ :=
  ((Finset.Icc 2 S.length) ×ˢ (Finset.univ : Finset (Fin n))).sup fun p =>
    MonDepMW.partsHit (MonDepMW.oneType G (S.getD (p.1 - 2) ∅))
      (MonDepMW.flipBall G (MonDepMW.oneType G (S.getD (p.1 - 1) ∅)) r p.2)

/-- **A chain as an input or output**: `ℓ`, then the `ℓ` sets as blocks of `n` cells `0/1` (published `setBits`). -/
noncomputable def chainCode {n : ℕ} (S : List (Finset (Fin n))) : List ℤ :=
  (S.length : ℤ) :: S.flatMap MonDepMW.setBits

end FOMCMonDep


