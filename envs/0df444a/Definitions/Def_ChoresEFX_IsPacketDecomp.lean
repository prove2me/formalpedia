-- Prove2me | Definitions.Def_ChoresEFX_IsPacketDecomp
-- name    : ChoresEFX_IsPacketDecomp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:34.868266+00:00
-- url     : https://prove2.me/theorems/08069f9d-d4a1-4356-98d3-9af1a306034f
-- title:
--   The packet decomposition, Table 1 and the shape of a decomposition
-- statement:
--   A rounded bundle $Y$ is decomposed as $Y=S\sqcup K_1\sqcup\dots\sqcup K_\nu$.
--
--   - For $k=1$, the packets are the singletons of the chores with $p_g>\beta$, and $S$ is the rest.
--   - For $k\ge2$, let $T$ be a set of $k$ highest-price chores of $Y$. If the $(k+1)$-st chore has price greater than $\rho$, then $T$ and that singleton are the packets. Otherwise $T$ is the only packet when $p(T)>\rho$, and there is no packet when $p(T)\le\rho$.
--
--   **Table 1** bounds $p(S)$ by the entries $U+\beta,\ U,\ U-\beta$ for $k=1$, and $U+\rho,\ U,\ U-k\beta$ for $k\ge2$, in the columns $\nu=0,1,2$.
--
--   The decomposition prepares the third stage, in which packets are moved as whole units.
--
--   **Formalization Note** $\nu$ is the length of the list of packets. Ties among prices are free. `IsDecomposition` says that all residual bundles and all packets together partition the chores.
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Packet Decomposition and Table 1, p.11

import Mathlib
import Definitions.Def_ChoresEFX_IsCappedPriceStructure

namespace ChoresEFX

open Finset

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **A set of `k` highest-price chores** of `Y` (all of `Y` if `|Y| ≤ k`; any choice among price ties).

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…), "Packet Decomposition", p.11. -/
def IsTopK (p : κ → ℝ) (k : ℕ) (Y T : Finset κ) : Prop :=
  T ⊆ Y ∧ T.card = min k Y.card ∧ ∀ a ∈ T, ∀ b ∈ Y \ T, p b ≤ p a

/-- **The packet decomposition of one bundle**, "Packet Decomposition", p.11 (Qin et al., STOC 2027
submission).

For `k = 1`: the packets are the singletons `{g}` of the chores of `Y` with `p_g > β` and `S = Y \ H`.
For `k ≥ 2`: with `T` a set of `k` highest-price chores of `Y`, if the `(k+1)`-st chore has price `> ρ`,
then `T` and that singleton are the packets; otherwise there is one packet `T` when `p(T) > ρ`, and no
packet else. The residual bundle `S` is what remains.

**Formalization Note.** `ν_i` is the length of the list `K`. Ties among prices are free (paper.md
decision 8). -/
def IsAgentPacketDecomp (k : ℕ) (β ρ : ℝ) (p : κ → ℝ) (Y S : Finset κ) (K : List (Finset κ)) : Prop :=
  if k = 1 then
    K.Nodup ∧ (∀ P, P ∈ K ↔ ∃ g ∈ Y, β < p g ∧ P = {g}) ∧ S = Y.filter (fun g => ¬ β < p g)
  else
    ∃ T : Finset κ, IsTopK p k Y T ∧
      ((∃ e ∈ Y \ T, (∀ b ∈ Y \ T, p b ≤ p e) ∧ ρ < p e ∧ K = [T, ({e} : Finset κ)] ∧
           S = (Y \ T).erase e) ∨
        ((∀ e ∈ Y \ T, p e ≤ ρ) ∧
          ((ρ < priceOf p T ∧ K = [T] ∧ S = Y \ T) ∨ (priceOf p T ≤ ρ ∧ K = [] ∧ S = Y))))

/-- **The upper bound on `p(S_i)`**, Table 1, p.11 (Qin et al., STOC 2027 submission): with `ν = ν_i`,
for `k = 1` the entries are `U + β`, `U`, `U − β`; for `k ≥ 2` they are `U + ρ`, `U`, `U − kβ`.

**Formalization Note.** `ν ≥ 3` gets the last column; Lemma 3.5 shows that `ν ≤ 2`. -/
noncomputable def tableBound (k : ℕ) (β ρ U : ℝ) (ν : ℕ) : ℝ :=
  if k = 1 then
    (if ν = 0 then U + β else if ν = 1 then U else U - β)
  else
    (if ν = 0 then U + ρ else if ν = 1 then U else U - (k : ℝ) * β)

/-- The part of a decomposition: `inl i` is the residual bundle `S_i`, and `inr ⟨i, ℓ⟩` is the packet
`K_{i,ℓ}`; see "Packet Decomposition", p.11 (Qin et al., STOC 2027 submission). -/
def decompPart (S : ι → Finset κ) (K : ι → List (Finset κ)) :
    ι ⊕ (Σ i, Fin (K i).length) → Finset κ
  | Sum.inl i => S i
  | Sum.inr x => (K x.1).get x.2

/-- Residual bundles and packets together partition the chores: `Y_i = S_i ⊔ K_{i,1} ⊔ … ⊔ K_{i,ν_i}`
with `Y` a complete allocation, p.11 (Qin et al., STOC 2027 submission). -/
def IsDecomposition (S : ι → Finset κ) (K : ι → List (Finset κ)) : Prop :=
  ∀ g, ∃! x, g ∈ decompPart S K x

end ChoresEFX


