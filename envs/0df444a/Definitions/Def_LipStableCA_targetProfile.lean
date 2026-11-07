-- Prove2me | Definitions.Def_LipStableCA_targetProfile
-- name    : LipStableCA_targetProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:50:14.258195+00:00
-- url     : https://prove2.me/theorems/46cf3a28-2bc3-4fcd-91f5-4fc16ce459d3
-- title:
--   The hidden-target profiles of §5.1
-- statement:
--   Fix positive integers $q\le n$ and $k$ with $qk\le m/2$. $\mathcal Y$ is the set of ordered $q$-tuples of pairwise disjoint $k$-element subsets of $M$. For $Y\in\mathcal Y$, $v^Y_i(Q)=\mathbf 1\{Y_i\subseteq Q\}+|Q|/m$ for $i\le q$ and $v^Y_i(Q)=0$ for $i>q$. For a mechanism and a seed $\omega$, $C(\omega)$ is the number of pairs $(i,Y)$ of an active bidder $i$ and a tuple $Y$ with $Y_i\subseteq S_i(v^Y;\omega)$.
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), pp.23–24

import Definitions.Def_LipStableCA_Mechanism

namespace LipStableCA

variable {n m : ℕ}

open Classical in
/-- `𝒴`, p.23: all ordered `q`-tuples of pairwise disjoint `k`-element subsets of `M`. -/
noncomputable def targetTuples (q k m : ℕ) : Finset (Fin q → Finset (Fin m)) :=
  Finset.univ.filter fun Y =>
    (∀ a, (Y a).card = k) ∧ ∀ a a', a ≠ a' → Disjoint (Y a) (Y a')

open Classical in
/-- The profile `v^Y`, p.23: `v^Y_i(Q) = 1{Yᵢ ⊆ Q} + |Q|/m` for an active bidder `i ≤ q`, and
`v^Y_i(Q) = 0` for `i > q`. **Formalization Note.** Bidders `1, …, q` are those `i : Fin n` with
`i.val < q`. -/
noncomputable def targetProfile {q : ℕ} (Y : Fin q → Finset (Fin m)) : Profile n m :=
  fun i Q =>
    if h : i.val < q then (if Y ⟨i.val, h⟩ ⊆ Q then 1 else 0) + (Q.card : ℝ) / (m : ℝ) else 0

open Classical in
/-- `C(ω)`, Lemma 5.6, p.24: the number of pairs `(i, Y)` of an active bidder `i` and a tuple `Y ∈ 𝒴` such
that `Yᵢ ⊆ Sᵢ(v^Y; ω)`. -/
noncomputable def targetCount {Ω : Type*} {q : ℕ} (M : Mechanism n m Ω) (hq : q ≤ n) (k : ℕ)
    (ω : Ω) : ℕ :=
  ((Finset.univ ×ˢ targetTuples q k m).filter fun p : Fin q × (Fin q → Finset (Fin m)) =>
    p.2 p.1 ⊆ (M.alloc (targetProfile p.2) ω).1 (Fin.castLE hq p.1)).card

end LipStableCA


