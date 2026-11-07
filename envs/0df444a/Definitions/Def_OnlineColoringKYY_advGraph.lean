-- Prove2me | Definitions.Def_OnlineColoringKYY_advGraph
-- name    : OnlineColoringKYY_advGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:33.313003+00:00
-- url     : https://prove2.me/theorems/765926ca-1688-4dd6-ba6c-395c8ab37c40
-- title:
--   Graph $G_{A,x,n}$ built by the Section 4.2 adversary
-- statement:
--   Let $A$ be a deterministic online coloring algorithm, $x_0, \dots, x_{n-1} \in \{0,1\}^\ell$ the codes of the admissible sets, and $c(0), \dots, c(n-1)$ the colors produced by the adversary process. The **adversary's graph** $G_{A,x,n}$ on $\{0, \dots, n-1\}$ joins $i < j$ iff vertex $i$ was already paired when $j$ arrived (some $w < j$, $w \ne i$, has $c(w) = c(i)$) and its base color $\varphi(i)$ is not in $X_j$.
--
--   The definition module also proves that the prefix of $G_{A,x,n}$ at $v$ is the graph the adversary had built when $v$ arrived, so the color $A$ gives $v$ when $G_{A,x,n}$ is presented online is the color $c(v)$ of the process.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Adversary algorithm", printed p.13 (PDF p.15)

import Mathlib
import Definitions.Def_OnlineColoringKYY_OnlineColoringAlg
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_admits
import Definitions.Def_OnlineColoringKYY_baseColor
import Definitions.Def_OnlineColoringKYY_advEdge
import Definitions.Def_OnlineColoringKYY_stepGraph
import Definitions.Def_OnlineColoringKYY_advColors

set_option autoImplicit false

namespace OnlineColoringKYY

/-- The **graph built by the adversary of Section 4.2** against the deterministic algorithm `A`
with `n` vertices (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Adversary algorithm", printed p.13 = PDF p.15): on
`Fin n`, vertices `i < j` are adjacent iff `advEdge code (advColors A code n) i j`, i.e. iff `i` was
already paired when `j` arrived and its base color is not in `X_j`.

Every edge of vertex `j` to an earlier vertex depends only on the colors of the arrivals `< j`,
which are the colors `A` chose on the earlier prefixes (`prefixGraph_advGraph` below).

**Formalization Note** `code : ℕ → Fin ℓ → Bool` encodes the admissible sets `X_v`; Lemma 4.3
uses an injective code ("the adversary must choose different `X_v` for each vertex `v`"). -/
def advGraph {ℓ : ℕ} (A : OnlineColoringAlg) (code : ℕ → Fin ℓ → Bool) (n : ℕ) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => advEdge code (advColors A code n) i.val j.val

/-- The colors of the process are stable: arrivals before `v` keep their colors. -/
theorem advColors_stable {ℓ : ℕ} (A : OnlineColoringAlg) (code : ℕ → Fin ℓ → Bool) :
    ∀ (v k w : ℕ), w < v → advColors A code (v + k) w = advColors A code v w := by
  intro v k w hw
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, advColors, Function.update_of_ne (by omega), ih]

/-- The prefix of the adversary's graph at `v` is the graph the adversary had built when `v`
arrived, so the color the algorithm gives `v` on `advGraph` is the color of the process. -/
theorem prefixGraph_advGraph {ℓ : ℕ} (A : OnlineColoringAlg) (code : ℕ → Fin ℓ → Bool) (n : ℕ)
    (v : Fin n) :
    prefixGraph (advGraph A code n) v = stepGraph code (advColors A code v.val) v.val := by
  have key : ∀ i j : Fin (v.val + 1),
      advEdge code (advColors A code n) i.val j.val ↔
        advEdge code (advColors A code v.val) i.val j.val := by
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    obtain ⟨k, hk⟩ : ∃ k, n = v.val + 1 + k := ⟨n - (v.val + 1), by omega⟩
    have hst : ∀ w, w < v.val + 1 → advColors A code n w = advColors A code (v.val + 1) w := by
      intro w hw
      have h := advColors_stable A code (v.val + 1) k w hw
      rwa [show v.val + 1 + k = n by omega] at h
    have hst' : ∀ w, w < v.val → advColors A code (v.val + 1) w = advColors A code v.val w := by
      intro w hw; exact advColors_stable A code v.val 1 w hw
    unfold advEdge
    constructor
    · rintro ⟨hij, w, hw, hwi, hc, hna⟩
      refine ⟨hij, w, hw, hwi, ?_, hna⟩
      rwa [hst w (by omega), hst i (by omega), hst' w (by omega), hst' i (by omega)] at hc
    · rintro ⟨hij, w, hw, hwi, hc, hna⟩
      refine ⟨hij, w, hw, hwi, ?_, hna⟩
      rwa [hst w (by omega), hst i (by omega), hst' w (by omega), hst' i (by omega)]
  ext i j
  simp only [prefixGraph, advGraph, stepGraph, SimpleGraph.comap_adj, SimpleGraph.fromRel_adj,
    Fin.val_castLE, key, ne_eq, Fin.castLE_inj]

end OnlineColoringKYY


