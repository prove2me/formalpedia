-- Prove2me | Definitions.Def_DoublyEffIP_augLang
-- name    : DoublyEffIP_augLang
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:38.858671+00:00
-- url     : https://prove2.me/theorems/63755de6-a49f-4736-b671-644fd7675a43
-- title:
--   The augmented language $L^k_t[\Phi]$
-- statement:
--   Let $\Phi$ be a predicate on $k\times(\lambda+1)$ matrices of configurations. The **augmented language** is
--
--   $$
--   L^k_t[\Phi]=\{x \mid x\in L^k_t\ \wedge\ (t\ge\lambda\Rightarrow\Phi(M_x)=1)\},
--   $$
--
--   the batches of correct transition claims whose midpoint matrix satisfies $\Phi$ whenever $t\ge\lambda$. The predicate carries the auxiliary constraints (consistency of midpoints with checksums) that the recursive protocol accumulates.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Definition 10, p.19

import Mathlib
import Definitions.Def_DoublyEffIP_Lkt
import Definitions.Def_DoublyEffIP_midpointMatrix

set_option autoImplicit false

namespace DoublyEffIP

/-- **The augmented language `L^k_t[Φ]`** — Definition 10 of Chen–Hong–Kalai–Xi, *Towards a
Doubly Efficient IP = PSPACE*, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), p.19:
`L^k_t[Φ] := {x ∈ {0,1}^{k×2S} | x ∈ L^k_t ∧ (t ≥ λ ⟹ Φ(M_x) = 1)}`.

A batch `x` of `k` transition claims belongs to `augLang step t lam Φ` if every claim is a correct
`t`-step transition and, when `t ≥ λ`, its midpoint matrix satisfies the predicate `Φ`.

**Formalization Note.** `Φ` is a predicate on `k × (λ + 1)` matrices of configurations, the
paper's `Φ : {0,1}^{k×(S(λ+1))} → {0,1}` with "= 1" read as truth. -/
def augLang {C : Type*} (step : C → C) (t lam : ℕ) {k : ℕ}
    (Φ : (Fin k → Fin (lam + 1) → C) → Prop) : Set (Fin k → C × C) :=
  {x | x ∈ Lkt step t (Fin k) ∧ (lam ≤ t → Φ (midpointMatrix step t lam x))}

end DoublyEffIP


