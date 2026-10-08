-- Prove2me | Definitions.Def_ReluMIP_Ideal_Lifted5
-- name    : ReluMIP_Ideal_Lifted5
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:33.396629+00:00
-- url     : https://prove2.me/theorems/21efcc62-abb1-466d-a800-dd330bacc5c5
-- title:
--   §2.2, (5), pp. 5–6 — the lifted LP relaxation with the auxiliary variables retained
-- statement:
--   The lifted LP relaxation of the multiple choice formulation (5) consists of tuples $(x,y,z,x^0,x^1,y^0,y^1)$ with $0\le z\le1$ satisfying
--   $$
--   (x,y)=(x^0,y^0)+(x^1,y^1),\quad y^0=0\ge w\cdot x^0+b(1-z),\quad y^1=w\cdot x^1+bz\ge0,
--   $$
--   $$
--   L(1-z)\le x^0\le U(1-z),\qquad Lz\le x^1\le Uz.
--   $$
--   This keeps the auxiliary variables present in the paper's ideality claim. Its projection onto $(x,y,z)$ is the separately defined relaxation of (5).
-- source:
--   arXiv:1811.08359v2, §2.2, display (5a)–(5f), pp. 5–6

import Mathlib
import Definitions.Def_ReluMIP_Ideal_Setting

namespace ReluMIP.Ideal

/-- The LP relaxation of the *lifted* multiple-choice formulation (5), retaining the auxiliary
variables `x⁰`, `x¹`, `y⁰`, and `y¹`. The first component is `(x,y,z)`; the second is
`(x⁰,x¹,y⁰,y¹)`. This is the space in which the paper calls (5) ideal (§2.2, pp. 5–6). -/
def relax5Lift {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) :
    Set (((Fin η → ℝ) × ℝ × ℝ) × ((Fin η → ℝ) × (Fin η → ℝ) × ℝ × ℝ)) :=
  {p | p.1.1 = p.2.1 + p.2.2.1 ∧
    p.1.2.1 = p.2.2.2.1 + p.2.2.2.2 ∧
    p.2.2.2.1 = 0 ∧
    (∑ i, w i * p.2.1 i) + b * (1 - p.1.2.2) ≤ 0 ∧
    p.2.2.2.2 = (∑ i, w i * p.2.2.1 i) + b * p.1.2.2 ∧
    0 ≤ p.2.2.2.2 ∧
    (∀ i, L i * (1 - p.1.2.2) ≤ p.2.1 i ∧ p.2.1 i ≤ U i * (1 - p.1.2.2)) ∧
    (∀ i, L i * p.1.2.2 ≤ p.2.2.1 i ∧ p.2.2.1 i ≤ U i * p.1.2.2) ∧
    0 ≤ p.1.2.2 ∧ p.1.2.2 ≤ 1}

end ReluMIP.Ideal


