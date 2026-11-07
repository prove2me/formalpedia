-- Prove2me | Definitions.Def_CubicProductLB_IsTwoSimple
-- name    : CubicProductLB_IsTwoSimple
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:16:05.965757+00:00
-- url     : https://prove2.me/theorems/eff4aca8-ee3d-4d17-ac5a-6a9f0544fab5
-- title:
--   2-simple functions
-- statement:
--   A function $g : \{0,1\}^M \to \mathbb F_2$ is **2-simple** if there are an integer $s \ge 0$, functions $g_1, \dots, g_s : \{0,1\}^M \to \mathbb F_2$ and indices $j_1, \dots, j_s \in [M]$ with
--   $$g(y) = \sum_{q=1}^s g_q(y) \pmod 2,$$
--   where each $g_q$ is independent of the coordinate $y_{j_q}$. Different summands may omit different variables.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Definition 15, Eqs. (258)–(259), p.31

import Mathlib

namespace CubicProductLB

/-- `g : {0,1}^M → F_2` is 2-simple: a finite sum over `F_2` of functions `g_q`, each independent of
one coordinate `y_{j_q}` (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 15, Eqs. (258)–(259), p.31). -/
def IsTwoSimple {M : ℕ} (g : (Fin M → Bool) → ZMod 2) : Prop :=
  ∃ (s : ℕ) (gs : Fin s → (Fin M → Bool) → ZMod 2) (js : Fin s → Fin M),
    (∀ y, g y = ∑ q, gs q y) ∧ ∀ q y b, gs q (Function.update y (js q) b) = gs q y

end CubicProductLB


