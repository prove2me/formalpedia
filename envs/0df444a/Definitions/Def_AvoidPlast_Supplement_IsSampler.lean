-- Prove2me | Definitions.Def_AvoidPlast_Supplement_IsSampler
-- name    : AvoidPlast_Supplement_IsSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:57:04.412855+00:00
-- url     : https://prove2.me/theorems/cfd2af86-139f-4a83-a9a1-1116357d5d84
-- title:
--   Samplable in polynomial time and space $n^\delta$
-- statement:
--   A machine $S$ samples the ensemble $Y$ in polynomial time and space $O(N^\delta)$ if on $(1^N,\rho)$, with $\rho$ a uniform string of the fixed length $a(N^a+1)$ on a read-only tape, it halts within $a(N^a+1)$ steps, uses work space at most $a(N^\delta+1)$, and its output is distributed exactly as $Y_N$.
--
--   **Formalization Note** The random string has the machine's time bound as its fixed length, so its length carries no advice.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 3.4, p.14; Theorem 5.4, p.23

import Mathlib
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_workSpace
import Definitions.Def_AvoidPlast_Supplement_Ensemble

namespace AvoidPlast.Supplement

open AvoidPlast

/-- `S` samples the ensemble `Y` in polynomial time and space `O(n^δ)` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 3.4,
p.14, and the hypothesis of Theorem 5.4, p.23): on `(1^N, ρ)` with `|ρ| = a(N^a + 1)` it halts
within `a(N^a + 1)` steps in work space `a(N^δ + 1)` (the random tape is read-only), and its
output on uniform `ρ` is distributed exactly as `Y_N`.

**Formalization Note** The random string has the machine's own time bound as its fixed length,
so its length carries no advice (as in the base `InPrBPstarL`). -/
def IsSampler (S : Machine 2) (a : ℕ) (Y : Ensemble) (δ : ℝ) : Prop :=
  (∀ (N : ℕ) (ρ : List Bool), ρ.length = a * (N ^ a + 1) →
    HaltsWithin S ![List.replicate N true, ρ] (a * (N ^ a + 1)) ∧
    (workSpace S ![List.replicate N true, ρ] : ℝ) ≤ a * ((N : ℝ) ^ δ + 1)) ∧
  ∀ (N : ℕ) (y : List Bool), (Y.dist N y).toReal =
    prob (a * (N ^ a + 1)) fun ρ => output S ![List.replicate N true, ρ] = y

end AvoidPlast.Supplement


