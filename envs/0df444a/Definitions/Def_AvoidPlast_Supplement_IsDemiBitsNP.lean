-- Prove2me | Definitions.Def_AvoidPlast_Supplement_IsDemiBitsNP
-- name    : AvoidPlast_Supplement_IsDemiBitsNP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:07:49.639688+00:00
-- url     : https://prove2.me/theorems/fbac6f66-3aa2-424e-915b-0edaeefb858a
-- title:
--   $\varepsilon$-demi-bits generators against NP (Definition 6.2)
-- statement:
--   $g=\{g_n:\{0,1\}^{\ell(n)}\to\{0,1\}^n\}$ is an $\varepsilon$-demi-bits generator against $\mathsf{NP}$ if no $\mathsf{NP}$ verifier $V$ satisfies, for every sufficiently large $n$:
--
--   1. for at least $\varepsilon(n)\cdot2^n$ strings $y\in\{0,1\}^n$, $\exists w: V(y,w)=1$;
--   2. for every $y$ in the range of $g_n$, $\forall w: V(y,w)=0$.
--
--   **Formalization Note** Definition 6.2 is written for one $n$; a uniform verifier breaks the generator when it works at every large length, matching "for every sufficiently large $n$" in Corollary 6.7.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 6.2, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_IsPolyNTime

namespace AvoidPlast.Supplement

open AvoidPlast

/-- `g = {g_n : {0,1}^{ℓ(n)} → {0,1}^n}` is an `ε`-demi-bits generator against NP (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728),
Definition 6.2, p.33): no NP verifier `V` satisfies, for every sufficiently large `n`,
(1) at least `ε(n)·2^n` strings `y ∈ {0,1}^n` have `∃ w : V(y, w) = 1`, and (2) every `y` in the
range of `g_n` has `∀ w : V(y, w) = 0`. Witnesses have polynomial length.

**Formalization Note** Definition 6.2 is stated for one `n`; security against a uniform verifier
is asymptotic, and the verifier must work at every large length (matching "for every sufficiently
large `n`" in Corollary 6.7). -/
def IsDemiBitsNP (g : ℕ → List Bool → List Bool) (ℓ : ℕ → ℕ) (ε : ℕ → ℝ) : Prop :=
  ¬ ∃ (V : Machine 2) (a : ℕ), IsPolyNTime V a ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ε n ≤ prob n (fun y => ∃ w : List Bool, w.length ≤ a * (n ^ a + 1) ∧ Accepts V ![y, w]) ∧
    ∀ x : List Bool, x.length = ℓ n → ∀ w : List Bool, w.length ≤ a * (n ^ a + 1) →
      ¬ Accepts V ![g n x, w]

end AvoidPlast.Supplement


