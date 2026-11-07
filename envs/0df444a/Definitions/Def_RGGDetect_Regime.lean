-- Prove2me | Definitions.Def_RGGDetect_Regime
-- name    : RGGDetect_Regime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:37.996428+00:00
-- url     : https://prove2.me/theorems/215e2263-532f-43b9-b806-8dc255cf383a
-- title:
--   The asymptotic regime (1): $p\to0$, $p\ge n^{-1+\delta}$, $d\gg(np\log(1/p))^3$
-- statement:
--   Fix $\delta>0$. Sequences $p=p_n$ (edge density), $d=d_n$ (dimension) and $\tau=\tau_n$ (threshold), indexed by the number of vertices $n$, are **in the regime** when
--
--   1. $p_n\to0$;
--   2. $p_n\ge n^{-1+\delta}$ for all large $n$;
--   3. $d_n\gg(np_n\log(1/p_n))^3$, that is, for every $\varepsilon>0$, $(np_nL_n)^3\le\varepsilon d_n$ for all large $n$, where $L_n=\log(1/p_n)$; equivalently $\varepsilon_n=(np_nL_n)^3/d_n=o(1)$ as in (2);
--   4. $\mathbb P\{\langle x_1,x_2\rangle\ge\tau_n\}=p_n$ for all large $n$, $x_1,x_2$ independent uniform on $S^{d_n-1}$.
--
--   This is the hypothesis of the main theorem, and every asymptotic statement of the paper is made under it. By the paper's convention (p.2), constants may depend on $\delta$ and on fixed truncation cutoffs, but not on $n$, $p$ or $d$; the statements therefore choose their constants before the sequences.
--
--   **Formalization Note** $d\gg f$ is never written as $f/d\to0$, which $d=0$ would satisfy in Lean. All conditions are required only for large $n$.
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Theorem 1, eq. (1), p.1 (PDF p.3); eq. (2), p.2 (PDF p.4)

import Mathlib
import Definitions.Def_RGGDetect_unifSphere

open Filter Topology

namespace RGGDetect

/-- The asymptotic regime (1) of Theorem 1 for a fixed `δ` (arXiv:2610.08517, held version, Theorem 1,
p.1, eq. (1), with (2), p.2), for sequences indexed by the number of vertices `n`: edge density
`p n`, dimension `d n` and threshold `τ n`.

1. `p → 0`;
2. `p ≥ n^{-1+δ}` for all large `n`;
3. `d ≫ (n p log(1/p))³`: for every `ε > 0`, eventually `(n p log(1/p))³ ≤ ε d`
   (the paper's `ε_n = (npL)³/d = o(1)`, (2));
4. `τ` solves the cap equation `P{⟨x₁, x₂⟩ ≥ τ} = p` for all large `n`.

**Formalization Note** `d ≫ f` is written as `∀ ε > 0, eventually f ≤ ε d`, never as `f/d → 0`
(which `d = 0` satisfies in Lean). All four conditions are required only eventually; the paper's
statements are limits, so this covers its sequences. -/
def Regime (δ : ℝ) (p : ℕ → ℝ) (d : ℕ → ℕ) (τ : ℕ → ℝ) : Prop :=
  Tendsto p atTop (𝓝 0) ∧
  (∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-1 + δ) ≤ p n) ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ((n : ℝ) * p n * Real.log (1 / p n)) ^ 3 ≤ ε * d n) ∧
  (∀ᶠ n : ℕ in atTop, capProb (d n) (τ n) = p n)

end RGGDetect


