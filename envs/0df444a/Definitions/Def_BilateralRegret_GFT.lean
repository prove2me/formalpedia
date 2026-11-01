-- Prove2me | Definitions.Def_BilateralRegret_GFT
-- name    : BilateralRegret_GFT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:11:48.514659+00:00
-- url     : https://prove2.me/theorems/34b931b7-b503-45a1-b23a-6f46deeee4d0
-- title:
--   Gain from trade $\mathrm{GFT}(p,s,b)=(b-s)\,\mathbb I\{s\le p\le b\}$ and the uniform law on $[0,1]$
-- statement:
--   For a price $p$ and valuations $s$ (seller) and $b$ (buyer), the **gain from trade** is
--
--   $$
--   \mathrm{GFT}(p,s,b)=(b-s)\,\mathbb I\{s\le p\le b\}.
--   $$
--
--   A trade happens exactly when the posted price lies between the two valuations, and it then creates the surplus $b-s$. For $p,s,b\in[0,1]$, $\mathrm{GFT}(p,s,b)\in[0,1]$. This is the reward of the bilateral trade game.
--
--   The module also fixes the real indicator $\mathbb I\{P\}\in\{0,1\}$ of a proposition, the **uniform law** on $[0,1]$ (Lebesgue measure restricted to $[0,1]$, the law of every uniform draw of the player's randomization), and the extension of a finite sequence of rounds to an $\mathbb N$-indexed sequence used to run round-by-round recursions.
--
--   **Formalization Note** The formula is defined for all real arguments; the mission only evaluates it at prices in $[0,1]$ and valuations in $[0,1]$.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, Bilateral Trade: A Regret Minimization Perspective, arXiv:2109.12974v1, §2, p.6 (definition of GFT); App. C, p.22 (μ_L); App. C.2.1, p.24

import Mathlib

namespace BilateralRegret

open MeasureTheory

open Classical in
/-- The real indicator `𝕀{P}` of a proposition: `1` if `P` holds, `0` otherwise.

**Formalization Note.** Decidability is classical. -/
noncomputable def ind (P : Prop) : ℝ := if P then 1 else 0

/-- **Gain from trade.**
Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, *Bilateral Trade: A Regret Minimization
Perspective*, arXiv:2109.12974v1, §2, p.6: for all `p, s, b ∈ [0,1]`,
`GFT(p, s, b) := (b − s) 𝕀{s ≤ p ≤ b}` (also App. C.2.1, p.24, the reward function `ρ`).

**Formalization Note.** The formula is defined for all real `p, s, b`; every statement of the
mission only evaluates it at prices in `[0,1]` and at valuations that lie in `[0,1]`
(everywhere or almost surely). -/
noncomputable def GFT (p s b : ℝ) : ℝ := (b - s) * ind (s ≤ p ∧ p ≤ b)

/-- The uniform law on `[0,1]`, as a measure on `ℝ`: Lebesgue measure restricted to `[0,1]`
(the paper's `μ_L`, App. C, p.22). It is the law of every uniform draw `U_t` of the player's
randomization (Definition 2, p.23). -/
noncomputable def unif : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- Extend a finite sequence `f : Fin n → X` (rounds `1, …, n` stored at indices `0, …, n − 1`)
to `ℕ → X`, with value `0` at indices `≥ n`.

**Formalization Note.** Only used to run round-indexed recursions; no statement of the mission
reads an index `≥ n`. -/
def extendSeq {X : Type*} [Zero X] {n : ℕ} (f : Fin n → X) : ℕ → X :=
  fun i => if h : i < n then f ⟨i, h⟩ else 0

end BilateralRegret


