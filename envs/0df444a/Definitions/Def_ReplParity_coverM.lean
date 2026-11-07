-- Prove2me | Definitions.Def_ReplParity_coverM
-- name    : ReplParity_coverM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:41:54.03311+00:00
-- url     : https://prove2.me/theorems/41ba3776-1bb0-4eaf-9399-5d8b538d144e
-- title:
--   Stage parameters and block layout of the multistage cover
-- statement:
--   For $0<\varepsilon,\rho<1$ let $L=\lceil\log_2(4/\varepsilon)\rceil$, and for $j=1,\dots,L$
--   $$q_j=2^{-j},\qquad \eta_j=\frac{\rho}{1024}\,2^{-\lceil (L-j)/4\rceil},\qquad K_j=4\lceil128n^3/\eta_j^2\rceil,\qquad R_j=\lceil 8K_j/q_j\rceil .$$
--   Stage $j$ owns a block of $N_g(q_j,\eta_j)+R_j$ samples (the gate's samples, then the collection samples), and the blocks of stages $1,\dots,L$ are laid out consecutively; the total sample size is $\sum_{j=1}^{L}\big(N_g(q_j,\eta_j)+R_j\big)$. All blocks are reserved in advance, whether or not a stage skips.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), proof of Proposition 3.4, p.17 (PDF p.19); Figure 2, p.14

import Mathlib
import Definitions.Def_ReplParity_Vec
import Definitions.Def_ReplParity_gate
import Definitions.Def_ReplParity_tokenMinHash

namespace ReplParity

/-- **Stage parameters of the multistage cover (proof of Proposition 3.4).** Shen, Zhong,
*Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027
submission (manuscript sha256 40424491…), proof of Proposition 3.4, p.17 (PDF p.19): "Let
L = ⌈log₂(4/ε)⌉, and for j ∈ [L] let q_j = 2^{−j} and η_j = (ρ/1024) 2^{−⌈(L−j)/4⌉}. … it lets
K_j = 4⌈128n³/η_j²⌉, takes a fresh block of R_j = ⌈8K_j/q_j⌉ samples".

`coverL ε = L`. -/
noncomputable def coverL (ε : ℝ) : ℕ := ⌈Real.logb 2 (4 / ε)⌉₊

/-- `q_j = 2^{−j}`. -/
noncomputable def stageQ (j : ℕ) : ℝ := (2 : ℝ) ^ (-(j : ℤ))

/-- `η_j = (ρ/1024) 2^{−⌈(L−j)/4⌉}`. -/
noncomputable def stageEta (ε ρ : ℝ) (j : ℕ) : ℝ :=
  ρ / 1024 * (2 : ℝ) ^ (-⌈((coverL ε : ℝ) - j) / 4⌉)

/-- `K_j = 4⌈128n³/η_j²⌉`. -/
noncomputable def stageK (n : ℕ) (ε ρ : ℝ) (j : ℕ) : ℕ := tokK n (stageEta ε ρ j)

/-- `R_j = ⌈8K_j/q_j⌉`. -/
noncomputable def stageR (n : ℕ) (ε ρ : ℝ) (j : ℕ) : ℕ :=
  ⌈8 * (stageK n ε ρ j : ℝ) / stageQ j⌉₊

/-- The block of stage `j`: the gate's `N_g(q_j, η_j)` samples followed by `R_j` samples. -/
noncomputable def stageLen (n : ℕ) (ε ρ : ℝ) (j : ℕ) : ℕ :=
  gateN (stageQ j) (stageEta ε ρ j) + stageR n ε ρ j

/-- The offset of the block of stage `j` (stages `1, …, j − 1` come first). -/
noncomputable def stageOff (n : ℕ) (ε ρ : ℝ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico 1 j, stageLen n ε ρ i

/-- The total sample size `Σ_{j=1}^{L} (N_g(q_j, η_j) + R_j)` of the multistage cover: "All blocks
are reserved in advance" (p.17). -/
noncomputable def coverM (n : ℕ) (ε ρ : ℝ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 (coverL ε), stageLen n ε ρ j

/-- The `k`-th sample of a sequence of `M` samples (`0` past the end; never used past the end by
the constructions, whose blocks lie inside the sample). -/
def sampleAt {n M : ℕ} (S : Fin M → Vec n) (k : ℕ) : Vec n :=
  if h : k < M then S ⟨k, h⟩ else 0

end ReplParity


