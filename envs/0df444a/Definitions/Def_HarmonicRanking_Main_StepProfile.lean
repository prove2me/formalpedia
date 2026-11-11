-- Prove2me | Definitions.Def_HarmonicRanking_Main_StepProfile
-- name    : HarmonicRanking_Main_StepProfile
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:53.89487+00:00
-- url     : https://prove2.me/theorems/232cc0a1-90b6-4f4f-8510-74c655a7fa97
-- title:
--   Step scores and the finite threshold game
-- statement:
--   Fix $m\ge1$ and a nonincreasing positive real height vector $H_1,\ldots,H_m$, with the bookkeeping value $H_{m+1}=0$. The score equals $H_i$ on $[(i-1)/m,i/m)$ and equals zero at 1. For $i,j\in[m]$, put
--
--   $$
--   g_{ij}=\frac{H_j}{H_i+H_j},\quad g_{i,m+1}=0,\quad q_{ij}=g_{ij}-g_{i,j+1},\quad
--   r_{ij}=(m-j+1)g_{ij}-(m-j)g_{i,j+1}.
--   $$
--
--   A threshold pair $a,b\in\{0,\ldots,m\}^m$ is admissible if $U_{ij}\widetilde V_{ij}=0$ in every cell, where $U_{ij}=1_{j>a_i}$ and $\widetilde V_{ij}=1_{i>b_j}$. With $P_i=g_{i,a_i+1}$, $Q_j=g_{j,b_j+1}$, and $S_{ij}=(1-U_{ij})(1-\widetilde V_{ij})$, its payoff is
--
--   $$
--   \Gamma_m^H(a,b)=\frac1{m^2}\sum_{i,j}\left[S_{ij}+(U_{ij}+\widetilde V_{ij})(P_i+Q_j)\right].
--   $$
--
--   The finite game value is the minimum over all such thresholds, without monotonicity between different coordinates. The network and continuous comparison use this same score table.
--
--   **Formalization Note** A cell index in $\mathrm{Fin}\,m$ represents the paper's index one larger; threshold counts keep their original values. The final increment uses $g_{i,m+1}=0$ explicitly.
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), pp. 15–17, Eqs. (20)–(33)

import Definitions.Def_HarmonicRanking_Main_Game

set_option autoImplicit false
noncomputable section

namespace HarmonicRanking.Main

/-- Fin m index i represents the paper's one-based index i+1. -/
def IsProfile {m : ℕ} (H : Fin m → ℝ) : Prop :=
  0 < m ∧ (∀ i, 0 < H i) ∧ Antitone H

/-- A total bookkeeping array, zero at m (the paper's m+1) and beyond. -/
def height {m : ℕ} (H : Fin m → ℝ) (j : ℕ) : ℝ :=
  if hj : j < m then H ⟨j, hj⟩ else 0

/-- Floor chooses the right-continuous half-open grid cell. -/
def stepScore {m : ℕ} (H : Fin m → ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x < 1 then height H ⌊(m : ℝ) * x⌋₊ else 0

def gridGain {m : ℕ} (H : Fin m → ℝ) (i : Fin m) (j : ℕ) : ℝ :=
  if j < m then height H j / (H i + height H j) else 0

def q {m : ℕ} (H : Fin m → ℝ) (i j : Fin m) : ℝ :=
  gridGain H i j.val - gridGain H i (j.val + 1)

def rCoeff {m : ℕ} (H : Fin m → ℝ) (i j : Fin m) : ℝ :=
  ((m : ℝ) - j.val) * gridGain H i j.val -
    ((m : ℝ) - j.val - 1) * gridGain H i (j.val + 1)

abbrev Thresholds (m : ℕ) := (Fin m → Fin (m+1)) × (Fin m → Fin (m+1))

/-- j+1 > a_i, using zero-based cell j and the unchanged threshold count a_i. -/
def discreteU {m : ℕ} (c : Thresholds m) (i j : Fin m) : ℝ :=
  if (c.1 i).val ≤ j.val then 1 else 0

def discreteV {m : ℕ} (c : Thresholds m) (i j : Fin m) : ℝ :=
  if (c.2 j).val ≤ i.val then 1 else 0

def discreteAdmissible {m : ℕ} (c : Thresholds m) : Prop :=
  ∀ i j, discreteU c i j * discreteV c i j = 0

def GammaFinite {m : ℕ} (H : Fin m → ℝ) (c : Thresholds m) : ℝ :=
  (∑ i, ∑ j,
    ((1 - discreteU c i j) * (1 - discreteV c i j) +
      (discreteU c i j + discreteV c i j) *
        (gridGain H i (c.1 i).val + gridGain H j (c.2 j).val))) / (m : ℝ)^2

/-- Finite nonempty threshold domain, without monotonicity across its coordinates. -/
def finiteGameValue {m : ℕ} (H : Fin m → ℝ) : ℝ :=
  sInf {v | ∃ c : Thresholds m, discreteAdmissible c ∧ GammaFinite H c = v}

end HarmonicRanking.Main


