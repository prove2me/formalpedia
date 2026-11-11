-- Prove2me | Definitions.Def_TerracedZonal_Excess_Config
-- name    : TerracedZonal_Excess_Config
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:29.100219+00:00
-- url     : https://prove2.me/theorems/4328540d-ae07-4c64-bbdf-345af3838de7
-- title:
--   The TerracedZonal$_0$ configuration with zonal latitudes
-- statement:
--   Given populations $m_0,\dots,m_{K-1}$ (with $\sum_k m_k=N-2$ for a Stage-1 output), the configuration consists of the poles $(0,0,\pm1)$ and $m_k$ points on ring $k$:
--
--   1. **Heights (eq. (8)).** With $m_{\mathrm{above},k}=1+\sum_{j<k}m_j$ and $m_{\mathrm{below},k}=1+\sum_{j>k}m_j$, $z_k=\dfrac{m_{\mathrm{below},k}-m_{\mathrm{above},k}}{N-1}$ (no relaxation step).
--   2. **Phases (eq. (9)).** $\alpha_0=0$ and $\alpha_k=\big(\alpha_{k-1}+1/(2\operatorname{lcm}(m_{k-1},m_k))\big)\bmod 1$.
--   3. **Points (eq. (22)).** $r_k=\sqrt{\max(0,1-z_k^2)}$, $\phi_{k,j}=2\pi(j/m_k+\alpha_k)$ and
--
--   $$x_{k,j}=\big(r_k\cos\phi_{k,j},\ r_k\sin\phi_{k,j},\ z_k\big),\qquad j=0,\dots,m_k-1.$$
--
--   This is the configuration $X_N$ of Theorem 4.3: the output of TerracedZonal$_0$ before the four relaxation steps of Stage 2.
--
--   **Formalization Note** The points are indexed by the two poles and the pairs (ring, position on the ring), a set with $2+\sum_k m_k$ elements, which is $N$ for a Stage-1 output. `mod 1` is `Int.fract`.
-- source:
--   Kabra, Dehaen, Karlova, Hamilton, Carreira, Ovsjanikov, Barron, STOC 2027 submission #638 (October 2026), eqs. (8)–(9) pp. 7–8 (PDF 8–9), App. C.4 eq. (22) p. 22 (PDF 23)

import Definitions.Def_TerracedZonal_Excess_Stage1
import Definitions.Def_TerracedZonal_Excess_Energy

namespace TerracedZonal.Excess

open Real

/-- `m_{above,k} = 1 + ∑_{j<k} m_j`: points strictly above ring `k`, counting the north pole,
§2.2 item 1, p. 7 (PDF 8). -/
noncomputable def mAbove {N : ℕ} (m : Pops N) (k : Fin (ringCount N)) : ℕ :=
  1 + ∑ j : Fin (ringCount N), if j < k then m j else 0

/-- `m_{below,k} = 1 + ∑_{j>k} m_j`: points strictly below ring `k`, counting the south pole. -/
noncomputable def mBelow {N : ℕ} (m : Pops N) (k : Fin (ringCount N)) : ℕ :=
  1 + ∑ j : Fin (ringCount N), if k < j then m j else 0

/-- Zonal equilibrium heights `z_k^{zonal} = (m_{below,k} - m_{above,k}) / (N - 1)`, eq. (8),
p. 7 (PDF 8); no relaxation step of Stage 2 is applied. -/
noncomputable def zZonal (N : ℕ) (m : Pops N) (k : Fin (ringCount N)) : ℝ :=
  ((mBelow m k : ℝ) - (mAbove m k : ℝ)) / ((N : ℝ) - 1)

/-- Phases (9), p. 8 (PDF 9): `α₀ = 0`, `α_k = (α_{k-1} + 1/(2 lcm(m_{k-1}, m_k))) mod 1`,
as a sequence over ring indices (`mod 1` on a nonnegative real is `Int.fract`). -/
noncomputable def phaseSeq {N : ℕ} (m : Pops N) : ℕ → ℝ
  | 0 => 0
  | k + 1 => Int.fract (phaseSeq m k + 1 / (2 * (Nat.lcm (popAt m k) (popAt m (k + 1)) : ℝ)))

/-- Ring radius `r_k = √(max(0, 1 - z_k²))`, App. C.4, p. 22 (PDF 23). -/
noncomputable def ringRadius (N : ℕ) (m : Pops N) (k : Fin (ringCount N)) : ℝ :=
  Real.sqrt (max 0 (1 - zZonal N m k ^ 2))

/-- Azimuths `φ_{k,j} = 2π (j/m_k + α_k)`, eq. (22), p. 22 (PDF 23). -/
noncomputable def azimuth (N : ℕ) (m : Pops N) (k : Fin (ringCount N)) (j : ℕ) : ℝ :=
  2 * π * ((j : ℝ) / (m k : ℝ) + phaseSeq m k)

/-- Index set of the configuration: the two poles (`true` = north, `false` = south) and,
for each ring `k`, its points `j = 0, …, m_k - 1`. It has `2 + ∑_k m_k` elements. -/
abbrev ConfigIndex (N : ℕ) (m : Pops N) := Bool ⊕ (Σ k : Fin (ringCount N), Fin (m k))

/-- The TerracedZonal₀ configuration with latitudes `z^{zonal}` (before relaxation), phases (9),
and coordinates (22), App. C.4, p. 22 (PDF 23): the poles `(0, 0, ±1)` and the ring points
`x_{k,j} = (r_k cos φ_{k,j}, r_k sin φ_{k,j}, z_k)`. -/
noncomputable def config (N : ℕ) (m : Pops N) : ConfigIndex N m → EuclideanSpace ℝ (Fin 3)
  | Sum.inl true => !₂[0, 0, 1]
  | Sum.inl false => !₂[0, 0, -1]
  | Sum.inr ⟨k, j⟩ =>
      !₂[ringRadius N m k * Real.cos (azimuth N m k j.val),
          ringRadius N m k * Real.sin (azimuth N m k j.val), zZonal N m k]

end TerracedZonal.Excess


