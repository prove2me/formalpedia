-- Prove2me | Definitions.Def_BlottoFPTAS_Main_Reduction
-- name    : BlottoFPTAS_Main_Reduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:42:26.418883+00:00
-- url     : https://prove2.me/theorems/f97f3382-394e-4c0a-ace8-170d04e177c1
-- title:
--   Light battlefields, the reduced game, the arc-minimum reconstruction L(P) and the finite shifts
-- statement:
--   Let $w'_j\ge1$ be integer weights with $Q'=\sum_jw'_j$ and $v'_j=w'_j/Q'$, and $e=2^{-a}$. Battlefield $j$ is **light** if $v'_j\le e/10$; if more than $k=8/e$ are light, they are **replaced** by $k$ representative battlefields of value $V/k$, $V=\sum_{j\text{ light}}v'_j$. The reduced battlefields are the kept ones (in their original order) followed by the $k$ representatives; $v_{\mathrm{red}}$ is $v'_j$ on kept battlefields and $V/k$ on representatives.
--
--   **Reconstruction (17).** For a reduced allocation with sorted representative bids $x_{(0)}\le\dots\le x_{(k-1)}$, let $Z(t)=kx_{(r)}$ on $[r/k,(r+1)/k)$. The light battlefields, in order, receive consecutive arcs of the circle $[0,1)$ of lengths $p_j=v'_j/V$, all rotated by $\omega$; light battlefield $j$ bids
--   $$X_j=p_j\operatorname*{ess\,inf}_{t\in I_j(\omega)}Z(t),$$
--   the least $kx_{(r)}$ over the cells $[r/k,(r+1)/k)$ meeting the arc in positive length, times $p_j$; kept battlefields keep their bids. $L(P)$ is the law of the reconstructed allocation for $x\sim P$ and an independent $\omega\sim\mathrm{Unif}[0,1)$.
--
--   **Finite shifts (28).** $W_G=\sum_{j\text{ light}}w'_j$, $D_{\mathrm{sh}}=kW_G$, $t_\ell=\lfloor(2\ell+1)D_{\mathrm{sh}}/(2S_{\mathrm{out}})\rfloor$ and $\omega_\ell=(t_\ell+\tfrac12)/D_{\mathrm{sh}}$ for $0\le\ell<S_{\mathrm{out}}$.
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 31, §5.1; pp. 43–44, §5.4, Eq. (17); p. 70, App. F.2, Eq. (28)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Params

open scoped BigOperators
open MeasureTheory

namespace BlottoFPTAS.Main

/-!
# Light battlefields, the reduced game and the reconstruction `L(P)` (§5.1, p. 31; §5.4,
pp. 43–44; App. F.2, p. 70)

The data are `n` original battlefields, `a ≥ 1` (`e = 2^{-a}`) and the positive integer weights
`w′_j` of the first rounding, with `Q′ = ∑_j w′_j` and `v′_j = w′_j / Q′`.

* Battlefield `j` is **light** if `v′_j ≤ e/10`. If more than `k = 8/e` battlefields are light
  (`Replaced`), they are replaced by `k` representative battlefields of value `V/k`, where `V` is
  the total light value.
* **Reduced battlefields** are `Fin (mRed)`, `mRed = (number of kept battlefields) + k`: index
  `i < |kept|` is the `i`-th kept battlefield in the original order, index `|kept| + r` is
  representative `r`. `vRed` is the reduced value vector (`v′_j` for kept `j`, `V/k` for
  representatives). (The paper does not fix an order of the reduced battlefields; any order gives
  the same game.)
* **Reconstruction** (§5.4, Eq. (17)): for a reduced allocation `x` and a shift `ω ∈ [0, 1)`, sort
  the representative bids `x_(0) ≤ ⋯ ≤ x_(k−1)` and put `Z(t) = k x_(r)` on `[r/k, (r+1)/k)`.
  The light battlefields, in their original order, get consecutive arcs of the circle `[0, 1)` of
  lengths `p_j = v′_j / V`, all rotated by `ω`; the arc of `j` is `(α_j, α_j + p_j)` modulo one with
  `α_j = ω + ∑_{h light, h < j} p_h`. Light battlefield `j` bids
  `X_j = p_j · ess inf_{t ∈ I_j(ω)} Z(t)`, the smallest `k x_(r)` over the cells `[r/k, (r+1)/k)`
  that meet the arc in positive length (`Meets`), times `p_j`; kept battlefields keep their bids.
* `reconLaw P` is the law `L(P)` of the reconstructed allocation when `x ∼ P` and
  `ω ∼ Unif[0, 1)` are independent.
* **Finite shifts** (§5.4, p. 44; Eq. (28), p. 70): `W_G = ∑_{j light} w′_j`, `D_sh = k W_G`,
  `t_ℓ = ⌊(2ℓ + 1) D_sh / (2 S_out)⌋` and `ω_ℓ = (t_ℓ + 1/2) / D_sh`, `0 ≤ ℓ < S_out`.
-/

section

variable {n : ℕ} (a : ℕ) (w' : Fin n → ℕ)

/-- `v′_j = w′_j / Q′`. -/
noncomputable def vPrime (j : Fin n) : ℝ :=
  (w' j : ℝ) / ∑ h, (w' h : ℝ)

/-- Battlefield `j` is light: `v′_j ≤ e/10`. -/
def IsLight (j : Fin n) : Prop :=
  vPrime w' j ≤ eR a / 10

open Classical in
/-- The set of light battlefields. -/
noncomputable def lightSet : Finset (Fin n) :=
  Finset.univ.filter fun j => IsLight a w' j

/-- The light battlefields are replaced: more than `k = 8/e` of them are light. -/
def Replaced : Prop :=
  kRep a < (lightSet a w').card

open Classical in
/-- The kept battlefields, in their original order. -/
noncomputable def keptList : List (Fin n) :=
  (List.finRange n).filter fun j => ¬ IsLight a w' j

/-- The number `m` of reduced battlefields (in the replaced case). -/
noncomputable def mRed : ℕ :=
  (keptList a w').length + kRep a

/-- `V`, the total light value. -/
noncomputable def Vlight : ℝ :=
  ∑ j ∈ lightSet a w', vPrime w' j

/-- The reduced value vector `v_red`. -/
noncomputable def vRed (i : Fin (mRed a w')) : ℝ :=
  if h : i.val < (keptList a w').length then vPrime w' ((keptList a w').get ⟨i.val, h⟩)
  else Vlight a w' / kRep a

/-- The arc length `p_j = v′_j / V` of a light battlefield. -/
noncomputable def pLight (j : Fin n) : ℝ :=
  vPrime w' j / Vlight a w'

/-- The bid of the reduced allocation `x` on reduced index `i` (`0` out of range). -/
noncomputable def redBid (x : Fin (mRed a w') → ℝ) (i : ℕ) : ℝ :=
  if h : i < mRed a w' then x ⟨i, h⟩ else 0

/-- The sorted representative bids `x_(0) ≤ ⋯ ≤ x_(k−1)`; `sortedRep x r` is `x_(r)`. -/
noncomputable def sortedRep (x : Fin (mRed a w') → ℝ) (r : ℕ) : ℝ := by
  classical
  exact ((List.ofFn fun s : Fin (kRep a) => redBid a w' x ((keptList a w').length + s)).mergeSort
    (fun u v => decide (u ≤ v))).getD r 0

/-- The cell `[r/k, (r+1)/k)` (taken modulo one) meets the arc `(α, α + p)` in positive
length. -/
def Meets (k : ℕ) (α p : ℝ) (r : ℕ) : Prop :=
  ∃ z : ℤ, ((r : ℝ) + k * z) / k < α + p ∧ α < ((r : ℝ) + 1 + k * z) / k

open Classical in
/-- The start `α_j = ω + ∑_{h light, h < j} p_h` of the arc of light battlefield `j`. -/
noncomputable def arcStart (ω : ℝ) (j : Fin n) : ℝ :=
  ω + ∑ h ∈ (lightSet a w').filter (fun h => h < j), pLight a w' h

open Classical in
/-- The reconstructed allocation on the original battlefields (Eq. (17)): a light battlefield
`j` bids `p_j · min {k x_(r) : the cell r meets the arc of j}`; a kept battlefield keeps its
reduced bid. -/
noncomputable def recon (x : Fin (mRed a w') → ℝ) (ω : ℝ) (j : Fin n) : ℝ :=
  if IsLight a w' j then
    pLight a w' j * ⨅ r : {r : Fin (kRep a) // Meets (kRep a) (arcStart a w' ω j) (pLight a w' j) r},
      (kRep a : ℝ) * sortedRep a w' x r
  else redBid a w' x ((keptList a w').idxOf j)

/-- `L(P)`: the law of the reconstructed allocation for `x ∼ P` and an independent
`ω ∼ Unif[0, 1)`. -/
noncomputable def reconLaw (P : Measure (Fin (mRed a w') → ℝ)) : Measure (Fin n → ℝ) :=
  (P.prod (volume.restrict (Set.Ico (0 : ℝ) 1))).map fun xω => recon a w' xω.1 xω.2

/-- `W_G = ∑_{j light} w′_j`. -/
noncomputable def WG : ℕ :=
  ∑ j ∈ lightSet a w', w' j

/-- `D_sh = k W_G`. -/
noncomputable def Dsh : ℕ :=
  kRep a * WG a w'

/-- The finite shift `ω_ℓ = (t_ℓ + 1/2)/D_sh` with `t_ℓ = ⌊(2ℓ + 1) D_sh / (2 S_out)⌋`
(Eq. (28)). -/
noncomputable def shift (ℓ : ℕ) : ℝ :=
  ((⌊((2 * ℓ + 1 : ℕ) : ℝ) * Dsh a w' / (2 * Sout a)⌋ : ℝ) + 1 / 2) / Dsh a w'

end

end BlottoFPTAS.Main


