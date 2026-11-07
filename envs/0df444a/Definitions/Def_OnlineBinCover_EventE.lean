-- Prove2me | Definitions.Def_OnlineBinCover_EventE
-- name    : OnlineBinCover_EventE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:51:15.567197+00:00
-- url     : https://prove2.me/theorems/054e0420-00dc-4629-a8b8-09e06bb0a459
-- title:
--   Input cutoffs, the concentration event $\mathcal E$ and the deterministic cutoff $t^\prime_M$
-- statement:
--   Fix the sample $I_p$ and $\varepsilon$; ranks in the input are in decreasing order of size with ties by label.
--
--   1. $R_i$ is the input rank of the boundary item of the sample groups $G^p_1,\dots,G^p_i$ (the item defining $t_i$), $R_0=0$, $R_K=|L|$; $R_M$ is the input rank of the item defining $t_M$. The input medium items $M$ have ranks $R_K+1,\dots,R_M$ and the input small items $S$ ranks above $R_M$.
--   2. The event $\mathcal E$:
--   $$\Big|\frac{\mathrm{vol}(I_p)}p-\mathrm{vol}(I)\Big|\le2\mathrm{vol}(I)^{2/3},\quad \Big|R_i-\frac{i\,\mathrm{vol}(I)}{K\varepsilon}\Big|\le\frac4\varepsilon\mathrm{vol}(I)^{2/3}\ (i\in[K]),\quad \big|R_M-(1+\varepsilon^{-1})\mathrm{vol}(I)\big|\le\frac4\varepsilon\mathrm{vol}(I)^{2/3}.$$
--   3. $R'_M=\lfloor(1+\varepsilon^{-1})\mathrm{vol}(I)-\frac4\varepsilon\mathrm{vol}(I)^{2/3}\rfloor$; $t'_M$ is the size of the item of rank $R'_M$; $S'$ holds the items of rank above $R'_M$ and $M'$ those of ranks $|L|+1,\dots,R'_M$.
--   4. $\tau=\mathrm{vol}(S_p)/(p\sqrt{\mathrm{vol}(I)})$ and $t_M$ is the smallest size in $M_p$.
--
--   These are the quantities of Lemmas B.4, B.6 and B.8.
--
--   **Formalization Note** $R_i$ is the largest input rank of a large sample item in groups $1,\dots,i$, which is the paper's $R_i$ when $G^p_i$ is nonempty. $R'_M$ uses the natural-number floor ($0$ for a negative argument). $t'_M$ is written as the least size among the items of rank at most $R'_M$, the same value.
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), §3.1, p.9 (PDF p.10); App. B.1, p.21 (PDF p.22); App. B.3, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_OnlineBinCover_ConfigLP

namespace OnlineBinCover

/-!
# Input cutoffs, the concentration event `E` and the deterministic cutoff `t′_M`

Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…), §3.1 p.9 and App. B.1 p.21 (the input ranks
`R_i`, `R_M` and the event `E`), App. B.3 pp.23 (`R′_M`, `t′_M`, `S′`, `M′`, `τ`).

The sample `J` and `ε` are fixed; ranks in the whole input are `rankIn s univ` (decreasing size,
ties by label, the same rule as in the sample).

**Formalization Note.**
* `Rcum s J ε i` is the input rank of the boundary item of the first `i` sample groups: the largest
  input rank of a large sample item in groups `1, …, i`. It is the paper's `R_i` when group `i` is
  nonempty (and `R_{i−1}` otherwise); `Rcum … 0 = 0 = R_0` and `Rcum … K = R_K = |L|`.
* `RMrank` is the input rank `R_M` of the boundary item defining `t_M` (the largest input rank of a
  large or medium sample item). The input classes are `M` = ranks `R_K + 1, …, R_M` and `S` = ranks
  above `R_M`; they agree with `classOf`.
* `EventE s J ε p` is the event `E` (p.21) with `vol(Ip) = volOn s J`.
* `R′_M = ⌊(1 + ε^{-1}) vol(I) − (4/ε) vol(I)^{2/3}⌋` (`Nat.floor`, which is `0` for a negative
  argument); `t′_M` is the size of the item of rank `R′_M`, written as the least size among the
  items of rank at most `R′_M` (`0` if there are none); `S′` contains the items of rank above
  `R′_M`, `M′` those of ranks `|L| + 1, …, R′_M`.
* `τ = vol(Sp) / (p √vol(I))`; `t_M` is the smallest size in `Mp` (`0` if `Mp` is empty).
-/

open Finset

/-- The input rank of the boundary item of sample groups `1, …, i` (`R_i`). -/
noncomputable def Rcum {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) (i : ℕ) : ℕ :=
  ((largeOf s J ε).filter (fun a => groupIdx s J ε a < i)).sup (rankIn s univ)

/-- The input rank `R_M` of the boundary item defining `t_M`. -/
noncomputable def RMrank {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) : ℕ :=
  (largeOf s J ε ∪ medOf s J ε).sup (rankIn s univ)

/-- The input medium items `M`: ranks `R_K + 1, …, R_M`. -/
noncomputable def inputM {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) :
    Finset (Fin n) :=
  univ.filter (fun a => Rcum s J ε (Kof ε) < rankIn s univ a ∧ rankIn s univ a ≤ RMrank s J ε)

/-- The input small items `S`: ranks above `R_M`. -/
noncomputable def inputS {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) :
    Finset (Fin n) :=
  univ.filter (fun a => RMrank s J ε < rankIn s univ a)

/-- The concentration event `E` (App. B.1, p.21). -/
def EventE {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε p : ℝ) : Prop :=
  |volOn s J / p - vol s| ≤ 2 * vol s ^ ((2 : ℝ) / 3) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ Kof ε →
      |(Rcum s J ε i : ℝ) - (i : ℝ) * vol s / ((Kof ε : ℝ) * ε)| ≤
        4 / ε * vol s ^ ((2 : ℝ) / 3)) ∧
    |(RMrank s J ε : ℝ) - (1 + ε⁻¹) * vol s| ≤ 4 / ε * vol s ^ ((2 : ℝ) / 3)

/-- `R′_M = ⌊(1 + ε^{-1}) vol(I) − (4/ε) vol(I)^{2/3}⌋` (App. B.3, p.23). -/
noncomputable def RMprime {n : ℕ} (s : Fin n → ℝ) (ε : ℝ) : ℕ :=
  ⌊(1 + ε⁻¹) * vol s - 4 / ε * vol s ^ ((2 : ℝ) / 3)⌋₊

/-- `t′_M`, the size of the item of rank `R′_M`. -/
noncomputable def tMprime {n : ℕ} (s : Fin n → ℝ) (ε : ℝ) : ℝ :=
  by classical exact
    if h : (univ.filter (fun a => rankIn s univ a ≤ RMprime s ε)).Nonempty then
      (univ.filter (fun a => rankIn s univ a ≤ RMprime s ε)).inf' h s
    else 0

/-- `S′`: the items after the cutoff `R′_M`. -/
noncomputable def Sprime {n : ℕ} (s : Fin n → ℝ) (ε : ℝ) : Finset (Fin n) :=
  univ.filter (fun a => RMprime s ε < rankIn s univ a)

/-- `M′`: the items of ranks `|L| + 1, …, R′_M`. -/
noncomputable def Mprime {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) :
    Finset (Fin n) :=
  univ.filter (fun a => Rcum s J ε (Kof ε) < rankIn s univ a ∧ rankIn s univ a ≤ RMprime s ε)

/-- `t_M`, the smallest size in `Mp`. -/
noncomputable def tM {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) : ℝ :=
  by classical exact if h : (medOf s J ε).Nonempty then (medOf s J ε).inf' h s else 0

/-- `τ = vol(Sp) / (p √vol(I))`. -/
noncomputable def tau {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε p : ℝ) : ℝ :=
  volOn s (smallOf s J ε) / (p * Real.sqrt (vol s))

end OnlineBinCover


