-- Prove2me | Definitions.Def_KTaxi_Competitive_Analysis
-- name    : KTaxi_Competitive_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:48.68103+00:00
-- url     : https://prove2.me/theorems/4a751c57-9b1b-4936-87af-d3238e125eca
-- title:
--   Quantities of the analysis: $Z_m$, $\Delta_{m,i}$, $\Delta_m$, augmenting chains $M_m$, the level $\ell$, $C_m(T)$, $\varepsilon_m$, $g_m$
-- statement:
--   Fix an online ordered list $x=(x_1,\dots,x_k)$, an adversary configuration $Y$ and a pickup $r$, and write $d_i=d(x_i,r)$.
--
--   1. $X_m$ is the multiset of locations of the first $m$ entries of a list.
--   2. $Z_m=\sum_{i=1}^m w_i/d_i$ (used when $d_1,\dots,d_m>0$).
--   3. $\Delta_{m,i}=D(X_m-x_i+r,Y)-D(X_m,Y)$ for $i\le m$: the change of the level-$m$ matching cost if taxi $x_i$ were moved to $r$; and $\Delta_m=\sum_{i=1}^m\frac{w_i}{d_i}\Delta_{m,i}$.
--   4. An **augmenting chain** is a sequence of matchings $M_0=\emptyset,M_1,\dots,M_k$, $M_m$ an injection of the positions $1,\dots,m$ into the adversary's taxis, such that each $M_m$ is optimal (its cost is $D(X_m,Y)$) and $M_m$ arises from $M_{m-1}$ by augmenting along one alternating path: positions $i_0=m,i_1,\dots,i_t<m$, distinct, with $M_m(i_s)=M_{m-1}(i_{s+1})$ for $s<t$, $M_m(i_t)=y_m$ an adversary taxi not used by $M_{m-1}$, and $M_m=M_{m-1}$ on all other old positions. In particular the images $Y_m=\{y_1,\dots,y_m\}$ are nested.
--   5. $\ell$ is the **first level whose matching uses $r$**: $1\le\ell\le k$, $M_\ell$ matches some position to an adversary taxi located at $r$, and no $M_m$ with $m<\ell$ does. Equivalently, $\ell$ is the first index with $y_\ell=r$ (as a location).
--   6. $C_m(T)=\sum_{i\le m,\ d_i\le T}d\bigl(x_i,M_m(x_i)\bigr)$ and
--   $$
--   \varepsilon_m=\min\{\varepsilon\ge0:\ C_m(T)\le\varepsilon T\ \text{for every }T>0\},
--   $$
--   with $\varepsilon_0=0$.
--   7. $g_m=\bigl(D(X_m,Y)-D(X_{m-1},Y)\bigr)/d_m$.
--
--   These are the quantities of Claims 3.1 and 4.4–4.6, Lemma 4.3 and the §4.2 computations.
--
--   **Formalization Note** Positions are 0-based slots (`weight j` is the paper's $w_{j+1}$), levels `m : ℕ` count leading slots. A chain is `M : ℕ → Fin k → Fin k` (`M m` matters only on slots `< m`), with the structure `IsAugmentingChain`; `IsFirstUse Y r M ℓ` characterises $\ell$. `epsLevel` is the real `sInf` of the set in 6: when $d_i>0$ for the relevant slots the set is nonempty, closed and bounded below, so this is the minimum; if some relevant $d_i=0$ with a positive matching edge the set is empty and `sInf` returns $0$, which is why the claims carry positivity hypotheses. `gNorm x Y r j` is $g_{j+1}$, indexed by the slot `j` of the new taxi. `normZ` and `levelDelta` divide by $d_i$ and are used only under $d_i>0$.
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Claim 3.1 (PDF p. 5); §4.1 (PDF p. 7, Z_m); §4.2 (PDF p. 8, Δ_{m,i}, the matchings M_m and ℓ); §4.3 (PDF pp. 8–11, ε_{ℓ−1}, Δ_m, ε_m, g_m, C_m(T))

import Mathlib
import Definitions.Def_KTaxi_Competitive_Potential

namespace KTaxi.Competitive

/-! # Quantities of the analysis of §§3–4

Coester, Huang, Poon, STOC 2027 submission #96, Claim 3.1 (PDF p. 5), §4.1 (PDF p. 7),
§4.2 (PDF p. 8), §4.3 (PDF pp. 8–11).

Slots `j : Fin k` are 0-based (paper rank `j + 1`); levels `m : ℕ` count leading slots.
Throughout, `x : Fin k → V` is the online ordered list, `Y : Fin k → V` the adversary
configuration and `r` the pickup; `d_j = d(x_j, r)`.
-/

open Finset

variable {V : Type*} [MetricSpace V] {k : ℕ}

/-- The multiset `X_m` of locations in the level-`m` prefix of the ordered list `x`. -/
def prefixMultiset (x : Fin k → V) (m : ℕ) : Multiset V :=
  (univ.filter fun j : Fin k => j.val < m).val.map x

/-- The normalizing constant `Z_m = ∑_{j < m} w_j / d_j` of level `m` (meaningful when
`d_j > 0` for the slots `j < m`). -/
noncomputable def normZ (x : Fin k → V) (r : V) (m : ℕ) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin k => j.val < m), weight j / dist (x j) r

/-- `Δ_{m,i} = D(X_m - x_i + r, Y) - D(X_m, Y)`: the change of the level-`m` matching cost if
the taxi in slot `i` (with `i < m`) were moved to `r`. -/
noncomputable def moveDelta (x Y : Fin k → V) (r : V) (m : ℕ) (i : Fin k) : ℝ :=
  levelCost (Function.update x i r) Y m - levelCost x Y m

/-- `Δ_m = ∑_{i < m} (w_i / d_i) Δ_{m,i}`, so that `Δ_m / Z_m` is the expected change of the
level-`m` matching cost. -/
noncomputable def levelDelta (x Y : Fin k → V) (r : V) (m : ℕ) : ℝ :=
  ∑ i ∈ univ.filter (fun i : Fin k => i.val < m), weight i / dist (x i) r * moveDelta x Y r m i

/-- **Augmenting chain of optimal matchings** (§4.2, PDF p. 8). `M m` is a matching of the
level-`m` prefix into the adversary taxis (only its values on slots `< m` matter), for
`0 ≤ m ≤ k`:
1. `M m` is injective on the slots `< m`;
2. `M m` is an optimal matching: its cost is `D(X_m, Y)`;
3. for `1 ≤ m ≤ k`, `M m` is obtained from `M (m-1)` by augmenting along exactly one alternating
   path `p 0, p 1, …, p t` of slots that starts at the new slot `p 0 = m - 1`, visits distinct
   old slots `p 1, …, p t < m - 1`, gives each `p s` (`s < t`) the old partner of `p (s+1)`, ends
   by matching `p t` to an adversary taxi `y_m` unused by `M (m-1)`, and leaves all other old
   slots unchanged. -/
structure IsAugmentingChain (x Y : Fin k → V) (M : ℕ → Fin k → Fin k) : Prop where
  injOn : ∀ m ≤ k, ∀ i j : Fin k, i.val < m → j.val < m → M m i = M m j → i = j
  optimal : ∀ m ≤ k,
    ∑ j ∈ univ.filter (fun j : Fin k => j.val < m), dist (x j) (Y (M m j)) = levelCost x Y m
  augment : ∀ m, 1 ≤ m → m ≤ k → ∃ (t : ℕ) (p : Fin (t + 1) → Fin k),
    Function.Injective p ∧ (p 0).val = m - 1 ∧
    (∀ s : Fin (t + 1), s ≠ 0 → (p s).val < m - 1) ∧
    (∀ s : Fin t, M m (p s.castSucc) = M (m - 1) (p s.succ)) ∧
    (∀ j : Fin k, j.val < m - 1 → M (m - 1) j ≠ M m (p (Fin.last t))) ∧
    (∀ j : Fin k, j.val < m - 1 → j ∉ Set.range p → M m j = M (m - 1) j)

/-- `ℓ` is the **first level whose matching uses `r`** (§4.2, PDF p. 8): `1 ≤ ℓ ≤ k`, the
level-`ℓ` matching matches some prefix slot to an adversary taxi located at `r`, and no level
`m < ℓ` does (locations, not taxi identities, are compared). For an augmenting chain this is the
first index with `y_ℓ = r`. -/
def IsFirstUse (Y : Fin k → V) (r : V) (M : ℕ → Fin k → Fin k) (ℓ : ℕ) : Prop :=
  1 ≤ ℓ ∧ ℓ ≤ k ∧ (∃ j : Fin k, j.val < ℓ ∧ Y (M ℓ j) = r) ∧
    ∀ m < ℓ, ∀ j : Fin k, j.val < m → Y (M m j) ≠ r

/-- `C_m(T) = ∑_{j < m, d_j ≤ T} d(x_j, M_m(x_j))`: the length of the level-`m` matching
edges whose online endpoint is within distance `T` of `r` (PDF p. 10). -/
noncomputable def nearCost (x Y : Fin k → V) (r : V) (M : ℕ → Fin k → Fin k) (m : ℕ) (T : ℝ) :
    ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin k => j.val < m ∧ dist (x j) r ≤ T), dist (x j) (Y (M m j))

/-- `ε_m = min {ε ≥ 0 : C_m(T) ≤ ε T for every T > 0}` (PDF pp. 8, 10). Written as an infimum;
when `d_j > 0` for all slots `j < m` the set is nonempty, closed and bounded below, so the
infimum is a minimum. `ε_0 = 0`. -/
noncomputable def epsLevel (x Y : Fin k → V) (r : V) (M : ℕ → Fin k → Fin k) (m : ℕ) : ℝ :=
  sInf {ε : ℝ | 0 ≤ ε ∧ ∀ T : ℝ, 0 < T → nearCost x Y r M m T ≤ ε * T}

/-- The normalized matching-cost decrease `g_m = (D(X_m, Y) - D(X_{m-1}, Y)) / d_m`
(PDF p. 10) at level `m = j + 1`, written with the slot `j` of the new taxi. -/
noncomputable def gNorm (x Y : Fin k → V) (r : V) (j : Fin k) : ℝ :=
  (levelCost x Y (j.val + 1) - levelCost x Y j.val) / dist (x j) r

end KTaxi.Competitive


