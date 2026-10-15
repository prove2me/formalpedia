-- Prove2me | Definitions.Def_StrictCompatLB_MeanField_Occupancy
-- name    : StrictCompatLB_MeanField_Occupancy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:14.983407+00:00
-- url     : https://prove2.me/theorems/4d68bee5-97ad-4ba6-873f-61be41173f09
-- title:
--   Queue-length states, global and local empirical distributions, occupancy, the spaces 𝒳 and 𝒴, ε-bad dispatchers, and the Lyapunov functions (H.3)
-- statement:
--   A state of the system with $N$ servers is a vector $z=(z_v)_{v\in V_N}\in\mathcal S_N=\mathbb N^{V_N}$ of queue lengths. For a state $z$:
--
--   1. $Q_i(z)=|\{v:z_v\ge i\}|$ is the number of servers with at least $i$ tasks, and $q_i(z)=Q_i(z)/N$ is the **global occupancy** (so $q_0(z)=1$).
--   2. $x_i(z)=|\{v:z_v=i\}|/N$ is the **global empirical queue length distribution** (GEQD), and for a dispatcher $w$, $x^w_i(z)=|\{v\in\mathcal N_w:z_v=i\}|/|\mathcal N_w|$ is the **local empirical queue length distribution** (LEQD).
--   3. $\mathcal X=\{x\in\ell_1:\ x_i\ge0,\ \sum_{i\ge0}x_i=1\}$ and $\mathcal Y=\{q\in\ell_1:\ q_i\in[0,1],\ q_i\ge q_j\text{ for }i<j\}$ are the spaces of empirical distributions and of occupancies.
--   4. A dispatcher $w$ is **$\varepsilon$-good** in state $z$ if $\sum_{i\ge0}|x_i(z)-x^w_i(z)|<\varepsilon$ and **$\varepsilon$-bad** otherwise (Definition 4.4); $B^\varepsilon_N(z)$ is the number of $\varepsilon$-bad dispatchers.
--   5. The **Lyapunov functions** (H.3): for $k\ge1$,
--   $$V_k(z)=\sum_{i=k}^\infty\sum_{j=i}^\infty Q_j(z).$$
--   6. The set (H.10) $C_\Gamma=\{z\in\mathcal S_N:\sum_{i\ge1}Q_i(z)\le\Gamma\}$, and the tail sums $\sum_{i\ge k}q_i(z)$ and $\sum_{i\ge j}\omega_iq_i(z)$ for weights $\omega$.
--
--   These are the statistics in terms of which the mean-field limit, the stability analysis and the tightness of the steady states are stated.
--
--   **Formalization Note** States are `Fin N → ℕ`. The occupancy is indexed from $i=0$ with $q_0(z)=1$ (for $N\ge1$), so that it is a state in the sense of `PowerTwoChoices.Limit.IsState`; the paper's $q(z)=(q_i(z))_{i\ge1}$ and its $\ell_1$ norm are recovered because coordinate $0$ equals $1$ on both sides of every distance used. $\mathcal Y$ is encoded as `IsState q` (which gives $q_0=1$, $q\ge0$ and $q$ nonincreasing, hence $q\le1$) together with summability of $(q_i)_{i\ge1}$. The $\ell_1$ distance in Definition 4.4 is `PowerOfDUniversality.Fluid.l1dist`, valued in $[0,\infty]$. All infinite sums over levels in items 5–6 are finite sums, since $Q_i(z)=0$ above the longest queue. The LEQD divides by $|\mathcal N_w|$; it is only used where $\mathcal N_w\ne\emptyset$.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 7, §1.4 (ℓ_1, ℓ^ω_1); p. 9, §2 (S_N, X_i, x_i, x^w_i, Q_i, q_i, 𝒳, 𝒴); p. 16, Definition 4.4, (4.3); p. 17 (B^ε_N); p. 47, (H.3); p. 48, (H.10)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_GraphConditions
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open Finset
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-! States of the load-balancing system and their statistics (Rutten & Mukherjee,
arXiv:2008.07562v2, §2, p. 9; §1.4, p. 7; Def. 4.4, p. 16; (H.3), p. 47; (H.10), p. 48).
A state `z ∈ S_N = ℕ^{V_N}` is the vector `z : Fin N → ℕ` of queue lengths of the `N` servers. -/

/-- `Q_i(z) = |{v ∈ V_N : z_v ≥ i}|`, the number of servers with at least `i` tasks
(so `Q_0(z) = N`). -/
def Qcount {N : ℕ} (z : Fin N → ℕ) (i : ℕ) : ℕ :=
  (univ.filter (fun v => i ≤ z v)).card

/-- The global occupancy `q_i(z) = Q_i(z)/N`, as a sequence indexed from `i = 0`
(`q_0(z) = 1` for `N ≥ 1`; the paper's `q(z) = (q_i(z))_{i ≥ 1}`). -/
noncomputable def occ {N : ℕ} (z : Fin N → ℕ) : ℕ → ℝ :=
  fun i => (Qcount z i : ℝ) / (N : ℝ)

/-- The global empirical queue length distribution (GEQD) `x_i(z) = |{v : z_v = i}|/N`. -/
noncomputable def geqd {N : ℕ} (z : Fin N → ℕ) : ℕ → ℝ :=
  fun i => ((univ.filter (fun v => z v = i)).card : ℝ) / (N : ℝ)

/-- The local empirical queue length distribution (LEQD) of dispatcher `w`:
`x^w_i(z) = |{v ∈ 𝒩_w : z_v = i}| / |𝒩_w|` (`0` when `𝒩_w = ∅`). -/
noncomputable def leqd (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) : ℕ → ℝ :=
  fun i => (((nbrW M G N w).filter (fun v => z v = i)).card : ℝ) / ((nbrW M G N w).card : ℝ)

/-- The space `𝒳` of empirical queue length distributions (p. 9): `x ∈ ℓ₁`, `x_i ≥ 0`,
`∑_{i ≥ 0} x_i = 1`. -/
def InX (x : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ HasSum x 1

/-- The occupancy space `𝒴` (p. 9): `q_i ∈ [0, 1]`, `q_i ≥ q_j` for `i < j`, and `q ∈ ℓ₁`;
written with the index-`0` convention `q_0 = 1` of `PowerTwoChoices.Limit.IsState`
(which gives `q ≥ 0` and `q` nonincreasing, hence `q ≤ 1`) and summability of
`(q_i)_{i ≥ 1}`. -/
def InY (q : ℕ → ℝ) : Prop :=
  PowerTwoChoices.Limit.IsState q ∧ Summable (fun i => q (i + 1))

/-- The largest queue length `max_v z_v` (`0` when `N = 0`); `Q_i(z) = 0` for `i` above it. -/
def maxLen {N : ℕ} (z : Fin N → ℕ) : ℕ :=
  univ.sup z

/-- `∑_{i ≥ k} q_i(z)`, a finite sum since `q_i(z) = 0` for `i > max_v z_v`. -/
noncomputable def tailSum {N : ℕ} (k : ℕ) (z : Fin N → ℕ) : ℝ :=
  ∑ i ∈ Ico k (maxLen z + 1), occ z i

/-- `∑_{i ≥ j} ω_i q_i(z)`, a finite sum since `q_i(z) = 0` for `i > max_v z_v`. -/
noncomputable def weightedTail {N : ℕ} (ω : ℕ → ℝ) (j : ℕ) (z : Fin N → ℕ) : ℝ :=
  ∑ i ∈ Ico j (maxLen z + 1), ω i * occ z i

/-- The Lyapunov function (H.3) (p. 47): `V_k(z) = ∑_{i ≥ k} ∑_{j ≥ i} Q_j(z)`, a finite sum
since `Q_j(z) = 0` for `j > max_v z_v`. -/
noncomputable def lyap {N : ℕ} (k : ℕ) (z : Fin N → ℕ) : ℝ :=
  ∑ i ∈ Ico k (maxLen z + 1), ∑ j ∈ Ico i (maxLen z + 1), (Qcount z j : ℝ)

/-- The set `C_Γ = {z ∈ S_N : ∑_{i ≥ 1} Q_i(z) ≤ Γ}` of (H.10) (p. 48). -/
def CGamma (N : ℕ) (Γ : ℝ) : Set (Fin N → ℕ) :=
  {z | (∑ i ∈ Ico 1 (maxLen z + 1), (Qcount z i : ℝ)) ≤ Γ}

/-- The number `B^ε_N` of `ε`-bad dispatchers in state `z` (Def. 4.4, p. 16; p. 17):
`w` is `ε`-good if `∑_{i ≥ 0} |x_i(z) − x^w_i(z)| < ε` and `ε`-bad otherwise. The `ℓ₁` sum is
`PowerOfDUniversality.Fluid.l1dist`, computed in `[0, ∞]`. -/
noncomputable def badCount (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (ε : ℝ) (z : Fin N → ℕ) : ℕ :=
  (univ.filter (fun w : Fin (M N) =>
    ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist (geqd z) (leqd M G N z w))).card

end StrictCompatLB.MeanField


