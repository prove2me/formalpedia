-- Prove2me | Definitions.Def_SmoothBandit_Regret_Algorithm
-- name    : SmoothBandit_Regret_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:46.964281+00:00
-- url     : https://prove2.me/theorems/a456e43a-127a-4a90-8263-dd9462fb3418
-- title:
--   §3, pp. 14–18, and §4.1, p. 22 — Algorithm 1 (SmoothBandit): grid, epochs (10), local polynomial estimator, decision regions (6)–(9), the regret, and the events ℳ_k, 𝒢_k
-- statement:
--   This file writes out Algorithm 1 (SmoothBandit) of Hu, Kallus and Mao as a function of the observed data and the coins, its regret, and the events used in its analysis. Everything depends on the horizon $T$, the model parameters (through $\mathfrak b(\beta)$, $c_0$, $d$, $p$ and $C_0$) and the support $\mathcal X$.
--
--   **Grid (§3.2.2).** Let $\delta = T^{-\beta/(2\beta+d)}(\log T)^{-1}$ and
--   $$G' = \Big\{\Big(\tfrac{2j_1+1}{2}\delta, \dots, \tfrac{2j_d+1}{2}\delta\Big) : j_i \in \{0, \dots, \lceil\delta^{-1}\rceil - 1\}\Big\}.$$
--   $g(x)$ is the point of $G'$ closest to $x$, and among several closest points the one closest to the origin. $\mathrm{Cube}(x) = \{x' \in \mathcal X : g(x') = g(x)\}$, and $G$ is the set of grid points whose cube has positive mass.
--
--   **Epochs (§3.2.3).** With $\epsilon_k = 2^{-k}$, epoch $k$ has length
--   $$n_k = \Big\lceil \frac4p\Big(\frac{\log(T\delta^{-d})}{C_0\epsilon_k^2}\Big)^{\frac{2\beta+d}{2\beta}} + \frac2{p^2}\log T\Big\rceil ,$$
--   its rounds are $\mathcal T_k = \{t : \sum_{i<k} n_i < t \le \min(\sum_{i \le k} n_i, T)\}$, and the number of epochs $K$ is the least integer with $\sum_{k \le K} n_k \ge T$.
--
--   **Local polynomial regression (Definition 3).** Given samples $(X_s, Y_s)$, a point $x$, a bandwidth $h$ and a degree $l$, $\hat\eta^{LP}(x; S, h, l) = \hat\vartheta_0$ is the value at $x$ of the polynomial $\theta(u; x, \vartheta, l) = \sum_{|r| \le l}\vartheta_r(u - x)^r$ that minimises $\sum_{s : X_s \in \mathcal B(x, h)}(Y_s - \theta(X_s; x, \vartheta, l))^2$; it is $0$ when the minimiser is not unique.
--
--   **Algorithm 1.** Start with $\mathcal E_{\pm1,1} = \emptyset$ and $\mathcal R_1 = \mathcal X$. In every round of epoch $k$, pull $+1$ if $X_t \in \bigcup_{j \le k}\mathcal E_{+1,j}$, else $-1$ if $X_t \in \bigcup_{j \le k}\mathcal E_{-1,j}$, else toss the fair coin. After epoch $k$, with $S_{a,k}$ the samples of arm $a$ in epoch $k$, $N_{a,k} = |S_{a,k}|$ and $H_{a,k} = N_{a,k}^{-1/(2\beta+d)}$:
--   1. $\mathcal D_{a,k}$ is the union of the cubes of $\mathcal R_k \cap G$ at whose centre $((\bigcup_{j \le k}\mathcal E_{a,j}) \cup \mathcal R_k) \cap \mathcal X$ is not weakly $(c_0/2^d, H_{a,k})$-regular (6);
--   2. on the remaining cubes of $\mathcal R_k \cap G$, $\hat\tau_k = \hat\eta^{LP}(\cdot; S_{+1,k}, H_{+1,k}, \mathfrak b(\beta)) - \hat\eta^{LP}(\cdot; S_{-1,k}, H_{-1,k}, \mathfrak b(\beta))$ at the cube centre (7);
--   3. $\mathcal E_{a,k+1}$ collects those cubes with $a\hat\tau_k > \epsilon_k$, together with $\mathcal D_{-a,k}$ (8), and $\mathcal R_{k+1}$ those with $|\hat\tau_k| \le \epsilon_k$ (9).
--
--   The **regret** of the algorithm with horizon $T$ is $R_T(\hat\pi) = E\big[\sum_{t=1}^T (Y_t(\pi^*(X_t)) - Y_t(A_t))\big]$.
--
--   **Events (§4.1).** $\mathcal M_k = \{N_{1,k} \wedge N_{-1,k} \ge (\log(T\delta^{-d})/(C_0\epsilon_k^2))^{(2\beta+d)/(2\beta)}\}$, $\mathcal G_k = \{\sup_{x \in \mathcal R_k \cap \mathcal D^C_{1,k} \cap \mathcal D^C_{-1,k}} |\hat\tau_k(x) - \tau(x)| \le \epsilon_k\}$, and $\bar{\mathcal G}_k$, $\bar{\mathcal M}_k$ are their intersections over $1 \le j \le k$ (the whole space for $k = 0$).
--
--   **Formalization Note.** Regions are finite sets of grid cells, so they are unions of cubes by construction (Lemma 4); $\mathcal R_1$ is every cell of $G'$, whose cubes cover $\mathcal X$. The tests "$x \in \mathcal R_{k-1} \cap G$" of (6), (8), (9) are read on cells: a cube is processed whenever its cell lies in the region, even if its centre is outside $\mathcal X$ (the page uses such centres, p. 18), and regularity in (6) is tested at the centre, which need not lie in the set. $G$ uses Lebesgue volume instead of the context law, equivalent under Assumption 3. The samples are indexed by their rounds. $H$ uses $\max(N, 1)$: the page's $N = 0$ gives $H = \infty$, Lean's $0^{-x}$ would give $0$. The algorithm reads only $\mathcal X$, the contexts, the coins and the rewards of the pulled arms. The supremum in $\mathcal G_k$ is taken in the extended reals ($-\infty$ over the empty set); $\hat\tau_k(x)$ is the estimate at $g(x)$ (11).
-- source:
--   Hu, Kallus & Mao, Smooth Contextual Bandits, arXiv:1909.02553v4, pp. 14–18 and 22: Definition 3 (4), Algorithm 1 (6)–(9), §3.2.2 (grid), §3.2.3 (10) and K, (11), §2.1 (2), §4.1 (ℳ_k, 𝒢_k, Ḡ_k, M̄_k)

import Mathlib
import Definitions.Def_SmoothBandit_Regret_Model

noncomputable section

namespace SmoothBandit.Regret

open MeasureTheory ProbabilityTheory Classical

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-! ### Grid structure (§3.2.2) -/

/-- The cube side `δ = T^{-β/(2β+d)} (log T)^{-1}`. -/
def delta (P : Params) (d T : ℕ) : ℝ :=
  (T : ℝ) ^ (-(P.β / (2 * P.β + d))) * (Real.log T)⁻¹

/-- Grid indices `j = (j_1, …, j_d)`. -/
abbrev Idx (d : ℕ) := Fin d → ℕ

/-- The index set of `G'`: `j_i ∈ {0, …, ⌈δ^{-1}⌉ - 1}`. -/
def grid (P : Params) (d T : ℕ) : Finset (Idx d) :=
  Fintype.piFinset fun _ => Finset.range ⌈(delta P d T)⁻¹⌉₊

/-- The grid point `((2j_1+1)/2 δ, …, (2j_d+1)/2 δ)` of `G'`. -/
def center (P : Params) (d T : ℕ) (j : Idx d) : E d :=
  WithLp.toLp 2 (fun i => (2 * (j i : ℝ) + 1) / 2 * delta P d T)

/-- `g(x)`: the index of the grid point of `G'` closest to `x`; among several closest points, the one
closest to the origin. (These ties form a box of grid points, whose point nearest the origin is
unique.) -/
def gIdx (P : Params) (d T : ℕ) (x : E d) : Idx d :=
  let near := (grid P d T).filter
    (fun j => ∀ j' ∈ grid P d T, dist x (center P d T j) ≤ dist x (center P d T j'))
  let tie := near.filter (fun j => ∀ j' ∈ near, ‖center P d T j‖ ≤ ‖center P d T j'‖)
  if h : tie.Nonempty then h.choose else fun _ => 0

/-- `Cube(x) = {x' ∈ 𝒳 : g(x') = g(x)}`, indexed by the grid index `j = g(x)`. -/
def Cube (P : Params) (T : ℕ) (M : Machine d Ω) (j : Idx d) : Set (E d) :=
  {x | x ∈ M.𝒳 ∧ gIdx P d T x = j}

/-- `G = {x ∈ G' : P(Cube(x) ∩ 𝒳) > 0}`, with the probability replaced by Lebesgue volume
(equivalent under Assumption 3). -/
def Gset (P : Params) (T : ℕ) (M : Machine d Ω) : Finset (Idx d) :=
  (grid P d T).filter (fun j => 0 < volume (Cube P T M j))

/-- The region `⋃_{j ∈ S} Cube(j) ⊆ 𝒳` of a set `S` of grid cells. -/
def pts (P : Params) (T : ℕ) (M : Machine d Ω) (S : Finset (Idx d)) : Set (E d) :=
  {x | x ∈ M.𝒳 ∧ gIdx P d T x ∈ S}

/-! ### Epoch structure (§3.2.3) -/

/-- The error tolerance `ϵ_k = 2^{-k}`. -/
def eps (k : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ k

/-- The epoch length (10):
`n_k = ⌈(4/p) (log(T δ^{-d}) / (C0 ϵ_k^2))^{(2β+d)/(2β)} + (2/p^2) log T⌉`. -/
def nEp (P : Params) (d T k : ℕ) : ℕ :=
  ⌈4 / pConst P d *
      (Real.log (T * (delta P d T ^ d)⁻¹) / (C0 P d * eps k ^ 2)) ^
        ((2 * P.β + d) / (2 * P.β)) +
    2 / pConst P d ^ 2 * Real.log T⌉₊

/-- The first (Lean, 0-based) round of epoch `k ≥ 1`: `∑_{i=1}^{k-1} n_i`. -/
def epStart (P : Params) (d T k : ℕ) : ℕ := ∑ i ∈ Finset.Ico 1 k, nEp P d T i

/-- The rounds `𝒯_k` of epoch `k ≥ 1`, 0-based: `∑_{i<k} n_i ≤ t < min(∑_{i≤k} n_i, T)`. -/
def epTimes (P : Params) (d T k : ℕ) : Finset ℕ :=
  Finset.Ico (epStart P d T k) (min (epStart P d T (k + 1)) T)

/-- The number of epochs `K`: the least integer with `∑_{k=1}^K n_k ≥ T`. -/
def numEpochs (P : Params) (d T : ℕ) : ℕ :=
  sInf {K : ℕ | T ≤ ∑ k ∈ Finset.Icc 1 K, nEp P d T k}

/-- The epoch `k ≥ 1` containing the 0-based round `t`. -/
def epochOf (P : Params) (d T t : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ t < epStart P d T (k + 1)}

/-! ### Local polynomial regression (Definition 3) -/

/-- The degree-`l` polynomial model `θ(u; x, ϑ, l) = ∑_{|r| ≤ l} ϑ_r (u - x)^r`. -/
def theta {l : ℕ} (u x : E d) (ϑ : multiIdx d l → ℝ) : ℝ :=
  ∑ r : multiIdx d l, ϑ r * mono r.1 (u - x)

/-- The least-squares objective (4): `∑_{s ∈ S, X_s ∈ B(x,h)} (Y_s - θ(X_s; x, ϑ, l))^2`, for the
samples `(X_s, Y_s)`, `s ∈ S`. -/
def lsObj (S : Finset ℕ) (Xs : ℕ → E d) (Ys : ℕ → ℝ) (x : E d) (h : ℝ) (l : ℕ)
    (ϑ : multiIdx d l → ℝ) : ℝ :=
  ∑ s ∈ S.filter (fun s => dist (Xs s) x ≤ h), (Ys s - theta (Xs s) x ϑ) ^ 2

/-- Definition 3: `η̂^LP(x; S, h, l) = θ(x; x, ϑ̂_x, l)` for the minimiser `ϑ̂_x` of (4), and `0`
if the minimiser is not unique. -/
def etaLP (S : Finset ℕ) (Xs : ℕ → E d) (Ys : ℕ → ℝ) (x : E d) (h : ℝ) (l : ℕ) : ℝ :=
  if hu : ∃! ϑ : multiIdx d l → ℝ, ∀ ϑ', lsObj S Xs Ys x h l ϑ ≤ lsObj S Xs Ys x h l ϑ' then
    theta x x hu.exists.choose
  else 0

/-! ### Algorithm 1 (SmoothBandit) -/

/-- The decision regions at the start of epoch `k`, as sets of grid cells:
`E a` holds `⋃_{j=1}^k ℰ_{a,j}` and `R` holds `ℛ_k`. -/
structure Regions (d : ℕ) where
  E : Arm → Finset (Idx d)
  R : Finset (Idx d)

/-- Line 1: `ℰ_{±1,1} = ∅` and `ℛ_1 = 𝒳` (every cell). -/
def initRegions (P : Params) (d T : ℕ) : Regions d := ⟨fun _ => ∅, grid P d T⟩

/-- Lines 3 and 12–14: pull `+1` on `⋃_j ℰ_{+1,j}`, else `-1` on `⋃_j ℰ_{-1,j}`, else the fair
coin. -/
def pullRule (P : Params) (T : ℕ) (M : Machine d Ω) (st : Regions d) (x : E d) (c : Bool) : Arm :=
  if x ∈ pts P T M (st.E true) then true
  else if x ∈ pts P T M (st.E false) then false
  else c

/-- Lines 5 and 16: the rounds `t ∈ 𝒯_k` with `A_t = a`, when epoch `k` is played with regions
`st`. -/
def sampleTimes (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) (st : Regions d) (ω : Ω)
    (a : Arm) : Finset ℕ :=
  (epTimes P d T k).filter (fun t => pullRule P T M st (M.X t ω) (M.coin t ω) = a)

/-- The bandwidth `H = N^{-1/(2β+d)}`, with `N` replaced by `max N 1` (the page's `N = 0` gives
`H = ∞`). -/
def Hbw (P : Params) (d N : ℕ) : ℝ :=
  ((max N 1 : ℕ) : ℝ) ^ (-(1 / (2 * P.β + d)))

/-- The bandwidth `H_{a,k}` of arm `a` after epoch `k` played with regions `st`. -/
def Hof (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) (st : Regions d) (ω : Ω) (a : Arm) : ℝ :=
  Hbw P d (sampleTimes P T M k st ω a).card

/-- The local polynomial estimate `η̂^LP(x; S_{a,k}, H_{a,k}, b(β))` at a point `x`. -/
def etaHatOf (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) (st : Regions d) (ω : Ω) (a : Arm)
    (x : E d) : ℝ :=
  etaLP (sampleTimes P T M k st ω a) (fun t => M.X t ω) (fun t => M.Y t ω a) x
    (Hof P T M k st ω a) (bOf P.β)

/-- The CATE estimate (7) at the centre of cell `c`. -/
def tauHatOf (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) (st : Regions d) (ω : Ω)
    (c : Idx d) : ℝ :=
  etaHatOf P T M k st ω true (center P d T c) - etaHatOf P T M k st ω false (center P d T c)

/-- The data support `((⋃_j ℰ_{a,j}) ∪ ℛ_k) ∩ 𝒳` of arm `a`. -/
def suppOf (P : Params) (T : ℕ) (M : Machine d Ω) (st : Regions d) (a : Arm) : Set (E d) :=
  pts P T M (st.E a ∪ st.R)

/-- The inestimable region (6): the cells of `ℛ_k ∩ G` at whose centre the data support of arm `a`
is not weakly `(c0/2^d, H_{a,k})`-regular. -/
def Dof (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) (st : Regions d) (ω : Ω) (a : Arm) :
    Finset (Idx d) :=
  (st.R ∩ Gset P T M).filter (fun c =>
    ¬ RegularVolumeAt (P.c0 / 2 ^ d) (Hof P T M k st ω a) (suppOf P T M st a) (center P d T c))

/-- The cells of `ℛ_k ∩ G ∩ 𝒟^C_{1,k} ∩ 𝒟^C_{-1,k}`, where the CATE is estimated. -/
def goodOf (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) (st : Regions d) (ω : Ω) :
    Finset (Idx d) :=
  (st.R ∩ Gset P T M).filter (fun c => c ∉ Dof P T M k st ω true ∧ c ∉ Dof P T M k st ω false)

/-- Line 10, (8) and (9): the regions for epoch `k + 1` from the regions and the samples of
epoch `k`. -/
def nextRegions (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) (st : Regions d) (ω : Ω) :
    Regions d :=
  let good := goodOf P T M k st ω
  ⟨fun a => st.E a ∪
      (good.filter (fun c => eps k < armSign a * tauHatOf P T M k st ω c) ∪
        Dof P T M k st ω (!a)),
    good.filter (fun c => |tauHatOf P T M k st ω c| ≤ eps k)⟩

/-- The regions at the start of epoch `k ≥ 1` on the sample path `ω` (index `0` is unused). -/
def regions (P : Params) (T : ℕ) (M : Machine d Ω) : ℕ → Ω → Regions d
  | 0, _ => initRegions P d T
  | 1, _ => initRegions P d T
  | k + 2, ω => nextRegions P T M (k + 1) (regions P T M (k + 1) ω) ω

/-- `⋃_{j=1}^k ℰ_{a,j}`, as cells. -/
def Ecum (P : Params) (T : ℕ) (M : Machine d Ω) (a : Arm) (k : ℕ) (ω : Ω) : Finset (Idx d) :=
  (regions P T M k ω).E a

/-- `ℛ_k`, as cells. -/
def Rk (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) (ω : Ω) : Finset (Idx d) :=
  (regions P T M k ω).R

/-- `N_{a,k} = |S_{a,k}|`. -/
def Nk (P : Params) (T : ℕ) (M : Machine d Ω) (a : Arm) (k : ℕ) (ω : Ω) : ℕ :=
  (sampleTimes P T M k (regions P T M k ω) ω a).card

/-- `H_{a,k} = N_{a,k}^{-1/(2β+d)}` (with `max N 1`). -/
def Hk (P : Params) (T : ℕ) (M : Machine d Ω) (a : Arm) (k : ℕ) (ω : Ω) : ℝ :=
  Hbw P d (Nk P T M a k ω)

/-- `𝒟_{a,k}`, as cells. -/
def Dk (P : Params) (T : ℕ) (M : Machine d Ω) (a : Arm) (k : ℕ) (ω : Ω) : Finset (Idx d) :=
  Dof P T M k (regions P T M k ω) ω a

/-- The cells of `ℛ_k ∩ 𝒟^C_{1,k} ∩ 𝒟^C_{-1,k}` (within `G`). -/
def goodK (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) (ω : Ω) : Finset (Idx d) :=
  goodOf P T M k (regions P T M k ω) ω

/-- `τ̂_k` at the centre of cell `c`, from the samples of epoch `k`. -/
def tauHat (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) (ω : Ω) (c : Idx d) : ℝ :=
  tauHatOf P T M k (regions P T M k ω) ω c

/-- The data support `((⋃_{j=1}^k ℰ_{a,j}) ∪ ℛ_k) ∩ 𝒳`. -/
def suppK (P : Params) (T : ℕ) (M : Machine d Ω) (a : Arm) (k : ℕ) (ω : Ω) : Set (E d) :=
  suppOf P T M (regions P T M k ω) a

/-- The arm `A_t` that Algorithm 1, run with horizon `T`, pulls at the 0-based round `t`. -/
def pull (P : Params) (T : ℕ) (M : Machine d Ω) (t : ℕ) (ω : Ω) : Arm :=
  pullRule P T M (regions P T M (epochOf P d T t) ω) (M.X t ω) (M.coin t ω)

/-- The regret (2) of Algorithm 1 with horizon `T`:
`R_T(π̂) = E[∑_{t=1}^T (Y_t(π*(X_t)) - Y_t(A_t))]`. -/
def regret (P : Params) (M : Machine d Ω) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T,
    ∫ ω, (M.Y t ω (piStar M (M.X t ω)) - M.Y t ω (pull P T M t ω)) ∂M.P

/-! ### The events of §4.1 -/

/-- `ℳ_k = {N_{1,k} ∧ N_{-1,k} ≥ (log(T δ^{-d}) / (C0 ϵ_k^2))^{(2β+d)/(2β)}}`. -/
def Mev (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) : Set Ω :=
  {ω | (Real.log (T * (delta P d T ^ d)⁻¹) / (C0 P d * eps k ^ 2)) ^
        ((2 * P.β + d) / (2 * P.β)) ≤
      ((min (Nk P T M true k ω) (Nk P T M false k ω) : ℕ) : ℝ)}

/-- `sup_{x ∈ ℛ_k ∩ 𝒟^C_{1,k} ∩ 𝒟^C_{-1,k}} |τ̂_k(x) - τ(x)|` (in `EReal`; `⊥` on the empty set),
with `τ̂_k(x)` the estimate at `g(x)` (11). -/
def supErr (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) (ω : Ω) : EReal :=
  ⨆ x ∈ pts P T M (goodK P T M k ω), ((|tauHat P T M k ω (gIdx P d T x) - tau M x| : ℝ) : EReal)

/-- `𝒢_k = {sup_{x ∈ ℛ_k ∩ 𝒟^C_{1,k} ∩ 𝒟^C_{-1,k}} |τ̂_k(x) - τ(x)| ≤ ϵ_k}`. -/
def Gev (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) : Set Ω :=
  {ω | supErr P T M k ω ≤ ((eps k : ℝ) : EReal)}

/-- `Ḡ_k = ⋂_{1 ≤ j ≤ k} 𝒢_j` (the whole space for `k = 0`). -/
def Gbar (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) : Set Ω :=
  {ω | ∀ j, 1 ≤ j → j ≤ k → ω ∈ Gev P T M j}

/-- `M̄_k = ⋂_{1 ≤ j ≤ k} ℳ_j` (the whole space for `k = 0`). -/
def Mbar (P : Params) (T : ℕ) (M : Machine d Ω) (k : ℕ) : Set Ω :=
  {ω | ∀ j, 1 ≤ j → j ≤ k → ω ∈ Mev P T M j}

end SmoothBandit.Regret


