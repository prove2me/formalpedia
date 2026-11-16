-- Prove2me | Definitions.Def_HarmonicRanking_Main_Supplement_GridGames
-- name    : HarmonicRanking_Main_Supplement_GridGames
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:45:26.505407+00:00
-- url     : https://prove2.me/theorems/a32979f4-e6ac-4b2c-a378-4e6e7d1ff492
-- title:
--   Whole-cell game $\gamma_{UW,m}$, two-path game $V_m$, reflection and $P^\perp_m$
-- statement:
--   Fix a grid size $m\ge 1$ and write $[m]=\{1,\dots,m\}$. This file defines the finite-grid objects of Appendix A (pp. 28–29).
--
--   1. $\mathfrak G_{\mathrm{comp},m}$ is the set of tables $\hat g=(\hat g_{ij})_{i,j\in[m]}\in[0,1]^{m\times m}$ that are nondecreasing in $i$, nonincreasing in $j$ and satisfy $\hat g_{ij}+\hat g_{ji}=1$, with the appended boundary value $\hat g_{i,m+1}:=0$.
--   2. For threshold vectors $a,b\in\{0,\dots,m\}^m$ let $U_{ij}=\mathbf 1\{j>a_i\}$, $\tilde V_{ij}=\mathbf 1\{i>b_j\}$ and $S_{ij}=(1-U_{ij})(1-\tilde V_{ij})$; $T_m$ is the set of pairs with $U_{ij}\tilde V_{ij}=0$ for all $i,j$, and $T_{UW,m}$ adds that $a$ and $b$ are nondecreasing. Equation (43) is
--   $$\hat\Gamma_m(\hat g,a,b)=\frac1{m^2}\sum_{i,j=1}^m\Big[S_{ij}+(U_{ij}+\tilde V_{ij})\big(\hat g_{i,a_i+1}+\hat g_{j,b_j+1}\big)\Big],$$
--   and (44) is $\gamma_{UW,m}=\max_{\hat g\in\mathfrak G_{\mathrm{comp},m}}\min_{(a,b)\in T_{UW,m}}\hat\Gamma_m(\hat g,a,b)$.
--   3. $B_m$ is the set of paths $a=(a_0,\dots,a_m)\in\{0,\dots,m\}^{m+1}$ with $a_0\le\dots\le a_m=m$. For $j\in\{0,\dots,m-1\}$, $a^-_j=\min\{k\in\{0,\dots,m\}:a_k>j\}$ and $\ell_a(i)=1-a^-_{i-1}/m$.
--   4. $K_m$ is the set of tables $g(i,r)$, $i,r\in[m]$, with implicit boundary $g(i,0):=0$, such that $g(i,1)\ge0$, $g(i,r)\le g(i,r+1)$ and $g(i,r)+g(r,i)=1$. Equation (45) is
--   $$\Phi_g(a,b)=1+\frac1{m^2}\sum_{i=1}^m\Big[a_{i-1}\big(g(i,a_{i-1})-1\big)+b_{i-1}\big(g(i,b_{i-1})-1\big)\Big]+\frac1m\sum_{i=1}^m\Big[\ell_b(i)\,g(i,a_{i-1})+\ell_a(i)\,g(i,b_{i-1})\Big],$$
--   and (46) is $V_m=\max_{g\in K_m}\min_{a,b\in B_m}\Phi_g(a,b)$.
--   5. The reflection of Lemma A.1 is $(R\hat g)(k,r)=\hat g_{m+1-k,m+1-r}$, $(R\hat g)(k,0)=0$, and $P^\perp_m=\{(c,d)\in B_m^2: X_{kr}Y_{rk}=0\ \forall k,r\in[m]\}$ with $X_{kr}=\mathbf 1\{c_{k-1}\ge r\}$, $Y_{kr}=\mathbf 1\{d_{k-1}\ge r\}$.
--
--   These are the two max–min games whose values Theorem 7.1 identifies with the Mahdian–Yan linear program.
--
--   **Formalization Note** Indices are zero-based: `Fin m` index `i` is the paper's `i+1`, and a path in $B_m$ is a map `Fin (m+1) → Fin (m+1)`. The threshold domain $T_m$ reuses the published `Thresholds`, `discreteU`, `discreteV`, `discreteAdmissible`. The boundary values $\hat g_{i,m+1}=0$ and $g(i,0)=0$ are supplied by the accessors `ghatNext` and `gAt`. All maxima and minima are taken as suprema and infima in `EReal`, so no junk value arises; the inner minima range over finite nonempty sets. The infimum defining $a^-_j$ is a natural-number infimum of a set that is nonempty for every $a\in B_m$ and $j<m$.
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF pp. 16 (eqs. (25)–(26)), 28–29 (eqs. (43)–(46), Lemma A.1)

import Definitions.Def_HarmonicRanking_Main_StepProfile

set_option autoImplicit false
noncomputable section

namespace HarmonicRanking.Main.Supplement

/-! Throughout, `Fin m` index `i` stands for the paper's one-based index `i + 1`. -/

/-- `𝔊comp,m` (App. A, p. 28): tables `ĝ ∈ [0,1]^{m×m}`, nondecreasing in the row index,
nonincreasing in the column index, with `ĝ_ij + ĝ_ji = 1`. -/
def IsCompTable {m : ℕ} (gh : Fin m → Fin m → ℝ) : Prop :=
  (∀ i j, 0 ≤ gh i j ∧ gh i j ≤ 1) ∧
  (∀ j, Monotone (fun i => gh i j)) ∧
  (∀ i, Antitone (gh i)) ∧
  (∀ i j, gh i j + gh j i = 1)

/-- `ĝ_{i,k+1}` for `k ∈ {0,…,m}`, with the appended boundary value `ĝ_{i,m+1} := 0`
(zero-based: column `k` of row `i`, and `0` when `k = m`). -/
def ghatNext {m : ℕ} (gh : Fin m → Fin m → ℝ) (i : Fin m) (k : ℕ) : ℝ :=
  if hk : k < m then gh i ⟨k, hk⟩ else 0

/-- `T_UW,m`: admissible threshold pairs `(a,b) ∈ T_m` (reusing the published `T_m`) with
both `a` and `b` nondecreasing. -/
def IsTUW {m : ℕ} (c : Thresholds m) : Prop :=
  discreteAdmissible c ∧ Monotone c.1 ∧ Monotone c.2

/-- Equation (43): `Γ̂_m(ĝ,a,b) = m⁻² Σ_{i,j} [S_ij + (U_ij + Ṽ_ij)(ĝ_{i,a_i+1} + ĝ_{j,b_j+1})]`
with `S_ij = (1-U_ij)(1-Ṽ_ij)`. -/
def GammaHat {m : ℕ} (gh : Fin m → Fin m → ℝ) (c : Thresholds m) : ℝ :=
  (∑ i, ∑ j,
    ((1 - discreteU c i j) * (1 - discreteV c i j) +
      (discreteU c i j + discreteV c i j) *
        (ghatNext gh i (c.1 i).val + ghatNext gh j (c.2 j).val))) / (m : ℝ) ^ 2

/-- Inner value `min_{(a,b) ∈ T_UW,m} Γ̂_m(ĝ,a,b)` (a minimum over a finite set). -/
def wholeCellMin {m : ℕ} (gh : Fin m → Fin m → ℝ) : EReal :=
  ⨅ (c : Thresholds m) (_ : IsTUW c), ((GammaHat gh c : ℝ) : EReal)

/-- Equation (44): `γ_UW,m = max_{ĝ ∈ 𝔊comp,m} min_{(a,b) ∈ T_UW,m} Γ̂_m(ĝ,a,b)`. -/
def gammaUW (m : ℕ) : EReal :=
  ⨆ (gh : Fin m → Fin m → ℝ) (_ : IsCompTable gh), wholeCellMin gh

/-- `B_m`: paths `a = (a_0,…,a_m) ∈ {0,…,m}^{m+1}` with `a_0 ≤ ⋯ ≤ a_m = m`. -/
def IsPath {m : ℕ} (a : Fin (m + 1) → Fin (m + 1)) : Prop :=
  Monotone a ∧ a (Fin.last m) = Fin.last m

/-- `a⁻_j = min {k ∈ {0,…,m} : a_k > j}`. -/
def pathInv {m : ℕ} (a : Fin (m + 1) → Fin (m + 1)) (j : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ hk : k < m + 1, j < (a ⟨k, hk⟩).val}

/-- `ℓ_a(i) = 1 - a⁻_{i-1}/m` (zero-based `i` stands for the paper's `i+1`). -/
def ell {m : ℕ} (a : Fin (m + 1) → Fin (m + 1)) (i : Fin m) : ℝ :=
  1 - (pathInv a i.val : ℝ) / (m : ℝ)

/-- `K_m`: tables `g(i,r)`, `i,r ∈ [m]` (implicit `g(i,0) = 0`) with `g(i,1) ≥ 0`,
`g(i,r) ≤ g(i,r+1)` and `g(i,r) + g(r,i) = 1`. -/
def IsKTable {m : ℕ} (g : Fin m → Fin m → ℝ) : Prop :=
  (∀ i : Fin m, 0 ≤ g i ⟨0, Fin.pos i⟩) ∧
  (∀ i, Monotone (g i)) ∧
  (∀ i r, g i r + g r i = 1)

/-- `g(i,k)` for `k ∈ {0,…,m}`, with the implicit boundary `g(i,0) := 0`
(zero-based: entry `k-1` of row `i` when `1 ≤ k ≤ m`). -/
def gAt {m : ℕ} (g : Fin m → Fin m → ℝ) (i : Fin m) (k : ℕ) : ℝ :=
  if hk : 0 < k ∧ k ≤ m then g i ⟨k - 1, by omega⟩ else 0

/-- Equation (45):
`Φ_g(a,b) = 1 + m⁻² Σ_i [a_{i-1}(g(i,a_{i-1}) - 1) + b_{i-1}(g(i,b_{i-1}) - 1)]
  + m⁻¹ Σ_i [ℓ_b(i) g(i,a_{i-1}) + ℓ_a(i) g(i,b_{i-1})]`. -/
def Phi {m : ℕ} (g : Fin m → Fin m → ℝ) (a b : Fin (m + 1) → Fin (m + 1)) : ℝ :=
  1 + (∑ i : Fin m,
        (((a i.castSucc).val : ℝ) * (gAt g i (a i.castSucc).val - 1) +
          ((b i.castSucc).val : ℝ) * (gAt g i (b i.castSucc).val - 1))) / (m : ℝ) ^ 2
    + (∑ i : Fin m,
        (ell b i * gAt g i (a i.castSucc).val + ell a i * gAt g i (b i.castSucc).val)) / (m : ℝ)

/-- Inner value `min_{a,b ∈ B_m} Φ_g(a,b)` (a minimum over a finite set). -/
def twoPathMin {m : ℕ} (g : Fin m → Fin m → ℝ) : EReal :=
  ⨅ (a : Fin (m + 1) → Fin (m + 1)) (_ : IsPath a) (b : Fin (m + 1) → Fin (m + 1))
    (_ : IsPath b), ((Phi g a b : ℝ) : EReal)

/-- Equation (46): `V_m = max_{g ∈ K_m} min_{a,b ∈ B_m} Φ_g(a,b)`. -/
def Vval (m : ℕ) : EReal :=
  ⨆ (g : Fin m → Fin m → ℝ) (_ : IsKTable g), twoPathMin g

/-- The reflection `(Rĝ)(k,r) = ĝ_{m+1-k, m+1-r}` (Lemma A.1); the boundary `(Rĝ)(k,0) = 0`
is the implicit boundary of `gAt`. -/
def reflect {m : ℕ} (gh : Fin m → Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fun k r => gh (Fin.rev k) (Fin.rev r)

/-- `P⊥_m`: pairs `(c,d) ∈ B_m²` with `X_kr Y_rk = 0` for all `k,r ∈ [m]`, where
`X_kr = 1{c_{k-1} ≥ r}` and `Y_kr = 1{d_{k-1} ≥ r}`. -/
def IsTransposeFree {m : ℕ} (c d : Fin (m + 1) → Fin (m + 1)) : Prop :=
  IsPath c ∧ IsPath d ∧
    ∀ k r : Fin m, ¬ (r.val + 1 ≤ (c k.castSucc).val ∧ k.val + 1 ≤ (d r.castSucc).val)

/-- `min_{(c,d) ∈ P⊥_m} Φ_g(c,d)`. -/
def transposeFreeMin {m : ℕ} (g : Fin m → Fin m → ℝ) : EReal :=
  ⨅ (c : Fin (m + 1) → Fin (m + 1)) (d : Fin (m + 1) → Fin (m + 1))
    (_ : IsTransposeFree c d), ((Phi g c d : ℝ) : EReal)

end HarmonicRanking.Main.Supplement


