-- Prove2me | Definitions.Def_LogSupermodularBIS_Main_Interaction
-- name    : LogSupermodularBIS_Main_Interaction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:06.408982+00:00
-- url     : https://prove2.me/theorems/5ba6c37e-c78d-4966-8f6e-4d088d737faf
-- title:
--   Hoeffding decomposition, the parameters (4.1), bin scores, the penalized objective (4.4), Walsh characters and the witness assumption (4.2)
-- statement:
--   For a function $\varphi$ of $k$ independent uniform inputs, $E_j$ integrates out coordinate $j$, and the **Hoeffding component** on $S\subseteq[k]$ is
--   $$\varphi_S=\prod_{j\in S}(I-E_j)\prod_{j\notin S}E_j\,\varphi,$$
--   computed as $\sum_{T\subseteq S}(-1)^{|S\setminus T|}E_{[k]\setminus T}\varphi$. The degree-$D$ tail is $\Pi_{>D}\varphi=\sum_{|S|>D}\varphi_S$, and $\|\varphi\|_2=(E\varphi(U)^2)^{1/2}$ is the unsquared $L^2$ norm. Interaction degree counts input coordinates.
--
--   For $d\ge2$, $B\ge1$ and $\Lambda=2B$, the parameters (4.1) are $s=\min\{j\ge0:2^j\ge64d\}$, $m=4^s$, $A_0=\log m+1$, $G_0=A_0+2\Lambda$ and $\kappa=\min\{j\ge0:2^j\ge64dG_0\}$. The bins are $Y_i=\lfloor mU_i\rfloor\in\{0,\dots,m-1\}$ and the bin scores are $\bar a_j=m[H(j/m)-H((j+1)/m)]$.
--
--   A **candidate** is a vector $u=(u_1,\dots,u_k)$ whose $i$th row is a real-valued function of $Y_1,\dots,Y_i$. With $\psi_t(y)=t\min\{y,1\}$ for $t\ge0$ and $t\max\{y,0\}$ for $t<0$, $\mathrm{clip}(y)=\min\{1,\max\{0,y\}\}$ and $\mathrm{dist}(y,[0,1])=|y-\mathrm{clip}(y)|$, the **penalized objective** is
--   $$J_v(u)=\sum_{i=1}^kE\,\psi_{\bar a_{Y_i}}(u_i(Y))+E\,\Phi^L(u(Y))-\Lambda\sum_{i=1}^kE\,\mathrm{dist}(u_i(Y),[0,1]).\tag{4.4}$$
--   Identifying a bin with its $2s$ binary digits, $\chi_\beta(y)=(-1)^{\beta\cdot y}$ and $\chi_\beta(Y)=\prod_j\chi_{\beta_j}(Y_j)$; the support of $\beta$ is $\{j:\beta_j\ne0\}$, and $F_i$ is the set of $\beta$ whose support lies in $\{1,\dots,i\}$ and has at most $D$ elements.
--
--   The **witness assumption** (4.2) at a node $v$ with $k=d-|v|\ge1$ free coordinates asks for a guide $g$ on these $k$ inputs with
--   $$\log Z_{\Phi_v}-\mathcal P(g)\le b^*,\qquad\|\Pi_{>D}g_i\|_2\le\frac1{128dG_0}\quad(1\le i\le k),$$
--   where $d$ and $B$ are the original parameters.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), pp. 19–23 (PDF 20–24), §4.1–4.2, (4.1), (4.2), (4.4), Walsh characters

import Mathlib
import Definitions.Def_LogSupermodularBIS_Main_Variational

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-!
# Interaction degree and the finite search space (§4, pp. 19–24)

Functions of `k` independent uniform inputs are maps `φ : (Fin k → ℝ) → ℝ` integrated against
`unifCube k`. Bins are `Y_i = ⌊m U_i⌋ ∈ {0, …, m−1}`, represented as `Fin m`.
-/

/-- `E_A φ`: integrate out the coordinates in `A` (keep the others). -/
noncomputable def integrateOut {k : ℕ} (A : Finset (Fin k)) (φ : (Fin k → ℝ) → ℝ)
    (u : Fin k → ℝ) : ℝ :=
  ∫ t, φ (fun j => if j ∈ A then t j else u j) ∂unifCube k

/-- The Hoeffding component `φ_S = Π_{j∈S}(I − E_j) Π_{j∉S} E_j φ`, expanded as
`Σ_{T ⊆ S} (−1)^{|S∖T|} E_{[k]∖T} φ`. -/
noncomputable def hoeffdingComponent {k : ℕ} (S : Finset (Fin k)) (φ : (Fin k → ℝ) → ℝ)
    (u : Fin k → ℝ) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * integrateOut Tᶜ φ u

/-- The degree-`D` tail `Π_{>D} φ = Σ_{|S|>D} φ_S`. -/
noncomputable def highDegreeTail {k : ℕ} (D : ℕ) (φ : (Fin k → ℝ) → ℝ) (u : Fin k → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun S => D < S.card),
    hoeffdingComponent S φ u

/-- The unsquared `L²` norm `‖φ‖₂ = (E φ(U)²)^{1/2}` under independent uniform inputs. -/
noncomputable def l2Norm {k : ℕ} (φ : (Fin k → ℝ) → ℝ) : ℝ :=
  Real.sqrt (∫ u, φ u ^ 2 ∂unifCube k)

/-- `s = min{j ≥ 0 : 2^j ≥ 64 d}` of (4.1). -/
def paramS (d : ℕ) : ℕ := Nat.find (⟨64 * d, (Nat.lt_two_pow_self).le⟩ : ∃ j, 64 * d ≤ 2 ^ j)

/-- The number of bins `m = 4^s` of (4.1). -/
def numBins (d : ℕ) : ℕ := 4 ^ paramS d

/-- `A_0 = log m + 1`. -/
noncomputable def paramA0 (d : ℕ) : ℝ := Real.log (numBins d) + 1

/-- `Λ = 2B`. -/
def paramLambda (B : ℕ) : ℝ := 2 * B

/-- `G_0 = A_0 + 2Λ`. -/
noncomputable def paramG0 (d B : ℕ) : ℝ := paramA0 d + 2 * paramLambda B

/-- `κ = min{j ≥ 0 : 2^j ≥ 64 d G_0}` of (4.1). -/
noncomputable def paramKappa (d B : ℕ) : ℕ :=
  Nat.find ((pow_unbounded_of_one_lt (64 * d * paramG0 d B) (by norm_num : (1 : ℝ) < 2)).imp
    fun _ h => h.le : ∃ j : ℕ, 64 * d * paramG0 d B ≤ (2 : ℝ) ^ j)

/-- The binary entropy `H`. -/
noncomputable def H (p : ℝ) : ℝ := Real.binEntropy p

/-- The bin score `ā_j = m [H(j/m) − H((j+1)/m)]`. -/
noncomputable def binScore (m : ℕ) (j : Fin m) : ℝ :=
  m * (H (j / m) - H ((j + 1 : ℝ) / m))

/-- The bin `⌊m u⌋` of an input `u ∈ (0,1)` (as a natural number). -/
noncomputable def binOf (m : ℕ) (u : ℝ) : ℕ := Int.toNat ⌊(m : ℝ) * u⌋

/-- The bin score `ā_{⌊m u⌋}` of the bin containing the input `u ∈ (0,1)` (`0` outside). -/
noncomputable def binScoreAt (m : ℕ) (u : ℝ) : ℝ :=
  if h : binOf m u < m then binScore m ⟨binOf m u, h⟩ else 0

/-- `ψ_t(y) = t min{y, 1}` if `t ≥ 0`, `t max{y, 0}` if `t < 0`. -/
noncomputable def psi (t y : ℝ) : ℝ := if 0 ≤ t then t * min y 1 else t * max y 0

/-- `clip(y) = min{1, max{0, y}}`. -/
noncomputable def clip (y : ℝ) : ℝ := min 1 (max 0 y)

/-- `dist(y, [0,1]) = |y − clip(y)|`. -/
noncomputable def distUnit (y : ℝ) : ℝ := |y - clip y|

/-- A candidate (§4.2): `u = (u_1, …, u_k)` whose `i`th row is a real-valued function of the
bins `Y_1, …, Y_i`. -/
def IsCandidate (k m : ℕ) (u : Fin k → (Fin k → Fin m) → ℝ) : Prop :=
  ∀ i : Fin k, ∀ y y' : Fin k → Fin m, (∀ j : Fin k, j ≤ i → y j = y' j) → u i y = u i y'

/-- The set of candidates. -/
def candidates (k m : ℕ) : Set (Fin k → (Fin k → Fin m) → ℝ) := {u | IsCandidate k m u}

/-- The expectation of a function of independent uniform bins. -/
noncomputable def binExpect {k m : ℕ} (φ : (Fin k → Fin m) → ℝ) : ℝ :=
  (∑ y, φ y) / (m : ℝ) ^ k

/-- The penalized objective (4.4) for a residual potential `Φ` on `k` coordinates, with `m` bins
and penalty `Λ`:
`J(u) = Σ_i E ψ_{ā_{Y_i}}(u_i(Y)) + E Φ^L(u(Y)) − Λ Σ_i E dist(u_i(Y), [0,1])`. -/
noncomputable def penalizedObjective {k : ℕ} (m : ℕ) (Λ : ℝ) (Φ : (Fin k → Bool) → ℝ)
    (u : Fin k → (Fin k → Fin m) → ℝ) : ℝ :=
  (∑ i : Fin k, binExpect fun y => psi (binScore m (y i)) (u i y)) +
    binExpect (fun y => lovaszExt Φ (fun i => u i y)) -
    Λ * ∑ i : Fin k, binExpect fun y => distUnit (u i y)

/-- The one-input Walsh character `χ_β(y) = (−1)^{β·y}` on bins `y ∈ {0, …, m−1}`, `m = 4^s`,
identified with their `2s` binary digits. -/
noncomputable def walsh1 (s : ℕ) (β y : ℕ) : ℝ :=
  ∏ r : Fin (2 * s), if β.testBit r && y.testBit r then (-1 : ℝ) else 1

/-- The Walsh character `χ_β(Y) = Π_j χ_{β_j}(Y_j)`. -/
noncomputable def walsh {k m : ℕ} (s : ℕ) (β : Fin k → Fin m) (y : Fin k → Fin m) : ℝ :=
  ∏ j : Fin k, walsh1 s (β j) (y j)

/-- The support `{j : β_j ≠ 0}` of a multi-index. -/
def walshSupport {k m : ℕ} (β : Fin k → Fin m) : Finset (Fin k) :=
  Finset.univ.filter fun j => (β j : ℕ) ≠ 0

/-- `F_i`: the multi-indices whose support lies in `{1, …, i}` and has at most `D` elements. -/
def walshRowIndices {k m : ℕ} (D : ℕ) (i : Fin k) : Finset (Fin k → Fin m) :=
  Finset.univ.filter fun β => (∀ j ∈ walshSupport β, j ≤ i) ∧ (walshSupport β).card ≤ D

/-- The residual at an internal node `v` of `W` as a potential on the `k = d − |v|` free inputs:
the normalized potential `Φ_v`. The witness assumption (4.2) at `v`: some guide `g` on these
`k` inputs has `log Z_{Φ_v} − P(g) ≤ b*` and `‖Π_{>D} g_i‖₂ ≤ 1/(128 d G_0)` for every row. -/
def WitnessAt {d : ℕ} (W : (Fin d → Bool) → ℚ) (B D : ℕ) (bstar : ℝ) (v : List Bool) : Prop :=
  ∃ g : (Fin (d - v.length) → ℝ) → Fin (d - v.length) → ℝ,
    IsGuide (d - v.length) g ∧
    Real.log (potentialPartition (residualPotential W v)) -
        variationalObjective (residualPotential W v) g ≤ bstar ∧
    ∀ i, l2Norm (highDegreeTail D fun u => g u i) ≤ 1 / (128 * d * paramG0 d B)

end LogSupermodularBIS.Main


