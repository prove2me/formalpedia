-- Prove2me | Definitions.Def_NetUnrelDesign_Main_Prepared
-- name    : NetUnrelDesign_Main_Prepared
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:10:36.777232+00:00
-- url     : https://prove2.me/theorems/69cb2a70-03e8-419c-95e5-eb09f5d9940c
-- title:
--   Rates, pivotal quantities, preparation data, the branch test, the box, the Burg center and output decoders
-- statement:
--   - **Rates** (1.3): $h=\log(2m)$, $L=\log(2m(k+1)/\varepsilon)$, $P(s)=(km^2+m^3\log(2m))\log(2m+\log(1/s))$.
--   - **Pivotal quantities.** $\Pr(Y\ge r)$ for $Y\sim\mathrm{Bin}(n,p)$. $d_e=\mathbb E\,b_e(\Pi)$. $T_x(\pi)=\sum_e x_eb_e(\pi)$. $S=(\log(2/\eta)+C\log^2(2n))/\log 2$.
--   - **Preparation** (§5): $B=1+\log M$; $Q_0=X\cap\{\lambda\ge\lambda_0-B\}$; $\Lambda=\max_X\lambda$. The second output of Lemma 5.1 with threshold $\eta$ and constant $\gamma$ consists of $x^0\in X$ and $\lambda_0=\lambda(x^0)$, satisfying:
--     - (5.2): $\lambda_0\ge\Lambda-1$;
--     - (5.3): $\underline u:=e^{-(\lambda_0+1)}\le u^*$, $\underline u>\eta/(eM)$ and $u(x^0)\le eMu^*$;
--     - a nonsingular $J$ with center $\bar x$ satisfying (5.6): $\bar x+JB_2\subseteq Q_0\subseteq\bar x+\gamma m^2JB_2$.
--   - **Branch test** (5.8): $\lambda_0-1-\log M\ge6\log n+2\log(4096/\varepsilon)$.
--   - **Box.** The floor is $\varepsilon^2/(e^2 2^{30}m^8)$ (5.9) and the box width $D=\log(e^22^{38}m^9/\varepsilon^3)$ (5.11). $X_W=X\cap[0,W]^m$.
--   - **Constants (4.3).** $a=\varepsilon/16$, $\ell=\lambda_0-B$, $\alpha=1+(2\log n+\log(128/a))/(\ell-2\log n)$, $\sigma=3/2-\alpha$, $\tau=a/64$.
--   - **Burg center** (§3.3, (D.3)). Put $U_j=\min\{W,\min_ib_i/A_{ij}\}$, $K=\{z:(U_jz_j)_j\in X_W\}$ and $\psi(z)=-\sum_j\log z_j$. A Burg center is $c\in K$ with $c>0$, such that $c_j\ge\frac34c^*_j$ for every minimizer $c^*$ of $\psi$ on the positive part of $K$, and $\sum_jz_j/c_j\le4m/3$ for all $z\in K$.
--   - **Candidate domain** of §6: $Q_0$ when (5.8) holds, $X_D$ otherwise.
--   - **Output decoders** for Lemma 4.2: the listed cuts and the frozen sum $h(y)=\sum_{C\in H}e^{-w_y(C)}$. For Lemma H.1: the selected point, given by its address, and the estimate $U$, equal to $+\infty$ on fallback.
--
--   **Formalization Note.** $\Lambda$ is written `sSup` ($\lambda$ is continuous and $X$ is compact and nonempty, so it is attained). $\min_i b_i/A_{ij}$ is an `iInf` over the $k\ge1$ rows. $\psi$'s minimizers are taken over $K\cap\{z>0\}$, where Lean's $\log$ is the true logarithm.
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), (1.3) (p. 2, PDF 3); Lemma 2.2 (p. 8, PDF 9); §3.1 (p. 9, PDF 10); §3.3 (p. 11, PDF 12) and App. D.3 (p. 35, PDF 36); §4 (p. 12–13, PDF 13–14: (4.3)); §5.1–5.3 (p. 15–17, PDF 16–18: (5.2), (5.3), (5.6), (5.8), (5.9), (5.11)); §6 (p. 18, PDF 19)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelDesign_Main_Interfaces

open scoped BigOperators Classical

noncomputable section

namespace NetUnrelDesign.Main

/-!
# Rates, pivotal quantities, preparation data, the branch test, the box and the Burg center

Mu-Xia Sun, *Fast Approximation Algorithms for Minimizing Network Unreliability* (2026),
doi:10.5281/zenodo.23914978: (1.3) (p. 2, PDF 3); Lemma 2.2 (p. 8, PDF 9); §3.1 (p. 9, PDF 10:
`d_e`, `T_x`, `S`); §3.3 and App. D.3 (p. 11, PDF 12; p. 35, PDF 36: the Burg center, (D.3));
§4 (p. 12–13, PDF 13–14: `a`, `B`, `ℓ`, (4.3)); §5.1–5.3 (p. 15–17, PDF 16–18: (5.2), (5.3),
`Q₀`, (5.6), (5.8), (5.9), (5.11)); §6 (p. 18, PDF 19: the candidate domain `D`).

* `logTwoM m = h = log(2m)`, `Lrate m k ε = L = log(2m(k+1)/ε)`,
  `prepCost m k s = P(s) = (km² + m³ log(2m)) log(2m + log(1/s))` (1.3).
* `binomTail n p r = Pr(Y ≥ r)` for `Y ~ Bin(n, p)`.
* `pivotalMean ends q e = d_e = E b_e(Π)`; `pivotalInvestment ends x π = T_x(π) = Σ_e x_e b_e(π)`;
  `tailScale n η C = S = (log(2/η) + C log²(2n))/log 2`.
* `cutSlack n = B = 1 + log M`; `regionQ0 I λ₀ = Q₀ = X ∩ {λ ≥ λ₀ − B}`;
  `maxLam I = Λ = max_X λ` (written `sSup`; `λ` is continuous and `X` compact and nonempty).
* `PrepData I η γ x⁰ λ₀ J x̄`: the second output of Lemma 5.1 (p. 16, PDF 17) — `x⁰ ∈ X`,
  `λ₀ = λ(x⁰)`, (5.2) `λ₀ ≥ Λ − 1`, (5.3) `u̲ := e^{−(λ₀+1)} ≤ u*`, `u̲ > η/(eM)`, `u(x⁰) ≤ eMu*`,
  `J` nonsingular and (5.6) `x̄ + JB₂ ⊆ Q₀ ⊆ x̄ + γm²JB₂`.
* `BranchHolds n ε λ₀` is the test (5.8): `λ₀ − 1 − log M ≥ 6 log n + 2 log(4096/ε)`.
* `riskFloor m ε = ε²/(e²·2³⁰·m⁸)` (5.9); `boxWidth m ε = log(e²·2³⁸·m⁹/ε³)` (5.11);
  `boxSet I W = X_W = X ∩ [0, W]^m`.
* (4.3): `aPar ε = a = ε/16`, `ellPar n λ₀ = ℓ = λ₀ − B`,
  `alphaPar n ε λ₀ = 1 + (2 log n + log(128/a))/(ℓ − 2 log n)`, `sigmaPar = 3/2 − α`,
  `tauPar ε = a/64`.
* The Burg center (§3.3, App. D.3): `U_j = min{W, min_i b_i/A_ij}`, the normalized set
  `K = {z : (U_j z_j)_j ∈ X_W}`, `ψ(z) = −Σ_j log z_j`; `BurgCenter I W c` says `c ∈ K`, `c > 0`,
  `c_j ≥ 3c*_j/4` for every minimizer `c*` of `ψ` over the positive part of `K`, and
  `Σ_j z_j/c_j ≤ 4m/3` for every `z ∈ K` ((D.3)).
* `candDomain I ε λ₀` is the candidate domain `D` of §6: `Q₀` when (5.8) holds, `X_D` with
  `D = boxWidth m ε` when it fails.
* Output decoders: `outCutList` and `frozenSum` (Lemma 4.2), `selectedPoint` and `selectedU`
  (Lemma H.1); see their docstrings for the cells.
-/

/-- `h = log(2m)`. -/
def logTwoM (m : ℕ) : ℝ := Real.log (2 * m)

/-- `L = log(2m(k+1)/ε)`. -/
def Lrate (m k : ℕ) (ε : ℝ) : ℝ := Real.log (2 * m * (k + 1) / ε)

/-- `P(s) = (km² + m³ log(2m)) log(2m + log(1/s))`. -/
def prepCost (m k : ℕ) (s : ℝ) : ℝ :=
  ((k : ℝ) * m ^ 2 + (m : ℝ) ^ 3 * Real.log (2 * m)) * Real.log (2 * m + Real.log (1 / s))

/-- `Pr(Y ≥ r)` for `Y ~ Bin(n, p)`. -/
def binomTail (n : ℕ) (p : ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc r n, (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

/-- `d_e = E b_e(Π)` under failure probabilities `q`. -/
def pivotalMean {n m : ℕ} (ends : Ends n m) (q : Fin m → ℝ) (e : Fin m) : ℝ :=
  expect q fun F => pivotal ends (partitionOf ends F) e

/-- `T_x(π) = Σ_e x_e b_e(π)`. -/
def pivotalInvestment {n m : ℕ} (ends : Ends n m) (x : Fin m → ℝ) (π : Setoid (Fin n)) : ℝ :=
  ∑ e, x e * pivotal ends π e

/-- `S = (log(2/η) + C log²(2n))/log 2`. -/
def tailScale (n : ℕ) (η C : ℝ) : ℝ := (Real.log (2 / η) + C * Real.log (2 * n) ^ 2) / Real.log 2

/-- `B = 1 + log M`. -/
def cutSlack (n : ℕ) : ℝ := 1 + Real.log (pairCount n)

/-- `Q₀ = X ∩ {λ ≥ λ₀ − B}`. -/
def regionQ0 {n m k : ℕ} (I : Instance n m k) (lam0 : ℝ) : Set (Fin m → ℝ) :=
  {x | x ∈ I.feasible ∧ lam0 - cutSlack n ≤ I.lam x}

/-- `Λ = max_X λ`. -/
def maxLam {n m k : ℕ} (I : Instance n m k) : ℝ := sSup (I.lam '' I.feasible)

/-- The second output of Lemma 5.1 with threshold `η` and constant `γ`: (5.2), (5.3), (5.6). -/
def PrepData {n m k : ℕ} (I : Instance n m k) (η γ : ℝ) (x0 : Fin m → ℝ) (lam0 : ℝ)
    (J : Matrix (Fin m) (Fin m) ℝ) (xbar : Fin m → ℝ) : Prop :=
  x0 ∈ I.feasible ∧ lam0 = I.lam x0 ∧
  maxLam I - 1 ≤ lam0 ∧
  Real.exp (-(lam0 + 1)) ≤ I.uStar ∧
  η / (Real.exp 1 * pairCount n) < Real.exp (-(lam0 + 1)) ∧
  I.u x0 ≤ Real.exp 1 * pairCount n * I.uStar ∧
  J.det ≠ 0 ∧
  ellipsoid xbar J 1 ⊆ regionQ0 I lam0 ∧
  regionQ0 I lam0 ⊆ ellipsoid xbar J (γ * (m : ℝ) ^ 2)

/-- The branch test (5.8): `λ₀ − 1 − log M ≥ 6 log n + 2 log(4096/ε)`. -/
def BranchHolds (n : ℕ) (ε lam0 : ℝ) : Prop :=
  6 * Real.log n + 2 * Real.log (4096 / ε) ≤ lam0 - 1 - Real.log (pairCount n)

/-- The risk floor `ε²/(e²·2³⁰·m⁸)` of (5.9). -/
def riskFloor (m : ℕ) (ε : ℝ) : ℝ := ε ^ 2 / (Real.exp 2 * 2 ^ 30 * (m : ℝ) ^ 8)

/-- The box width `D = log(e²·2³⁸·m⁹/ε³)` of (5.11). -/
def boxWidth (m : ℕ) (ε : ℝ) : ℝ := Real.log (Real.exp 2 * 2 ^ 38 * (m : ℝ) ^ 9 / ε ^ 3)

/-- `X_W = X ∩ [0, W]^m`. -/
def boxSet {n m k : ℕ} (I : Instance n m k) (W : ℝ) : Set (Fin m → ℝ) :=
  {x | x ∈ I.feasible ∧ ∀ e, x e ≤ W}

/-- `a = ε/16`. -/
def aPar (ε : ℝ) : ℝ := ε / 16

/-- `ℓ = λ₀ − B`. -/
def ellPar (n : ℕ) (lam0 : ℝ) : ℝ := lam0 - cutSlack n

/-- `α = 1 + (2 log n + log(128/a))/(ℓ − 2 log n)` of (4.3). -/
def alphaPar (n : ℕ) (ε lam0 : ℝ) : ℝ :=
  1 + (2 * Real.log n + Real.log (128 / aPar ε)) / (ellPar n lam0 - 2 * Real.log n)

/-- `σ = 3/2 − α` of (4.3). -/
def sigmaPar (n : ℕ) (ε lam0 : ℝ) : ℝ := 3 / 2 - alphaPar n ε lam0

/-- `τ = a/64` of (4.3). -/
def tauPar (ε : ℝ) : ℝ := aPar ε / 64

/-- The coordinate scale `U_j = min{W, min_i b_i/A_ij}`. -/
def burgScale {n m k : ℕ} (I : Instance n m k) (W : ℝ) (j : Fin m) : ℝ :=
  min W (⨅ i, I.b i / I.A i j)

/-- The normalized set `K = {z : (U_j z_j)_j ∈ X_W}`. -/
def normSet {n m k : ℕ} (I : Instance n m k) (W : ℝ) : Set (Fin m → ℝ) :=
  {z | (fun j => burgScale I W j * z j) ∈ boxSet I W}

/-- The Burg potential `ψ(z) = −Σ_j log z_j`. -/
def burg {m : ℕ} (z : Fin m → ℝ) : ℝ := -∑ j, Real.log (z j)

/-- The Burg center of §3.3 with the properties (D.3). -/
def BurgCenter {n m k : ℕ} (I : Instance n m k) (W : ℝ) (c : Fin m → ℝ) : Prop :=
  c ∈ normSet I W ∧ (∀ j, 0 < c j) ∧
  (∀ cs : Fin m → ℝ, cs ∈ normSet I W → (∀ j, 0 < cs j) →
    (∀ z ∈ normSet I W, (∀ j, 0 < z j) → burg cs ≤ burg z) → ∀ j, 3 / 4 * cs j ≤ c j) ∧
  ∀ z ∈ normSet I W, ∑ j, z j / c j ≤ 4 * (m : ℝ) / 3

/-- The candidate domain `D` of §6: `Q₀` if (5.8) holds, `X_D` with the width (5.11) otherwise. -/
def candDomain {n m k : ℕ} (I : Instance n m k) (ε lam0 : ℝ) : Set (Fin m → ℝ) :=
  if BranchHolds n ε lam0 then regionQ0 I lam0 else boxSet I (boxWidth m ε)

/-- Lemma 4.2's output: shore of listed cut `i` (vertex `v` is on it when integer output cell
`1 + i·n + v` is nonzero). -/
def outShore {I : OracleSpec} (s : State I) (n i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v : Fin n => outInt s (1 + i * n + v) ≠ 0

/-- Lemma 4.2's output list `H_x`: integer output cell `0` holds its length (a negative value
counts as `0`), entry `i` is the cut with shore `outShore s n i`. -/
def outCutList {I : OracleSpec} (s : State I) (n : ℕ) : List (Cut n) :=
  (List.range (outInt s 0).toNat).map fun i => cutOfShore (outShore s n i)

/-- The frozen sum `h(y) = Σ_{C ∈ L} e^{−w_y(C)}` of a list of cuts. -/
def frozenSum {n m : ℕ} (ends : Ends n m) (q0 : Fin m → ℝ) (L : List (Cut n)) (y : Fin m → ℝ) :
    ℝ :=
  (L.map fun C => Real.exp (-cutWeight ends (weightAt q0 y) C)).sum

/-- Lemma H.1's output point: the point of `ℝ^m` stored at real cells `p, …, p+m−1`, where `p` is
integer output cell `0`. -/
def selectedPoint {m : ℕ} (s : State (routineSpec m)) : Fin m → ℝ :=
  readVec m s.core.mem (outInt s 0)

/-- Lemma H.1's upper estimate `U`: `+∞` when integer output cell `1` is nonzero (fallback),
otherwise real output cell `0`. -/
def selectedU {m : ℕ} (s : State (routineSpec m)) : EReal :=
  if outInt s 1 ≠ 0 then ⊤ else ((outReal s 0 : ℝ) : EReal)

end NetUnrelDesign.Main


