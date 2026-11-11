-- Prove2me | Definitions.Def_SampQueryLB_WarmSLC_HardFamily
-- name    : SampQueryLB_WarmSLC_HardFamily
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:15:26.196086+00:00
-- url     : https://prove2.me/theorems/76ce1b50-a7b1-440f-9af5-06bb27ddec23
-- title:
--   §4.1 — the hard family $V^\Xi$: Gaussian tensor fields, cutoffs, truncations, gates, prefix potentials, the admissible event $E_n$ and the energy test $T_n$
-- statement:
--   Fix a block dimension $n$. Put $h=\lfloor (\log n)^{1/3}/32\rfloor$, $d_n=(h+1)n$, $Q=2^{h+1}$, $P=Q^{64}$, $K=Q^{74}$, $S_i=\sum_{k=0}^{h-i}K^k$, the even degrees $\mathcal P=\{4,6,\dots,P\}$, $\epsilon_g=1/100$, $\tau=8\log(2P)$, and the amplitudes
--   $$a_{i,p}=\frac{1}{p^4S_i^2\sqrt{(h-i+1)\log(2PS_i)}}.$$
--   A point $x\in\mathbb R^{d_n}$ has blocks $x_0,\dots,x_h\in\mathbb R^n$. For unit directions, $\psi_i(u_i,\dots,u_h)=u_i\otimes u_{i+1}^{\otimes K}\otimes\cdots\otimes u_h^{\otimes K^{h-i}}$, a unit tensor of order $S_i$. The coefficient space is $G_n=\bigoplus_{i\le h,p\in\mathcal P}\mathbb R^{n^{pS_i}}$ with the standard Gaussian law $\mu_n$, and
--   $$F^\Xi_{i,p}(u)=\sqrt n\,a_{i,p}\langle \Xi_{i,p},\psi_i(u)^{\otimes p}\rangle,\qquad \Phi_{i,p}(x)=\sqrt n\,a_{i,p}C_i(x)\psi_i(x)^{\otimes p},\qquad H^\Xi_{i,p}(x)=\langle\Xi,\Phi_{i,p}(x)\rangle,$$
--   with $\psi_i(x)=\psi_i(x_i/\|x_i\|,\dots,x_h/\|x_h\|)$, $H^\Xi_i=\sum_pH^\Xi_{i,p}$ and $\Phi_i=\sum_p\Phi_{i,p}$.
--
--   With $\varrho(t)=e^{-1/t}$ for $t>0$ and $0$ otherwise, the fixed smooth functions are those of footnotes 2–5: the radial cutoff $\chi$ (equal to $1$ on $[0.7,0.95]$, supported in $[0.65,1]$), the gate cutoff $J$ (equal to $1$ on $[0.75,0.9]$), the energy cutoff $g$ ($1$ on $(-\infty,1/2]$, $0$ on $[1,\infty)$) and the odd truncation $\varphi(t)=\int_0^t\frac{\varrho(2-|s|)}{\varrho(2-|s|)+\varrho(|s|-1)}ds$. Then $C_i(x)=\prod_{j\ge i}\chi(\|x_j\|/\sqrt n)$, $U_i(s)=\frac{n\beta_i^2}{\lambda}\varphi\big(\frac{\lambda s}{n\beta_i}\big)$ with $\lambda=\lambda_*/(h+1)^2$, and the amplitudes are $\beta_0=\eta_*\lambda$, $\beta_i=\eta_*\lambda\big(\sum_{j<i}D_j/\beta_j\big)^{-1}$ with $D_i=\frac{C_gP^5(h-i+1)\sqrt{\log 2P}}{\epsilon_g}S_i^3\log(2PS_i)$. The gate of level $i$ is
--   $$G^\Xi_i(x)=\Big(\prod_{j\ge i}J\big(\tfrac{\|x_j\|}{\sqrt n}\big)\Big)\,g\Big(\frac1\tau\log\sum_{p\in\mathcal P}2\cosh\Big(\frac{\tau}{\epsilon_g\beta_i}\Big[\frac{H^\Xi_{i,p}(x)}{na_{i,p}^2}+\beta_i\Big]\Big)\Big),$$
--   $A^\Xi_i=\prod_{j<i}G^\Xi_j$, and the prefix potentials are $V^\Xi_i=B+\sum_{j\le i}A^\Xi_jU_j(H^\Xi_j)$ with $B(x)=\frac34\|x\|^2$; $V^\Xi=V^\Xi_h$, $\pi^\Xi=\pi_{V^\Xi}$, $\gamma_n=\pi_B=N(0,\frac23I)$.
--
--   The **admissible event** is $E_n=\bigcap_{i,p}\{\Xi:\sup_{u_i,\dots,u_h\in S^{n-1}}|F^\Xi_{i,p}(u)|\le C_f\,n\,a_{i,p}\sqrt{(h-i+1)\log(2PS_i)}\}$; the **energy test** (Definition 4.6) is $T_n=\{(\Xi,x):0.75\sqrt n\le\|x_h\|\le0.9\sqrt n,\ \max_p|F^\Xi_{h,p}(x_h/\|x_h\|)/(na_{h,p}^2)+\beta_h|\le\epsilon_g\beta_h/4\}$. Also $T_i(x,y)=\prod_{k\ge i}\big(\frac{\langle x_k,y_k\rangle}{\|x_k\|\|y_k\|}\big)^{K^{k-i}}$, $d_i(x,y)=\min\{\|\psi_i(x)-\psi_i(y)\|,\|\psi_i(x)+\psi_i(y)\|\}$, the shell $\mathcal R_n=\{x:0.75\sqrt n\le\|x_j\|\le0.9\sqrt n\ \forall j\}$ and $\rho_*=Q^{-4}=P^{-1/16}$.
--
--   **Formalization Note.** `Vpre c Ξ k` is $B+\sum_{j<k}A^\Xi_jU_j(H^\Xi_j)$, so `Vpre c Ξ 0` $=V^\Xi_{-1}=B$ and `Vpre c Ξ (i+1)` $=V^\Xi_i$. Block $j$ of $x$ is the coordinates `finProdFinEquiv (j, a)`; slot $r$ of one copy of $\psi_i$ carries block $i+$`slotLevel K r` (one slot of block $i$, then $K$ of block $i+1$, …), and slot $m$ of $\psi_i^{\otimes p}$ is slot $m\bmod S_i$ of copy $\lfloor m/S_i\rfloor$. The direction of a zero block is $0$; every quantity the paper sets to zero when a participating block vanishes carries the factor $C_i(x)$, which is then $0$. `Consts` holds $(C_f,C_g,\eta_*,\lambda_*)$ and `ForChosenConstants Pr` says that `Pr` holds for all sufficiently extreme constants in the order of the proof of Proposition 4.2 ($C_f>0$ large; then $C_g\ge1$ large; then $\eta_*\in(0,1]$, $\lambda_*\in(0,1/2]$ small with $\eta_*\lambda_*\le1/4$).
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), pp. 23–27, §4.1 ((13)–(21), footnotes 2–5); pp. 30–31, (27)–(28); p. 33, Definition 4.6; p. 56, (61)–(62)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model

/-!
# The hard family of §4.1 and the energy test (Definition 4.6)

Zhou, Suzuki, arXiv:2611.05813 (held version dated November 3, 2026), pp. 23–27 (§4.1,
(13)–(21), footnotes 2–5), pp. 30–31 ((27)–(28)), p. 33 (Definition 4.6), p. 56 ((61)–(62)).

Conventions.
* `n` is the block dimension; `hh n = ⌊(log n)^{1/3}/32⌋`, `dn n = (h+1) n`,
  `QQ n = 2^{h+1}`, `PP n = Q^64`, `KK n = Q^74`, `S n i = Σ_{k=0}^{h-i} K^k`.
* A point of `ℝ^{d_n}` is `Point (dn n)`; its block `j` is `blk x j ∈ ℝ^n`, the coordinates
  `finProdFinEquiv (j, a)`, `a < n`.
* Levels are `Lvl n = Fin (h+1)`; degrees are `Deg n = {p : 4 ≤ p ≤ P, p even}`.
* The coefficient space `G_n = ⊕_{i,p} ℝ^{n^{p S_i}}` is `Coef n`, the Euclidean space on the
  index type `Σ (i, p), (Fin (p · S_i) → Fin n)`; `Ξ_{i,p}` is the block `(i, p)` of `Ξ`.
  `mu n` is the standard Gaussian law `µ_n` on it.
* Tensor slots. One copy of `ψ_i = u_i ⊗ u_{i+1}^{⊗K} ⊗ ⋯ ⊗ u_h^{⊗K^{h-i}}` has `S_i` slots; slot
  `r` carries the direction of block `i + slotLevel K r`, where `slotLevel K r` is the least `k`
  with `r < Σ_{l ≤ k} K^l` (first one slot of block `i`, then `K` slots of block `i+1`, …).
  `ψ_i^{⊗p}` has `p · S_i` slots, slot `m` being slot `m mod S_i` of copy `⌊m / S_i⌋`.
* Directions of zero blocks are `0` (`‖0‖⁻¹ • 0 = 0`); every expression the paper declares zero
  when a participating block vanishes carries a factor `C_i(x)`, which is `0` there (`χ(0) = 0`).
* `Consts` carries the absolute constants `(C_f, C_g, η_*, λ_*)`; `ForChosenConstants Pr` says that
  `Pr` holds for all sufficiently extreme constants, chosen in the paper's order (proof of
  Proposition 4.2): `C_f` large, then `C_g ≥ 1` large, then `η_* ∈ (0, 1]`, `λ_* ∈ (0, 1/2]`
  small with `η_* λ_* ≤ 1/4`.
-/

namespace SampQueryLB.WarmSLC

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory
open scoped ENNReal ContDiff RealInnerProductSpace

noncomputable section

/-! ## Parameters (61) -/

/-- `h = ⌊(log n)^{1/3} / 32⌋`. -/
def hh (n : ℕ) : ℕ := ⌊Real.log n ^ ((1 : ℝ) / 3) / 32⌋₊

/-- `d_n = (h + 1) n`. -/
def dn (n : ℕ) : ℕ := (hh n + 1) * n

/-- `Q = 2^{h+1}`. -/
def QQ (n : ℕ) : ℕ := 2 ^ (hh n + 1)

/-- `P = Q^64`. -/
def PP (n : ℕ) : ℕ := QQ n ^ 64

/-- `K = Q^74`. -/
def KK (n : ℕ) : ℕ := QQ n ^ 74

/-- Levels `0 ≤ i ≤ h`. -/
abbrev Lvl (n : ℕ) := Fin (hh n + 1)

/-- `S_i = Σ_{k=0}^{h-i} K^k`, the order of `ψ_i`. -/
def S (n : ℕ) (i : Lvl n) : ℕ := ∑ k ∈ Finset.range (hh n - i + 1), KK n ^ k

/-- The degree set `𝒫 = {4, 6, …, P}`. -/
def degs (n : ℕ) : Finset ℕ := (Finset.range (PP n + 1)).filter (fun p => 4 ≤ p ∧ Even p)

/-- Degrees `p ∈ 𝒫`. -/
abbrev Deg (n : ℕ) := {p : ℕ // p ∈ degs n}

/-- The energy tolerance `ϵ_g = 1/100`. -/
def epsG : ℝ := 1 / 100

/-- `τ = 8 log(2P)`. -/
def tau (n : ℕ) : ℝ := 8 * Real.log (2 * PP n)

/-- The amplitude `a_{i,p} = 1 / (p⁴ S_i² √((h − i + 1) log(2 P S_i)))` of (14). -/
def aa (n : ℕ) (i : Lvl n) (p : Deg n) : ℝ :=
  1 / ((p.1 : ℝ) ^ 4 * (S n i : ℝ) ^ 2 *
    Real.sqrt (((hh n - i + 1 : ℕ) : ℝ) * Real.log (2 * (PP n : ℝ) * S n i)))

/-! ## Absolute constants -/

/-- The absolute constants `C_f` (admissible event), `C_g`, `η_*`, `λ_*` (amplitudes). -/
structure Consts where
  Cf : ℝ
  Cg : ℝ
  eta : ℝ
  lam : ℝ

/-- `Pr` holds for all sufficiently extreme absolute constants, chosen in the order of the proof of
Proposition 4.2: `C_f > 0` large, then `C_g ≥ 1` large, then `η_* ∈ (0,1]` and `λ_* ∈ (0,1/2]`
small with `η_* λ_* ≤ 1/4`. -/
def ForChosenConstants (Pr : Consts → Prop) : Prop :=
  ∃ Cf0 : ℝ, ∀ Cf : ℝ, 0 < Cf → Cf0 ≤ Cf →
    ∃ Cg0 : ℝ, ∀ Cg : ℝ, 1 ≤ Cg → Cg0 ≤ Cg →
      ∃ eta0 : ℝ, 0 < eta0 ∧ ∃ lam0 : ℝ, 0 < lam0 ∧
        ∀ eta lam : ℝ, 0 < eta → eta ≤ 1 → eta ≤ eta0 → 0 < lam → lam ≤ 1 / 2 → lam ≤ lam0 →
          eta * lam ≤ 1 / 4 → Pr ⟨Cf, Cg, eta, lam⟩

/-- `λ = λ_* / (h+1)²`. -/
def lamN (c : Consts) (n : ℕ) : ℝ := c.lam / ((hh n : ℝ) + 1) ^ 2

/-- `D_i = C_g P⁵ (h − i + 1) √(log 2P) / ϵ_g · S_i³ log(2 P S_i)` of (18) (`i` a natural number,
used for `i ≤ h`). -/
def DD (c : Consts) (n : ℕ) (i : ℕ) : ℝ :=
  c.Cg * (PP n : ℝ) ^ 5 * ((hh n - i + 1 : ℕ) : ℝ) * Real.sqrt (Real.log (2 * PP n)) / epsG *
    (∑ k ∈ Finset.range (hh n - i + 1), (KK n : ℝ) ^ k) ^ 3 *
    Real.log (2 * PP n * ∑ k ∈ Finset.range (hh n - i + 1), (KK n : ℝ) ^ k)

/-- `(β_i, Σ_{j<i} D_j/β_j)`, computed successively: `β_0 = η_* λ`,
`β_i = η_* λ (Σ_{j<i} D_j/β_j)^{-1}` for `i ≥ 1` (18). -/
def betaAux (c : Consts) (n : ℕ) : ℕ → ℝ × ℝ
  | 0 => (c.eta * lamN c n, 0)
  | i + 1 =>
      let s := (betaAux c n i).2 + DD c n i / (betaAux c n i).1
      (c.eta * lamN c n * s⁻¹, s)

/-- The amplitude `β_i`. -/
def beta (c : Consts) (n : ℕ) (i : ℕ) : ℝ := (betaAux c n i).1

/-! ## The fixed smooth functions (footnotes 2–5) -/

/-- `ϱ(t) = e^{-1/t}` for `t > 0`, `0` otherwise. -/
def bumpRho (t : ℝ) : ℝ := if 0 < t then Real.exp (-1 / t) else 0

/-- The radial cutoff `χ` of footnote 2 (`= 1` on `[0.7, 0.95]`, support `[0.65, 1]`). -/
def chiCut (r : ℝ) : ℝ :=
  bumpRho (r - 0.65) / (bumpRho (r - 0.65) + bumpRho (0.7 - r)) *
    (bumpRho (1 - r) / (bumpRho (1 - r) + bumpRho (r - 0.95)))

/-- The odd truncation `φ(t) = ∫_0^t ϱ(2−|s|)/(ϱ(2−|s|) + ϱ(|s|−1)) ds` of footnote 3. -/
def phiTrunc (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, bumpRho (2 - |s|) / (bumpRho (2 - |s|) + bumpRho (|s| - 1))

/-- The gate's radial cutoff `J` of footnote 4 (`= 1` on `[0.75, 0.9]`, support in `(0.7, 0.95)`). -/
def Jcut (r : ℝ) : ℝ :=
  bumpRho (r - 0.725) / (bumpRho (r - 0.725) + bumpRho (0.75 - r)) *
    (bumpRho (0.925 - r) / (bumpRho (0.925 - r) + bumpRho (r - 0.9)))

/-- The energy-error cutoff `g(t) = ϱ(1−t)/(ϱ(1−t) + ϱ(t − 1/2))` of footnote 5. -/
def gCut (t : ℝ) : ℝ := bumpRho (1 - t) / (bumpRho (1 - t) + bumpRho (t - 1 / 2))

/-- The energy truncation `U_i(s) = (n β_i²/λ) φ(λ s / (n β_i))` of (17). -/
def Ucut (c : Consts) (n : ℕ) (i : ℕ) (s : ℝ) : ℝ :=
  (n : ℝ) * beta c n i ^ 2 / lamN c n * phiTrunc (lamN c n * s / ((n : ℝ) * beta c n i))

/-! ## Blocks, directions and tensors -/

/-- Block `j` of a point of `ℝ^{d_n}`. -/
def blk {n : ℕ} (x : Point (dn n)) (j : Lvl n) : Point n :=
  WithLp.toLp 2 (fun a : Fin n => x (finProdFinEquiv (j, a)))

/-- The direction `x_j / ‖x_j‖` of block `j` (`0` when `x_j = 0`). -/
def dir {n : ℕ} (x : Point (dn n)) (j : Lvl n) : Point n := ‖blk x j‖⁻¹ • blk x j

/-- A family of block directions indexed by natural numbers (`0` beyond `h`). -/
def extendDirs {n : ℕ} (u : Lvl n → Point n) (j : ℕ) : Point n :=
  if h : j < hh n + 1 then u ⟨j, h⟩ else 0

/-- `slotLevel K r`: the least `k` with `r < Σ_{l ≤ k} K^l` (for `K ≥ 1`), i.e. slot `r` of
`ψ_i` carries block `i + slotLevel K r`. -/
def slotLevel (K r : ℕ) : ℕ :=
  ((Finset.range (r + 1)).filter (fun k => ∑ l ∈ Finset.range (k + 1), K ^ l ≤ r)).card

/-- The entries of `ψ_i(u_i, …, u_h)^{⊗p}`, indexed by `Fin (p · S_i) → Fin n`. -/
def tensorPow {n : ℕ} (i : Lvl n) (p : ℕ) (u : Lvl n → Point n) (ι : Fin (p * S n i) → Fin n) :
    ℝ :=
  ∏ m : Fin (p * S n i), extendDirs u ((i : ℕ) + slotLevel (KK n) ((m : ℕ) % S n i)) (ι m)

/-- The unit tensor `ψ_i(x) = ψ_i(x_i/‖x_i‖, …, x_h/‖x_h‖)` of order `S_i`. -/
def psi {n : ℕ} (i : Lvl n) (x : Point (dn n)) : EuclideanSpace ℝ (Fin (S n i) → Fin n) :=
  WithLp.toLp 2 (fun ι : Fin (S n i) → Fin n =>
    ∏ m : Fin (S n i), extendDirs (dir x) ((i : ℕ) + slotLevel (KK n) (m : ℕ)) (ι m))

/-- The radial cutoff `C_i(x) = Π_{j=i}^h χ(‖x_j‖/√n)` of (16). -/
def Ccut {n : ℕ} (i : Lvl n) (x : Point (dn n)) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Lvl n => i ≤ j), chiCut (‖blk x j‖ / Real.sqrt n)

/-! ## Coefficients, features and fields -/

/-- Index set of `G_n = ⊕_{i,p} ℝ^{n^{p S_i}}`. -/
abbrev CIdx (n : ℕ) := Σ ip : Lvl n × Deg n, (Fin (ip.2.1 * S n ip.1) → Fin n)

/-- The coefficient space `G_n`. -/
abbrev Coef (n : ℕ) := EuclideanSpace ℝ (CIdx n)

/-- The coefficient law `µ_n = N(0, I_{G_n})`. -/
def mu (n : ℕ) : Measure (Coef n) := stdGaussian (Coef n)

/-- The degree-`p` angular function `F^Ξ_{i,p}(u_i, …, u_h) = √n a_{i,p} ⟨Ξ_{i,p}, ψ_i(u)^{⊗p}⟩`
of (15) (it depends only on `u_i, …, u_h`). -/
def angF {n : ℕ} (Ξ : Coef n) (i : Lvl n) (p : Deg n) (u : Lvl n → Point n) : ℝ :=
  Real.sqrt n * aa n i p * ∑ ι : Fin (p.1 * S n i) → Fin n, Ξ ⟨(i, p), ι⟩ * tensorPow i p.1 u ι

/-- The feature `Φ_{i,p}(x) = √n a_{i,p} C_i(x) ψ_i(x)^{⊗p}`, placed in block `(i, p)` of `G_n`. -/
def feat {n : ℕ} (i : Lvl n) (p : Deg n) (x : Point (dn n)) : Coef n :=
  WithLp.toLp 2 (fun k : CIdx n =>
    if k.1 = (i, p) then
      Real.sqrt n * aa n k.1.1 k.1.2 * Ccut k.1.1 x * tensorPow k.1.1 k.1.2.1 (dir x) k.2
    else 0)

/-- `Φ_i(x) = ⊕_p Φ_{i,p}(x)`. -/
def featLevel {n : ℕ} (i : Lvl n) (x : Point (dn n)) : Coef n := ∑ p : Deg n, feat i p x

/-- The field `H^Ξ_{i,p}(x) = ⟨Ξ_{i,p}, Φ_{i,p}(x)⟩ = C_i(x) F^Ξ_{i,p}(x_i/‖x_i‖, …)`. -/
def fieldp {n : ℕ} (Ξ : Coef n) (i : Lvl n) (p : Deg n) (x : Point (dn n)) : ℝ :=
  ⟪Ξ, feat i p x⟫

/-- The field of level `i`, `H^Ξ_i(x) = ⟨Ξ_i, Φ_i(x)⟩ = Σ_p H^Ξ_{i,p}(x)`. -/
def field {n : ℕ} (Ξ : Coef n) (i : Lvl n) (x : Point (dn n)) : ℝ := ⟪Ξ, featLevel i x⟫

/-- The normalized degree-`p` energy `H^Ξ_{i,p}(x) / (n a_{i,p}²)`. -/
def energy {n : ℕ} (Ξ : Coef n) (i : Lvl n) (p : Deg n) (x : Point (dn n)) : ℝ :=
  fieldp Ξ i p x / ((n : ℝ) * aa n i p ^ 2)

/-! ## Gates and potentials -/

/-- The gate `G^Ξ_i(x)` of (19). -/
def gate (c : Consts) {n : ℕ} (Ξ : Coef n) (i : Lvl n) (x : Point (dn n)) : ℝ :=
  (∏ j ∈ Finset.univ.filter (fun j : Lvl n => i ≤ j), Jcut (‖blk x j‖ / Real.sqrt n)) *
    gCut ((1 / tau n) * Real.log (∑ p : Deg n,
      2 * Real.cosh (tau n / (epsG * beta c n i) * (energy Ξ i p x + beta c n i))))

/-- The gate product `A^Ξ_i(x) = Π_{j<i} G^Ξ_j(x)`. -/
def gateProd (c : Consts) {n : ℕ} (Ξ : Coef n) (i : Lvl n) (x : Point (dn n)) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Lvl n => j < i), gate c Ξ j x

/-- The quadratic base `B(x) = (3/4) ‖x‖²`. -/
def Bq {d : ℕ} (x : Point d) : ℝ := 3 / 4 * ‖x‖ ^ 2

/-- Prefix potentials: `Vpre c Ξ k = B + Σ_{j < k} A^Ξ_j U_j(H^Ξ_j)`, so `Vpre c Ξ 0 = V^Ξ_{-1} = B`
and `Vpre c Ξ (i+1) = V^Ξ_i`. -/
def Vpre (c : Consts) {n : ℕ} (Ξ : Coef n) (k : ℕ) (x : Point (dn n)) : ℝ :=
  Bq x + ∑ j ∈ Finset.univ.filter (fun j : Lvl n => (j : ℕ) < k),
    gateProd c Ξ j x * Ucut c n j (field Ξ j x)

/-- The hard potential `V^Ξ = V^Ξ_h` of (13). -/
def Vhard (c : Consts) {n : ℕ} (Ξ : Coef n) : Point (dn n) → ℝ := Vpre c Ξ (hh n + 1)

/-- The target `π^Ξ = π_{V^Ξ_h}`. -/
def piHard (c : Consts) {n : ℕ} (Ξ : Coef n) : Measure (Point (dn n)) := gibbs (Vhard c Ξ)

/-- `γ_n = N(0, (2/3) I_{d_n})`, the target of `B`. -/
def gammaN (n : ℕ) : Measure (Point (dn n)) := gibbs (Bq (d := dn n))

/-! ## Admissible event, energy test, kernels -/

/-- The last level `h`. -/
def lastLvl (n : ℕ) : Lvl n := Fin.last (hh n)

/-- The admissible event `E_n` of (21). -/
def Eadm (c : Consts) (n : ℕ) : Set (Coef n) :=
  {Ξ | ∀ (i : Lvl n) (p : Deg n) (u : Lvl n → Point n), (∀ j, i ≤ j → ‖u j‖ = 1) →
    |angF Ξ i p u| ≤ c.Cf * n * aa n i p *
      Real.sqrt (((hh n - i + 1 : ℕ) : ℝ) * Real.log (2 * (PP n : ℝ) * S n i))}

/-- The energy test `T_n` of Definition 4.6. -/
def energyTest (c : Consts) (n : ℕ) : Set (Coef n × Point (dn n)) :=
  {z | 0.75 * Real.sqrt n ≤ ‖blk z.2 (lastLvl n)‖ ∧ ‖blk z.2 (lastLvl n)‖ ≤ 0.9 * Real.sqrt n ∧
    ∀ p : Deg n, |angF z.1 (lastLvl n) p (dir z.2) / ((n : ℝ) * aa n (lastLvl n) p ^ 2) +
      beta c n (hh n)| ≤ epsG * beta c n (hh n) / 4}

/-- The section `T_n(Ξ) = {x : (Ξ, x) ∈ T_n}`. -/
def testSet (c : Consts) {n : ℕ} (Ξ : Coef n) : Set (Point (dn n)) := {x | (Ξ, x) ∈ energyTest c n}

/-- `T_i(x, y) = Π_{k=i}^h (⟨x_k, y_k⟩ / (‖x_k‖ ‖y_k‖))^{K^{k-i}}` of (28). -/
def Tcorr {n : ℕ} (i : Lvl n) (x y : Point (dn n)) : ℝ :=
  ∏ k ∈ Finset.univ.filter (fun k : Lvl n => i ≤ k),
    (⟪blk x k, blk y k⟫ / (‖blk x k‖ * ‖blk y k‖)) ^ (KK n ^ ((k : ℕ) - i))

/-- The projective distance `d_i(x, y) = min{‖ψ_i(x) − ψ_i(y)‖, ‖ψ_i(x) + ψ_i(y)‖}` of (62). -/
def dproj {n : ℕ} (i : Lvl n) (x y : Point (dn n)) : ℝ :=
  min ‖psi i x - psi i y‖ ‖psi i x + psi i y‖

/-- The shell region `ℛ_n = {x : 0.75√n ≤ ‖x_j‖ ≤ 0.9√n for every j}` of §7.1 (also `R` of
Definition 6.1). -/
def shell (n : ℕ) : Set (Point (dn n)) :=
  {x | ∀ j : Lvl n, 0.75 * Real.sqrt n ≤ ‖blk x j‖ ∧ ‖blk x j‖ ≤ 0.9 * Real.sqrt n}

/-- `ρ_* = P^{-1/16} = Q^{-4}`. -/
def rhoStar (n : ℕ) : ℝ := ((QQ n : ℝ) ^ 4)⁻¹

end

end SampQueryLB.WarmSLC


