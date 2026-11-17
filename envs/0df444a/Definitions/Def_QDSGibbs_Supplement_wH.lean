-- Prove2me | Definitions.Def_QDSGibbs_Supplement_wH
-- name    : QDSGibbs_Supplement_wH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:25:37.470196+00:00
-- url     : https://prove2.me/theorems/8e795a55-b449-40e1-a224-9d8bb28e0f4c
-- title:
--   Hamming Wasserstein distance $W_H$, diagonal influence $D^{\mathrm{diag}}$, heat-bath and finite-time QBP kernels, $s_*$, $\omega_B$, $C_B$, $\partial B$, $\chi$
-- statement:
--   Setting of §4.1: configurations $x\in[d]^\Lambda$, a product-basis diagonal Hamiltonian with energies $H(x)$, and the Gibbs distribution $\pi(x)\propto e^{-\beta H(x)}$.
--
--   1. The **Hamming distance** $d_H(x,y)=\#\{i:x_i\neq y_i\}$ and the **Wasserstein distance** $$W_H(p,q)=\inf_{\gamma}\sum_{x,y}\gamma(x,y)\,d_H(x,y),$$ the infimum over couplings $\gamma\ge0$ of $p$ and $q$ (row sums $p$, column sums $q$).
--   2. $x\sim_j y$ when $x,y$ differ exactly at $j$; the **diagonal influence** of a stochastic matrix $R$ is $D^{\mathrm{diag}}_R(j)=\max_{x\sim_j y}W_H(R(x,\cdot),R(y,\cdot))$, and for a labelled block family and $m\ge1$, $$\Gamma_{\mathscr B}((R_B)_B)=\frac1m\max_j\sum_B\bigl(D^{\mathrm{diag}}_{R_B}(j)-1\bigr).$$
--   3. The **heat-bath kernel** $H_B((u,\xi),(v,\xi'))=\mathbf 1\{\xi=\xi'\}\,\pi^\xi_B(v)$ (4.3), and the **finite-time QBP kernel** $R_B(T)(x,y)=\langle y|e^{T\mathcal K_B}(|x\rangle\langle x|)|y\rangle$, the diagonal restriction of the QBP block channel.
--   4. Writing $H(u,\xi)=H_B(u)+W_\xi(u)+H_{B^c}(\xi)$ with $W_\xi(u)$ the value of the crossing interaction, $$s_*=\min_{B,\xi}\Bigl[e^{\beta\min_uW_\xi(u)/2}\sum_v\sigma^B_\beta(v)e^{-\beta W_\xi(v)/2}\Bigr],\qquad \omega_B=\sup_\xi\bigl(\max_uW_\xi(u)-\min_uW_\xi(u)\bigr),$$ with $\sigma^B_\beta\propto e^{-\beta H_B}$ the block Gibbs law; $C_B=\sum_{\alpha\text{ crossing }B}\|h_\alpha\|$; $\partial B$ the exterior sites sharing an interaction term with $B$; $\chi=m^{-1}\max_j\#\{B:j\in B\cup\partial B\}$; $b=\max_B|B|$.
--
--   These are the objects of the classical DS contraction theorem (Theorem 4.2).
--
--   **Formalization Note** $W_H$ and $D^{\mathrm{diag}}$ take values in $[0,\infty]$ (no coupling gives $\infty$). "$\Gamma\le b-a$" with $a,b\ge0$ is recorded without real subtraction as $\sum_BD^{\mathrm{diag}}_{R_B}(j)+ma\le|\mathscr B|+mb$ for every $j$ (`GammaLe`). $R_B(T)$ is the real part of the diagonal entry of the base mission's `blockChannel`.
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), §4.1 pp.25–28, (4.3) p.26, definitions of D^diag and Γ p.27, Theorem 4.2 p.28; C_B p.11

import Mathlib
import Definitions.Def_QDSGibbs_blockChannel
import Definitions.Def_QDSGibbs_Supplement_perturb

open scoped Matrix ENNReal

namespace QDSGibbs.Supplement

/-- The **Hamming distance** `d_H(x, y) = #{i : x_i ≠ y_i}` on configurations `[d]^Λ`
(Rouzé–Stilck França, arXiv:2610.03578, held file sha256 ede55815…, §4.1, p.26). -/
def hamming {N : ℕ} {d : Fin N → ℕ} (x y : Cfg d) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card

/-- `γ` is a **coupling** of the nonnegative vectors `p` and `q`: a nonnegative matrix whose row sums
are `p` and whose column sums are `q` (arXiv:2610.03578, §4.1, p.26, optimal transport). -/
def IsCoupling {α : Type} [Fintype α] (p q : α → ℝ) (γ : α → α → ℝ) : Prop :=
  (∀ x y, 0 ≤ γ x y) ∧ (∀ x, ∑ y, γ x y = p x) ∧ (∀ y, ∑ x, γ x y = q y)

/-- The **Wasserstein-1 distance for the Hamming metric** `W_H(p, q) = inf_γ Σ_{x,y} γ(x,y) d_H(x,y)`
between probability vectors on `[d]^Λ` (arXiv:2610.03578, §4.1, p.26).

**Formalization Note** Valued in `ℝ≥0∞`. The infimum is over couplings; if `p` and `q` admit none
(a negative entry, or different total masses) the value is `⊤`, never the junk `0` of a real
infimum over the empty set. On probability vectors it is the optimal-transport cost. -/
noncomputable def wH {N : ℕ} {d : Fin N → ℕ} (p q : Cfg d → ℝ) : ℝ≥0∞ :=
  ⨅ (γ : Cfg d → Cfg d → ℝ) (_ : IsCoupling p q γ),
    ENNReal.ofReal (∑ x, ∑ y, γ x y * (hamming x y : ℝ))

/-- `x ∼_j y`: the configurations differ at `j` and agree at every other site (arXiv:2610.03578,
§4.1, p.26). -/
def AdjAt {N : ℕ} {d : Fin N → ℕ} (j : Fin N) (x y : Cfg d) : Prop :=
  x j ≠ y j ∧ ∀ i, i ≠ j → x i = y i

/-- The **diagonal influence** `D^diag_R(j) = max_{x ∼_j y} W_H(R(x,·), R(y,·))` of a stochastic
matrix `R` on `[d]^Λ` (arXiv:2610.03578, §4.1, p.27). `R x` is the row `R(x, ·)`.

**Formalization Note** `ℝ≥0∞`-valued supremum over the finitely many pairs `x ∼_j y`. -/
noncomputable def dDiag {N : ℕ} {d : Fin N → ℕ} (R : Cfg d → Cfg d → ℝ) (j : Fin N) : ℝ≥0∞ :=
  ⨆ (x : Cfg d) (y : Cfg d) (_ : AdjAt j x y), wH (R x) (R y)

/-- `Γ_𝓑((R_B)_B) ≤ b − a`, where `Γ_𝓑((R_B)_B) = (1/m) max_j Σ_B (D^diag_{R_B}(j) − 1)`
(arXiv:2610.03578, §4.1, p.27), for a finite labelled family `(R_B)_{B ∈ ι}` and `a, b ≥ 0`.

**Formalization Note** Written without subtraction: for every site `j`,
`Σ_B D^diag_{R_B}(j) + m a ≤ |ι| + m b` in `ℝ≥0∞` (`|ι|` is the number of labelled blocks, counted
with multiplicity). For `a, b ≥ 0` this is exactly the real inequality (and it fails when some
`D^diag` is infinite). So `Γ ≤ −κ` is `GammaLe R m κ 0`, and (4.10) is
`GammaLe R m κ (2bχe^{−s_* T})`. -/
def GammaLe {N : ℕ} {d : Fin N → ℕ} {ι : Type} [Fintype ι] (R : ι → Cfg d → Cfg d → ℝ) (m : ℕ)
    (a b : ℝ) : Prop :=
  ∀ j : Fin N, ∑ B, dDiag (R B) j + ENNReal.ofReal ((m : ℝ) * a) ≤
    (Fintype.card ι : ℝ≥0∞) + ENNReal.ofReal ((m : ℝ) * b)

/-- The classical energy `H(x) = ⟨x|H|x⟩` of a configuration (arXiv:2610.03578, §4.1, p.25; `H` is
diagonal in the product basis). -/
noncomputable def energy {N : ℕ} {d : Fin N → ℕ} (A : Op d) (x : Cfg d) : ℝ := (A x x).re

/-- An interaction is **classical**: every on-site term `V_i` and every interaction term `h_α` is
diagonal in the product basis (arXiv:2610.03578, §4.1, p.25, "product-basis diagonal
Hamiltonian"). -/
def IsDiagonalInteraction {N : ℕ} {d : Fin N → ℕ} (I : Interaction d) : Prop :=
  (∀ i (x y : Cfg d), x ≠ y → I.V i x y = 0) ∧ (∀ α (x y : Cfg d), x ≠ y → I.h α x y = 0)

/-- The **block heat-bath kernel** `H_B((u, ξ), (v, ξ′)) = 1{ξ = ξ′} π^ξ_B(v)` (arXiv:2610.03578,
(4.3), p.26), with `π(x) ∝ e^{−βH(x)}` the full Gibbs distribution and `π^ξ_B` its conditional law
on `B` given the exterior configuration `ξ`.

**Formalization Note** `π^ξ_B(v) = e^{−βH(v,ξ)} / Σ_z e^{−βH(z,ξ)}` (the normalization of `π`
cancels); `glue B z x` is the configuration equal to `z` on `B` and to `x` off `B`. -/
noncomputable def heatBath {N : ℕ} {d : Fin N → ℕ} (β : ℝ) (I : Interaction d) (B : Finset (Fin N))
    (x y : Cfg d) : ℝ :=
  if ∀ i, i ∉ B → x i = y i then
    Real.exp (-β * energy (ham I) y) / ∑ z : SubCfg d B, Real.exp (-β * energy (ham I) (glue B z x))
  else 0

/-- The **finite-time QBP kernel** `R_B(T)(x, y) = ⟨y| e^{T K_B}(|x⟩⟨x|) |y⟩`, the diagonal
restriction of the QBP block channel `Φ_B(T) = e^{T K_B}` (arXiv:2610.03578, §4.1, p.28;
Theorem 4.2).

**Formalization Note** `Φ_B(T)` is the base mission's `blockChannel β I B univ T`; the real part of
the diagonal entry is taken (it is real for the diagonal Hamiltonians of §4.1). -/
noncomputable def diagKernel {N : ℕ} {d : Fin N → ℕ} (β : ℝ) (I : Interaction d)
    (B : Finset (Fin N)) (T : ℝ) (x y : Cfg d) : ℝ :=
  (blockChannel β I B Finset.univ T (Matrix.single x x 1) y y).re

/-- The quantity inside the minimum defining `s_*` (arXiv:2610.03578, Theorem 4.2, p.28) for the
block `B` and the exterior configuration `ξ` (the restriction of `x` to `B^c`):
`e^{β min_u W_ξ(u)/2} Σ_v σ^B_β(v) e^{−βW_ξ(v)/2}`, where `W_ξ(u)` is the value of the crossing
interaction `W_∂B` at `(u, ξ)` and `σ^B_β(v) ∝ e^{−βH_B(v)}` is the block Gibbs law.

**Formalization Note** The minimum over the finitely many `u ∈ [d]^B` is a real `⨅` over a finite
nonempty type. `H_B(v)` is read off at `(v, ξ)`; it does not depend on `ξ`. -/
noncomputable def sStarAt {N : ℕ} {d : Fin N → ℕ} (β : ℝ) (I : Interaction d) (B : Finset (Fin N))
    (x : Cfg d) : ℝ :=
  Real.exp (β * (⨅ u : SubCfg d B, energy (cross I B) (glue B u x)) / 2) *
    ∑ v : SubCfg d B,
      (Real.exp (-β * energy (hamOn I B) (glue B v x)) /
          ∑ w : SubCfg d B, Real.exp (-β * energy (hamOn I B) (glue B w x))) *
        Real.exp (-β * energy (cross I B) (glue B v x) / 2)

/-- `s_* = min_{B, ξ} [e^{β min_u W_ξ(u)/2} Σ_v σ^B_β(v) e^{−βW_ξ(v)/2}]` (arXiv:2610.03578,
Theorem 4.2, p.28).

**Formalization Note** Minimum over the finitely many labels and configurations (a real `⨅` over
finite nonempty types). -/
noncomputable def sStar {N : ℕ} {d : Fin N → ℕ} {ι : Type} (β : ℝ) (I : Interaction d)
    (blk : ι → Finset (Fin N)) : ℝ :=
  ⨅ (B : ι) (x : Cfg d), sStarAt β I (blk B) x

/-- The **oscillation** `ω_B = sup_ξ (max_u W_ξ(u) − min_u W_ξ(u))` of the crossing interaction
(arXiv:2610.03578, Theorem 4.2, p.28). -/
noncomputable def omegaB {N : ℕ} {d : Fin N → ℕ} (I : Interaction d) (B : Finset (Fin N)) : ℝ :=
  ⨆ x : Cfg d, ((⨆ u : SubCfg d B, energy (cross I B) (glue B u x)) -
    ⨅ u : SubCfg d B, energy (cross I B) (glue B u x))

open Classical in
/-- `C_B = Σ_{α : X_α ∩ B ≠ ∅, X_α ∩ B^c ≠ ∅} ‖h_α‖` (arXiv:2610.03578, p.11). -/
noncomputable def cB {N : ℕ} {d : Fin N → ℕ} (I : Interaction d) (B : Finset (Fin N)) : ℝ :=
  ∑ α ∈ Finset.univ.filter (fun α => Crosses (I.X α) B), opNorm (I.h α)

open Classical in
/-- The **exterior boundary** `∂B`: the sites of `Λ ∖ B` sharing an interaction term with `B`
(arXiv:2610.03578, §4.1, pp.26, 28). -/
noncomputable def bdry {N : ℕ} {d : Fin N → ℕ} (I : Interaction d) (B : Finset (Fin N)) :
    Finset (Fin N) :=
  Finset.univ.filter fun i => i ∉ B ∧ ∃ α, i ∈ I.X α ∧ (I.X α ∩ B).Nonempty

open Classical in
/-- `χ = m^{−1} max_j #{B : j ∈ B ∪ ∂B}` (arXiv:2610.03578, Theorem 4.2, p.28); labels are counted
with multiplicity.

**Formalization Note** The maximum over sites is a real `⨆` over `Fin N` (a maximum for `N ≥ 1`). -/
noncomputable def chi {N : ℕ} {d : Fin N → ℕ} {ι : Type} [Fintype ι] (I : Interaction d)
    (blk : ι → Finset (Fin N)) (m : ℕ) : ℝ :=
  ⨆ j : Fin N,
    ((Finset.univ.filter fun B => j ∈ blk B ∪ bdry I (blk B)).card : ℝ) / (m : ℝ)

/-- `b = max_B |B|` (arXiv:2610.03578, Theorem 4.2, p.28). -/
def maxCard {N : ℕ} {ι : Type} [Fintype ι] (blk : ι → Finset (Fin N)) : ℕ :=
  Finset.univ.sup fun B => (blk B).card

end QDSGibbs.Supplement


