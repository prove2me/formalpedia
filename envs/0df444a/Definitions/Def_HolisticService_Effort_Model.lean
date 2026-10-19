-- Prove2me | Definitions.Def_HolisticService_Effort_Model
-- name    : HolisticService_Effort_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:13:54.927782+00:00
-- url     : https://prove2.me/theorems/5dd13447-b31f-490b-8b81-fcd9efda9732
-- title:
--   §3.2–§3.3, pp. 8–12, App. pp. 26–27 — service design problem: efforts, values, variabilities, correlation matrix, mean-variance utility, Prop. 1 closed form, thresholds
-- statement:
--   The multi-step service design model of Bellos and Kavadias.
--
--   A service process has steps $i \in \mathcal J = \{1,\dots,n\}$. At each step the provider invests an effort $\delta_i \in [0,1]$ and charges one price $\pi$ for the whole service.
--
--   1. **Parameters.** For each step: functional values $V^H_i > V^L_i \ge 0$ at full and minimal effort; standard deviations $\sigma^H_i, \sigma^L_i \ge 0$ of the experience at full and minimal effort, with $\sigma^H_i \ne \sigma^L_i$ (the step is *routine* if $\sigma^H_i < \sigma^L_i$ and *non-routine* if $\sigma^H_i > \sigma^L_i$); a unit cost $c_i$; technical couplings $\beta_{j,i}$ (how much the functional value at step $j$ enhances that at step $i$), with $\beta_{i,i} = 1$, $\beta_{j,i} \in [0,1)$ for $j \ne i$ and $\sum_{i \ne j}\beta_{j,i} \in [0,1)$; and $c_i \in (\sum_{j\ne i}\beta_{j,i}, 1)$. Globally: a risk aversion $r > 0$, a reservation profit $\pi_0 \ge 0$, and a correlation matrix $\mathbf P$ with $[\mathbf P]_{i,i} = 1$, $[\mathbf P]_{i,j} = \rho_{i,j} \in (-1,1)$ for $i \ne j$, symmetric and positive definite. These are the *standing assumptions*.
--
--   2. **Values and variabilities.** For an effort vector $\delta$,
--   $$V_i = \delta_i V^H_i + (1-\delta_i)V^L_i, \qquad \mathcal V_i = \sum_{j=1}^n \beta_{j,i}V_j, \qquad \sigma_i = \delta_i\sigma^H_i + (1-\delta_i)\sigma^L_i.$$
--
--   3. **Utility and the design problem.** The customers' mean-variance net utility is
--   $$\mathcal U(\delta,\pi) = \sum_{i=1}^n \mathcal V_i - \frac r2\Big(\sum_{i=1}^n \sigma_i^2 + 2\sum\sum_{i<j}\rho_{i,j}\sigma_i\sigma_j\Big) - \pi.$$
--   A design $(\delta,\pi)$ is *feasible* if $0 \le \delta_i \le 1$ for all $i$ and $\pi - \sum_i V_i c_i \ge \pi_0$. An *optimal design* is a feasible pair maximizing $\mathcal U$ over all feasible pairs, and an *optimal effort* $\delta^*$ is the effort of an optimal design. The function $\delta^*$ of the parameters returns an optimal effort when one exists.
--
--   4. **Auxiliary objects of the analysis.** The price $\tilde\pi(\delta) = \pi_0 + \sum_i V_i c_i$ and $\tilde{\mathcal U}(\delta) = \mathcal U(\delta,\tilde\pi(\delta))$; the effective cost $\tilde c_i = c_i - \sum_{m\ne i}\beta_{i,m}$; the Hessian entries $-r(\sigma^H_i-\sigma^L_i)(\sigma^H_j-\sigma^L_j)\rho_{i,j}$; the partial derivative
--   $$g_i(\delta) = (1-\tilde c_i)(V^H_i-V^L_i) - r(\sigma^H_i-\sigma^L_i)\sum_{j=1}^n\big(\delta_j(\sigma^H_j-\sigma^L_j)+\sigma^L_j\big)\rho_{i,j};$$
--   the closed form
--   $$\hat\delta_i = \sum_{j=1}^n \frac{(1-\tilde c_j)(V^H_j-V^L_j)}{r(\sigma^H_i-\sigma^L_i)(\sigma^H_j-\sigma^L_j)}[\mathbf P^{-1}]_{i,j} - \frac{\sigma^L_i}{\sigma^H_i-\sigma^L_i};$$
--   and the thresholds
--   $$\underline{\Delta V}_i = \frac{r(\sigma^H_i-\sigma^L_i)|\mathbf P|}{(1-\tilde c_i)|\mathbf P[-i;-i]|}\Big(\sigma^L_i - \sum_{j\in\mathcal J\setminus i}\frac{(1-\tilde c_j)(V^H_j-V^L_j)(-1)^{i+j}|\mathbf P[-j;-i]|}{r(\sigma^H_j-\sigma^L_j)|\mathbf P|}\Big),$$
--   and $\overline{\Delta V}_i$, the same expression with $\sigma^H_i$ in place of $\sigma^L_i$ in the bracket. Here $\mathbf P[-j;-i]$ is $\mathbf P$ with row $j$ and column $i$ removed. The *interior condition* is $V^H_i - V^L_i \in (\underline{\Delta V}_i, \overline{\Delta V}_i)$ for all $i$. *No technical coupling* means $\beta_{j,i} = 0$ for $j \ne i$, the paper's simplification for the rest of §4. Finally, the parameters can be perturbed one coordinate at a time: $c_i$, $V^H_i$ (with $V^L_i$ fixed) or $\sigma^H_i$ (with $\sigma^L_i$ fixed) replaced by a value $t$.
--
--   These objects are shared by every statement of the mission: Proposition 1 identifies $\delta^*$ with $\hat\delta$, and Proposition 3 differentiates $\delta^*$ in the perturbed parameters.
--
--   **Formalization Note** Steps are `Fin n`, 0-based. All values are real. The utility is defined by its mean-variance expression; no random variables appear. $(-1)^{i+j}|\mathbf P[-j;-i]|$ is written `adjugate P i j` and $|\mathbf P[-i;-i]|$ is `adjugate P i i` (Mathlib's `adjugate_fin_succ_eq_det_submatrix`). Two hypotheses are added to the page: $r > 0$ (the page has $r \ge 0$, but Proposition 1 divides by $r$) and $\sigma^H_i \ne \sigma^L_i$ (every step is routine or non-routine, and Proposition 1 divides by $\sigma^H_i - \sigma^L_i$); $\sigma^L_i, \sigma^H_i \ge 0$ is implicit in their being standard deviations. Positive definiteness is the page's p. 26 statement. The optimal-effort function returns $0$ when no optimal design exists; under the standing and interior assumptions an optimum exists and is unique. Division by zero and the inverse of a singular matrix return $0$ in Lean; the standing assumptions exclude every such case.
-- source:
--   Bellos & Kavadias, Service design for a holistic customer experience: a process framework, authors' manuscript (Management Science 2020, doi:10.1287/mnsc.2020.3609), pp. 8–14 and 26–27, §3.2, §3.3, §4 (interior condition p. 13, Σβ → 0 p. 14), proof of Proposition 1

import Mathlib

namespace HolisticService.Effort

/-- The primitives of the multi-step service design model of Bellos & Kavadias (§3.2–§3.3, pp. 8–12).
Steps are `Fin n` (0-based: Lean step `i` is the paper's step `i + 1`). `β j i` is the paper's
`β_{j,i}`, the extent to which the functional value at step `j` enhances the one at step `i`;
`P i j` is the correlation `ρ_{i,j}` of the experiential values at steps `i` and `j`. -/
structure Params (n : ℕ) where
  /-- `V^H_i`, the functional value of step `i` at full effort -/
  VH : Fin n → ℝ
  /-- `V^L_i`, the functional value of step `i` at minimal effort -/
  VL : Fin n → ℝ
  /-- `σ^H_i`, the standard deviation of the experience at full effort -/
  sH : Fin n → ℝ
  /-- `σ^L_i`, the standard deviation of the experience at minimal effort -/
  sL : Fin n → ℝ
  /-- `c_i`, the unit cost of functional value at step `i` -/
  c : Fin n → ℝ
  /-- `β j i = β_{j,i}` (technical coupling) -/
  β : Fin n → Fin n → ℝ
  /-- `r`, the customers' risk aversion -/
  r : ℝ
  /-- `π₀`, the provider's reservation profit -/
  π0 : ℝ
  /-- `P`, the correlation matrix, `P i j = ρ_{i,j}` -/
  P : Matrix (Fin n) (Fin n) ℝ

variable {n : ℕ}

/-- The standing assumptions of §3.2–§3.3 (pp. 8–12) and of the proof of Proposition 1 (p. 26):
`V^H_i > V^L_i ≥ 0`; `β_{i,i} = 1`, `β_{j,i} ∈ [0,1)` for `j ≠ i`, `Σ_{i≠j} β_{j,i} ∈ [0,1)` (p. 9);
`c_i ∈ (Σ_{j≠i} β_{j,i}, 1)` (p. 12); `π₀ ≥ 0`; `r > 0` (added: the page has `r ≥ 0`, Proposition 1
divides by `r`); `σ^L_i, σ^H_i ≥ 0` (standard deviations); `σ^H_i ≠ σ^L_i` (added: every step is routine
or non-routine); `P` symmetric with unit diagonal and off-diagonal entries in `(-1,1)` (p. 11), and
positive definite (p. 26). -/
def Params.Standing (M : Params n) : Prop :=
  (∀ i, 0 ≤ M.VL i ∧ M.VL i < M.VH i) ∧
  (∀ i, M.β i i = 1) ∧
  (∀ j i, j ≠ i → 0 ≤ M.β j i ∧ M.β j i < 1) ∧
  (∀ j, 0 ≤ ∑ i ∈ Finset.univ.erase j, M.β j i ∧ ∑ i ∈ Finset.univ.erase j, M.β j i < 1) ∧
  (∀ i, ∑ j ∈ Finset.univ.erase i, M.β j i < M.c i ∧ M.c i < 1) ∧
  0 ≤ M.π0 ∧ 0 < M.r ∧
  (∀ i, 0 ≤ M.sL i ∧ 0 ≤ M.sH i) ∧
  (∀ i, M.sH i ≠ M.sL i) ∧
  M.P.IsSymm ∧ (∀ i, M.P i i = 1) ∧ (∀ i j, i ≠ j → -1 < M.P i j ∧ M.P i j < 1) ∧
  M.P.PosDef

/-- `V_i = δ_i V^H_i + (1 − δ_i) V^L_i` (p. 8). -/
def Vval (M : Params n) (δ : Fin n → ℝ) (i : Fin n) : ℝ :=
  δ i * M.VH i + (1 - δ i) * M.VL i

/-- `𝒱_i = Σ_j β_{j,i} V_j` (p. 9). -/
def calV (M : Params n) (δ : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, M.β j i * Vval M δ j

/-- `σ_i = δ_i σ^H_i + (1 − δ_i) σ^L_i` (p. 9). -/
def sig (M : Params n) (δ : Fin n → ℝ) (i : Fin n) : ℝ :=
  δ i * M.sH i + (1 - δ i) * M.sL i

/-- The customers' mean-variance net utility (p. 12):
`𝒰(δ, π) = Σ_i 𝒱_i − (r/2)(Σ_i σ_i² + 2 Σ Σ_{i<j} ρ_{i,j} σ_i σ_j) − π`. -/
noncomputable def utility (M : Params n) (δ : Fin n → ℝ) (π : ℝ) : ℝ :=
  ∑ i, calV M δ i
    - M.r / 2 * (∑ i, sig M δ i ^ 2
        + 2 * ∑ i, ∑ j, if i < j then M.P i j * sig M δ i * sig M δ j else 0)
    - π

/-- Feasibility in the design problem of §3.3 (p. 12): `0 ≤ δ_i ≤ 1` for every step, and
`π − Σ_i V_i c_i ≥ π₀`. -/
def Feasible (M : Params n) (δ : Fin n → ℝ) (π : ℝ) : Prop :=
  (∀ i, 0 ≤ δ i ∧ δ i ≤ 1) ∧ M.π0 ≤ π - ∑ i, Vval M δ i * M.c i

/-- An optimal design: a feasible `(δ, π)` maximizing `𝒰` over all feasible pairs (§3.3, p. 12). -/
def IsOptimalDesign (M : Params n) (δ : Fin n → ℝ) (π : ℝ) : Prop :=
  Feasible M δ π ∧ ∀ δ' π', Feasible M δ' π' → utility M δ' π' ≤ utility M δ π

/-- `δ` is an optimal effort `δ*`: the effort of some optimal design. -/
def IsOptimalEffort (M : Params n) (δ : Fin n → ℝ) : Prop :=
  ∃ π, IsOptimalDesign M δ π

/-- The optimal effort as a function of the parameters: an optimal effort of the §3.3 problem when one
exists (Proposition 1 makes it unique under the standing and interior assumptions), and `0` otherwise. -/
noncomputable def optEffort (M : Params n) : Fin n → ℝ :=
  open Classical in
  if h : ∃ δ, IsOptimalEffort M δ then Classical.choose h else 0

/-- The optimal price for a given effort (proof of Proposition 1, p. 26):
`π̃(δ) = π₀ + Σ_i V_i c_i`. -/
def πtil (M : Params n) (δ : Fin n → ℝ) : ℝ :=
  M.π0 + ∑ i, Vval M δ i * M.c i

/-- `Ũ(δ) = 𝒰(δ, π̃(δ))` (proof of Proposition 1, p. 26). -/
noncomputable def Utilde (M : Params n) (δ : Fin n → ℝ) : ℝ :=
  utility M δ (πtil M δ)

/-- The effective cost `c_j − Σ_{m≠j} β_{j,m}` (Proposition 1, p. 13). -/
def ctil (M : Params n) (j : Fin n) : ℝ :=
  M.c j - ∑ m ∈ Finset.univ.erase j, M.β j m

/-- The printed Hessian of `Ũ` (proof of Proposition 1, p. 26), entry `(i,j)`:
`−r (σ^H_i − σ^L_i)(σ^H_j − σ^L_j) ρ_{i,j}`. -/
def hessU (M : Params n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => -M.r * (M.sH i - M.sL i) * (M.sH j - M.sL j) * M.P i j

/-- The printed partial derivative (p. 27):
`∂Ũ/∂δ_i = (1 − (c_i − Σ_{m≠i} β_{i,m}))(V^H_i − V^L_i) − r(σ^H_i − σ^L_i) Σ_j (δ_j(σ^H_j − σ^L_j) + σ^L_j) ρ_{i,j}`. -/
def gradU (M : Params n) (δ : Fin n → ℝ) (i : Fin n) : ℝ :=
  (1 - ctil M i) * (M.VH i - M.VL i)
    - M.r * (M.sH i - M.sL i) * ∑ j, (δ j * (M.sH j - M.sL j) + M.sL j) * M.P i j

/-- The closed form of Proposition 1 (p. 13, p. 27):
`δ̂_i = Σ_j (1 − (c_j − Σ_{m≠j} β_{j,m}))(V^H_j − V^L_j) / (r(σ^H_i − σ^L_i)(σ^H_j − σ^L_j)) [P⁻¹]_{i,j}
  − σ^L_i/(σ^H_i − σ^L_i)`. -/
noncomputable def δhat (M : Params n) (i : Fin n) : ℝ :=
  ∑ j, (1 - ctil M j) * (M.VH j - M.VL j) / (M.r * (M.sH i - M.sL i) * (M.sH j - M.sL j)) * M.P⁻¹ i j
    - M.sL i / (M.sH i - M.sL i)

/-- The lower threshold `ΔV_i` (proof of Proposition 1, p. 27), with `(−1)^{i+j}|P[−j;−i]|` written
as `adjugate P i j` and `|P[−i;−i]|` as `adjugate P i i`:
`r(σ^H_i − σ^L_i)|P| / ((1 − c̃_i)|P[−i;−i]|) · (σ^L_i − Σ_{j≠i} (1 − c̃_j)(V^H_j − V^L_j)(−1)^{i+j}|P[−j;−i]| / (r(σ^H_j − σ^L_j)|P|))`. -/
noncomputable def ΔVlo (M : Params n) (i : Fin n) : ℝ :=
  M.r * (M.sH i - M.sL i) * M.P.det / ((1 - ctil M i) * M.P.adjugate i i) *
    (M.sL i - ∑ j ∈ Finset.univ.erase i,
      (1 - ctil M j) * (M.VH j - M.VL j) * M.P.adjugate i j / (M.r * (M.sH j - M.sL j) * M.P.det))

/-- The upper threshold `ΔV̄_i` (proof of Proposition 1, p. 27): as `ΔVlo` with `σ^H_i` in place of
`σ^L_i` in the bracket. -/
noncomputable def ΔVhi (M : Params n) (i : Fin n) : ℝ :=
  M.r * (M.sH i - M.sL i) * M.P.det / ((1 - ctil M i) * M.P.adjugate i i) *
    (M.sH i - ∑ j ∈ Finset.univ.erase i,
      (1 - ctil M j) * (M.VH j - M.VL j) * M.P.adjugate i j / (M.r * (M.sH j - M.sL j) * M.P.det))

/-- The interior condition of §4 (p. 13): `V^H_i − V^L_i ∈ (ΔV_i, ΔV̄_i)` for every step `i`. -/
def Interior (M : Params n) : Prop :=
  ∀ i, ΔVlo M i < M.VH i - M.VL i ∧ M.VH i - M.VL i < ΔVhi M i

/-- The simplification of the rest of §4 (p. 14), `Σ_{j≠i} β_{i,j} → 0`: no technical coupling,
`β_{j,i} = 0` for `j ≠ i`. -/
def NoTechCoupling (M : Params n) : Prop :=
  ∀ j i, j ≠ i → M.β j i = 0

/-- The parameters with `c_i` replaced by `t`, all else fixed. -/
def withC (M : Params n) (i : Fin n) (t : ℝ) : Params n :=
  { M with c := Function.update M.c i t }

/-- The parameters with `V^H_i` replaced by `t`, all else fixed (in particular `V^L_i`). -/
def withVH (M : Params n) (i : Fin n) (t : ℝ) : Params n :=
  { M with VH := Function.update M.VH i t }

/-- The parameters with `σ^H_i` replaced by `t`, all else fixed (in particular `σ^L_i`). -/
def withSH (M : Params n) (i : Fin n) (t : ℝ) : Params n :=
  { M with sH := Function.update M.sH i t }

end HolisticService.Effort


