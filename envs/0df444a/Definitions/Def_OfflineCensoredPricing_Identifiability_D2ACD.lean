-- Prove2me | Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD
-- name    : OfflineCensoredPricing_Identifiability_D2ACD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:35.927985+00:00
-- url     : https://prove2.me/theorems/8f9c4537-ed2d-4a95-a019-a06dba22ed1c
-- title:
--   Algorithm 1 (D2ACD), p. 17 — data-driven algorithm under censored demand: quantile regression for b̂, empirical optimistic/pessimistic revenues, minimax price
-- statement:
--   The Data-Driven Algorithm under Censored Demand (D2ACD), Algorithm 1 of Bu, Simchi-Levi and Wang. Its inputs are the public data $y$, $[\underline p,\bar p]$, $[\underline b,\bar b]$, the pairs $(p_i, y_i)$ and the censored sales $\{S^j_i : i \in [K], j \in [N_i]\}$; it never uses $b$ or $F_\xi$.
--
--   **Step 1 (price sensitivity).** For each $i$, $\hat F^{SAA}_i(t) = \#\{j : S^j_i \le t\}/N_i$ is the empirical c.d.f., $\hat\beta_{i,1} < \dots < \hat\beta_{i,\hat M_i}$ are its breakpoints (the distinct sample values), and the modified quantile function is
--   $$\hat F^{-1}_i(x) = \begin{cases} \dfrac{(x - \hat F^{SAA}_i(\hat\beta_{i,k}))(\hat\beta_{i,k+1} - \hat\beta_{i,k})}{\hat F^{SAA}_i(\hat\beta_{i,k+1}) - \hat F^{SAA}_i(\hat\beta_{i,k})} + \hat\beta_{i,k}, & x \in (\hat F^{SAA}_i(\hat\beta_{i,k}), \hat F^{SAA}_i(\hat\beta_{i,k+1})],\ k \in [\hat M_i - 1],\\ \hat\beta_{i,1}, & x \le \hat F^{SAA}_i(\hat\beta_{i,1}).\end{cases}$$
--   With $\hat\gamma_i = \frac1{N_i}\sum_j \mathbb 1\{S^j_i < y_i\}$ and $\hat\gamma_{\min} = \min_i \hat\gamma_i$, the sensitivity estimate is the regression slope
--   $$\hat b = \arg\min_{b' \in [\underline b,\bar b]} \min_{a'\in\mathbb R} \sum_{i=1}^K \big(\hat F^{-1}_i(\hat\gamma_{\min}) - (a' - b'p_i)\big)^2.$$
--
--   **Step 2 (robust revenues).** $\hat i^* = \arg\max_i\{y_i + \hat bp_i\}$, $\hat\lambda = y_{\hat i^*} + \hat bp_{\hat i^*}$, $\hat\gamma = \max_i \hat\gamma_i$, and with $N^* = N_{\hat i^*}$:
--   $$\hat R(p) = p\cdot\frac1{N^*}\sum_{j}\min\{S^j_{\hat i^*} + \hat bp_{\hat i^*} - \hat bp,\ y\},$$
--   $$\hat R_1(p) = p\Big(-\hat\gamma\hat bp + \frac1{N^*}\sum_j(S^j_{\hat i^*} + \hat bp_{\hat i^*}) + (1-\hat\gamma)(y - \hat\lambda)\Big),\quad \hat R_2(p) = p\Big(-\hat bp + \frac1{N^*}\sum_j(S^j_{\hat i^*} + \hat bp_{\hat i^*})\Big),$$
--   $\hat{\tilde p} = (\hat\lambda - y)/\hat b$, $\hat R_{\max}(p) = \mathbb 1\{p<\hat{\tilde p}\}\hat R(p) + \mathbb 1\{p \ge \hat{\tilde p}\}\hat R_1(p)$ and $\hat R_{\min}(p) = \mathbb 1\{p<\hat{\tilde p}\}\hat R(p) + \mathbb 1\{p \ge \hat{\tilde p}\}\hat R_2(p)$.
--
--   **Step 3 (price).** $\hat p^*_{\max} = \arg\max_{[\underline p,\bar p]}\hat R_{\max}$, $\hat p^*_{\min} = \arg\max_{[\underline p,\bar p]}\hat R_{\min}$, $\hat W_{\max}(p) = \hat R_{\max}(\hat p^*_{\max}) - \hat R_{\max}(p)$, $\hat W_{\min}(p) = \hat R_{\min}(\hat p^*_{\min}) - \hat R_{\min}(p)$, and the output is
--   $$p^{\mathrm{D2ACD}} = \arg\min_{p\in[\underline p,\bar p]} \max\{\hat W_{\max}(p), \hat W_{\min}(p)\}.$$
--
--   The algorithm estimates the two robust revenue curves rather than the true revenue, and prices to balance the two estimated regrets; Lemmas 1, D.1, D.2, 2 and Theorem 2 analyse it, and Theorem 1 uses it as the witness of identifiability.
--
--   **Formalization Note** Every component is a function of the public inputs, the sample sizes and the censored sales only. Choices where the page leaves a selection open: $\hat b$ is the clamp to $[\underline b,\bar b]$ of the unconstrained least-squares slope $b^\dagger = -\sum_i(p_i - \bar p_{\mathrm{avg}})(\hat d_i - \hat d_{\mathrm{avg}})/\sum_i (p_i - \bar p_{\mathrm{avg}})^2$ with $\hat d_i = \hat F^{-1}_i(\hat\gamma_{\min})$ ((D.8), p. 44), which is the arg min of line 9 whenever the prices are not all equal; $\hat i^*$ is the least maximizing index; every arg max/arg min over $[\underline p,\bar p]$ is the largest one; $\hat F^{-1}_i(x) = \hat\beta_{i,\hat M_i}$ above $\hat F^{SAA}_i(\hat\beta_{i,\hat M_i}) = 1$ (never queried). Outside the algorithm's domain the output is $\underline p$: when some $N_i = 0$, and when no minimizer in Step 3 exists (impossible on genuine censored sales, for which $\hat R_{\max}$, $\hat R_{\min}$ are continuous). Indices are $0$-based; the type `Fin K` is assumed nonempty so that $\hat i^*$ is an index.
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), p. 17, Algorithm 1 (D2ACD), lines 1–24; γ̂ᵢ p. 10; b† (D.8) p. 44

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model

namespace OfflineCensoredPricing.Identifiability

open Set

/-!
# Algorithm 1 (D2ACD), p. 17

Every object below is a function of the public inputs `P` (the inventory `y`, the ranges `[p̲, p̄]`,
`[b̲, b̄]`, the historical prices `pᵢ` and inventories `yᵢ`), the sample sizes `Nv` and the censored
sales `S`, and of nothing else. Indices are `0`-based.
-/

variable {K : ℕ}

/-! ### Step 1: estimating the price sensitivity (lines 1–9) -/

/-- Line 4: the empirical c.d.f. `F̂^SAA_i(t) = #{j : S^j_i ≤ t} / Nᵢ`. -/
noncomputable def ecdfS {Nv : Fin K → ℕ} (S : Sample K Nv) (i : Fin K) (t : ℝ) : ℝ :=
  ((Finset.univ.filter (fun j => S i j ≤ t)).card : ℝ) / (Nv i : ℝ)

/-- Line 5: the breakpoints `β̂_{i,1} < ⋯ < β̂_{i,M̂ᵢ}` of `F̂^SAA_i`, i.e. the distinct sample values
at price `pᵢ` in increasing order (`M̂ᵢ` is the length of the list). -/
noncomputable def breakpts {Nv : Fin K → ℕ} (S : Sample K Nv) (i : Fin K) : List ℝ :=
  (Finset.univ.image (S i)).sort (· ≤ ·)

/-- Lines 6–7: the modified quantile function `F̂ᵢ⁻¹`. With `β̂_k` the breakpoints and `F̂_k = F̂^SAA_i(β̂_k)`
(`k = 0, …, M̂ᵢ − 1`):
* `F̂ᵢ⁻¹(x) = β̂_0` if `x ≤ F̂_0`;
* `F̂ᵢ⁻¹(x) = (x − F̂_k)(β̂_{k+1} − β̂_k)/(F̂_{k+1} − F̂_k) + β̂_k` if `x ∈ (F̂_k, F̂_{k+1}]`;
* `F̂ᵢ⁻¹(x) = β̂_{M̂ᵢ−1}` if `x > F̂_{M̂ᵢ−1} = 1` (never queried by the algorithm);
* `0` for an empty sample. The intervals `(F̂_k, F̂_{k+1}]` are disjoint, so at most one summand is
  nonzero. -/
noncomputable def quantMod {Nv : Fin K → ℕ} (S : Sample K Nv) (i : Fin K) (x : ℝ) : ℝ :=
  let bs := breakpts S i
  let M := bs.length
  let β : ℕ → ℝ := fun k => bs.getD k 0
  let F : ℕ → ℝ := fun k => ecdfS S i (β k)
  if M = 0 then 0
  else if x ≤ F 0 then β 0
  else if F (M - 1) < x then β (M - 1)
  else ∑ k ∈ Finset.range (M - 1),
    if F k < x ∧ x ≤ F (k + 1) then (x - F k) * (β (k + 1) - β k) / (F (k + 1) - F k) + β k
    else 0

/-- `γ̂ᵢ = (1/Nᵢ) ∑ⱼ 1{S^j_i < yᵢ}` (p. 10). -/
noncomputable def gammaHat (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) (i : Fin K) : ℝ :=
  ((Finset.univ.filter (fun j => S i j < P.yh i)).card : ℝ) / (Nv i : ℝ)

/-- Line 1: `γ̂_min = min_{i ∈ [K]} γ̂ᵢ`. -/
noncomputable def gammaHatMin (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) : ℝ :=
  ⨅ i, gammaHat P S i

/-- `d̂ᵢ = F̂ᵢ⁻¹(γ̂_min)`, the regression responses of line 9 ((D.8), p. 44). -/
noncomputable def dHat (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) (i : Fin K) : ℝ :=
  quantMod S i (gammaHatMin P S)

/-- The unconstrained least-squares slope of line 9 ((D.8), p. 44):
`b† = −∑ᵢ (pᵢ − p̄_avg)(d̂ᵢ − d̂_avg) / ∑ᵢ (pᵢ − p̄_avg)²`. -/
noncomputable def bDagger (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) : ℝ :=
  let pAvg := (1 / (K : ℝ)) * (∑ i, P.p i)
  let dAvg := (1 / (K : ℝ)) * (∑ i, dHat P S i);
  -(∑ i, (P.p i - pAvg) * (dHat P S i - dAvg)) / (∑ i, (P.p i - pAvg) ^ 2)

/-- Line 9: `b̂ = arg min_{b' ∈ [b̲, b̄]} min_{a' ∈ ℝ} ∑ᵢ (F̂ᵢ⁻¹(γ̂_min) − (a' − b' pᵢ))²`, written as the
clamp of `b†` to `[b̲, b̄]` (the minimizer of this strictly convex quadratic in `b'` whenever the prices
`pᵢ` are not all equal). -/
noncomputable def bHat (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) : ℝ :=
  max P.blo (min P.bhi (bDagger P S))

/-! ### Step 2: estimating the optimistic and pessimistic revenues (lines 10–18) -/

/-- The indices attaining `max_{i ∈ [K]} {yᵢ + b̂ pᵢ}`. -/
noncomputable def iStarSet (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) : Finset (Fin K) :=
  Finset.univ.filter (fun i => ∀ j, P.yh j + bHat P S * P.p j ≤ P.yh i + bHat P S * P.p i)

lemma iStarSet_nonempty [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) :
    (iStarSet P S).Nonempty := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => P.yh i + bHat P S * P.p i) Finset.univ_nonempty
  exact ⟨i, by simpa [iStarSet] using fun j => hi j (Finset.mem_univ j)⟩

/-- Line 11: `î* = arg max_{i ∈ [K]} {yᵢ + b̂ pᵢ}`, the least index among ties. -/
noncomputable def iStar [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) : Fin K :=
  (iStarSet P S).min' (iStarSet_nonempty P S)

/-- Line 12: `λ̂ = y_{î*} + b̂ p_{î*}`. -/
noncomputable def lamHat [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) : ℝ :=
  P.yh (iStar P S) + bHat P S * P.p (iStar P S)

/-- Line 12: `γ̂ = max_{i ∈ [K]} γ̂ᵢ`. -/
noncomputable def gammaHatMax (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) : ℝ :=
  ⨆ i, gammaHat P S i

/-- `(1/N_{î*}) ∑ⱼ (S^j_{î*} + b̂ p_{î*})`, the average used in lines 14–15. -/
noncomputable def shiftedMean [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) : ℝ :=
  (∑ j, (S (iStar P S) j + bHat P S * P.p (iStar P S))) / (Nv (iStar P S) : ℝ)

/-- Line 13: `R̂(q) = q · (1/N_{î*}) ∑ⱼ min{S^j_{î*} + b̂ p_{î*} − b̂ q, y}`. -/
noncomputable def RHat [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) (q : ℝ) : ℝ :=
  q * ((∑ j, min (S (iStar P S) j + bHat P S * P.p (iStar P S) - bHat P S * q) P.y) /
    (Nv (iStar P S) : ℝ))

/-- Line 14: `R̂₁(q) = q · (−γ̂ b̂ q + (1/N_{î*}) ∑ⱼ (S^j_{î*} + b̂ p_{î*}) + (1 − γ̂)(y − λ̂))`. -/
noncomputable def R1Hat [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) (q : ℝ) : ℝ :=
  q * (-(gammaHatMax P S) * bHat P S * q + shiftedMean P S +
    (1 - gammaHatMax P S) * (P.y - lamHat P S))

/-- Line 15: `R̂₂(q) = q · (−b̂ q + (1/N_{î*}) ∑ⱼ (S^j_{î*} + b̂ p_{î*}))`. -/
noncomputable def R2Hat [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) (q : ℝ) : ℝ :=
  q * (-(bHat P S) * q + shiftedMean P S)

/-- Line 16: `p̂~ = (λ̂ − y)/b̂`. -/
noncomputable def pTildeHat [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) : ℝ :=
  (lamHat P S - P.y) / bHat P S

/-- Line 17: `R̂_max(q) = 1{q < p̂~} R̂(q) + 1{q ≥ p̂~} R̂₁(q)`. -/
noncomputable def RHatMax [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) (q : ℝ) :
    ℝ :=
  if q < pTildeHat P S then RHat P S q else R1Hat P S q

/-- Line 18: `R̂_min(q) = 1{q < p̂~} R̂(q) + 1{q ≥ p̂~} R̂₂(q)`. -/
noncomputable def RHatMin [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) (q : ℝ) :
    ℝ :=
  if q < pTildeHat P S then RHat P S q else R2Hat P S q

/-! ### Step 3: computing the algorithm's price (lines 19–24) -/

/-- Line 20: `p̂*_max = arg max_{q ∈ [p̲, p̄]} R̂_max(q)` (the largest maximizer). -/
noncomputable def pHatMax [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) : ℝ :=
  argmaxIcc P.plo P.phi (RHatMax P S)

/-- Line 20: `p̂*_min = arg max_{q ∈ [p̲, p̄]} R̂_min(q)` (the largest maximizer). -/
noncomputable def pHatMin [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) : ℝ :=
  argmaxIcc P.plo P.phi (RHatMin P S)

/-- Line 21: `Ŵ_max(q) = R̂_max(p̂*_max) − R̂_max(q)`. -/
noncomputable def WHatMax [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) (q : ℝ) :
    ℝ :=
  RHatMax P S (pHatMax P S) - RHatMax P S q

/-- Line 22: `Ŵ_min(q) = R̂_min(p̂*_min) − R̂_min(q)`. -/
noncomputable def WHatMin [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) (q : ℝ) :
    ℝ :=
  RHatMin P S (pHatMin P S) - RHatMin P S q

/-- The set of minimizers over `[p̲, p̄]` of `max{Ŵ_max(q), Ŵ_min(q)}`. -/
def pD2ACDSet [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) : Set ℝ :=
  {q ∈ Icc P.plo P.phi | ∀ q' ∈ Icc P.plo P.phi,
    max (WHatMax P S q) (WHatMin P S q) ≤ max (WHatMax P S q') (WHatMin P S q')}

/-- Line 23: `p^D2ACD = arg min_{q ∈ [p̲, p̄]} max{Ŵ_max(q), Ŵ_min(q)}`, the largest minimizer. If no
minimizer exists (possible only for inputs that are not censored sales), the output is `p̲`. -/
noncomputable def pD2ACD [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv) : ℝ :=
  open Classical in
  if (pD2ACDSet P S).Nonempty then sSup (pD2ACDSet P S) else P.plo

/-- **D2ACD** (Algorithm 1, p. 17) as a data-driven algorithm for the public inputs `P`. A dataset
with an empty sample at some historical price is outside the algorithm's domain; there it outputs
`p̲`. -/
noncomputable def d2acd [NeZero K] (P : Public K) : Algorithm K :=
  open Classical in
  fun Nv S => if ∃ i, Nv i = 0 then P.plo else pD2ACD P S

end OfflineCensoredPricing.Identifiability


