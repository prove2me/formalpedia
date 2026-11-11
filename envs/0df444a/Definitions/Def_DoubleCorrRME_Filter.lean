-- Prove2me | Definitions.Def_DoubleCorrRME_Filter
-- name    : DoubleCorrRME_Filter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:21.650199+00:00
-- url     : https://prove2.me/theorems/fb7968d4-bbbe-42da-8c93-a313cf1a7acc
-- title:
--   Regular users, the capped update, soft losses and Algorithm 3 as a relation
-- statement:
--   This definition collects the objects of the sample-level filter analysis (§5.2).
--
--   1. **Context**: clean data $z$, observed data $x$, the set $B$ of users replaced by the user-level adversary, the index set $\mathcal I$ of the first stable reference and the mean $\mu$, with the corruption guarantee of Definition 1.1, $|\mathcal I|\ge(1-\alpha')Nn$, and $\{z_k:k\in\mathcal I\}$ $(\alpha',\Delta)$-stable with respect to $(\mu,I_d)$.
--   2. **Regular good users** (Definition 5.2): $\mathcal G=[N]\setminus B$, $D_i=\{j:x_{i,j}\neq z^{\mathrm{tr}}_{i,j}\}$, $\theta_0=K_0\alpha'/\varepsilon$, $\mathcal R=\{i\in\mathcal G:|D_i|\le\theta_0n\}$, and the matched set $\mathcal S_g=\{(i,j):i\in\mathcal R,u_i>0,j\notin D_i\}$.
--   3. **Capped update** (Definition 5.5, Algorithm 5): $\gamma=\theta_1/(2\max_{i\in\mathcal A,j}\tilde\tau_{i,j})$, $w^{(r)}_{i,j}=w_{i,j}(1-\gamma\tilde\tau_{i,j})^r$, $u^{(r+1)}_i=u^{(r)}_i\mathbf 1\{\ell_i(w^{(r+1)})<\theta_1\}$, stopped at $R_{\mathrm{stop}}=\min\{r:\langle p^{(r)},\tilde\tau\rangle\le\sigma_0/8\}$.
--   4. **Soft losses** (Definitions 5.8, 5.12): $L_g^{(t)},L_b^{(t)}$, the decrease $p^{(t,r)}-\tilde p^{(t,r+1)}$ with $\tilde p^{(t,r+1)}=\mathrm{diag}(u^{(t,r)})w^{(t,r+1)}$ summed over $r<R_{\mathrm{stop}}$ on $\mathcal S_g$ and on its complement, and $0$ at rounds without an update.
--   5. **Algorithm 3** with successful approximations: a trajectory of weights, scores, epoch estimates $\hat\Lambda_k$ and stopping times. It starts at $u\equiv1/N$, $w\equiv1/n$. Each epoch has $T=\lceil8\log(2d)\rceil$ rounds and starts with $\hat\Lambda_k$ a $\nu$-approximation ($\nu=1/40$) of $\|M_s\|_2$ above $16C_Q\kappa$. Each round uses $\nu$-approximate QUE scores for the epoch's MMW density with $\eta=(1-\nu)/\hat\Lambda_k$, zero on inactive users, and applies the capped update when $\langle p,\tilde\tau\rangle>\hat\Lambda_k/10$. A complete run ends at an epoch boundary whose estimate is at most $16C_Q\kappa$.
--
--   **Formalization Note** The randomized subroutines (power method, Algorithm 6) are replaced by their success guarantees, as in Lemma 5.15's "conditioned on successful approximations". The stopping time is a relation, so no empty minimum is ever evaluated.
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Algorithm 3, p.31 (PDF p.32); Algorithm 5, p.32 (PDF p.33); Definitions 5.2, 5.3, 5.5, p.33 (PDF p.34); Definition 5.8, pp.36–37; Definition 5.12, p.39 (PDF p.40)

import Mathlib
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm
import Definitions.Def_DoubleCorrRME_Model
import Definitions.Def_DoubleCorrRME_Stability
import Definitions.Def_DoubleCorrRME_Params
import Definitions.Def_DoubleCorrRME_Weights

namespace DoubleCorrRME

/-!
# The sample-level filter: regular users, the capped update, soft losses, Algorithm 3

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…): Algorithm 3, p.31
(PDF p.32); Algorithm 5, p.32 (PDF p.33); Definitions 5.2, 5.3, Remark 5.4, Definition 5.5, p.33
(PDF p.34); Definition 5.8, pp.36–37 (PDF pp.37–38); Definition 5.12, p.39 (PDF p.40).

**Formalization Note.**
* **Context.** The lemmas of §5 talk about one realization: clean data `z`, observed data `x`, the
  set `B` of users replaced by the user-level adversary, the index set `ℐ` of the first stable
  reference (Lemma 4.1, Part 1) and the mean `µ`. `IsContext` collects the corruption guarantee of
  Definition 1.1 for `(z, x, B)`, `|ℐ| ≥ (1 − α′)Nn`, the `(α′, ∆)`-stability of
  `{z_k : k ∈ ℐ}` with respect to `(µ, I_d)`, and the §4.1 ranges `ε > 0`, `α ≥ 0`, `δ ∈ (0, 0.1)`.
  Here `α′ = alphaP C_ref …` and `∆ = deltaP C_∆ α′`. The data `x` are those passed to Algorithm 3;
  the lemmas are translation invariant, so they are stated in the original coordinates with `µ`.
* **Definition 5.2.** `𝒢 := [N] \ B`, `D_i := {j : x_{i,j} ≠ z^tr_{i,j}}`, `θ₀ := K₀α′/ε`,
  `ℛ := {i ∈ 𝒢 : |D_i| ≤ θ₀ n}`; all *defined* from the context.
* **Definition 5.5.** `w^(t,r)_{i,j} = w^(t)_{i,j}(1 − γτ̃_{i,j})^r` (Algorithm 5, line 4, the closed
  form of the recursion), and `u^(t,r+1)_i = u^(t,r)_i 1{ℓ_i(w^(t,r+1)) < θ₁}` (the recursion).
  `γ := θ₁/(2 max_{i∈𝒜, j} τ̃_{i,j})`; the maximum is a fold of `max` starting at `0`, which equals
  the paper's maximum since `τ̃ ≥ 0` and `σ₀ = ⟨p, τ̃⟩ > 0` makes some active score positive.
  The stopping time `R_stop := min{r ≥ 0 : ⟨p^(t,r), τ̃⟩ ≤ σ₀/8}` is carried as a relation
  (`IsRStop`), so no default value of an empty minimum is ever used.
* **Algorithm 3** is a relation on a trajectory (`Stage1Traj`): QUE rounds `t` are numbered
  consecutively across epochs; epoch `k` consists of the rounds `kT, …, kT + T − 1` with
  `T = ⌈8 log(2d)⌉`, and `Λ̂_k` is its power-method estimate. "Conditioned on successful
  power-method and QUE-score approximations" becomes hypotheses: `Λ̂_k` is a `ν`-approximation of
  `‖M_s(u^(kT), w^(kT))‖₂`, i.e. `(1 − ν)Λ₀ ≤ Λ̂_k ≤ (1 + ν)Λ₀`, and each `τ̃^(t)` is a
  `ν`-approximate QUE score matrix (Definition 3.9) for the MMW density of the epoch with
  `η = (1 − ν)/Λ̂_k` and gains `M_s(u^(s+1), w^(s+1))`, with `ν = 1/40`. The randomized subroutines
  themselves (power method, Algorithm 6) and the failure probabilities `δ_t` do not appear.
-/

/-- The approximation parameter `ν = 1/40` of Algorithm 3, line 2. -/
noncomputable def nu : ℝ := 1 / 40

/-- The epoch length `T = ⌈8 log(2d)⌉` of Algorithm 3, line 2. -/
noncomputable def epochLen (d : ℕ) : ℕ := ⌈8 * Real.log (2 * (d : ℝ))⌉₊

/-- `Λ̂` is a `ν`-approximation of `Λ₀`: `(1 − ν)Λ₀ ≤ Λ̂ ≤ (1 + ν)Λ₀`. -/
def IsNuApprox (ν Λ₀ Λhat : ℝ) : Prop := (1 - ν) * Λ₀ ≤ Λhat ∧ Λhat ≤ (1 + ν) * Λ₀

/-- The realization the lemmas of §5 live on (see the module note): Definition 1.1 for `(z, x, B)`,
the first stable reference `ℐ` of Lemma 4.1, Part 1, and the §4.1 ranges. -/
def IsContext (Cref CΔ : ℝ) {N n d : ℕ} (ε α δ : ℝ) (z x : Fin N → Fin n → Vec d)
    (B : Finset (Fin N)) (I : Finset (Fin N × Fin n)) (μ : Vec d) : Prop :=
  0 < ε ∧ 0 ≤ α ∧ 0 < δ ∧ δ < 1 / 10 ∧
    (B.card : ℝ) ≤ ε * N ∧
    ((Finset.univ.filter fun k : Fin N × Fin n => k.1 ∉ B ∧ x k.1 k.2 ≠ z k.1 k.2).card : ℝ) ≤
      α * N * n ∧
    (1 - alphaP Cref N n d α δ) * ((N : ℝ) * n) ≤ I.card ∧
    IsStable (fun k : Fin N × Fin n => z k.1 k.2) I (alphaP Cref N n d α δ)
      (deltaP CΔ (alphaP Cref N n d α δ)) μ 1

open Classical in
/-- Definition 5.2: `D_i := {j ∈ [n] : x_{i,j} ≠ z^tr_{i,j}}`. -/
noncomputable def Dset {N n d : ℕ} (z x : Fin N → Fin n → Vec d) (I : Finset (Fin N × Fin n))
    (μ : Vec d) (i : Fin N) : Finset (Fin n) :=
  Finset.univ.filter fun j => x i j ≠ ztr z I μ i j

open Classical in
/-- Definition 5.2: the regular good users `ℛ := {i ∈ 𝒢 : |D_i| ≤ θ₀ n}`, with `𝒢 := [N] \ B` and
`θ₀ := K₀α′/ε`. -/
noncomputable def regular {N n d : ℕ} (K0 α' ε : ℝ) (z x : Fin N → Fin n → Vec d)
    (B : Finset (Fin N)) (I : Finset (Fin N × Fin n)) (μ : Vec d) : Finset (Fin N) :=
  (Finset.univ \ B).filter fun i => ((Dset z x I μ i).card : ℝ) ≤ K0 * α' / ε * n

open Classical in
/-- Lemma 5.6: `𝒮_g := {(i, j) : i ∈ ℛ, u_i > 0, j ∉ D_i}` (matched regular-good samples). -/
noncomputable def goodSet {N n : ℕ} (R : Finset (Fin N)) (D : Fin N → Finset (Fin n))
    (u : Fin N → ℝ) : Finset (Fin N × Fin n) :=
  Finset.univ.filter fun k => k.1 ∈ R ∧ 0 < u k.1 ∧ k.2 ∉ D k.1

open Classical in
/-- `τ_max := max_{i ∈ 𝒜, j} τ̃_{i,j}` over the active users `𝒜 = {i : u_i > 0}` (as a fold of `max`
from `0`; see the module note). -/
noncomputable def tauMax {N n : ℕ} (u : Fin N → ℝ) (τ' : Fin N → Fin n → ℝ) : ℝ :=
  (Finset.univ.filter fun k : Fin N × Fin n => 0 < u k.1).fold max 0 fun k => τ' k.1 k.2

/-- Definition 5.5: `γ := θ₁ / (2 τ_max)`. -/
noncomputable def capGamma {N n : ℕ} (θ1 : ℝ) (u : Fin N → ℝ) (τ' : Fin N → Fin n → ℝ) : ℝ :=
  θ1 / (2 * tauMax u τ')

/-- Definition 5.5: `w^(t,r)_{i,j} = w_{i,j}(1 − γτ̃_{i,j})^r`. -/
noncomputable def capW {N n : ℕ} (θ1 : ℝ) (u : Fin N → ℝ) (w : Fin N → Fin n → ℝ)
    (τ' : Fin N → Fin n → ℝ) (r : ℕ) : Fin N → Fin n → ℝ :=
  fun i j => w i j * (1 - capGamma θ1 u τ' * τ' i j) ^ r

/-- Definition 5.5: `u^(t,0) = u`, `u^(t,r+1)_i = u^(t,r)_i 1{ℓ_i(w^(t,r+1)) < θ₁}`. -/
noncomputable def capU {N n : ℕ} (θ1 : ℝ) (u : Fin N → ℝ) (w : Fin N → Fin n → ℝ)
    (τ' : Fin N → Fin n → ℝ) : ℕ → Fin N → ℝ
  | 0 => u
  | r + 1 => fun i => if loss (capW θ1 u w τ' (r + 1)) i < θ1 then capU θ1 u w τ' r i else 0

/-- Definition 5.5: `p^(t,r) := diag(u^(t,r)) w^(t,r)`. -/
noncomputable def capP {N n : ℕ} (θ1 : ℝ) (u : Fin N → ℝ) (w : Fin N → Fin n → ℝ)
    (τ' : Fin N → Fin n → ℝ) (r : ℕ) : Fin N → Fin n → ℝ :=
  prodW (capU θ1 u w τ' r) (capW θ1 u w τ' r)

/-- Definition 5.5: `r` is the stopping time
`R_stop = min{r ∈ ℤ_{≥0} : ⟨p^(t,r), τ̃⟩ ≤ σ₀/8}`, `σ₀ := ⟨p^(t,0), τ̃⟩`. -/
def IsRStop {N n : ℕ} (θ1 : ℝ) (u : Fin N → ℝ) (w : Fin N → Fin n → ℝ)
    (τ' : Fin N → Fin n → ℝ) (r : ℕ) : Prop :=
  pairing (capP θ1 u w τ' r) τ' ≤ pairing (prodW u w) τ' / 8 ∧
    ∀ r' < r, pairing (prodW u w) τ' / 8 < pairing (capP θ1 u w τ' r') τ'

/-- Definition 5.8: the soft product-weight loss of the capped update on the index set `S`,
`∑_{r < R} ∑_{(i,j) ∈ S} (p^(t,r)_{i,j} − p̃^(t,r+1)_{i,j})` with
`p̃^(t,r+1) := diag(u^(t,r)) w^(t,r+1)`. With `S = 𝒮_g` it is `L_g^(t)`, with the complement of
`𝒮_g` it is `L_b^(t)`, and `R = R_stop`. -/
noncomputable def softLoss {N n : ℕ} (θ1 : ℝ) (u : Fin N → ℝ) (w : Fin N → Fin n → ℝ)
    (τ' : Fin N → Fin n → ℝ) (R : ℕ) (S : Finset (Fin N × Fin n)) : ℝ :=
  ∑ r ∈ Finset.range R, ∑ k ∈ S,
    (capP θ1 u w τ' r k.1 k.2 - capU θ1 u w τ' r k.1 * capW θ1 u w τ' (r + 1) k.1 k.2)

/-- A trajectory of Algorithm 3: weights `u^(t)`, `w^(t)` and approximate scores `τ̃^(t)` at every
QUE round `t`, the power-method estimate `Λ̂_k` of every epoch `k`, and the stopping time of every
round's capped update. -/
structure Stage1Traj (N n : ℕ) where
  u : ℕ → Fin N → ℝ
  w : ℕ → Fin N → Fin n → ℝ
  τ : ℕ → Fin N → Fin n → ℝ
  Λhat : ℕ → ℝ
  rstop : ℕ → ℕ

/-- Round `t` of the trajectory performs a capped update: `σ̃^(t) = ⟨p^(t), τ̃^(t)⟩ > Λ̂/10`
(Algorithm 3, line 17), with `Λ̂` the estimate of the epoch containing `t`. -/
def Stage1Traj.Updated {N n : ℕ} (d : ℕ) (tr : Stage1Traj N n) (t : ℕ) : Prop :=
  tr.Λhat (t / epochLen d) / 10 < pairing (prodW (tr.u t) (tr.w t)) (tr.τ t)

/-- The MMW density `Ψ^(t)` used at round `t` of epoch `k` (Definition 3.7 with
`t₀ = kT`, `η = (1 − ν)/Λ̂_k` and gains `F^(s) = M_s(u^(s+1), w^(s+1))`). -/
noncomputable def Stage1Traj.psi {N n d : ℕ} (x : Fin N → Fin n → Vec d) (tr : Stage1Traj N n)
    (k t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  mmwDensity ((1 - nu) / tr.Λhat k) (fun s => covS x (tr.u (s + 1)) (tr.w (s + 1)))
    (k * epochLen d) t

/-- Algorithm 3 run on `x` with parameters `ε, α′, κ` and constants `C_Q, K₁` has completed its
first `K` epochs along `tr`, with successful approximations: the initialization of line 3; at the
start of every epoch `k < K` the estimate `Λ̂_k` is a `ν`-approximation of `‖M_s(u^(kT), w^(kT))‖₂`
and exceeds `16 C_Q κ` (no break, line 8); in every round `t` of the epoch, `τ̃^(t)` is a
`ν`-approximate QUE score matrix for the epoch's MMW density, vanishes on inactive users (line 15),
and the next weights are the capped update at its stopping time if `σ̃^(t) > Λ̂_k/10` (line 18,
Algorithm 5 with `θ₁ = K₁α′/ε`) and unchanged otherwise (line 20). -/
def IsStage1Prefix {N n d : ℕ} (x : Fin N → Fin n → Vec d) (ε α' κ CQ K1 : ℝ)
    (tr : Stage1Traj N n) (K : ℕ) : Prop :=
  tr.u 0 = (fun _ => 1 / (N : ℝ)) ∧ tr.w 0 = (fun _ _ => 1 / (n : ℝ)) ∧
    ∀ k < K,
      IsNuApprox nu (HighDimProb.QuadraticForms.opNorm
        (covS x (tr.u (k * epochLen d)) (tr.w (k * epochLen d)))) (tr.Λhat k) ∧
      16 * CQ * κ < tr.Λhat k ∧
      ∀ t, k * epochLen d ≤ t → t < (k + 1) * epochLen d →
        IsApproxQUE nu x (tr.u t) (tr.w t) (tr.psi x k t) (tr.τ t) ∧
        (∀ i j, tr.u t i = 0 → tr.τ t i j = 0) ∧
        ((tr.Updated d t →
            IsRStop (K1 * α' / ε) (tr.u t) (tr.w t) (tr.τ t) (tr.rstop t) ∧
            tr.u (t + 1) = capU (K1 * α' / ε) (tr.u t) (tr.w t) (tr.τ t) (tr.rstop t) ∧
            tr.w (t + 1) = capW (K1 * α' / ε) (tr.u t) (tr.w t) (tr.τ t) (tr.rstop t)) ∧
          (¬ tr.Updated d t → tr.u (t + 1) = tr.u t ∧ tr.w (t + 1) = tr.w t))

/-- A complete run of Algorithm 3 with successful approximations: `K` epochs, and then the estimate
`Λ̂_K` at round `t* = KT` is a `ν`-approximation of `‖M_s(u^(t*), w^(t*))‖₂` with `Λ̂_K ≤ 16 C_Q κ`
(the break of line 9). The output is `(w^(t*), 𝒜^(t*))` with `𝒜^(t*) = {i : u^(t*)_i > 0}`. -/
def IsStage1Run {N n d : ℕ} (x : Fin N → Fin n → Vec d) (ε α' κ CQ K1 : ℝ)
    (tr : Stage1Traj N n) (K : ℕ) : Prop :=
  IsStage1Prefix x ε α' κ CQ K1 tr K ∧
    IsNuApprox nu (HighDimProb.QuadraticForms.opNorm
      (covS x (tr.u (K * epochLen d)) (tr.w (K * epochLen d)))) (tr.Λhat K) ∧
    tr.Λhat K ≤ 16 * CQ * κ

open Classical in
/-- Definitions 5.8 and 5.12: the soft loss `L_g^(t)` of round `t` on the matched regular-good
samples `𝒮_g^(t) = goodSet R D (u^(t))`, with `θ₁` the removal threshold: the soft loss of the capped
update stopped at `R_stop` if round `t` performs one, and `0` otherwise. -/
noncomputable def Stage1Traj.lossG {N n : ℕ} (d : ℕ) (θ1 : ℝ) (R : Finset (Fin N))
    (D : Fin N → Finset (Fin n)) (tr : Stage1Traj N n) (t : ℕ) : ℝ :=
  if tr.Updated d t then
    softLoss θ1 (tr.u t) (tr.w t) (tr.τ t) (tr.rstop t) (goodSet R D (tr.u t))
  else 0

open Classical in
/-- Definitions 5.8 and 5.12: the soft loss `L_b^(t)` of round `t` on the samples outside
`𝒮_g^(t)`, and `0` if round `t` performs no capped update. -/
noncomputable def Stage1Traj.lossB {N n : ℕ} (d : ℕ) (θ1 : ℝ) (R : Finset (Fin N))
    (D : Fin N → Finset (Fin n)) (tr : Stage1Traj N n) (t : ℕ) : ℝ :=
  if tr.Updated d t then
    softLoss θ1 (tr.u t) (tr.w t) (tr.τ t) (tr.rstop t) (goodSet R D (tr.u t))ᶜ
  else 0

open Classical in
/-- Definition 5.3: the active users `𝒜^(t) := {i : u^(t)_i > 0}`. -/
noncomputable def active {N : ℕ} (u : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i => 0 < u i

end DoubleCorrRME


