-- Prove2me | Definitions.Def_JointNonManip_Supplement_UnifiedProtocol
-- name    : JointNonManip_Supplement_UnifiedProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:29:20.373701+00:00
-- url     : https://prove2.me/theorems/0c9daf01-0ce7-48cf-90fe-dd3e6a47bbf6
-- title:
--   The unified defection-robust profile $A^\star_{L,T}$, its adversaries, expected CSPs and completed menu
-- statement:
--   The horizon-aware profile $A^\star_{L,T}$ of Appendix A.11, for an admissible codebook and a fixed rule computing auxiliary-game equilibria. Rounds are $t=1,\dots,T$.
--
--   **Public virtual state** (the same at every learner; updated from the optimizer's actions only). If $m_T<T$, the state starts in the *reading phase*, which prescribes the fixed pure learner profile in rounds $t\le m_T$. At the end of round $m_T$, with $\hat p$ the frequency of $c_\star$ among $c^{(1)},\dots,c^{(m_T)}$, the unique $j$ with $|\hat p-\theta_j|\le1/(3M_T)$ is decoded, if it exists, and the *commitment phase* prescribes $\hat q^{(t)}=q_j$; otherwise the *approachability phase* starts with $U=0$. During commitment, approachability with $U=0$ starts after the first round $t$ with $\big\|\sum_{r=m_T+1}^t(e_{c^{(r)}}-z_j)\big\|_1>m_T$. In the approachability phase, $(\tilde y^{(t)},\hat x^{(t)})$ is a mixed Nash equilibrium of the auxiliary game with optimizer utility $\langle U,y\otimes\bigotimes_ix_i\rangle$ and the original learner utilities, $\hat q^{(t)}=\bigotimes_i\hat x_i^{(t)}$, $s^{(t)}=\tilde y^{(t)}\otimes\hat q^{(t)}$, and afterwards $U\leftarrow U+e_{c^{(t)}}\otimes\hat q^{(t)}-s^{(t)}$. Phase changes take effect in the next round. If $m_T\ge T$, the state is a fresh approachability run from round 1.
--
--   **Private state** of learner $i$, initially *monitoring* with statistics $D_{i,\varphi}=0$. While monitoring she plays $\bar p_i^{(t)}=(1-\gamma_T)\hat x_i^{(t)}+\gamma_T\,\mathrm{Unif}(A_i)$, then computes $\nu_i^{(t)}(b)=u_i(c^{(t)},b,\bar p_{-i}^{(t)})$ (the others at their *prescribed* monitoring distributions), $\hat v_i^{(t)}(b)=r_i^{(t)}\mathbf 1\{a_i^{(t)}=b\}/\bar p_i^{(t)}(b)$ with $r_i^{(t)}=u_i(a^{(t)})$, and
--   $$D_{i,\varphi}(t)=D_{i,\varphi}(t-1)+\sum_{a\in A_i}\bar p_i^{(t)}(a)\big[\hat v_i^{(t)}(\varphi(a))-\hat v_i^{(t)}(a)-\nu_i^{(t)}(\varphi(a))+\nu_i^{(t)}(a)\big]\quad(\varphi\in\Phi_i).$$
--   If $\max_\varphi|D_{i,\varphi}(t)|>h_i(t)$ she uses a fresh bandit fallback from round $t+1$ on, permanently: row weights $W_{ab}=1$ initially; each round she plays the stationary distribution $x=xQ$ of $Q(a,b)=(1-\beta_i)W_{ab}/\sum_cW_{ac}+\beta_i/k_i$ and, with her sampled action $A$ and normalized gain $b=(r_i^{(t)}+1)/2$, updates $W_{ar}\leftarrow W_{ar}\exp\big(\tfrac{\beta_i}{k_i}\tfrac{x(a)}{x(r)}b\,\mathbf 1\{A=r\}\big)$.
--
--   **Laws of play.**
--   1. Against an *admissible adversary* (the optimizer together with the other learners, who may deviate and correlate), in round $t$ the actions $(c^{(t)},a_{-i}^{(t)})$ are drawn from a distribution chosen as a function of the realized past, and independently $a_i^{(t)}\sim p_i^{(t)}$, learner $i$'s actual mixed action. $\mathbb E[R_i^{\mathrm{sw}}(T)]$ is the expectation of the realized swap regret $\max_{\varphi}\sum_t[u_i(c^{(t)},\varphi(a_i^{(t)}),a_{-i}^{(t)})-u_i(a^{(t)})]$.
--   2. When all learners follow the protocol and the optimizer follows an adaptive policy $\pi\in\Pi_T$, the expected CSP is $\phi_T(\pi,A^\star_{L,T})=\mathbb E\big[\frac1T\sum_te_{c^{(t)}}\otimes\bigotimes_ip_i^{(t)}\big]$ with the actual mixed strategies; the completed menu is $\mathcal M^\star_T=\overline{\{\phi_T(\pi,A^\star_{L,T}):\pi\in\Pi_T\}}$, and $d_{H,1}$ is the Hausdorff distance for the $\ell_1$ norm on $\mathbb R^A$. Finally $V=\max_{s\in S_{\mathrm{NE}}}\langle u_0,s\rangle$.
--
--   **Formalization Note** The auxiliary equilibrium is the published `IsAuxNE`, chosen by an arbitrary `AuxNESelector`. The decoding uses `∃!` and classical choice; the stationary distribution is chosen classically among the lotteries with $x=xQ$ (unique here); for $k_i=1$ it is the point mass on the only action. An adversary is a distribution on all of $A$ of which only the $(c,a_{-i})$-marginal is used. $d_{H,1}$ is `Metric.hausdorffEDist` on `PiLp 1`.
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), Appendix A.11, "The unified protocol", steps 1–4, pp.33–34; "Specification of the bandit fallback", p.35; Theorem A.5, pp.35–36

import Mathlib
import Definitions.Def_JointNonManip_Algorithm1
import Definitions.Def_JointNonManip_Supplement_Codebook

namespace JointNonManip.Supplement

/-!
# The unified defection-robust profile `A⋆_{L,T}` and its laws of play

Collina, Fullerton, Liu & Weinberg, *Non-manipulability and Approachability Beyond Two-Player
Games* (manuscript, STOC 2027 submission), Appendix A.11, pp.33–35 ("The unified protocol",
steps 1–4; "Specification of the bandit fallback"), and Theorem A.5, pp.35–36.

Rounds are `Fin T`; round `t` of the paper is index `t − 1`. A trajectory prefix
`h : Fin n → A` lists the realized joint actions `(c(r), a_L(r))` of the first `n` rounds.

**Public virtual state** (identical at every learner; a function of the optimizer's past actions
only). The phase in force in a round is `reading`, `commit j` or `approach U` (`U ∈ ℝ^A`).
* Horizons with `m_T < T`: start in `reading`. After round `m_T` the frequency `p̂` of `c⋆` among
  `c(1), …, c(m_T)` is decoded to the unique `j` with `|p̂ − θⱼ| ≤ 1/(3M_T)`, if one exists
  (→ `commit j`), else → `approach 0`. After each commitment round `t` the test
  `‖∑_{r=m_T+1}^{t} (e_{c(r)} − zⱼ)‖₁ ≤ m_T` is run; at its first failure → `approach 0`.
  After an approachability round, `U ← U + e_{c(t)} ⊗ q̂(t) − s(t)`. Every change takes effect in
  the following round.
* Horizons with `m_T ≥ T` (the finitely many small horizons): no menu completion; a fresh
  approachability run from round 1 (`approach 0`).
* Virtual prescription `x̂(t)`: the reading pure profile, `x_j` of the codebook, or the learners'
  part of the selected auxiliary-game equilibrium `(ỹ(t), x̂(t))` for `U`; `q̂(t) = ⊗ᵢ x̂ᵢ(t)` and
  `s(t) = ỹ(t) ⊗ q̂(t)`.

**Private state** of learner `i` (`monitor D` or `fallback W`), starting at `monitor 0`.
* While monitoring she plays `p̄ᵢ(t) = (1 − γ_T) x̂ᵢ(t) + γ_T Unif(Aᵢ)`; after the round,
  `νᵢ(b) = uᵢ(c(t), b, p̄₋ᵢ(t))` (other learners at their *prescribed* monitoring distributions),
  `v̂ᵢ(b) = rᵢ(t) 1{aᵢ(t) = b} / p̄ᵢ(t)(b)` with `rᵢ(t) = uᵢ(a(t))`, and for every `φ ∈ Φᵢ`,
  `D_{i,φ}(t) = D_{i,φ}(t−1) + ∑_a p̄ᵢ(t)(a)[v̂ᵢ(φ(a)) − v̂ᵢ(a) − νᵢ(φ(a)) + νᵢ(a)]`. If
  `max_φ |D_{i,φ}(t)| > hᵢ(t)`, a fresh fallback instance (`W ≡ 1`) is used from round `t + 1` on.
* In fallback she plays the stationary distribution `x = xQ` of
  `Q(a, b) = (1 − βᵢ) W_{ab} / ∑_c W_{ac} + βᵢ/kᵢ` and updates, with normalized gain
  `g = (rᵢ(t) + 1)/2` and her sampled action `A = aᵢ(t)`,
  `W_{ar} ← W_{ar} exp((βᵢ/kᵢ)(x(a)/x(r)) g 1{A = r})`.

**Formalization Note**
* The auxiliary-game equilibrium is the published `IsAuxNE`, computed by an arbitrary
  deterministic `AuxNESelector`; statements quantify over all selectors and all admissible
  codebooks (`Codebook`).
* The decoding "the unique `j`, if one exists" is `∃! j`, read with classical choice.
* The stationary distribution `x = xQ` is chosen classically among the lotteries `x` with
  `x = xQ` (it exists and is unique, since `Q` is row-stochastic with positive entries); the
  fallback value when none exists is never used. For `kᵢ = 1` the only lottery is the point mass
  on the only action, so the formula plays the only action, as the paper prescribes.
* Learner `i`'s actual mixed action in round `t` (`actualMix`) is a deterministic function of the
  realized past: her private state depends only on `c`, her own actions and her realized
  utilities.
* Clause 1 of Theorem A.5 is against an **adversary** (`Adversary i T`): the optimizer and all
  other learners, possibly deviating and correlated, choose in round `t` a joint distribution `μ`
  over `A` as a function of the whole realized past (which determines learner `i`'s current mixed
  strategy); only its marginal on `(c, a₋ᵢ)` matters, and learner `i`'s sample
  `aᵢ(t) ∼ p̄ᵢ(t)` is independent of it.
* Clauses 2–3: all learners follow the protocol and the optimizer follows a published horizon-`T`
  `Policy` (the class `Π_T`, adaptive over the whole realized past). `φ_T(π, A⋆_{L,T})` is the
  expectation of `(1/T) ∑ₜ e_{c(t)} ⊗ ⊗ᵢ pᵢ(t)` with the **actual** mixed strategies.
* `d_{H,1}` is the Hausdorff extended distance of `PiLp 1` (the ℓ₁ norm on `ℝ^A`), applied to the
  images of the sets under `WithLp.toLp 1`; closures are taken in `ℝ^A` (whose topology is that of
  every norm).
-/

open Finset

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-! ### Public virtual protocol (steps 1 and 3, pp.33–34) -/

/-- The phase of the public virtual state in force in a round. -/
inductive Phase (J : ℕ) (A : Type) where
  /-- The reading phase (rounds `1, …, m_T`). -/
  | reading : Phase J A
  /-- The commitment phase with decoded label `j`. -/
  | commit : Fin J → Phase J A
  /-- The approachability phase with cumulative discrepancy `U`. -/
  | approach : (A → ℝ) → Phase J A

/-- The decoded label: the unique `j` with `|p̂ − θⱼ| ≤ 1/(3M_T)`, if one exists (p.34). -/
noncomputable def decode {u : L → A0 × ((i : L) → Act i) → ℝ} {T : ℕ} (C : Codebook u T)
    (phat : ℝ) : Option (Fin C.J) := by
  classical
  exact if h : ∃! j : Fin C.J, |phat - C.theta j| ≤ 1 / (3 * (MT C.J T : ℝ)) then
    some h.exists.choose else none

/-- The virtual prescription `x̂(t) = (x̂ᵢ(t))ᵢ` in a phase (step 1, p.34). -/
noncomputable def prescription {u : L → A0 × ((i : L) → Act i) → ℝ} {T : ℕ}
    (S : AuxNESelector u) (C : Codebook u T) :
    Phase C.J (A0 × ((i : L) → Act i)) → (i : L) → Act i → ℝ
  | .reading => fun i => pointMass (C.aRead i)
  | .commit j => (C.prof j).2
  | .approach U => (S.sel U).2

/-- The public phase in force in round `n` (index `n`, paper round `n + 1`) after the optimizer
history `h = (c(1), …, c(n))` (steps 1 and 3, p.34; the small-horizon rule, p.33). -/
noncomputable def pubPhase {u : L → A0 × ((i : L) → Act i) → ℝ} {T : ℕ}
    (S : AuxNESelector u) (C : Codebook u T) :
    (n : ℕ) → (Fin n → A0) → Phase C.J (A0 × ((i : L) → Act i))
  | 0, _ => if mT T < T then .reading else .approach 0
  | n + 1, h =>
      match pubPhase S C n (Fin.init h) with
      | .reading =>
          if n + 1 = mT T then
            match decode C ((((Finset.univ.filter fun r : Fin (n + 1) => h r = C.cstar).card : ℕ) :
                ℝ) / (mT T : ℝ)) with
            | some j => .commit j
            | none => .approach 0
          else .reading
      | .commit j =>
          if l1dist (∑ r ∈ Finset.univ.filter (fun r : Fin (n + 1) => mT T ≤ r.val),
              (pointMass (h r) - C.z j)) 0 ≤ (mT T : ℝ) then .commit j else .approach 0
      | .approach U =>
          .approach (U + (otimes (pointMass (h (Fin.last n)))
              (AGT.profileProb (S.sel U).2) - otimes (S.sel U).1 (AGT.profileProb (S.sel U).2)))

/-- The optimizer-action path `(c(1), …, c(n))` of a trajectory prefix. -/
def cPath {n : ℕ} (h : Fin n → A0 × ((i : L) → Act i)) : Fin n → A0 :=
  fun r => (h r).1

/-- The prescribed monitoring distribution `p̄ⱼ(t) = (1 − γ_T) x̂ⱼ(t) + γ_T Unif(Aⱼ)` of every
learner `j` in round `n`, given the optimizer history (step 2, p.34). -/
noncomputable def monitorMix {u : L → A0 × ((i : L) → Act i) → ℝ} {T : ℕ}
    (S : AuxNESelector u) (C : Codebook u T) (n : ℕ) (hc : Fin n → A0) (j : L) :
    Act j → ℝ :=
  fun b => (1 - gammaT T) * prescription S C (pubPhase S C n hc) j b +
    gammaT T * (1 / (Fintype.card (Act j) : ℝ))

/-! ### Bandit fallback (p.35) -/

/-- The matrix `Q(a, b) = (1 − βᵢ) W_{ab} / ∑_c W_{ac} + βᵢ/kᵢ` (p.35). -/
noncomputable def fallbackQ (i : L) (T : ℕ) (W : Act i → Act i → ℝ) : Act i → Act i → ℝ :=
  fun a b => (1 - betaI Act i T) * W a b / (∑ c, W a c) +
    betaI Act i T / (Fintype.card (Act i) : ℝ)

/-- A stationary lottery `x = xQ` of `Q` (classical choice; unique for the positive
row-stochastic matrices used here). -/
noncomputable def stationaryOf {α : Type} [Fintype α] (Q : α → α → ℝ) : α → ℝ := by
  classical
  exact if h : ∃ x : α → ℝ, AGT.IsLottery x ∧ ∀ b, x b = ∑ a, x a * Q a b then h.choose
    else fun _ => 1 / (Fintype.card α : ℝ)

/-- The fallback's mixed action `x = xQ` for the weights `W` (p.35). -/
noncomputable def fallbackMix (i : L) (T : ℕ) (W : Act i → Act i → ℝ) : Act i → ℝ :=
  stationaryOf (fallbackQ (Act := Act) i T W)

/-- The fallback update `W_{ar} ← W_{ar} exp((βᵢ/kᵢ)(x(a)/x(r)) g 1{A = r})` with sampled action
`A` and normalized gain `g` (p.35). -/
noncomputable def fallbackUpdate (i : L) (T : ℕ) (W : Act i → Act i → ℝ) (A : Act i) (g : ℝ) :
    Act i → Act i → ℝ :=
  fun a r => W a r * Real.exp (betaI Act i T / (Fintype.card (Act i) : ℝ) *
    (fallbackMix i T W a / fallbackMix i T W r) * g * (if A = r then 1 else 0))

/-! ### Private state (steps 2 and 4, p.34) -/

/-- Learner `i`'s private state: monitoring with statistics `D_{i,φ}`, or bandit fallback with
row weights `W`. -/
inductive PrivState (α : Type) where
  /-- Monitoring, with the statistics `(D_φ)_{φ : α → α}`. -/
  | monitor : ((α → α) → ℝ) → PrivState α
  /-- Bandit fallback, with the row weights `W`. -/
  | fallback : (α → α → ℝ) → PrivState α

/-- Learner `i`'s private state in round `n` (index `n`, paper round `n + 1`) after the realized
trajectory prefix `h` (step 4, p.34). -/
noncomputable def privState (u : L → A0 × ((i : L) → Act i) → ℝ) {T : ℕ}
    (S : AuxNESelector u) (C : Codebook u T) (i : L) :
    (n : ℕ) → (Fin n → A0 × ((i : L) → Act i)) → PrivState (Act i)
  | 0, _ => .monitor 0
  | n + 1, h =>
      match privState u S C i n (Fin.init h) with
      | .monitor D =>
          let c : A0 := (h (Fin.last n)).1
          let a : (j : L) → Act j := (h (Fin.last n)).2
          let r : ℝ := u i (h (Fin.last n))
          let pbar : (j : L) → Act j → ℝ := monitorMix S C n (cPath (Fin.init h))
          let nu : Act i → ℝ := fun b =>
            ∑ a' : (j : L) → Act j,
              AGT.profileProb (Function.update pbar i (pointMass b)) a' * u i (c, a')
          let vhat : Act i → ℝ := fun b => r * (if a i = b then 1 else 0) / pbar i b
          let D' : (Act i → Act i) → ℝ := fun φ =>
            D φ + ∑ x : Act i, pbar i x * (vhat (φ x) - vhat x - nu (φ x) + nu x)
          if hThr Act i T ((n : ℝ) + 1) <
              Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun φ : Act i → Act i => |D' φ|) then
            .fallback (fun _ _ => 1)
          else .monitor D'
      | .fallback W =>
          .fallback (fallbackUpdate i T W ((h (Fin.last n)).2 i) ((u i (h (Fin.last n)) + 1) / 2))

/-- Learner `i`'s **actual mixed action** `pᵢ(t)` in round `n` after the realized prefix `h`
(step 2, p.34): the monitoring distribution while monitoring, the fallback's `x = xQ` otherwise. -/
noncomputable def actualMix (u : L → A0 × ((i : L) → Act i) → ℝ) {T : ℕ}
    (S : AuxNESelector u) (C : Codebook u T) (i : L) (n : ℕ)
    (h : Fin n → A0 × ((i : L) → Act i)) : Act i → ℝ :=
  match privState u S C i n h with
  | .monitor _ => monitorMix S C n (cPath h) i
  | .fallback W => fallbackMix i T W

/-! ### Clause 1: an adhering learner against an adversary -/

/-- An **admissible adversary** against learner `i` at horizon `T` (p.33): in round `t`, the
optimizer and the other learners jointly draw their actions from a distribution `μ t h` on `A`
(only its marginal on `(c, a₋ᵢ)` matters) chosen as a function of the whole realized past `h`,
without seeing learner `i`'s fresh sample. -/
structure Adversary (A0 : Type) {L : Type} (Act : L → Type) [Fintype A0] [Fintype L]
    [DecidableEq L] [∀ i, Fintype (Act i)] (i : L) (T : ℕ) where
  /-- The joint distribution of the other players' current actions. -/
  μ : (t : Fin T) → (Fin t → A0 × ((i : L) → Act i)) → A0 × ((i : L) → Act i) → ℝ
  /-- It is a lottery. -/
  isLottery : ∀ t h, AGT.IsLottery (μ t h)

/-- The probability of the trajectory `ω` when learner `i` follows `A⋆_{L,T}` against the
adversary `adv`: in round `t`, `(c(t), a₋ᵢ(t))` follows the `(c, a₋ᵢ)`-marginal of `μ`, and
independently `aᵢ(t) ∼ pᵢ(t)`. -/
noncomputable def advTrajWeight (u : L → A0 × ((i : L) → Act i) → ℝ) {T : ℕ}
    (S : AuxNESelector u) (C : Codebook u T) (i : L) (adv : Adversary A0 Act i T)
    (ω : Fin T → A0 × ((i : L) → Act i)) : ℝ :=
  ∏ t : Fin T,
    (∑ b : Act i, adv.μ t (histPrefix ω t) ((ω t).1, Function.update (ω t).2 i b)) *
      actualMix u S C i t (histPrefix ω t) ((ω t).2 i)

/-- Learner `i`'s expected realized swap regret `E[R_i^sw(T)]` (maximum over swaps inside the
expectation) against the adversary `adv` (Theorem A.5, clause 1). -/
noncomputable def advExpSwapRegret (u : L → A0 × ((i : L) → Act i) → ℝ) {T : ℕ}
    (S : AuxNESelector u) (C : Codebook u T) (i : L) (adv : Adversary A0 Act i T) : ℝ :=
  ∑ ω : Fin T → A0 × ((i : L) → Act i), advTrajWeight u S C i adv ω * swapRegret u i ω

/-! ### Clauses 2–3: all learners follow the protocol -/

/-- The joint actual mixed action `⊗ᵢ pᵢ(t)` of the learners in round `n` after the prefix `h`. -/
noncomputable def jointActual (u : L → A0 × ((i : L) → Act i) → ℝ) {T : ℕ}
    (S : AuxNESelector u) (C : Codebook u T) (n : ℕ) (h : Fin n → A0 × ((i : L) → Act i)) :
    ((i : L) → Act i) → ℝ :=
  AGT.profileProb (fun j => actualMix u S C j n h)

/-- The probability of the trajectory `ω` when the optimizer follows `π ∈ Π_T` and every learner
follows `A⋆_{L,T}`. -/
noncomputable def starTrajWeight (u : L → A0 × ((i : L) → Act i) → ℝ) {T : ℕ}
    (S : AuxNESelector u) (C : Codebook u T) (π : Policy A0 Act T)
    (ω : Fin T → A0 × ((i : L) → Act i)) : ℝ :=
  ∏ t : Fin T, π.y t (histPrefix ω t) (ω t).1 *
    jointActual u S C t (histPrefix ω t) (ω t).2

/-- The expected CSP `φ_T(π, A⋆_{L,T}) = E[(1/T) ∑ₜ e_{c(t)} ⊗ ⊗ᵢ pᵢ(t)]` (Definition 2.3 with
the actual mixed strategies; p.36). -/
noncomputable def starExpCSP (u : L → A0 × ((i : L) → Act i) → ℝ) {T : ℕ}
    (S : AuxNESelector u) (C : Codebook u T) (π : Policy A0 Act T) :
    A0 × ((i : L) → Act i) → ℝ :=
  ∑ ω : Fin T → A0 × ((i : L) → Act i), starTrajWeight u S C π ω •
    ((T : ℝ)⁻¹ • ∑ t : Fin T,
      otimes (pointMass (ω t).1) (jointActual u S C t (histPrefix ω t)))

/-- The completed menu `M⋆_T = closure {φ_T(π, A⋆_{L,T}) : π ∈ Π_T}` (Theorem A.5, clause 3). -/
def starMenu (u : L → A0 × ((i : L) → Act i) → ℝ) {T : ℕ} (S : AuxNESelector u)
    (C : Codebook u T) : Set (A0 × ((i : L) → Act i) → ℝ) :=
  closure (Set.range fun π : Policy A0 Act T => starExpCSP u S C π)

/-- The ℓ₁ Hausdorff (extended) distance `d_{H,1}` between two sets of vectors on a finite type. -/
noncomputable def hausdorffL1 {α : Type} [Fintype α] (X Y : Set (α → ℝ)) : ENNReal :=
  Metric.hausdorffEDist ((WithLp.toLp 1 : (α → ℝ) → PiLp 1 (fun _ : α => ℝ)) '' X)
    ((WithLp.toLp 1 : (α → ℝ) → PiLp 1 (fun _ : α => ℝ)) '' Y)

/-- `V = max_{s ∈ S_NE} ⟨u₀, s⟩` (Theorem A.5, clause 2), as the real supremum (the maximum:
`S_NE` is nonempty and compact). -/
noncomputable def valueV (u : L → A0 × ((i : L) → Act i) → ℝ)
    (u0 : A0 × ((i : L) → Act i) → ℝ) : ℝ :=
  sSup ((fun s => pairing u0 s) '' SNE u)

end JointNonManip.Supplement


