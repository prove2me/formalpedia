-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_alg5Process
-- name    : IntroDelayAMDP_Supplement_alg5Process
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:50:48.122194+00:00
-- url     : https://prove2.me/theorems/771e027f-11a1-4b9f-a6af-e1ac1b31dba8
-- title:
--   Algorithm 5 — processing one episode
-- statement:
--   The processing step of **Algorithm 5** (policy optimization with MGRR for linear AMDPs with delayed feedback). Episode $\kappa$ is **skipped** unless (i) $d_\kappa\le\bar d$, (ii) at least $\sqrt K$ episodes were processed before it, and (iii) $\kappa+d_\kappa\le K-\sqrt K-\bar d$.
--
--   1. If not skipped: for every layer $h$ the regions $(C_j,\hat p_j,\hat\Sigma_j)_j$ are built by Algorithm 2 from the layer-$h$ features $\phi_{j,h}=\phi(s_{j,h},a_{j,h})$ of the last $\sqrt K$ processed episodes; $u_\kappa(s,a)=0$ iff $\phi(s,a)$ lies in a region of its layer and that layer has fewer than $\nu$ unfinished estimates; with $\hat p_\kappa(s,a)$ the empirical probability of that region,
--   $$b_\kappa(s)=H\theta\sum_{a:u_\kappa(s,a)=0}\frac{\pi_\kappa(a\mid s)}{\hat p_\kappa(s,a)}+4H\sum_{a:u_\kappa(s,a)=1}\pi_\kappa(a\mid s)\quad(23),$$
--   and $\hat Q_\kappa(s,a)\leftarrow-b_\kappa(s)-4H(H-h-1)u_\kappa(s,a)-K^{-3}$ for $s\in\mathcal S_h$.
--   2. Skipped or not: every unfinished estimate started by episode $k$ at layer $h$ in region $C_j$ makes its $n$-th attempt; $\kappa$ is accepted with probability $\min\{1,\alpha_{k,\kappa}\}$ (Eq. (4)),
--   $$Z_n=\Bigl(I-\frac{\mathbf 1[\kappa\text{ accepted},\ \phi_{\kappa,h}\in C_j]}{8d\log(1+1/\lambda)}\hat\Sigma_j^{-1/2}\phi_{\kappa,h}\phi_{\kappa,h}^\top\hat\Sigma_j^{-1/2}\Bigr)Z_{n-1}\quad(25),$$
--   every $(s,a)\in\mathcal S_h\times\mathcal A$ with $\phi(s,a)\in C_j$ receives the piece $v_n(s,a)=\phi(s,a)^\top\hat\Sigma_j^{-1/2}Z_n\hat\Sigma_j^{-1/2}\phi_{k,h}Y_{k,h}/(16d\log(1+1/\lambda))$ (24) in $\hat Q_k(s,a)$, and the estimate finishes when $n=M_j-1$.
--   3. If not skipped: for each layer $h$ with $u_\kappa(s_{\kappa,h},a_{\kappa,h})=0$, with $C_j$ the region containing $\phi_{\kappa,h}$, $Y_{\kappa,h}$ is computed by Eq. (21),
--   $$Y_{\kappa,h}=L_{\kappa,h}-\sum_{h'=h+1}^{H-1}\Bigl(\prod_{h''=h+1}^{h'-1}(1-u_\kappa(s_{\kappa,h''},a_{\kappa,h''}))\Bigr)\bigl(b_\kappa(s_{\kappa,h'})+4H(H-h'-1)u_\kappa(s_{\kappa,h'},a_{\kappa,h'})\bigr),$$
--   an MGRR estimate starts in $C_j$ with $Z_0=I$ and $M_j=\lceil m_0/\hat p_j\rceil$, and $v_0$ is added to $\hat Q_\kappa(s,a)$ for every $(s,a)\in\mathcal S_h\times\mathcal A$ with $\phi(s,a)\in C_j$.
--
--
--   **Formalization Note** $\hat\Sigma_j^{-1/2}$, the square root of the Moore–Penrose pseudo-inverse of the positive semi-definite $\hat\Sigma_j$, is computed by the functional calculus with $x\mapsto(\sqrt x)^{-1}$ (and $0^{-1}=0$ on the kernel). The counts of unfinished estimates are taken at the start of processing. An estimate makes one attempt with each of the next $M_j-1$ processed episodes (p.44): it is unfinished at its start iff $M_j\ge2$, which always holds for the parameters of App. B.1 once $C_0\ge1$. Episodes are $0$-based, so (iii) reads $\kappa+1+d_\kappa+\sqrt K+\bar d\le K$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 5, lines 4–17, p.59; App. C.1, p.58; Algorithm 3 and Eqs. (21), (23)–(25), pp.18–19

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_accProb
import Definitions.Def_IntroDelayAMDP_lossToGo
import Definitions.Def_IntroDelayAMDP_Supplement_LinParams
import Definitions.Def_IntroDelayAMDP_Supplement_LinState
import Definitions.Def_IntroDelayAMDP_Supplement_RemovalRule
import Definitions.Def_IntroDelayAMDP_Supplement_regionOf
import Definitions.Def_IntroDelayAMDP_Supplement_alg2

namespace IntroDelayAMDP.Supplement

open Matrix

open Classical in
/-- **Processing one episode in Algorithm 5** (Algorithm 5, lines 4–17, printed p.59, PDF p.61; App. C.1,
printed p.58, PDF p.60; Algorithm 3, lines 4–18 and Eqs. (21), (23)–(25), printed pp.18–19, PDF pp.20–21, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)).
Given the state `σ`, the 0-based episode `κ` being processed (its policy `π_κ = σ.pol κ` was stored when it
was played), the trajectories `traj j h = (s_{j,h}, a_{j,h})` and the acceptance coins `coin κ k h` (uniform, for
the attempt of the estimate `(k, h)` with episode `κ`), it performs:
* skipping (App. C.1): `κ` is skipped unless (i) `d_κ ≤ d̄`, (ii) at least `√K` episodes were processed before
  it, and (iii) `κ + d_κ ≤ K − √K − d̄` (1-based `κ`; for the 0-based `κ`: `κ + 1 + d_κ + √K + d̄ ≤ K`);
* lines 4–7 (not skipped): for every layer `h`, the regions of Algorithm 2 from the layer-`h` features
  `ϕ_{j,h} = ϕ(s_{j,h}, a_{j,h})` of the last `√K` processed episodes; `u_κ(s, a) = 0` iff `ϕ(s, a)` lies in a
  region of its layer and that layer has fewer than `ν` unfinished estimates; `p̂_κ(s, a)` the `p̂_j` of that
  region; the bonus (23) `b_κ(s) = Hθ ∑_{a: u_κ=0} π_κ(a | s)/p̂_κ(s, a) + 4H ∑_{a: u_κ=1} π_κ(a | s)`; and
  `Q̂_κ(s, a) ← −b_κ(s) − 4H(H − h − 1)u_κ(s, a) − K^{−3}` for `s ∈ S_h`;
* lines 8–12 (skipped or not): every unfinished estimate `(k, h)` in its region `C_j` makes its `n`-th attempt:
  episode `κ` is accepted iff `coin κ k h < min{1, α_{k,κ}}` (Eq. (4) for `π_k, π_κ` along `κ`'s trajectory up to
  layer `h`); `Z_n = (I − 1[accepted, ϕ_{κ,h} ∈ C_j]/(8d log(1 + 1/λ)) Σ̂_j^{−1/2}ϕ_{κ,h}ϕ_{κ,h}ᵀΣ̂_j^{−1/2}) Z_{n−1}`
  (Eq. (25)); every `(s, a) ∈ S_h × A` with `ϕ(s, a) ∈ C_j` gets the piece
  `v_n(s, a) = ϕ(s, a)ᵀΣ̂_j^{−1/2}Z_nΣ̂_j^{−1/2}ϕ_{k,h}Y_{k,h}/(16d log(1 + 1/λ))` (Eq. (24)) added to `Q̂_k(s, a)`; the
  estimate finishes if `n = M_j − 1`;
* lines 13–17 (not skipped): for each layer `h` with `u_κ(s_{κ,h}, a_{κ,h}) = 0`, with `C_j` the region containing
  `ϕ_{κ,h}`: `Y_{κ,h} = L_{κ,h} − ∑_{h′=h+1}^{H−1} (∏_{h″=h+1}^{h′−1}(1 − u_κ(s_{κ,h″}, a_{κ,h″})))(b_κ(s_{κ,h′}) +
  4H(H − h′ − 1)u_κ(s_{κ,h′}, a_{κ,h′}))` (Eq. (21)); an MGRR estimate starts in `C_j` with `Z₀ = I` and
  `M_j = ⌈m₀/p̂_j⌉`, and `v₀` is added to `Q̂_κ(s, a)` for every `(s, a) ∈ S_h × A` with `ϕ(s, a) ∈ C_j`;
* `κ` is appended to the processed episodes.

**Formalization Note.** `Σ̂_j^{−1/2}`, the square root of the Moore–Penrose pseudo-inverse of the positive
semi-definite `Σ̂_j` (Notation, printed p.12), is `cfc (x ↦ (√x)⁻¹) Σ̂_j` (with Lean's `0⁻¹ = 0` on the kernel).
`u_κ` and the counts of unfinished estimates are taken at the start of processing `κ` (line 6 precedes
line 8). Every estimate makes "one attempt with each of the next `M_j − 1`" processed episodes (printed
p.44): it starts unfinished iff `M_j ≥ 2` and finishes at `n + 1 = M_j`; for the parameters of App. B.1
`M_j ≥ m₀ ≥ 2`, so this is line 12 verbatim. The losses `ℓ κ` enter only through `L_{κ,h}` of a non-skipped
`κ`, whose losses have arrived (`d_κ ≤ d̄`). Estimates are keyed by `(k, h)`: an episode starts at most one
estimate per layer. -/
noncomputable def alg5Process {X A : Type} [Fintype A] {d H : ℕ} (L : LayeredSpace X H)
    (φ : X → A → Fin d → ℝ) (ℓ : ℕ → X → A → ℝ) (p : LinParams) (rule : RemovalRule d)
    (K sqrtK dbar : ℕ) (dl : ℕ → ℕ) (traj : ℕ → ℕ → X × A) (coin : ℕ → ℕ → ℕ → ℝ)
    (σ : LinState X A d) (κ : ℕ) : LinState X A d :=
  let r : ℝ := 2 * d * Real.log (1 + 1 / p.lam)
  let skipped : Prop :=
    ¬ (dl κ ≤ dbar ∧ sqrtK ≤ σ.processed.length ∧ κ + 1 + dl κ + sqrtK + dbar ≤ K)
  let π : X → A → ℝ := σ.pol κ
  let feat : ℕ → ℕ → Fin d → ℝ := fun j h => φ (traj j h).1 (traj j h).2
  let last : List ℕ := σ.processed.drop (σ.processed.length - sqrtK)
  let regs : ℕ → List (Region d) := fun h =>
    alg2 rule (last.map (fun j => feat j h)) p.lam p.theta sqrtK
  let cnt : ℕ → ℕ := fun h => ((Finset.range K).filter (fun k => σ.active k h)).card
  let est : X → A → Prop := fun s a =>
    (regionOf (regs (L.layer s)) r (φ s a)).isSome ∧ cnt (L.layer s) < p.nu
  let uR : X → A → ℝ := fun s a => if est s a then 0 else 1
  let phat : X → A → ℝ := fun s a =>
    (((regionOf (regs (L.layer s)) r (φ s a)).bind (fun j => (regs (L.layer s))[j]?)).map
      Region.phat).getD 0
  let b : X → ℝ := fun s =>
    (H : ℝ) * p.theta * ∑ a, (if est s a then π s a / phat s a else 0) +
      4 * (H : ℝ) * ∑ a, (if est s a then 0 else π s a)
  let Yv : ℕ → ℝ := fun h =>
    lossToGo (ℓ κ) H (traj κ) h -
      ∑ h' ∈ Finset.Ico (h + 1) H,
        (∏ h'' ∈ Finset.Ico (h + 1) h', (1 - uR (traj κ h'').1 (traj κ h'').2)) *
          (b (traj κ h').1 + 4 * (H : ℝ) * ((H : ℝ) - h' - 1) * uR (traj κ h').1 (traj κ h').2)
  let qinit : X → A → ℝ := fun s a =>
    -b s - 4 * (H : ℝ) * ((H : ℝ) - L.layer s - 1) * uR s a - ((K : ℝ) ^ 3)⁻¹
  -- attempts of the unfinished estimates (lines 8–12)
  let acc : ℕ → ℕ → Prop := fun k h =>
    coin κ k h < min 1 (accProb (σ.pol k) π (fun i : Fin (h + 1) => traj κ i))
  let inC : ℕ → ℕ → (Fin d → ℝ) → Prop := fun k h v => regionOf (σ.regs k h) r v = some (σ.reg k h)
  let Shalf : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ := fun k h =>
    cfc (fun x : ℝ => (Real.sqrt x)⁻¹) ((((σ.regs k h)[σ.reg k h]?).map Region.sig).getD 0)
  let Z' : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ := fun k h =>
    (1 - ((if acc k h ∧ inC k h (feat κ h) then (1 : ℝ) else 0) / (8 * d * Real.log (1 + 1 / p.lam))) •
        (Shalf k h * vecMulVec (feat κ h) (feat κ h) * Shalf k h)) * σ.Z k h
  let piece : ℕ → ℕ → (Fin d → ℝ) → ℝ := fun k h v =>
    (v ⬝ᵥ ((Shalf k h * Z' k h * Shalf k h) *ᵥ feat k h)) * σ.Y k h /
      (16 * d * Real.log (1 + 1 / p.lam))
  -- starts of new estimates (lines 13–17)
  let start : ℕ → Prop := fun h => ¬ skipped ∧ h < H ∧ est (traj κ h).1 (traj κ h).2
  let jOf : ℕ → ℕ := fun h => (regionOf (regs h) r (feat κ h)).getD 0
  let phatOf : ℕ → ℝ := fun h => (((regs h)[jOf h]?).map Region.phat).getD 0
  let Mof : ℕ → ℕ := fun h => ⌈(p.m0 : ℝ) / phatOf h⌉₊
  let S0 : ℕ → Matrix (Fin d) (Fin d) ℝ := fun h =>
    cfc (fun x : ℝ => (Real.sqrt x)⁻¹) ((((regs h)[jOf h]?).map Region.sig).getD 0)
  let v0 : ℕ → (Fin d → ℝ) → ℝ := fun h v =>
    (v ⬝ᵥ ((S0 h * S0 h) *ᵥ feat κ h)) * Yv h / (16 * d * Real.log (1 + 1 / p.lam))
  { qhat := fun k s a =>
      if k = κ then
        (if skipped then σ.qhat k s a
         else qinit s a +
           (if start (L.layer s) ∧ regionOf (regs (L.layer s)) r (φ s a) = some (jOf (L.layer s))
            then v0 (L.layer s) (φ s a) else 0))
      else σ.qhat k s a +
        (if σ.active k (L.layer s) ∧ inC k (L.layer s) (φ s a)
         then piece k (L.layer s) (φ s a) else 0)
    pol := σ.pol
    processed := σ.processed ++ [κ]
    regs := fun k => if k = κ ∧ ¬ skipped then regs else σ.regs k
    active := fun k h =>
      if k = κ then start h ∧ 1 < Mof h
      else σ.active k h ∧ ¬ (σ.nAtt k h + 1 + 1 = σ.Mcap k h)
    nAtt := fun k h => if k = κ then 0 else if σ.active k h then σ.nAtt k h + 1 else σ.nAtt k h
    Z := fun k h => if k = κ then 1 else if σ.active k h then Z' k h else σ.Z k h
    Mcap := fun k h => if k = κ then Mof h else σ.Mcap k h
    Y := fun k h => if k = κ then Yv h else σ.Y k h
    reg := fun k h => if k = κ then jOf h else σ.reg k h }

end IntroDelayAMDP.Supplement


