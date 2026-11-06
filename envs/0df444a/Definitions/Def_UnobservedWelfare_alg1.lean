-- Prove2me | Definitions.Def_UnobservedWelfare_alg1
-- name    : UnobservedWelfare_alg1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:40.345412+00:00
-- url     : https://prove2.me/theorems/64edd46e-97ee-4282-a44f-6aa18fa42107
-- title:
--   Algorithm 1: Gibbs-mean pricing and production
-- statement:
--   Fix $0<\gamma\le1$ and $\kappa\ge80/\gamma$. The schedule is
--   $$s_t=\frac{T-t+1}{T-t+3},\qquad \rho_t=\frac{2}{T-t+1},\qquad w_{jt}=\prod_{r=j+1}^t s_r,\qquad M_t=\sum_{j<t}w_{jt}.$$
--   With $a_j(z)=a(z;p_j,X_j)$ and $f(x)=\tfrac12(1-x)_+^2$, the inventory correction and history score are
--   $$\Gamma_{w}(z)=\frac{\gamma W}{2}\sum_j w_j(1-a_j(z))_+^2,\qquad H_w(z)=(M+1)c^*(z)-W\sum_j w_j\log a_j(z),$$
--   and the inventory potential is $\Phi_w(A)=\kappa W\log\int e^{-[A\cdot z+\Gamma_w(z)]/(\kappa W)}dz$ for $A\gg0$, $+\infty$ otherwise. In round $t$, Algorithm 1 chooses
--   $$q_t\in\arg\min_{v\in[0,1]^m}\{c(v)+\Phi_{w_t}(I_{t-1}+v)\},$$
--   sets $A_t=I_{t-1}+q_t$, computes the Gibbs means $p^I_t=\bar z^{A_t\cdot z+\Gamma_{w_t}}_{\kappa W}$ and $p^H_t=\bar z^{H_{w_t}}_{W}$ (37), and posts $p_t=(p^I_t+p^H_t)/2$. It uses only $m,T,W,c,\gamma,\kappa$ and past prices and purchases.
--
--   **Formalization Note** The policy recomputes $I_{t-1}$ from the history with its own production. When the production problem has no minimizer the policy returns $0$; Lemma 4.1 shows a unique minimizer exists for every valid history. Indices of $s,\rho,w,M$ are the paper's.
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), §3.1, pp.20–21 (PDF pp.22–23): (37) and Algorithm 1; §4.2, p.24 (PDF p.26): $f$

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC
import Definitions.Def_UnobservedWelfare_expectedRegret
import Definitions.Def_UnobservedWelfare_gibbsMean

open Matrix

namespace UnobservedWelfare

/-- The discount factor `s_t := (T − t + 1)/(T − t + 3)` of paper round `t` (Cheng–Tao–Xing
manuscript, §3.1, p.20 (PDF p.22)). The index `t` is the paper's (1-based) round. -/
noncomputable def sched (T t : ℕ) : ℝ := ((T : ℝ) - t + 1) / ((T : ℝ) - t + 3)

/-- The relative discount rate `ρ_t := (1 − s_t)/s_t = 2/(T − t + 1)` of paper round `t`
(Cheng–Tao–Xing manuscript, §3.1, p.20 (PDF p.22)). -/
noncomputable def rho (T t : ℕ) : ℝ := 2 / ((T : ℝ) - t + 1)

/-- The weight `w_{jt} := ∏_{r=j+1}^{t} s_r` of purchase record `j` in paper round `t`
(Cheng–Tao–Xing manuscript, §3.1, p.20 (PDF p.22)); `w_{tt} = 1` (empty product). Both indices are
the paper's. -/
noncomputable def wt (T j t : ℕ) : ℝ := ∏ r ∈ Finset.Ioc j t, sched T r

/-- The total weight `M_t := Σ_{j<t} w_{jt}` before the purchase of paper round `t`, with
`M_1 = 0` (Cheng–Tao–Xing manuscript, §3.1, p.20 (PDF p.22)). -/
noncomputable def mass (T t : ℕ) : ℝ := ∑ j ∈ Finset.Ico 1 t, wt T j t

/-- The weights in paper round `t` of the first `n` purchase records: the record `i : Fin n` is the
paper's record `j = i + 1`, with weight `w_{jt}`. With `n = t − 1` this is the paper's `w_t`; with
`n = t` it is `w⁺_t = (w_t, 1)` (Cheng–Tao–Xing manuscript, §3.1, p.20 (PDF p.22)). -/
noncomputable def wts (T t n : ℕ) : Fin n → ℝ := fun i => wt T (i + 1) t

/-- The record correction `f(x) := (1 − x)_+^2 / 2` (Cheng–Tao–Xing manuscript, §4.2, p.24 (PDF
p.26)). -/
noncomputable def recCorr (x : ℝ) : ℝ := (max (1 - x) 0) ^ 2 / 2

/-- The inventory correction `Γ_w(z) := (γW/2) Σ_j w_j (1 − a_j(z))_+^2` of a weighted list of
purchase records `(p_j, X_j)` (Cheng–Tao–Xing manuscript, §3.1, p.20 (PDF p.22); extended to any
weighted list on p.22 (PDF p.24)). -/
noncomputable def invCorr {m n : ℕ} (W γ : ℝ) (w : Fin n → ℝ)
    (rec : Fin n → (Fin m → ℝ) × (Fin m → ℝ)) (z : Fin m → ℝ) : ℝ :=
  γ * W / 2 * ∑ j, w j * (max (1 - affineRecord W (rec j).1 (rec j).2 z) 0) ^ 2

/-- The observable history score `H_w(z) := (M + 1) c*(z) − W Σ_j w_j log a_j(z)`, `M = Σ_j w_j`
(Cheng–Tao–Xing manuscript, §3.1, p.20 (PDF p.22); extended to any weighted list on p.22 (PDF
p.24)). It is used for `z ≫ 0`, where every record is positive. -/
noncomputable def histScore {m n : ℕ} (W : ℝ) (c : (Fin m → ℝ) → ℝ) (w : Fin n → ℝ)
    (rec : Fin n → (Fin m → ℝ) × (Fin m → ℝ)) (z : Fin m → ℝ) : ℝ :=
  (∑ j, w j + 1) * costConj c z - W * ∑ j, w j * Real.log (affineRecord W (rec j).1 (rec j).2 z)

/-- The inventory potential `Φ_w(A) := κW log ∫_{ℝ^m_{++}} e^{−[A·z + Γ_w(z)]/(κW)} dz` for `A ≫ 0`,
and `Φ_w(A) = +∞` otherwise (Cheng–Tao–Xing manuscript, p.21 (PDF p.23)).

**Formalization Note** `EReal`-valued, so that the `+∞` value off the open orthant is exact and no
junk real value can make a boundary inventory optimal. -/
noncomputable def invPotential {m n : ℕ} (W γ κ : ℝ) (w : Fin n → ℝ)
    (rec : Fin n → (Fin m → ℝ) × (Fin m → ℝ)) (A : Fin m → ℝ) : EReal := by
  classical exact
  if A ∈ posOrthant m then
    ((κ * W * Real.log (gibbsZ (κ * W) (fun z => A ⬝ᵥ z + invCorr W γ w rec z)) : ℝ) : EReal)
  else ⊤

/-- The inventory price `p^I = E_{π^V_{κW}}[Z]` for the energy `V(z) = A·z + Γ_w(z)` (Cheng–Tao–Xing
manuscript, (37), p.20 (PDF p.22)). -/
noncomputable def inventoryPrice {m n : ℕ} (W γ κ : ℝ) (w : Fin n → ℝ)
    (rec : Fin n → (Fin m → ℝ) × (Fin m → ℝ)) (A : Fin m → ℝ) : Fin m → ℝ :=
  gibbsMean (κ * W) (fun z => A ⬝ᵥ z + invCorr W γ w rec z)

/-- The history price `p^H = E_{π^{H_w}_W}[Z]` (Cheng–Tao–Xing manuscript, (37), p.20 (PDF
p.22)). -/
noncomputable def historyPrice {m n : ℕ} (W : ℝ) (c : (Fin m → ℝ) → ℝ) (w : Fin n → ℝ)
    (rec : Fin n → (Fin m → ℝ) × (Fin m → ℝ)) : Fin m → ℝ :=
  gibbsMean W (histScore W c w rec)

/-- `q` minimizes the production objective `v ↦ c(v) + Φ_w(I + v)` over `[0,1]^m` (Cheng–Tao–Xing
manuscript, Algorithm 1, line 3, p.21 (PDF p.23)); `I` is the inventory `I_{t−1}` carried into
the round. -/
def IsProdMin {m n : ℕ} (W γ κ : ℝ) (c : (Fin m → ℝ) → ℝ) (w : Fin n → ℝ)
    (rec : Fin n → (Fin m → ℝ) × (Fin m → ℝ)) (I q : Fin m → ℝ) : Prop :=
  q ∈ cube m ∧ ∀ v ∈ cube m,
    (c q : EReal) + invPotential W γ κ w rec (I + q) ≤ (c v : EReal) + invPotential W γ κ w rec (I + v)

/-- The production `q_t ∈ argmin_{v ∈ [0,1]^m} {c(v) + Φ_{w_t}(I_{t−1} + v)}` of Algorithm 1, line 3
(Cheng–Tao–Xing manuscript, p.21 (PDF p.23)).

**Formalization Note** A minimizer is chosen when one exists (the paper's Lemma 4.1 shows it exists
and is unique for valid histories), and `0` otherwise. -/
noncomputable def alg1Prod {m n : ℕ} (W γ κ : ℝ) (c : (Fin m → ℝ) → ℝ) (w : Fin n → ℝ)
    (rec : Fin n → (Fin m → ℝ) × (Fin m → ℝ)) (I : Fin m → ℝ) : Fin m → ℝ := by
  classical
  exact if h : ∃ q, IsProdMin W γ κ c w rec I q then h.choose else 0

/-- The inventory `I_k` that Algorithm 1 carries into (0-based) round `k`, recomputed from the
history of posted prices and purchases (Cheng–Tao–Xing manuscript, Algorithm 1, lines 1, 3, 4, 8,
p.21 (PDF p.23)): `I_0 = 0` and `I_{k+1} = I_k + q_{k+1} − X_{k+1}` with the algorithm's own
production. -/
noncomputable def alg1Inv {m : ℕ} (T : ℕ) (W γ κ : ℝ) (c : (Fin m → ℝ) → ℝ) :
    (k : ℕ) → (Fin k → (Fin m → ℝ) × (Fin m → ℝ)) → (Fin m → ℝ)
  | 0, _ => 0
  | k + 1, h =>
    alg1Inv T W γ κ c k (fun j => h j.castSucc) +
      alg1Prod W γ κ c (wts T (k + 1) k) (fun j => h j.castSucc)
        (alg1Inv T W γ κ c k (fun j => h j.castSucc)) - (h (Fin.last k)).2

/-- Algorithm 1, Gibbs-mean pricing and production, with parameters `γ, κ` (Cheng–Tao–Xing
manuscript, Algorithm 1, p.21 (PDF p.23), with (37), p.20 (PDF p.22)). In (0-based) round `k`
(paper round `t = k + 1`), from the history `(p_j, X_j)_{j<k}`: recompute the inventory
`I_{t−1}`, choose the production `q_t` minimizing `c(v) + Φ_{w_t}(I_{t−1} + v)` over the cube, set
`A_t = I_{t−1} + q_t`, and post `p_t = (p^I_t + p^H_t)/2`. The policy uses only
`m, T, W, c, γ, κ` and the history. -/
noncomputable def alg1 (m T : ℕ) (W : ℝ) (c : (Fin m → ℝ) → ℝ) (γ κ : ℝ) : Policy m :=
  fun k h =>
    let I := alg1Inv T W γ κ c k h
    let q := alg1Prod W γ κ c (wts T (k + 1) k) h I
    (q, (1 / 2 : ℝ) • (inventoryPrice W γ κ (wts T (k + 1) k) h (I + q) +
      historyPrice W c (wts T (k + 1) k) h))

end UnobservedWelfare


