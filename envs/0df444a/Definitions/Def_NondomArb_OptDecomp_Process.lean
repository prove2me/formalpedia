-- Prove2me | Definitions.Def_NondomArb_OptDecomp_Process
-- name    : NondomArb_OptDecomp_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T15:16:13.816636+00:00
-- url     : https://prove2.me/theorems/29b310b4-f64c-4bf5-a6a0-aade1a61976b
-- title:
--   §1.2, §6: adapted processes, the wealth process H • S_t, supermartingales under Q, adapted increasing processes
-- statement:
--   This definition adds the process vocabulary of the nondominated optional decomposition (Bouchard–Nutz, §6) to the market of the Model definition.
--
--   1. **Adapted process.** A real-valued process $V = (V_t)_{t = 0, \dots, T}$ is adapted if each $V_t$ is an $\mathcal F_t$-measurable function on $\Omega_t = \Omega_1^t$, that is, a universally measurable function of the first $t$ coordinates of the path. In particular $V_0$ is a constant.
--   2. **Wealth process (1.2).** For a strategy $H \in \mathcal H$ and $t \in \{0, \dots, T\}$,
--   $$H \bullet S_t = \sum_{u=1}^t H_u \Delta S_u, \qquad \Delta S_u = S_u - S_{u-1},$$
--   a function on $\Omega_t$; $H \bullet S_0 = 0$ and $H \bullet S_T$ is the terminal wealth.
--   3. **Supermartingale under $Q$.** For a probability measure $Q$ on $\Omega$, $V$ is a $Q$-supermartingale in the filtration $(\mathcal F_t)$ if every $V_t$ is $Q$-integrable and
--   $$E_Q[V_{t+1} \mathbf 1_B] \le E_Q[V_t \mathbf 1_B] \quad \text{for all } B \in \mathcal F_t,\ t = 0, \dots, T-1,$$
--   that is, $E_Q[V_{t+1} \mid \mathcal F_t] \le V_t$ $Q$-a.s.
--   4. **Adapted increasing process.** $K = (K_t)_{t=0, \dots, T}$ is adapted increasing if it is adapted and every path is nondecreasing: $K_t(\omega_1, \dots, \omega_t) \le K_{t+1}(\omega_1, \dots, \omega_{t+1})$ for all $t < T$ and all $\omega$.
--
--   These are the objects in which Theorem 6.1 is stated: a process that is a supermartingale under every martingale measure decomposes as $V_0 + H \bullet S - K$.
--
--   **Formalization Note.** A process is a family `V t : (Fin t → Ω₁) → ℝ`, read on $\Omega$ through the prefix map, so adaptedness is built into the type and measurability is universal measurability on $\Omega_t$. The supermartingale inequality is tested on Borel sets $B \subseteq \Omega_t$, which is equivalent to testing on $\mathcal F_t$ because $\mathcal F_t$ is the universal completion of $\mathcal B(\Omega_t)$. Adaptedness of $V$ is a separate hypothesis wherever it is needed. Monotonicity of $K$ is required for every path, not only quasi surely; the two readings give the same Theorem 6.1, because a quasi-surely increasing adapted $K$ with $K_0 = 0$ can be replaced by its running maximum $\max_{s \le t} K_s$, which is adapted, increasing on every path and quasi-surely equal to $K$.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 4, (1.2); pp. 33–34, §6, Theorem 6.1

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_OptDecomp_Model

namespace NondomArb.OptDecomp

open MeasureTheory

/-! §1.2 and §6 (pp. 4, 33–35) of Bouchard–Nutz: adapted real-valued processes on the
nondominated market, the wealth process `H • S_t`, supermartingales under a measure `Q`, and
adapted increasing processes. A process is a family `V t : Ω_t → ℝ`, `t = 0, …, T`; read on
`Ω` it is `ω ↦ V t (ω_1, …, ω_t)`, so a function on `Ω_t` is exactly an `F_t`-measurable
dependence on the first `t` coordinates. -/

section Process

variable {Ω₁ : Type*} [MeasurableSpace Ω₁] [TopologicalSpace Ω₁] {T d e : ℕ}

namespace Market

/-- An *adapted process* (p. 33): `V_t : Ω_t → ℝ` is `F_t`-measurable, i.e. universally
measurable on `Ω_t`, for `t = 0, …, T`. -/
def Adapted (_M : Market Ω₁ T d e) (V : (t : ℕ) → (Fin t → Ω₁) → ℝ) : Prop :=
  ∀ t ≤ T, NondomArb.Superhedge.IsUMeasurable (V t)

/-- **(1.2)** The wealth process at time `t ≤ T`, as a function on `Ω_t`:
`H • S_t = Σ_{u=1}^t H_u ΔS_u` (Lean index `u = 0, …, t − 1`, where `H u` is the paper's
`H_{u+1}` and `ΔS_{u+1} = S_{u+1} − S_u`). At `t = T` it is `wealth`. -/
def gainAt (M : Market Ω₁ T d e) (H : (u : ℕ) → (Fin u → Ω₁) → (Fin d → ℝ)) (t : ℕ)
    (ω : Fin t → Ω₁) : ℝ :=
  ∑ u : Fin t, H (u : ℕ) (NondomArb.Superhedge.pre ω u u.isLt.le) ⬝ᵥ
    (M.S ((u : ℕ) + 1) (NondomArb.Superhedge.pre ω ((u : ℕ) + 1) u.isLt) - M.S (u : ℕ) (NondomArb.Superhedge.pre ω u u.isLt.le))

/-- `V` is a *supermartingale under* `Q` in the filtration `(F_t)` (Theorem 6.1(i), p. 34):
every `V_t`, `t = 0, …, T`, is `Q`-integrable and `E_Q[V_{t+1} 1_B] ≤ E_Q[V_t 1_B]` for every
`B ∈ F_t`, `t = 0, …, T − 1` (adaptedness is assumed separately). Since `F_t` is the universal
completion of `B(Ω_t)`, Borel test sets `B ⊆ Ω_t` suffice. -/
def IsSupermartingale (_M : Market Ω₁ T d e) (V : (t : ℕ) → (Fin t → Ω₁) → ℝ)
    (Q : Measure (Fin T → Ω₁)) : Prop :=
  (∀ t (ht : t ≤ T), Integrable (fun ω => V t (NondomArb.Superhedge.pre ω t ht)) Q) ∧
  ∀ t (ht : t < T), ∀ B : Set (Fin t → Ω₁), MeasurableSet B →
    ∫ ω in (fun ω => NondomArb.Superhedge.pre ω t ht.le) ⁻¹' B, V (t + 1) (NondomArb.Superhedge.pre ω (t + 1) ht) ∂Q ≤
      ∫ ω in (fun ω => NondomArb.Superhedge.pre ω t ht.le) ⁻¹' B, V t (NondomArb.Superhedge.pre ω t ht.le) ∂Q

/-- An *adapted increasing process* (Theorem 6.1(ii), p. 34): `K_t` is `F_t`-measurable for
`t = 0, …, T`, and every path is nondecreasing, `K_t(ω_1, …, ω_t) ≤ K_{t+1}(ω_1, …, ω_{t+1})`
for all `t < T` and all `ω`. -/
def IsAdaptedIncreasing (M : Market Ω₁ T d e) (K : (t : ℕ) → (Fin t → Ω₁) → ℝ) : Prop :=
  M.Adapted K ∧ ∀ t < T, ∀ ω : Fin (t + 1) → Ω₁, K t (NondomArb.Superhedge.pre ω t (Nat.le_succ t)) ≤ K (t + 1) ω

end Market

end Process

end NondomArb.OptDecomp


