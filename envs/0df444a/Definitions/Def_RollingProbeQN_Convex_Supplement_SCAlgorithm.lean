-- Prove2me | Definitions.Def_RollingProbeQN_Convex_Supplement_SCAlgorithm
-- name    : RollingProbeQN_Convex_Supplement_SCAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:42:43.009642+00:00
-- url     : https://prove2.me/theorems/9380b217-7c14-4ef8-ace8-32140e618c13
-- title:
--   Algorithm 2 (SC-RP-QNPE) run against a gradient oracle, its queries and its stopping rule
-- statement:
--   **Algorithm 2** (SC-RP-QNPE) is run against a gradient oracle $G$ (the theorems take $G=\nabla f$). Initialize $x_0=z_0$, $A_0=0$, $M_{-1}=0$, $b=L_2R$, and query $G(x_0)$. At iteration $k=0,1,\dots$:
--
--   1. If the cached $G(x_k)$ is $0$, return $x_k$. Otherwise refresh the columns of group $g_{i_k}$, $i_k=(k\bmod\chi)+1$, by (4): $\tau_k=b/(\sqrt\chi L_2|g_{i_k}|(k+1)^2)$, $u_k=(G(x_k+\tau_kv_{g_{i_k}})-G(x_k))/\tau_k$, $M_ke_j=P_ju_k$ for $j\in g_{i_k}$ and $M_ke_j=M_{k-1}e_j$ otherwise, $B_k=\Pi_{\mathcal Z}((M_k+M_k^\top)/2)$; and form $\bar E_k$ by (5) with $\delta_j=\|x_{j+1}-x_j\|$: $\bar E_k=L_1$ for $k<\chi$, and $\bar E_k=\min\{L_1,2L_2\sum_{j=k-\chi+1}^{k-1}\delta_j+b/(k-\chi+2)^2\}$ otherwise.
--   2. Choose $\lambda_k$ by Subroutine 2.1 and set, by (13)–(14), $a_k=a(\lambda_k)$, $A_{k+1}=A_k+a_k$, $\eta_k=a_k(1+\mu A_k)/(1+\mu A_{k+1})$, $W_k=A_k+\eta_k$, $y_k=(A_kx_k+\eta_kz_k)/W_k$.
--   3. Query $G(y_k)$ and set $r_k=-(B_k+\lambda_k^{-1}I)^{-1}G(y_k)$, $x_{k+1}=y_k+r_k$.
--   4. Query $G(x_{k+1})$ (cached as the next anchor gradient) and set
--   $$z_{k+1}=z_k+\frac{a_k}{1+\mu A_{k+1}}\big[\mu(x_{k+1}-z_k)-G(x_{k+1})\big].$$
--   5. For a target accuracy $\varepsilon$, return $x_{k+1}$ once $A_{k+1}\ge R^2/(2\varepsilon)$.
--
--   The definition records the state at the start of every iteration, the quantities each iteration computes, whether iteration $k$ is executed, the list of oracle queries of each iteration (the probe point, $y_k$, $x_{k+1}$) and of the run (preceded by $x_0$), and the first-return rule with its returned point.
--
--   **Formalization Note** The run without Step 5 is frozen after a return at a zero gradient; the $\varepsilon$-run is that run stopped at its first return. Groups are 0-based ($k\bmod\chi$). The published `Config`, `colProj`, `groupVec`, `groupCard`, `clipZ` and `modelStep` are reused; the state is a new record because Algorithm 2's displacement $\delta_j=\|x_{j+1}-x_j\|$ differs from Algorithm 1's.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Algorithm 2, p. 15; (13)–(15), p. 13; (4)–(5), p. 9; Subroutine 2.1, p. 14

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_colProj
import Definitions.Def_RollingProbeQN_Convex_groupVec
import Definitions.Def_RollingProbeQN_Convex_groupCard
import Definitions.Def_RollingProbeQN_Convex_clipZ
import Definitions.Def_RollingProbeQN_Convex_modelStep
import Definitions.Def_RollingProbeQN_Convex_Config
import Definitions.Def_RollingProbeQN_Convex_Supplement_SCSubroutine

namespace RollingProbeQN.Convex.Supplement

/-- **The state of Algorithm 2 at the start of iteration `k`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 2, p. 15: "Initialize `x0 = z0`,
`A0 = 0`, `M−1 = 0` and `b = L2R`, and compute `∇f(x0)`."

Fields: the iterate `x = x_k`, the auxiliary iterate `z = z_k`, the weight `A = A_k`, the stored matrix
`M = M_{k−1}`, the cached oracle answer `gx` at `x_k`, the displacements `δ j = δ_j = ‖x_{j+1} − x_j‖`
for `j < k`, and the flag `done`, set when Step 1 has returned.

**Formalization Note.** A new record, not the published `RunState`, whose `δ` is Algorithm 1's
`‖y_j − x_j‖ + ‖r_j‖`. Entries `δ j` with `j ≥ k` are `0` and unused; after a return at a zero gradient
the state is frozen (reading R2 of the base mission). -/
structure SCState (d : ℕ) where
  /-- the iterate `x_k` -/
  x : EuclideanSpace ℝ (Fin d)
  /-- the auxiliary iterate `z_k` -/
  z : EuclideanSpace ℝ (Fin d)
  /-- the weight `A_k` -/
  A : ℝ
  /-- the stored matrix `M_{k−1}` -/
  M : Matrix (Fin d) (Fin d) ℝ
  /-- the cached oracle answer at `x_k` -/
  gx : EuclideanSpace ℝ (Fin d)
  /-- the displacements `δ_j = ‖x_{j+1} − x_j‖`, `j < k` -/
  δ : ℕ → ℝ
  /-- whether Step 1 has returned -/
  done : Bool

/-- **The quantities one iteration of Algorithm 2 computes.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 2, (13)–(15) and Subroutine 2.1,
pp. 13–15.

Fields: the probe radius `τ_k`, the probe point, the stored matrix `M_k`, the model `B_k`, the
certificate `Ē_k`, the model step `λ̄_k`, the bracket `(λ_k, λ⁺)` returned by Subroutine 2.1, the weight
`a_k`, the weight `A_{k+1}`, `η_k`, `W_k`, the center `y_k`, the step `r_k`, the iterate `x_{k+1}`, the
oracle answer at `x_{k+1}` and the auxiliary iterate `z_{k+1}`. -/
structure SCIterData (d : ℕ) where
  /-- the probe radius `τ_k` -/
  τ : ℝ
  /-- the probe point `x_k + τ_k v_{g_{i_k}}` -/
  probe : EuclideanSpace ℝ (Fin d)
  /-- the refreshed matrix `M_k` -/
  M : Matrix (Fin d) (Fin d) ℝ
  /-- the model `B_k` -/
  B : Matrix (Fin d) (Fin d) ℝ
  /-- the certificate `Ē_k` -/
  Ebar : ℝ
  /-- the model step `λ̄_k`, the upper end of the initial bracket -/
  lamBar : ℝ
  /-- the stepsize `λ_k` (lower end of the returned bracket) -/
  lam : ℝ
  /-- the upper end of the returned bracket -/
  lamPlus : ℝ
  /-- the weight `a_k` -/
  a : ℝ
  /-- the weight `A_{k+1}` -/
  A' : ℝ
  /-- `η_k = a_k(1 + μA_k)/(1 + μA_{k+1})` -/
  η : ℝ
  /-- `W_k = A_k + η_k` -/
  W : ℝ
  /-- the center `y_k` -/
  y : EuclideanSpace ℝ (Fin d)
  /-- the model step `r_k` -/
  r : EuclideanSpace ℝ (Fin d)
  /-- the new iterate `x_{k+1}` -/
  x' : EuclideanSpace ℝ (Fin d)
  /-- the oracle answer at `x_{k+1}` -/
  gx' : EuclideanSpace ℝ (Fin d)
  /-- the auxiliary iterate `z_{k+1}` -/
  z' : EuclideanSpace ℝ (Fin d)

/-- **Steps 1–4 of one iteration of Algorithm 2 against an oracle `G`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 2, p. 15, with (4)–(5), p. 9,
(13)–(15), p. 13 and Subroutine 2.1, p. 14. From the state at the start of iteration `k`:
1. refresh group `g_{i_k}`, `i_k = (k mod χ) + 1`, by (4): `τ_k = b/(√χ L2|g_{i_k}|(k+1)²)`,
   `u_k = (∇f(x_k + τ_k v_{g_{i_k}}) − ∇f(x_k))/τ_k`, `M_k e_j = P_j u_k` for `j ∈ g_{i_k}` and
   `M_k e_j = M_{k−1}e_j` otherwise, `B_k = Π_Z((M_k + M_kᵀ)/2)`; form `Ē_k` by (5) with
   `δ_j = ‖x_{j+1} − x_j‖`: `Ē_k = L1` for `k < χ`, else `min{L1, 2L2∑_{j=k−χ+1}^{k−1} δ_j + b/(k−χ+2)²}`;
2. `λ_k` by Subroutine 2.1 with `A_k`, `ζ_k = ‖z_k − x_k‖`, `g_k = ‖∇f(x_k)‖`, `Ē_k`; then
   `a_k` by (13), `A_{k+1} = A_k + a_k`, `η_k = a_k(1 + μA_k)/(1 + μA_{k+1})`, `W_k = A_k + η_k`,
   `y_k = (A_k x_k + η_k z_k)/W_k` (14);
3. `r_k = −(B_k + λ_k⁻¹I)⁻¹∇f(y_k)`, `x_{k+1} = y_k + r_k`;
4. `z_{k+1} = z_k + a_k/(1 + μA_{k+1})·[μ(x_{k+1} − z_k) − ∇f(x_{k+1})]` (15).

**Formalization Note.** Every gradient is a call of the oracle `G` (reading R3 of the base mission);
`∇f(x_k)` is the cached `st.gx`, so an iteration calls `G` at the probe point, at `y_k` and at
`x_{k+1}` only. The refreshed group has 0-based label `k % χ` (reading R5). The window
`{k−χ+1, …, k−1}` is `Finset.Ico (k + 1 − χ) k`, used only for `k ≥ χ`. `μ` and `R` are passed
explicitly; the configuration supplies `grp, S, L₁, L₂, b, σ`. -/
noncomputable def scIterData {d χ : ℕ} (cfg : Config d χ) (μ R : ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (k : ℕ) (st : SCState d) :
    SCIterData d :=
  let τ : ℝ := cfg.b / (Real.sqrt χ * cfg.L₂ * (groupCard cfg.grp (k % χ) : ℝ) * ((k : ℝ) + 1) ^ 2)
  let probe : EuclideanSpace ℝ (Fin d) := st.x + τ • groupVec cfg.grp (k % χ)
  let u : EuclideanSpace ℝ (Fin d) := τ⁻¹ • (G probe - st.gx)
  let M : Matrix (Fin d) (Fin d) ℝ :=
    fun i j => if (cfg.grp j : ℕ) = k % χ then colProj cfg.S j u i else st.M i j
  let B : Matrix (Fin d) (Fin d) ℝ := clipZ cfg.L₁ ((1 / 2 : ℝ) • (M + M.transpose))
  let Ebar : ℝ := if k < χ then cfg.L₁ else
    min cfg.L₁ (2 * cfg.L₂ * (∑ j ∈ Finset.Ico (k + 1 - χ) k, st.δ j)
      + cfg.b / ((k : ℝ) - (χ : ℝ) + 2) ^ 2)
  let out : ℝ × ℝ := sub21 cfg.L₁ cfg.L₂ R cfg.σ μ st.A ‖st.z - st.x‖ ‖st.gx‖ Ebar
  let lam : ℝ := out.1
  let a : ℝ := aSC μ st.A lam
  let A' : ℝ := st.A + a
  let η : ℝ := a * (1 + μ * st.A) / (1 + μ * A')
  let W : ℝ := st.A + η
  let y : EuclideanSpace ℝ (Fin d) := W⁻¹ • (st.A • st.x + η • st.z)
  let r : EuclideanSpace ℝ (Fin d) := modelStep B lam (G y)
  let x' : EuclideanSpace ℝ (Fin d) := y + r
  let gx' : EuclideanSpace ℝ (Fin d) := G x'
  { τ := τ, probe := probe, M := M, B := B, Ebar := Ebar, lamBar := rootSC Ebar cfg.σ μ,
    lam := lam, lamPlus := out.2, a := a, A' := A', η := η, W := W, y := y, r := r, x' := x',
    gx' := gx', z' := st.z + (a / (1 + μ * A')) • (μ • (x' - st.z) - gx') }

/-- **One iteration of Algorithm 2 (without the stopping rule of Step 5).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 2, p. 15: "1. Refresh and
certify. If `∇f(xk) = 0`, return `xk`. […] 4. Correct the momentum. Evaluate `∇f(xk+1)` and update
`zk+1` by (15)."

If the run has returned, the state is unchanged. If the cached oracle answer at `x_k` is zero, Step 1
returns: `done` is set and nothing else changes. Otherwise the state moves to `x_{k+1}`, `z_{k+1}`,
`A_{k+1}`, `M_k`, the cached answer at `x_{k+1}`, and records `δ_k = ‖x_{k+1} − x_k‖`.

**Formalization Note.** Reading R2 of the base mission: the return of Step 1 freezes the state. The
stopping rule of Step 5 is not part of the step; the ε-run is the run stopped at its first return
(`scEpsReturns`). -/
noncomputable def scStep {d χ : ℕ} (cfg : Config d χ) (μ R : ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (k : ℕ) (st : SCState d) :
    SCState d :=
  open Classical in
  if st.done then st
  else if st.gx = 0 then { st with done := true }
  else
    { x := (scIterData cfg μ R G k st).x', z := (scIterData cfg μ R G k st).z',
      A := (scIterData cfg μ R G k st).A', M := (scIterData cfg μ R G k st).M,
      gx := (scIterData cfg μ R G k st).gx',
      δ := Function.update st.δ k ‖(scIterData cfg μ R G k st).x' - st.x‖,
      done := false }

/-- **The run of Algorithm 2 (SC-RP-QNPE) with Subroutine 2.1 against an oracle `G`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 2, p. 15: "Initialize `x0 = z0`,
`A0 = 0`, `M−1 = 0` and `b = L2R`, and compute `∇f(x0)`. For `k = 0, 1, . . .`: […]".

`scRun cfg μ R G x₀ k` is the state at the start of iteration `k`; at `k = 0` it has `x = z = x₀`,
`A = 0`, `M = 0`, the oracle answer `G x₀` (the first query) and no recorded displacement.

**Formalization Note.** The run is a function of the oracle `G` (reading R3); the theorems take
`G = gradient f` and `cfg.b = L₂R`. -/
noncomputable def scRun {d χ : ℕ} (cfg : Config d χ) (μ R : ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d)) :
    ℕ → SCState d
  | 0 => { x := x₀, z := x₀, A := 0, M := 0, gx := G x₀, δ := fun _ => 0, done := false }
  | k + 1 => scStep cfg μ R G k (scRun cfg μ R G x₀ k)

/-- **The quantities of iteration `k` along the run of Algorithm 2.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 2, p. 15.

`scIterAt cfg μ R G x₀ k` is `scIterData` at the state `scRun cfg μ R G x₀ k`; its values are the
paper's when iteration `k` is executed (`scActive`). -/
noncomputable def scIterAt {d χ : ℕ} (cfg : Config d χ) (μ R : ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d))
    (k : ℕ) : SCIterData d :=
  scIterData cfg μ R G k (scRun cfg μ R G x₀ k)

/-- **Iteration `k` of Algorithm 2 is executed.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 2, Step 1, p. 15: "If
`∇f(xk) = 0`, return `xk`."

Iteration `k` is executed when the run has not returned before it and the oracle answer at `x_k` is
nonzero. -/
def scActive {d χ : ℕ} (cfg : Config d χ) (μ R : ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d))
    (k : ℕ) : Prop :=
  (scRun cfg μ R G x₀ k).done = false ∧ (scRun cfg μ R G x₀ k).gx ≠ 0

/-- **The oracle queries of iteration `k` of Algorithm 2.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, p. 15: "Each iteration queries the probe
gradient, `∇f(yk)` and `∇f(xk+1)`, which is cached as the next anchor gradient […]; Subroutine 2.1 uses
none."

Empty when the iteration is not executed, and `[probe point, y_k, x_{k+1}]` otherwise.

**Formalization Note.** Readings R3, R4 of the base mission: the gradient count is the number of oracle
calls. -/
noncomputable def scIterQueries {d χ : ℕ} (cfg : Config d χ) (μ R : ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d))
    (k : ℕ) : List (EuclideanSpace ℝ (Fin d)) :=
  open Classical in
  if scActive cfg μ R G x₀ k then
    [(scIterAt cfg μ R G x₀ k).probe, (scIterAt cfg μ R G x₀ k).y, (scIterAt cfg μ R G x₀ k).x']
  else []

/-- **All oracle queries of Algorithm 2 before iteration `k`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 2, p. 15, and §F.7, p. 63: "The
algorithm queries one initial gradient and at most three gradients per iteration".

`scAllQueries cfg μ R G x₀ k = [x₀] ++ scIterQueries 0 ++ ⋯ ++ scIterQueries (k − 1)`.

**Formalization Note.** Reading R4: the count includes the initial query at `x₀`. -/
noncomputable def scAllQueries {d χ : ℕ} (cfg : Config d χ) (μ R : ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d))
    (k : ℕ) : List (EuclideanSpace ℝ (Fin d)) :=
  x₀ :: (List.range k).flatMap (fun j => scIterQueries cfg μ R G x₀ j)

/-- **Iteration `k` of Algorithm 2 returns, for target accuracy `ε`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 2, p. 15: "1. […] If `∇f(xk) = 0`,
return `xk`. […] 5. Check progress. For target accuracy `ε`, return `xk+1` once `Ak+1 ≥ R²/(2ε)`."

Iteration `k` returns when the run has not returned before it and either the oracle answer at `x_k` is
zero (Step 1) or the iteration completes with `A_{k+1} ≥ R²/(2ε)` (Step 5). The ε-run is the run
stopped at the first such `k`. -/
def scEpsReturns {d χ : ℕ} (cfg : Config d χ) (μ R : ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d))
    (ε : ℝ) (k : ℕ) : Prop :=
  (scRun cfg μ R G x₀ k).done = false ∧
    ((scRun cfg μ R G x₀ k).gx = 0 ∨ R ^ 2 / (2 * ε) ≤ (scRun cfg μ R G x₀ (k + 1)).A)

/-- **The point Algorithm 2 returns at iteration `k`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 2, p. 15: Step 1 returns `xk`;
Step 5 returns `xk+1`.

`x_k` if the oracle answer at `x_k` is zero, and `x_{k+1}` otherwise. -/
noncomputable def scEpsOutput {d χ : ℕ} (cfg : Config d χ) (μ R : ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d))
    (k : ℕ) : EuclideanSpace ℝ (Fin d) :=
  open Classical in
  if (scRun cfg μ R G x₀ k).gx = 0 then (scRun cfg μ R G x₀ k).x
  else (scRun cfg μ R G x₀ (k + 1)).x

end RollingProbeQN.Convex.Supplement


