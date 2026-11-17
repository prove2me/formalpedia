-- Prove2me | Definitions.Def_RollingProbeQN_Convex_Supplement_OQN
-- name    : RollingProbeQN_Convex_Supplement_OQN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:45:34.357196+00:00
-- url     : https://prove2.me/theorems/9acd2d9e-3e30-430d-a750-95ab137c4339
-- title:
--   Algorithm 3 (RP-OQN), model and gradient variants, run against a gradient oracle
-- statement:
--   **Algorithm 3** (RP-OQN) is run against a gradient oracle $G$ with inputs $x_0$, a radius $D$, a learning rate $\eta$ and the variant. Set $\Delta_0=0$, $z_0=x_0$, $\theta_0=0$ and, in the model variant, $\tau_g=2D/(\sqrt\chi|g|)$ for every group $g$.
--
--   1. **Warm-up.** Query $G(x_0)$. In the model variant, query $G(x_0+\tau_gv_g)$ for every group $g$ and set column $j\in g$ of $M_0$ to $P_ju_g$, $u_g=(G(x_0+\tau_gv_g)-G(x_0))/\tau_g$.
--   2. **Iteration $n=0,1,\dots$** (a) If $n\ge1$, query $G(z_n)$, $z_n=x_n+\Delta_n/2$, and in the model variant refresh group $g_{i_n}$, $i_n=((n-1)\bmod\chi)+1$, by (33): $u_n=(G(z_n+\tau_gv_g)-G(z_n))/\tau_g$, $M_ne_j=P_ju_n$ for $j\in g$, $M_ne_j=M_{n-1}e_j$ otherwise. Set $B_n=(M_n+M_n^\top)/2$ (model) or $B_n=0$ (gradient). (b) In the model variant, $\Delta_{n+1}$ is a $\nu$-approximate solution of $\min_{\|\Delta\|\le D}\phi_n(\Delta)$ returned by a solver from the stored data; in the gradient variant $\Delta_{n+1}=\Pi_D(\Delta_n-\eta\theta_n-\eta G(z_n))$, where $\Pi_D(v)=v$ if $\|v\|\le D$ and $Dv/\|v\|$ otherwise. (c) Set $x_{n+1}=x_n+\Delta_{n+1}$, $w_{n+1}=x_n+\Delta_{n+1}/2$, query $G(w_{n+1})$ and set $\theta_{n+1}=G(w_{n+1})-G(z_n)-\tfrac12B_n(\Delta_{n+1}-\Delta_n)$.
--
--   The query list of a run of $N$ iterations is the warm-up ($x_0$, plus the $\chi$ probes in the model variant), then $w_1$, then for each $n=1,\dots,N-1$ the points $z_n$, $z_n+\tau_gv_g$ (model only) and $w_{n+1}$: $3N+\chi-1$ queries in the model variant and $2N$ in the gradient variant. A solver satisfies the **$\nu$-approximation property** if its output is a $\nu$-approximate solution (31) for every step and every input with symmetric $B$ and $\|\Delta_n\|\le D$.
--
--   **Formalization Note** The run is a function of the oracle and of the solver; the gradient variant never calls the solver. Solvers may depend on the step index, so every admissible sequence of approximate solutions is realized by some solver; one exists since an exact minimizer over the ball is a KKT point (Lemma I.3). Groups are 0-based; the published `colProj`, `groupVec` and `groupCard` are reused.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Algorithm 3, p. 20; (33), p. 20; cost, p. 21; Π_D, p. 71

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_colProj
import Definitions.Def_RollingProbeQN_Convex_groupVec
import Definitions.Def_RollingProbeQN_Convex_groupCard
import Definitions.Def_RollingProbeQN_Convex_Supplement_Conversion

namespace RollingProbeQN.Convex.Supplement

/-- **The projection `Π_D` onto the closed ball of radius `D`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, p. 71: "`ΠD(v) = v` if `‖v‖ ≤ D` and
`ΠD(v) = Dv/‖v‖` otherwise". -/
noncomputable def ballProj {d : ℕ} (D : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  if ‖v‖ ≤ D then v else (D / ‖v‖) • v

/-- **The fixed data of Algorithm 3 (RP-OQN).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 3, p. 20: "Input: `x0`, a radius
`D`, an episode length `T`, a learning rate `η`, a number of episodes `K`, a subproblem accuracy `ν`,
and the variant (model or gradient)", with the pattern `S` and the partition of Assumption 5.1.

Fields: the group map `grp`, the pattern `S`, the radius `D`, the learning rate `η`, and `model`
(`true` for the model variant, `false` for the gradient variant).

**Formalization Note.** `x₀` is an argument of the run, `T` and `K` enter through the horizon
`N = KT`, and `ν` through the solver hypothesis (`IsNuSolver`). -/
structure OQNConfig (d χ : ℕ) where
  /-- the group of each column (0-based) -/
  grp : Fin d → Fin χ
  /-- the sparsity pattern `S` -/
  S : Set (Fin d × Fin d)
  /-- the radius `D` -/
  D : ℝ
  /-- the learning rate `η` -/
  η : ℝ
  /-- `true`: model variant; `false`: gradient variant -/
  model : Bool

/-- **The state of Algorithm 3 at the start of iteration `n`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 3, p. 20.

Fields: `x = x_n`, `Δ = Δ_n`, `θ = θ_n`, the stored matrix `M` (`M_0` for `n ≤ 1`, `M_{n−1}` for
`n ≥ 1`), the midpoint `w = w_n` and the oracle answer `gw` at `w_n`.

**Formalization Note.** At `n = 0`, `w` and `gw` hold `x₀` and its oracle answer; no statement reads
them (episodes start at `n = 1`). -/
structure OQNState (d : ℕ) where
  /-- the iterate `x_n` -/
  x : EuclideanSpace ℝ (Fin d)
  /-- the increment `Δ_n` -/
  Δ : EuclideanSpace ℝ (Fin d)
  /-- the prediction error `θ_n` -/
  θ : EuclideanSpace ℝ (Fin d)
  /-- the stored matrix -/
  M : Matrix (Fin d) (Fin d) ℝ
  /-- the midpoint `w_n` -/
  w : EuclideanSpace ℝ (Fin d)
  /-- the oracle answer at `w_n` -/
  gw : EuclideanSpace ℝ (Fin d)

/-- **The quantities one iteration of Algorithm 3 computes.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 3, Step 2, p. 20.

Fields: the probe point `z_n`, the oracle answer at `z_n`, the displaced probe point `z_n + τ_g v_g`,
the matrix `M_n`, the model `B_n`, the increment `Δ_{n+1}`, `x_{n+1}`, `w_{n+1}`, the oracle answer at
`w_{n+1}` and `θ_{n+1}`. -/
structure OQNIterData (d : ℕ) where
  /-- the probe point `z_n` -/
  z : EuclideanSpace ℝ (Fin d)
  /-- the oracle answer at `z_n` -/
  gz : EuclideanSpace ℝ (Fin d)
  /-- the displaced probe point `z_n + τ_g v_g` -/
  probe : EuclideanSpace ℝ (Fin d)
  /-- the matrix `M_n` -/
  M : Matrix (Fin d) (Fin d) ℝ
  /-- the model `B_n` -/
  B : Matrix (Fin d) (Fin d) ℝ
  /-- the increment `Δ_{n+1}` -/
  Δ' : EuclideanSpace ℝ (Fin d)
  /-- the iterate `x_{n+1}` -/
  x' : EuclideanSpace ℝ (Fin d)
  /-- the midpoint `w_{n+1}` -/
  w' : EuclideanSpace ℝ (Fin d)
  /-- the oracle answer at `w_{n+1}` -/
  gw' : EuclideanSpace ℝ (Fin d)
  /-- the prediction error `θ_{n+1}` -/
  θ' : EuclideanSpace ℝ (Fin d)

/-- **The probe radius `τ_g = 2D/(√χ|g|)` of Algorithm 3.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, §5.2, p. 20: "`τg = 2D/(√χ|g|)` for every
group `g`".

**Formalization Note.** Groups are labelled `c : ℕ`, 0-based (reading R5 of the base mission). -/
noncomputable def oqnTau {d χ : ℕ} (cfg : OQNConfig d χ) (c : ℕ) : ℝ :=
  2 * cfg.D / (Real.sqrt χ * (groupCard cfg.grp c : ℝ))

/-- **The warm-up matrix `M_0` of the model variant.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 3, Step 1, p. 20: "Evaluate
`∇f(x0)`. In the model variant, evaluate `∇f(x0 + τg vg)` for every group `g` and store the `χ` blocks
in `M0` by the block formula of (33)", (33): `M e_j = P_j u` for `j ∈ g`,
`u = (∇f(x0 + τg vg) − ∇f(x0))/τg`.

Column `j` of `M_0` is `P_j u_g` for the group `g` of `j`. -/
noncomputable def oqnWarmM {d χ : ℕ} (cfg : OQNConfig d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => colProj cfg.S j ((oqnTau cfg (cfg.grp j : ℕ))⁻¹ •
    (G (x₀ + oqnTau cfg (cfg.grp j : ℕ) • groupVec cfg.grp (cfg.grp j : ℕ)) - G x₀)) i

/-- **The increment solver of the model variant, and its ν-approximation property.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 3, Step 2(b), p. 20: "Compute a
`ν`-approximate solution `Δn+1` of `min‖Δ‖≤D φn(Δ)`, with `φn` as in (30)".

A solver maps the step `n` and the stored data (`∇f(z_n)`, `θ_n`, `B_n`, `Δ_n`) to `Δ_{n+1}`;
`IsNuSolver D η ν solver` says that its output is a ν-approximate solution (31) for every step and every
input with symmetric `B` and `‖Δ_n‖ ≤ D`.

**Formalization Note.** Approximate solutions are not unique; the theorems quantify over every such
solver, which covers every admissible choice of `Δ_{n+1}` along the run (the dependence on `n` allows
any choice). Such a solver exists: an exact minimizer of `φ_n` over the ball is a KKT point
(Lemma I.3, p. 71). The solver queries no gradient. -/
def IsNuSolver {d : ℕ} (D η ν : ℝ)
    (solver : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →
      Matrix (Fin d) (Fin d) ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ (n : ℕ) (gz θ : EuclideanSpace ℝ (Fin d)) (B : Matrix (Fin d) (Fin d) ℝ)
    (Δn : EuclideanSpace ℝ (Fin d)), B.IsSymm → ‖Δn‖ ≤ D →
    IsNuApprox D η ν gz θ B Δn (solver n gz θ B Δn)

/-- **Step 2 of one iteration of Algorithm 3 against an oracle `G`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 3, p. 20, with (23), (29), (33):
"(a) Probe and read out. If `n ≥ 1`, evaluate `∇f(zn)` and, in the model variant, refresh the columns
of group `gin` by (33). Set `Bn = (Mn + Mnᵀ)/2` in the model variant and `Bn = 0` in the gradient
variant. (b) Choose the increment. Compute a `ν`-approximate solution `Δn+1` of `min‖Δ‖≤D φn(Δ)` […];
in the gradient variant, `Δn+1 = ΠD(Δn − ηθn − η∇f(zn))`. (c) Step and observe. Set
`xn+1 = xn + Δn+1`, `wn+1 = xn + 1/2 Δn+1` and `zn+1 = xn+1 + 1/2 Δn+1`; evaluate `∇f(wn+1)` and set
`θn+1 = ∇f(wn+1) − ∇f(zn) − 1/2 Bn(Δn+1 − Δn)`."

The refresh at `n ≥ 1` uses group `i_n = ((n − 1) mod χ) + 1`, i.e. 0-based label `(n − 1) % χ`:
`u_n = (∇f(z_n + τ_g v_g) − ∇f(z_n))/τ_g`, `M_n e_j = P_j u_n` for `j ∈ g`, `M_n e_j = M_{n−1}e_j`
otherwise; at `n = 0` no refresh is made and `M_0` is the warm-up matrix.

**Formalization Note.** `z_n = x_n + Δ_n/2` (so `z_0 = x₀`). Every gradient is an oracle call; at
`n = 0` the answer at `z_0 = x₀` is the warm-up query. The model variant's increment is
`solver n (G z_n) θ_n B_n Δ_n`; the gradient variant ignores the solver. -/
noncomputable def oqnIterData {d χ : ℕ} (cfg : OQNConfig d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (solver : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →
      Matrix (Fin d) (Fin d) ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (st : OQNState d) : OQNIterData d :=
  let z : EuclideanSpace ℝ (Fin d) := st.x + (1 / 2 : ℝ) • st.Δ
  let gz : EuclideanSpace ℝ (Fin d) := G z
  let c : ℕ := (n - 1) % χ
  let probe : EuclideanSpace ℝ (Fin d) := z + oqnTau cfg c • groupVec cfg.grp c
  let u : EuclideanSpace ℝ (Fin d) := (oqnTau cfg c)⁻¹ • (G probe - gz)
  let M : Matrix (Fin d) (Fin d) ℝ :=
    if cfg.model then
      (if 1 ≤ n then (fun i j => if (cfg.grp j : ℕ) = c then colProj cfg.S j u i else st.M i j)
       else st.M)
    else st.M
  let B : Matrix (Fin d) (Fin d) ℝ := if cfg.model then (1 / 2 : ℝ) • (M + M.transpose) else 0
  let Δ' : EuclideanSpace ℝ (Fin d) :=
    if cfg.model then solver n gz st.θ B st.Δ
    else ballProj cfg.D (st.Δ - cfg.η • st.θ - cfg.η • gz)
  let w' : EuclideanSpace ℝ (Fin d) := st.x + (1 / 2 : ℝ) • Δ'
  let gw' : EuclideanSpace ℝ (Fin d) := G w'
  { z := z, gz := gz, probe := probe, M := M, B := B, Δ' := Δ', x' := st.x + Δ', w' := w',
    gw' := gw', θ' := gw' - gz - (1 / 2 : ℝ) • Matrix.toEuclideanLin B (Δ' - st.Δ) }

/-- **The run of Algorithm 3 (RP-OQN) against an oracle `G`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 3, p. 20: "Set `N = KT`, `Δ0 = 0`,
`z0 = x0`, `θ0 = 0` […] 1. Warm-up. […] 2. For `n = 0, 1, . . . , N − 1`: […]".

`oqnRun cfg G solver x₀ n` is the state at the start of iteration `n`: `x_n`, `Δ_n`, `θ_n`, the stored
matrix, `w_n` and the oracle answer at `w_n`. At `n = 0`: `x₀`, `0`, `0`, the warm-up matrix (model
variant; `0` in the gradient variant).

**Formalization Note.** The run is a function of the oracle `G` and of the solver; the theorems take
`G = gradient f`. -/
noncomputable def oqnRun {d χ : ℕ} (cfg : OQNConfig d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (solver : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →
      Matrix (Fin d) (Fin d) ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x₀ : EuclideanSpace ℝ (Fin d)) : ℕ → OQNState d
  | 0 => { x := x₀, Δ := 0, θ := 0, M := if cfg.model then oqnWarmM cfg G x₀ else 0, w := x₀,
           gw := G x₀ }
  | n + 1 =>
    { x := (oqnIterData cfg G solver n (oqnRun cfg G solver x₀ n)).x',
      Δ := (oqnIterData cfg G solver n (oqnRun cfg G solver x₀ n)).Δ',
      θ := (oqnIterData cfg G solver n (oqnRun cfg G solver x₀ n)).θ',
      M := (oqnIterData cfg G solver n (oqnRun cfg G solver x₀ n)).M,
      w := (oqnIterData cfg G solver n (oqnRun cfg G solver x₀ n)).w',
      gw := (oqnIterData cfg G solver n (oqnRun cfg G solver x₀ n)).gw' }

/-- **The oracle queries of iteration `n` of Algorithm 3.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, p. 21: "In the model variant, iteration
`n ≥ 1` queries three gradients: at the probe point `zn`, at the displaced probe point `zn + τg vg`, and
at the new midpoint `wn+1`; the gradient at `z0 = x0` and the `χ` warm-up probes are queried once. […]
In the gradient variant, iteration `n ≥ 1` queries two gradients, at `zn` and at `wn+1`".

`[w_1]` at `n = 0`; `[z_n, z_n + τ_g v_g, w_{n+1}]` (model) or `[z_n, w_{n+1}]` (gradient) at `n ≥ 1`. -/
noncomputable def oqnIterQueries {d χ : ℕ} (cfg : OQNConfig d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (solver : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →
      Matrix (Fin d) (Fin d) ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x₀ : EuclideanSpace ℝ (Fin d)) (n : ℕ) : List (EuclideanSpace ℝ (Fin d)) :=
  if n = 0 then [(oqnIterData cfg G solver n (oqnRun cfg G solver x₀ n)).w']
  else if cfg.model then
    [(oqnIterData cfg G solver n (oqnRun cfg G solver x₀ n)).z,
     (oqnIterData cfg G solver n (oqnRun cfg G solver x₀ n)).probe,
     (oqnIterData cfg G solver n (oqnRun cfg G solver x₀ n)).w']
  else
    [(oqnIterData cfg G solver n (oqnRun cfg G solver x₀ n)).z,
     (oqnIterData cfg G solver n (oqnRun cfg G solver x₀ n)).w']

/-- **All oracle queries of a run of Algorithm 3 with `N` iterations.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, p. 21: "A run of `N` iterations therefore
costs `3N + χ − 1` gradient queries. In the gradient variant, […] a run costs `2N`."

The warm-up queries (`x₀`, and in the model variant `x₀ + τ_g v_g` for the `χ` groups), followed by the
queries of iterations `0, …, N − 1`.

**Formalization Note.** Readings R3, R4 of the base mission: the count is the number of oracle calls,
including the warm-up. -/
noncomputable def oqnAllQueries {d χ : ℕ} (cfg : OQNConfig d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (solver : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →
      Matrix (Fin d) (Fin d) ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x₀ : EuclideanSpace ℝ (Fin d)) (N : ℕ) : List (EuclideanSpace ℝ (Fin d)) :=
  (x₀ :: (if cfg.model then
      (List.range χ).map (fun c => x₀ + oqnTau cfg c • groupVec cfg.grp c) else [])) ++
    (List.range N).flatMap (fun n => oqnIterQueries cfg G solver x₀ n)

end RollingProbeQN.Convex.Supplement


