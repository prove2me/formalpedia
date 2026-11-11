-- Prove2me | Definitions.Def_OptimalLCA_Matching_Optimizer
-- name    : OptimalLCA_Matching_Optimizer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:46:55.058081+00:00
-- url     : https://prove2.me/theorems/02783ca5-a61f-4614-b792-a6b9a7ff297e
-- title:
--   §5 — Algorithms 2 and 3, q̂, B_Δ, T_δ, q^(δ), the potential Φ₀, the comparison distributions q*
-- statement:
--   **Normalization** (5.1): $N(r)_{ua}=r_{ua}/\sum_{b\in I_u}r_{ub}$.
--
--   **Algorithm 3** (one round on $(x,q,\bar q)$), with $\eta=\tfrac13$ and $z=(x,q)$ the base of every box response:
--   $v=\eta g(x,q)$; $x^*=\mathrm{Resp}_{z,v}(q)$; gradient-stage score $c=\tfrac1{16}(v_q+2L^*(\psi(x^*)-\psi(x)))$; $q'=N(q\,e^{-c})$; $x'=\mathrm{Resp}_{z,v}(q')$;
--   $\tilde v=\tfrac\eta2 g(x',q')$; $x_a=\mathrm{Resp}_{z,\tilde v}(\bar q)$; $a=\tfrac1{64}(\tilde v_q+2L^*(\psi(x_a)-\psi(x)))$; $q^+=N(\sqrt{q\bar q}\,e^{-a})$; $x^+=\mathrm{Resp}_{z,\tilde v}(q^+)$; $\hat s=\tfrac1{64}(\tilde v_q+2L^*(\psi(x^+)-\psi(x)))$; $\bar q^+=N(\bar q\sqrt{q/q^+}\,e^{-\hat s})$. The round returns $(x^+,q^+,\bar q^+,q')$ and all intermediate quantities are recorded.
--
--   **Algorithm 2.** $x_0=(-1+1/\Delta)\mathbf 1$, $q_{0,uv}=1/(2\Delta^2)$ for $v\in N(u)$, $q_{0,u\perp}=1-\deg(u)/(2\Delta^2)$, $\bar q_0=q_0$, then $T$ rounds; the output is $\hat q=\frac1T\sum_{t<T}q'_t$. At an isolated vertex the block is the dummy alone, so all its distributions stay on the dummy (the paper's "isolated vertices return their dummy"); its price coordinate is carried but never enters a proposal update.
--
--   $B_\Delta=200+400\log(2\Delta)$; for $0<\delta<1$, $T_\delta=\lceil 3B_\Delta/\delta\rceil$ and $q^{(\delta)}$ is $\hat q$ with $T=T_\delta$.
--
--   **Potential.** $\Phi_0(w)=D^{32}_{z_0}(w)+64K_{\bar q_0}(w_q)$ with the regularizer and $K$ summed over nonisolated vertices (§5).
--
--   **Comparison distributions** (Lemma 3.1(c)): from a set $M$ of edges of $B(G)$, $u$ puts unit mass on $v$ if $(u,1)(v,2)\in M$ (here sides $0,1$), else on its dummy.
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), pp. 22–28, §5, (5.1), Algorithms 2–3, Theorem 5.1, §5.3–§5.4

import Mathlib
import Definitions.Def_OptimalLCA_Matching_SaddlePoint

/-!
# The optimization method: Algorithms 2 and 3 (Cohen–Roghani, §5)

A deterministic function of the graph `G` and the degree bound `Δ`.

* `normalize G r = N(r)`, `N(r)_{ua} = r_{ua} / ∑_{b ∈ I_u} r_{ub}` (5.1).
* `roundStep G x q qbar` is Algorithm 3 with `η = 1/3` and base `z = (x, q)` for all four
  box responses; it records every intermediate quantity: `xStar = x*`, the gradient-stage
  score `gradScore = (v_q + 2 L*(ψ(x*) - ψ(x))) / 16`, `qPrime = q'`, `xPrime = x'`,
  `xA = x_a`, `scoreA = a`, `qPlus = q⁺`, `xPlus = x⁺`, `scoreS = ŝ`, `qBarPlus = q̄⁺`.
* `initState G Δ`: `x₀ = (-1 + 1/Δ) 1`, `q_{0,uv} = 1/(2Δ²)` for `v ∈ N(u)`,
  `q_{0,u⊥} = 1 - deg(u)/(2Δ²)`, `q̄₀ = q₀`. At an isolated vertex the block is the dummy
  alone, so `q₀` puts mass one on it and every later main, auxiliary and tentative
  distribution keeps it there (the paper's "isolated vertices return their dummy"); the
  price coordinate of an isolated vertex is carried along but never enters any proposal
  update, since `L*` reads only prices of vertices with a neighbour.
* `optState G Δ t = (x_t, q_t, q̄_t)`, `optRound G Δ t` the data of round `t`.
* `qHat G Δ T = (1/T) ∑_{t<T} q'_t`, the output of Algorithm 2 after `T` rounds.
* `bDelta Δ = 200 + 400 log(2Δ)`, `tDelta Δ δ = ⌈3 B_Δ / δ⌉`, `qDelta G Δ δ = q^{(δ)}`.
* `nonisolated G`: the vertices of positive degree; `potential0 G Δ w = Φ₀(w) =
  D^{32}_{z₀}(w) + 64 K_{q̄₀}(w_q)`, with the sums of the regularizer and of `K` over
  nonisolated vertices (§5: "potential sums omit isolated vertices").
* `qStar G M`: the comparison distributions of Lemma 3.1(c) built from a set `M` of
  edges of `B(G)`: `u` puts unit mass on `v` if `(u,1)(v,2) ∈ M`, else on its dummy.
-/

namespace OptimalLCA.Matching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

section Defs

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The normalization `N(r)_{ua} = r_{ua} / ∑_{b ∈ I_u} r_{ub}` (5.1). -/
noncomputable def normalize (r : Idx G → ℝ) : Idx G → ℝ := fun i =>
  r i / ∑ j ∈ univ.filter (fun j : Idx G => owner j = owner i), r j

/-- All intermediate quantities of one round (Algorithm 3). -/
structure RoundData where
  xStar : V → ℝ
  gradScore : Idx G → ℝ
  qPrime : Idx G → ℝ
  xPrime : V → ℝ
  xA : V → ℝ
  scoreA : Idx G → ℝ
  qPlus : Idx G → ℝ
  xPlus : V → ℝ
  scoreS : Idx G → ℝ
  qBarPlus : Idx G → ℝ

/-- Algorithm 3 (one round) on the state `(x, q, q̄)`. -/
noncomputable def roundStep (x : V → ℝ) (q qbar : Idx G → ℝ) : RoundData G :=
  let η : ℝ := 1 / 3
  let z : StateSpace G := (x, q)
  -- gradient stage
  let v : StateSpace G := η • gOp G (x, q)
  let xStar := resp G z v q
  let c : Idx G → ℝ := fun i =>
    (v.2 i + 2 * adjL G (fun j => psi (xStar j) - psi (x j)) i) / 16
  let qPrime := normalize G (fun i => q i * Real.exp (-c i))
  let xPrime := resp G z v qPrime
  -- extragradient stage
  let vt : StateSpace G := (η / 2) • gOp G (xPrime, qPrime)
  let xA := resp G z vt qbar
  let a : Idx G → ℝ := fun i =>
    (1 / 64) * (vt.2 i + 2 * adjL G (fun j => psi (xA j) - psi (x j)) i)
  let qPlus := normalize G (fun i => Real.sqrt (q i * qbar i) * Real.exp (-a i))
  let xPlus := resp G z vt qPlus
  let s : Idx G → ℝ := fun i =>
    (1 / 64) * (vt.2 i + 2 * adjL G (fun j => psi (xPlus j) - psi (x j)) i)
  let qBarPlus := normalize G (fun i => qbar i * Real.sqrt (q i / qPlus i) * Real.exp (-s i))
  ⟨xStar, c, qPrime, xPrime, xA, a, qPlus, xPlus, s, qBarPlus⟩

/-- The optimizer state `(x, q, q̄)`. -/
structure OptState where
  x : V → ℝ
  q : Idx G → ℝ
  qbar : Idx G → ℝ

/-- The initial proposal distributions `q₀` of Algorithm 2. -/
noncomputable def initQ (Δ : ℕ) : Idx G → ℝ
  | .inl u => 1 - (G.degree u : ℝ) / (2 * (Δ : ℝ) ^ 2)
  | .inr _ => 1 / (2 * (Δ : ℝ) ^ 2)

/-- The initial state of Algorithm 2: `x₀ = (-1 + 1/Δ) 1`, `q₀`, `q̄₀ = q₀`. -/
noncomputable def initState (Δ : ℕ) : OptState G :=
  ⟨fun _ => -1 + 1 / (Δ : ℝ), initQ G Δ, initQ G Δ⟩

/-- The state `(x_t, q_t, q̄_t)` after `t` rounds. -/
noncomputable def optState (Δ : ℕ) : ℕ → OptState G
  | 0 => initState G Δ
  | t + 1 =>
      let s := optState Δ t
      let r := roundStep G s.x s.q s.qbar
      ⟨r.xPlus, r.qPlus, r.qBarPlus⟩

/-- The data of round `t` (run on `optState G Δ t`). -/
noncomputable def optRound (Δ : ℕ) (t : ℕ) : RoundData G :=
  roundStep G (optState G Δ t).x (optState G Δ t).q (optState G Δ t).qbar

/-- The output of Algorithm 2 after `T` rounds: `q̂ = (1/T) ∑_{t<T} q'_t`. -/
noncomputable def qHat (Δ : ℕ) (T : ℕ) : Idx G → ℝ := fun i =>
  (1 / (T : ℝ)) * ∑ t ∈ range T, (optRound G Δ t).qPrime i

/-- The nonisolated vertices. -/
noncomputable def nonisolated : Finset V :=
  univ.filter (fun v => 0 < G.degree v)

/-- The potential at time `0`: `Φ₀(w) = D^{32}_{z₀}(w) + 64 K_{q̄₀}(w_q)`, sums over
nonisolated vertices. -/
noncomputable def potential0 (Δ : ℕ) (w : StateSpace G) : ℝ :=
  bregman G (nonisolated G) 32 ((initState G Δ).x, (initState G Δ).q) w +
    64 * relEnt G (nonisolated G) (initState G Δ).qbar w.2

/-- The comparison distributions of Lemma 3.1(c) built from a set `M` of edges of `B(G)`:
`u` puts unit mass on `v` if `(u,1)(v,2) ∈ M` (sides `0, 1` here), else on its dummy. -/
noncomputable def qStar (M : Finset (Sym2 (V × Fin 2))) : Idx G → ℝ := by
  classical
  exact fun i => match i with
    | .inl u => if ∃ v : V, s((u, 0), (v, 1)) ∈ M then 0 else 1
    | .inr d => if s((d.fst, 0), (d.snd, 1)) ∈ M then 1 else 0

end Defs

/-- `B_Δ = 200 + 400 log(2Δ)`. -/
noncomputable def bDelta (Δ : ℕ) : ℝ := 200 + 400 * Real.log (2 * (Δ : ℝ))

/-- `T_δ = ⌈3 B_Δ / δ⌉`. -/
noncomputable def tDelta (Δ : ℕ) (δ : ℝ) : ℕ := ⌈3 * bDelta Δ / δ⌉₊

/-- `q^{(δ)} = (1/T_δ) ∑_{t < T_δ} q'_t`. -/
noncomputable def qDelta {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (δ : ℝ) : Idx G → ℝ :=
  qHat G Δ (tDelta Δ δ)

end OptimalLCA.Matching


