-- Prove2me | Definitions.Def_PrivateRoutingSignaling_PTAS_Supplement_ShortPathInstance
-- name    : PrivateRoutingSignaling_PTAS_Supplement_ShortPathInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:45:10.552883+00:00
-- url     : https://prove2.me/theorems/ab2f079f-23eb-47ab-9da4-882544d84b1b
-- title:
--   The §6 short-path MAX-CUT construction with the continuous smoothing of Remark 6.6
-- statement:
--   Let $G$ be a simple graph on vertices $1,\dots,N$. For $a<b$ the **ramp** is $0$ for $x\le a$, $\frac{x-a}{b-a}$ for $a\le x\le b$ and $1$ for $x\ge b$.
--
--   1. The **network** has, for each vertex $i$, a node $m_i$, an arc from the source to $m_i$ and three parallel arcs from $m_i$ to the sink. The resulting two-arc paths are $A_i$, $L_i$, $R_i$.
--   2. The **designated dual solution** has $Y_{A_i,R_i}=1$, $Y_{L_i,R_j}=\frac14$ when $j=i$ or $(i,j)\in E$, and all other entries zero.
--   3. For $0<\eta\le\frac12$ the **smoothed hard state** $H$ puts $\tilde g$, the ramp on $\bigl[\frac1N,\frac{1+\eta}N\bigr]$, on every source arc, puts $\tilde h$, the ramp on $\bigl[\frac{1-\eta}{2N},\frac1{2N}\bigr]$, on the second arc of every $R_i$, and puts $0$ on the second arcs of $A_i,L_i$.
--   4. Let $\mathcal U=\{A_i,L_i\}$ and $S_U=\{j:Y_{U,R_j}>0\}$. The smoothed state $P_U$ has zero latency on every source arc, constant $\frac12$ on the second arc of $U$, the ramp $\tilde\ell$ on $\bigl[\frac{Y_{U,R_j}}2,\frac{(1+\eta)Y_{U,R_j}}2\bigr]$ on the second arc of $R_j$ for $j\in S_U$, and constant $1$ on every other second arc.
--   5. State $Q_i$ has zero latency on every source arc and on the second arc of $R_i$, and constant $1$ on every other second arc.
--   6. For a hard-state prior $\lambda_H$ the priors are $\lambda_H$ on $H$, $\frac1{8N}$ on each $P_U$, $\frac1{2N}$ on each $Q_i$, and $\frac14-\lambda_H$ on a dummy state with zero latency.
--
--   Writing $\tilde D^\theta$ for the dual functions of these continuous latencies,
--
--   $$
--   \tilde D^{\mathrm{aux}}(y)=\frac1{8N}\sum_{U\in\mathcal U}\tilde D^{P_U}(y)+\frac1{2N}\sum_{i\in[N]}\tilde D^{Q_i}(y).
--   $$
--
--   This is the continuous instance of Remark 6.6 and Lemma 6.7, used behind Theorem 6.8.
--
--   **Formalization Note** Arc $i$ is the source arc of gadget $i$ and arcs $N+3i$, $N+3i+1$, $N+3i+2$ are the second arcs of $A_i$, $L_i$, $R_i$ (for $0\le i<N$). States are $0=H$, $1+i=P_{A_i}$, $N+1+i=P_{L_i}$, $2N+1+i=Q_i$ and $3N+1$ the dummy. A dual matrix is read on paths through their second arcs.
-- source:
--   Yu Cheng, Tianle Jiang, The Complexity of Private Signaling in Nonatomic Routing Games, STOC 2027 submission #439 (October 2026), §6.1 p. 31 (network, g, h, H, Y), §6.2 pp. 33–34 (Q_i, U, S_U, P_U, ℓ), §6.3 p. 36 (priors, D^aux), Remark 6.6 pp. 36–37 (smoothing), p. 37 (λ_H, η, dummy state); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf; SHA-256 766b4afa05d6c7c4c106ed83a73221ca4d951eeca5cce863930177ed26fd4e61

import Mathlib
import Definitions.Def_PrivateRoutingSignaling_PTAS_Supplement_Dual

set_option autoImplicit false
open scoped BigOperators

namespace PrivateRoutingSignaling.PTAS.Supplement

open PrivateRoutingSignaling.PTAS

/-- The continuous ramp of Remark 6.6 (p. 36): zero up to `a`, linear from zero to one on
`[a, b]`, one from `b` on. -/
noncomputable def ramp (a b x : ℝ) : ℝ :=
  if x ≤ a then 0 else if x ≤ b then (x - a) / (b - a) else 1

namespace ShortPath

variable (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]

/-- The network of §6.1 (p. 31): source `0`, sink `1`, intermediate node `m_i = 2+i`. Arc `i`
goes from the source to `m_i`; arcs `N+3i`, `N+3i+1`, `N+3i+2` go from `m_i` to the sink and
are the second arcs of the paths `A_i`, `L_i`, `R_i`. Every path has two arcs. -/
def network : RoutingNetwork :=
  ⟨N + 2, 4 * N,
    ⟨fun a => if h : a.val < N then ⟨0, by omega⟩ else ⟨2 + (a.val - N) / 3, by omega⟩,
     fun a => if h : a.val < N then ⟨2 + a.val, by omega⟩ else ⟨1, by omega⟩⟩,
    ⟨0, by omega⟩, ⟨1, by omega⟩, 2⟩

/-- Adjacency `(i,j) ∈ E` for vertex indices. -/
def adj (i j : ℕ) : Prop := ∃ (hi : i < N) (hj : j < N), G.Adj ⟨i, hi⟩ ⟨j, hj⟩

/-- The designated dual solution of §6.1 (p. 31), on second-arc indices `b = N+3i+k`:
`Y_{A_i,R_i} = 1`, `Y_{L_i,R_j} = 1/4` if `j = i` or `(i,j) ∈ E`, all other entries zero. -/
noncomputable def Yn (b b' : ℕ) : ℝ := by
  classical
  exact
    if N ≤ b ∧ N ≤ b' ∧ b < 4 * N ∧ b' < 4 * N then
      (if (b - N) % 3 = 0 ∧ (b' - N) % 3 = 2 ∧ (b' - N) / 3 = (b - N) / 3 then 1
       else if (b - N) % 3 = 1 ∧ (b' - N) % 3 = 2 ∧
          ((b' - N) / 3 = (b - N) / 3 ∨ adj N G ((b - N) / 3) ((b' - N) / 3)) then 1 / 4
       else 0)
    else 0

/-- `Y` on paths, read through their second arcs. -/
noncomputable def Y : DualMatrix (network N) :=
  fun p q => match pathArcs (network N) p, pathArcs (network N) q with
    | [_, b], [_, b'] => Yn N G b.val b'.val
    | _, _ => 0

/-- Smoothed hard state `H` (§6.1 p. 31 with Remark 6.6): `g̃` on every source arc, `h̃` on the
second arc of every `R_i`, zero on the second arcs of `A_i`, `L_i`. -/
noncomputable def hardLatency (η : ℝ) (a : ℕ) (x : ℝ) : ℝ :=
  if a < N then ramp (1 / N) ((1 + η) / N) x
  else if (a - N) % 3 = 2 then ramp ((1 - η) / (2 * N)) (1 / (2 * N)) x
  else 0

/-- Smoothed state `P_U` for `U` with second arc `u = N+3i+k`, `k ∈ {0,1}` (`U = A_i` or `L_i`)
(p. 34 with Remark 6.6): zero on source arcs, `1/2` on `u`, the ramp `ℓ̃` on `[Y_{U,R_j}/2,
(1+η)Y_{U,R_j}/2]` on the second arc of `R_j` for `j ∈ S_U = {j : Y_{U,R_j} > 0}`, one on every
other second arc. -/
noncomputable def pLatency (η : ℝ) (u a : ℕ) (x : ℝ) : ℝ :=
  if a < N then 0
  else if a = u then 1 / 2
  else if (a - N) % 3 = 2 ∧ 0 < Yn N G u a then
    ramp (Yn N G u a / 2) ((1 + η) * Yn N G u a / 2) x
  else 1

/-- State `Q_i` (p. 33): zero on every source arc and on the second arc of `R_i`, one on every
other second arc. -/
def qLatency (i a : ℕ) (_x : ℝ) : ℝ :=
  if a < N then 0 else if a = N + 3 * i + 2 then 0 else 1

/-- States `0 = H`; `1+i = P_{A_i}`; `N+1+i = P_{L_i}`; `2N+1+i = Q_i` (`i < N`); `3N+1` dummy. -/
noncomputable def latency (η : ℝ) (θ : Fin (3 * N + 2)) (a : Fin (4 * N)) (x : ℝ) : ℝ :=
  if θ.val = 0 then hardLatency N η a.val x
  else if θ.val ≤ N then pLatency N G η (N + 3 * (θ.val - 1)) a.val x
  else if θ.val ≤ 2 * N then pLatency N G η (N + 3 * (θ.val - N - 1) + 1) a.val x
  else if θ.val ≤ 3 * N then qLatency N (θ.val - 2 * N - 1) a.val x
  else 0

/-- Priors (pp. 36–37): `λ_H`, `λ_{P_U} = 1/(8N)`, `λ_{Q_i} = 1/(2N)`, dummy `1/4 − λ_H`. -/
noncomputable def prior (priorH : ℝ) (θ : Fin (3 * N + 2)) : ℝ :=
  if θ.val = 0 then priorH
  else if θ.val ≤ 2 * N then 1 / (8 * N)
  else if θ.val ≤ 3 * N then 1 / (2 * N)
  else 1 / 4 - priorH

/-- The continuous private signaling instance of §6.3 (p. 37) with smoothing `η` and hard-state
prior `λ_H`. -/
noncomputable def inst (η priorH : ℝ) : Instance where
  network := network N
  states := 3 * N + 2
  prior := prior N priorH
  latency := latency N G η

def hState : Fin (3 * N + 2) := ⟨0, by omega⟩
def pAState (i : Fin N) : Fin (3 * N + 2) := ⟨1 + i.val, by omega⟩
def pLState (i : Fin N) : Fin (3 * N + 2) := ⟨N + 1 + i.val, by omega⟩
def qState (i : Fin N) : Fin (3 * N + 2) := ⟨2 * N + 1 + i.val, by omega⟩

/-- `D̃^θ(y)` for the smoothed latencies of state `θ` (Remark 6.6). -/
noncomputable def dTilde (η : ℝ) (θ : Fin (3 * N + 2)) (y : DualMatrix (network N)) : ℝ :=
  dualValueL (network N) (latency N G η θ) y

/-- `D̃^aux(y) = (1/(8N)) ∑_{U ∈ 𝒰} D̃^{P_U}(y) + (1/(2N)) ∑_i D̃^{Q_i}(y)` (p. 36). -/
noncomputable def dauxTilde (η : ℝ) (y : DualMatrix (network N)) : ℝ :=
  ∑ i : Fin N, (dTilde N G η (pAState N i) y + dTilde N G η (pLState N i) y) / (8 * N) +
    ∑ i : Fin N, dTilde N G η (qState N i) y / (2 * N)

end ShortPath

end PrivateRoutingSignaling.PTAS.Supplement


