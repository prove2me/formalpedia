-- Prove2me | Definitions.Def_SmoothedMIS_testSet
-- name    : SmoothedMIS_testSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:39.67293+00:00
-- url     : https://prove2.me/theorems/98b14952-5b3b-4e51-9ec5-546a2dcafa97
-- title:
--   Case analysis of §4.2.1: $H_0,L_0,X_0,Z_H,t,Q,Z_Q,F_0,X_0^+,U,B_h,T_h$, robust success, events $E$, $E_0$
-- statement:
--   Fix a base graph $G$ and the coins $\omega=(\omega_R,\omega_\kappa)$. With $\deg$ taken in $G$:
--   1. $H_0=\{v:\deg_G(v)>B_0\}$ (base-high), $L_0=V\setminus H_0$ (base-low), $M=|H_0|$, $X_0=N_G(H_0)\cap L_0$, $Z_H=N^2_G[H_0]$, $z_H=|Z_H|$;
--   2. $t=\min\{B_0,\lfloor n/(16Mk)\rfloor\}$, $Q=\{v\in L_0:\deg_{G[L_0]}(v)>t\}$, $Z_Q=N^2_{G[L_0]}[Q]$, $z_Q=|Z_Q|$;
--   3. the random base-low graph $F_0=\mathcal G[L_0]$, $X_0^+=N_{F_0}[X_0]$, and the pool $U=L_0\setminus(X_0^+\cup Q)$;
--   4. $I_{hv}=\mathbf 1[hv\in R\text{ and }\kappa_{hv}=1]$ and the sample $B_h=\{v\in L_0\setminus X_0: I_{hv}=1\}$;
--   5. the **test vertices** $T_h$: the vertices of $B_h\cap U$ that are isolated in $F_0^2[B_h]$, i.e. at $F_0$-distance more than $2$ from every other vertex of $B_h$;
--   6. $v\in T_h$ is **robustly successful** if (S1) $h'v\notin R$ and (S2) $I_{h'w}=0$ for every $w\in N_{F_0}(v)$, for every $h'\in H_0\setminus\{h\}$;
--   7. the event $E$: every vertex has at most $2\lambda$ incident edges in $R$; the event $E_0$: (a) every base-low vertex has at most $2\lambda$ random neighbours in $L_0$ and (b) $|X_0^+|\le n/4$.
--
--   These are the objects of Lemmas 4.6–4.13.
--
--   **Formalization Note** $G[L_0]$ and $F_0$ are graphs on all $n$ vertices whose vertices outside $L_0$ are isolated, which changes no degree or distance inside $L_0$. $t$ is used only when $M>0$ (Lean's division by $0$ gives $t=0$ otherwise).
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), §4.2.1, pp.20–26 (PDF pp.22–28); Definition 3.4, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_SmoothedMIS_activeSet

namespace SmoothedMIS

variable {n : ℕ}

/-- Base-high vertices `H0 = {v : deg_G(v) > B0}` (§4.2.1, p.20). -/
def H0 (G : SimpleGraph (Fin n)) : Set (Fin n) := {v | B0 n < deg G v}

/-- Base-low vertices `L0 = V \ H0` (§4.2.1, p.20). -/
def L0 (G : SimpleGraph (Fin n)) : Set (Fin n) := (H0 G)ᶜ

/-- `M = |H0|` (§4.2.1, p.20). -/
noncomputable def M (G : SimpleGraph (Fin n)) : ℕ := (H0 G).ncard

/-- `X0 = N_G(H0) ∩ L0` (§4.2.1, p.20). -/
def X0 (G : SimpleGraph (Fin n)) : Set (Fin n) := {v | v ∈ L0 G ∧ ∃ h ∈ H0 G, G.Adj v h}

/-- `Z_H = N²_G[H0]` (§4.2.1, p.20). -/
def ZH (G : SimpleGraph (Fin n)) : Set (Fin n) := twoHop G (H0 G)

/-- `z_H = |Z_H|` (§4.2.1, p.20). -/
noncomputable def zH (G : SimpleGraph (Fin n)) : ℕ := (ZH G).ncard

/-- `t = min{B0, ⌊n/(16Mk)⌋}` (§4.2.1, Case (2), p.22). Only used when `M > 0`; Lean's
division by `0` gives `t = 0` otherwise. -/
noncomputable def tParam (a : ℝ) (G : SimpleGraph (Fin n)) : ℕ :=
  min (B0 n) ⌊(n : ℝ) / (16 * (M G : ℝ) * (kParam a n : ℝ))⌋₊

/-- The subgraph of `H` induced on `L0`, as a graph on all of `Fin n` whose vertices outside `L0`
are isolated. -/
def onL0 (G H : SimpleGraph (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => H.Adj u v ∧ u ∈ L0 G ∧ v ∈ L0 G

/-- `Q = {v ∈ L0 : deg_{G[L0]}(v) > t}` (§4.2.1, p.22). -/
def Qset (a : ℝ) (G : SimpleGraph (Fin n)) : Set (Fin n) :=
  {v | v ∈ L0 G ∧ tParam a G < deg (onL0 G G) v}

/-- `Z_Q = N²_{G[L0]}[Q]` (§4.2.1, p.22). -/
def ZQ (a : ℝ) (G : SimpleGraph (Fin n)) : Set (Fin n) := twoHop (onL0 G G) (Qset a G)

/-- `z_Q = |Z_Q|` (§4.2.1, p.22). -/
noncomputable def zQ (a : ℝ) (G : SimpleGraph (Fin n)) : ℕ := (ZQ a G).ncard

/-- The base-low graph `F0 = 𝒢[L0]` (p.24), random. -/
def F0 (G : SimpleGraph (Fin n)) (ωR : Sym2 (Fin n) → Bool) : SimpleGraph (Fin n) :=
  onL0 G (addSmooth G ωR)

/-- `X0⁺ = N_{F0}[X0]` (p.24). -/
def X0plus (G : SimpleGraph (Fin n)) (ωR : Sym2 (Fin n) → Bool) : Set (Fin n) :=
  closedNbhd (F0 G ωR) (X0 G)

/-- The pool `U = L0 \ (X0⁺ ∪ Q)` (p.25). -/
def pool (a : ℝ) (G : SimpleGraph (Fin n)) (ωR : Sym2 (Fin n) → Bool) : Set (Fin n) :=
  L0 G \ (X0plus G ωR ∪ Qset a G)

/-- `I_hv = 1[hv ∈ R and κ_hv = 1]` (p.25). -/
def Ind (G : SimpleGraph (Fin n)) (ω : Coins n) (h v : Fin n) : Prop :=
  Radj G ω.1 h v ∧ ω.2 s(h, v) = true

/-- The sample `B_h = {v ∈ L0 \ X0 : I_hv = 1}` (p.25). -/
def sample (G : SimpleGraph (Fin n)) (ω : Coins n) (h : Fin n) : Set (Fin n) :=
  {v | v ∈ L0 G ∧ v ∉ X0 G ∧ Ind G ω h v}

/-- **The test vertices** `T_h` of a base-high vertex `h` (Dey, Dufoulon, Moses Jr., Pandurangan,
*Smoothed Analysis for Distributed MIS* (manuscript, sha256 dc2131db…), §4.2.1, p.26): the
vertices of `B_h ∩ U` that are isolated in `F0²[B_h]`, i.e. at `F0`-distance more than `2` from
every other vertex of `B_h` (Definition 3.4, p.14).

**Formalization Note** `F0`, `G[L0]` are graphs on `Fin n` with the vertices outside `L0`
isolated, which leaves degrees and distances inside `L0` unchanged. Distances are
`SimpleGraph.edist` (`∞` between components). `k = ⌈a ln n⌉`, so the test set depends on `a`
through `t`. -/
def testSet (a : ℝ) (G : SimpleGraph (Fin n)) (ω : Coins n) (h : Fin n) : Set (Fin n) :=
  {v | v ∈ sample G ω h ∧ v ∈ pool a G ω.1 ∧
    ∀ u ∈ sample G ω h, u ≠ v → 2 < (F0 G ω.1).edist u v}

/-- Robust success of `v ∈ T_h` (p.26): (S1) `h'v ∉ R` and (S2) `I_{h'w} = 0` for every
`w ∈ N_{F0}(v)`, for every `h' ∈ H0 \ {h}`. -/
def RobustSuccess (G : SimpleGraph (Fin n)) (ω : Coins n) (h v : Fin n) : Prop :=
  (∀ h' ∈ H0 G, h' ≠ h → ¬ Radj G ω.1 h' v) ∧
    ∀ w, (F0 G ω.1).Adj v w → ∀ h' ∈ H0 G, h' ≠ h → ¬ Ind G ω h' w

/-- The event `E` of Lemma 4.6 (p.20): every vertex has at most `2λ` incident edges in `R`. -/
def EventE (β : ℝ) (G : SimpleGraph (Fin n)) (ωR : Sym2 (Fin n) → Bool) : Prop :=
  ∀ v, (({u | Radj G ωR v u}.ncard : ℕ) : ℝ) ≤ 2 * lam n β

/-- Property (a) of Lemma 4.9 (p.24): every base-low vertex has at most `2λ` random neighbours
in `L0`. -/
def EventE0a (β : ℝ) (G : SimpleGraph (Fin n)) (ωR : Sym2 (Fin n) → Bool) : Prop :=
  ∀ v ∈ L0 G, (({u | u ∈ L0 G ∧ Radj G ωR v u}.ncard : ℕ) : ℝ) ≤ 2 * lam n β

/-- The event `E0` of Lemma 4.9 (p.24): (a) and (b) `|X0⁺| ≤ n/4`. -/
def EventE0 (β : ℝ) (G : SimpleGraph (Fin n)) (ωR : Sym2 (Fin n) → Bool) : Prop :=
  EventE0a β G ωR ∧ (((X0plus G ωR).ncard : ℕ) : ℝ) ≤ (n : ℝ) / 4

end SmoothedMIS


