-- Prove2me | Definitions.Def_RGMISFast_Gamma
-- name    : RGMISFast_Gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:32.911368+00:00
-- url     : https://prove2.me/theorems/40f9a086-81f6-46c4-b3d1-27a64cb075ca
-- title:
--   Growth sets $\Gamma_{a,b}(A)$, boundary counts $K_{a,b}(A)$, $C_0$ and $\Gamma_{<a_M}(A)$
-- statement:
--   Let $G$ be a finite simple graph with root $u^*$ and ranks $r$; let $a>0$ and $b\in(a,\infty]$.
--
--   1. $\Gamma_{a,b}(A)$ is the set of vertices outside $A$ reachable from $A$ through vertices outside $A$ that are active at $a$ and have ranks below $b$; $\Gamma_{a,b}(A)=\varnothing$ if $A$ is not active at $a$.
--   2. $K_{a,b}(A)=|\{v\in N^-[A]:\tau(v)\ge a,\ r(v)<b\}|$ when $A$ is active at $a$, and $K_{a,b}(A)=0$ otherwise.
--   3. $\Gamma_m(A)=\Gamma_{a_m,a_{m-1}}(A)$ and $K_{m,i}(B)=K_{a_m,b_i}(B)$.
--   4. $C_0$ is the vertex set of the component of $u^*$ in $G_{a_0}$, and $C_0=\varnothing$ if the root is not active at $a_0$.
--   5. $\Gamma_{<a_M}(A)$ is the set of vertices outside $A$ reachable from $A$ by a path whose vertices outside $A$ all have rank below $a_M$ (no activity required).
--   6. $1-e^{-(b-a)}$, with value $1$ at $b=\infty$.
--
--   These sets bound how an admissible tree enters and grows within each time interval.
--
--   **Formalization Note** $b$ ranges over $\mathbb R\cup\{\infty\}$ (`WithTop ℝ`); reachability is taken in the subgraph induced by $A$ and the admissible outside vertices.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), §3, p.14 (PDF p.16) (K_{m,i}, Γ_m, C_0); §6.1, p.23 (PDF p.25) (Γ_{a,b}, K_{a,b}, q); App. A, p.29 (PDF p.31) (Γ_{<a_M})

import Mathlib
import Definitions.Def_RGMISFast_tau
import Definitions.Def_RGMISFast_IsRootConnected
import Definitions.Def_RGMISFast_rankCharge

set_option autoImplicit false

namespace RGMISFast

open Classical in
/-- `Γ_{a,b}(A)` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is
Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), §6.1, p.23): "Let
Γa,b(A) be the set of vertices outside A reachable from A through vertices outside A that are
active at a and have ranks below b. Set Γa,b(A) = ∅ if A is not active at a."

**Formalization Note** `b ∈ (a, ∞]` lives in `WithTop ℝ` (`b = ⊤` means no rank cutoff). A vertex
`w ∉ A` belongs to `Γ_{a,b}(A)` when it is reachable from a vertex of `A` in the subgraph induced
by `A` together with the vertices `y` with `a ≤ τ(y)` and `r(y) < b`. -/
noncomputable def GammaAB {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : V → ℝ) (a : ℝ) (b : WithTop ℝ) (A : Finset V) : Finset V :=
  if ActiveAt G r a A then
    Finset.univ.filter (fun w => w ∉ A ∧ ∃ x ∈ A,
      (restrictTo G {y | y ∈ A ∨ (a ≤ tau G r y ∧ ((r y : ℝ) : WithTop ℝ) < b)}).Reachable x w)
  else ∅

open Classical in
/-- `K_{a,b}(A)` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is
Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), §6.1, p.23):
"Ka,b(A) = |{v ∈ N−[A] : τ(v) ≥ a, r(v) < b}| when A is active at a, and set Ka,b(A) = 0
otherwise." `b ∈ (a, ∞]` lives in `WithTop ℝ`. -/
noncomputable def KAB {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : V → ℝ) (a : ℝ) (b : WithTop ℝ) (A : Finset V) : ℕ :=
  if ActiveAt G r a A then
    ((outerBdry G A).filter (fun v => a ≤ tau G r v ∧ ((r v : ℝ) : WithTop ℝ) < b)).card
  else 0

/-- `Γ_m(A) = Γ_{a_m, a_{m−1}}(A)` for `1 ≤ m ≤ M` (Dalirrooyfard, Makarychev, Mitrović,
Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript
sha256 e93cdfec…), §3, p.14): "the vertices outside A reachable from A by a path on which every
vertex outside A is active at am and has rank below am−1. Set Γm(A) = ∅ when A is not active at
am." -/
noncomputable def Gammam {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : V → ℝ) (m : ℕ) (A : Finset V) : Finset V :=
  GammaAB G r (am m) ((am (m - 1) : ℝ) : WithTop ℝ) A

/-- `K_{m,i}(B) = K_{a_m, b_i}(B)` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran,
*Randomized Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256
e93cdfec…), §3, p.14): `|{w ∈ N⁻[B] : τ(w) ≥ a_m, r(w) < b_i}|` for `B` active at `a_m`, and `0`
otherwise. -/
noncomputable def Kmi {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : V → ℝ) (m i : ℕ) (B : Finset V) : ℕ :=
  KAB G r (am m) (b i) B

open Classical in
/-- `C₀` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at
Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), §3, p.14): "Let C0 be the vertex
set of the component containing u∗ in Ga0, and let C0 = ∅ if the root is not active at a0." -/
noncomputable def C0 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : V → ℝ) (u : V) : Finset V :=
  if a0 ≤ tau G r u then
    Finset.univ.filter (fun v => a0 ≤ tau G r v ∧
      (restrictTo G {x | a0 ≤ tau G r x}).Reachable u v)
  else ∅

open Classical in
/-- `Γ_{<a_M}(A)` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is
Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), App. A, p.29): "the set
of vertices outside A reachable from A by a path whose vertices outside A all have rank below aM.
This definition does not require A to be active at any time." Here `M = Mof Δ`. -/
noncomputable def GammaLow {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (r : V → ℝ) (Δ : ℕ) (A : Finset V) : Finset V :=
  Finset.univ.filter (fun w => w ∉ A ∧ ∃ x ∈ A,
    (restrictTo G {y | y ∈ A ∨ r y < am (Mof Δ)}).Reachable x w)

/-- `1 − e^{−(b−a)}` for `b ∈ (a, ∞]`, with the value `1` at `b = ∞` (Dalirrooyfard, Makarychev,
Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*, STOC 2027 submission
(manuscript sha256 e93cdfec…), Lemma 6.1, p.23: "where we note 1 − e^{−(b−a)} → 1 as b → ∞"). -/
noncomputable def oneMinusExp (a : ℝ) (b : WithTop ℝ) : ℝ :=
  if hb : b = ⊤ then 1 else 1 - Real.exp (-(b.untop hb - a))

end RGMISFast


