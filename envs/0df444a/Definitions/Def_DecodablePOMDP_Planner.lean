-- Prove2me | Definitions.Def_DecodablePOMDP_Planner
-- name    : DecodablePOMDP_Planner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:07.382869+00:00
-- url     : https://prove2.me/theorems/7ffa08d3-0939-41e9-a744-d213e168c8c2
-- title:
--   The finite planner: states $\mathcal M_h$, successor $m^+$, table $\widehat V_h$, policy $\hat\pi$ and $W_h$
-- statement:
--   Fix $0<\eta\le1$ and $G=G_{|\mathcal Q|,\eta}$. Let $G_h(u)=\{g\in G:g_q=0\text{ for }q\notin\mathcal A_h(u)\}$.
--
--   1. A **finite planner state** at stage $h$ is $m=(h,u,g)$ with $u\in\mathcal U_h$, $\mathcal A_h(u)\ne\emptyset$ and $g\in G_h(u)$; $\mathcal M_h$ is the set of them, and $\beta_m=\Phi_h(u,g)$.
--   2. The **successor** $m^+(m,a,z)=(h+1,u^+,g^+)$ updates the suffix, computes $w^+$ by (12)–(13) from $g$, and rounds it within $G_{h+1}(u^+)$. If $P(z\mid\beta_m,a)=0$, the planner moves to a chosen admissible state of stage $h+1$ (footnote 3).
--   3. The **table** is $\widehat V_H(m)=0$ and, for $h\in[1:H-1]$,
--   $$\widehat V_h(m)=\max_{a\in\mathcal A}\sum_{z=(y,\hat s)\in\mathcal Z}P(z\mid\beta_m,a)\big(r_{h+1}(y)+\widehat V_{h+1}(m^+(m,a,z))\big);\tag{6}$$
--   $\hat a_h(m)$ is a maximiser (7).
--   4. The **planner policy** from $m$ plays $\hat a$ in the current memory and moves the memory by $m^+$ on each alive observation; from $m_1=(1,\emptyset,e_\perp)$ it is $\hat\pi$. $W_h(\beta,m)$ is its expected reward from time $h+1$ to $H$ in $\widetilde{\mathcal P}(L)$ when the hidden law at stage $h$ is $\beta$; $\beta_1(s,q)=\mu_1(s)\mathbf 1\{q=\perp\}$.
--
--   The planner's **free choices** (the fallback state of footnote 3, the coordinate receiving the remaining mass in the rounding, the maximiser in (7)) are a parameter; a choice is **admissible** when the fallback lies in $\mathcal M_{h+1}$ whenever that set is nonempty, the coordinate lies in the face, and the action maximises (7).
--
--   **Formalization Note** $\widehat V$ runs the recursion for $H-h$ stages; the maximum over the finite nonempty $\mathcal A$ is a real supremum. Statements quantify over all admissible choices.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), §4.1–§4.2, pp.10–11, (6)–(7), footnote 3

import Mathlib
import Definitions.Def_DecodablePOMDP_Update
import Definitions.Def_DecodablePOMDP_Grid
import Definitions.Def_DecodablePOMDP_Bayes
import Definitions.Def_DecodablePOMDP_Killed

namespace DecodablePOMDP

open Classical

/-- **Finite planner state** `m = (h, u, g)` (p.10): a stage, a suffix and a weight vector on
`Q = {⊥, 0, …, L−1}`. -/
abbrev PState (S A O : Type) (L : ℕ) := ℕ × Suffix A O S × (Option (Fin L) → ℝ)

/-- **Face grid** `G_h(u) := {g ∈ G : g_q = 0 for q ∉ A_h(u)}` with `G := G_{|Q|,η}` (p.10).

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.1, p.10: "fix some 0 < η ≤ 1, and let
G := G_{|Q|,η}. For each suffix, let Gh(u) := {g ∈ G : gq = 0 for q ∉ Ah(u)}." -/
noncomputable def gridFace {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (η : ℝ) (h : ℕ)
    (u : Suffix A O S) : Finset (Option (Fin L) → ℝ) :=
  (latticeGrid (Option (Fin L)) η).filter
    (fun g => ∀ q, q ∉ admissibleSet P D ρ L h u → g q = 0)

/-- **Finite planner states at stage `h`** `M_h` (p.10): the triples `(h, u, g)` with `u` a suffix
of the lengths of Definition 4 at stage `h`, `A_h(u) ≠ ∅`, and `g ∈ G_h(u)`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.1, p.10: "A finite planner state is a
triplet m = (h, u, g) with g ∈ Gh(u). Denote the collection of finite planner states at stage h by
Mh. … For the planner, Uh contains all suffixes of the lengths in Definition 4 with Ah(u) ≠ ∅,
including those not reachable from µ1." -/
def plannerStates {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (η : ℝ) (h : ℕ) :
    Set (PState S A O L) :=
  {m | m.1 = h ∧ IsSuffixAt L h m.2.1 ∧ (admissibleSet P D ρ L h m.2.1).Nonempty ∧
    m.2.2 ∈ gridFace P D ρ L η h m.2.1}

/-- **Belief of a planner state** `β_m := Φ_h(u, g)` (p.11, footnote 3). -/
noncomputable def beliefOf {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (m : PState S A O L) :
    Option (S × Option (Fin L)) → ℝ :=
  Phi P D ρ L m.1 m.2.1 m.2.2

/-- **The free choices of the planner** (pp.10–11, footnote 3; A.6): `fallback m a z` is the planner
state chosen after an observation `z` of probability `0` under `β_m` (footnote 3); `last 𝒜` is the
coordinate of `𝒜` that receives the remaining mass when rounding within the face `𝒜` (A.6, "the
last admissible coordinate"); `act m` is the action chosen among the maximisers of (7). -/
structure PlannerChoice (S A O : Type) (L : ℕ) where
  fallback : PState S A O L → A → O × S → PState S A O L
  last : Finset (Option (Fin L)) → Option (Fin L)
  act : PState S A O L → A

/-- **Planner successor** `m⁺(m, a, z)` (pp.10–11). For `m = (h, u, g)`, action `a` and alive
observation `z`: `h⁺ = h + 1`, `u⁺` the updated suffix, `w⁺` the normalised update (12)–(13) of
the weight `g` (Lemma 5), and `g⁺` the rounding of `w⁺` within `G_{h+1}(u⁺)` (remaining mass at
`ch.last A_{h+1}(u⁺)`). If `z` has probability `0` under `β_m`, the successor is the choice
`ch.fallback m a z` (footnote 3).

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), pp.10–11: "The time and suffix indices are
easily updated to h+ and u+. The planner computes the new weight vector w+ := w+(m, a, z) via
Lemma 5, taking the grid point g as the current weight vector. Then it rounds w+ to
g+ ∈ Gh+1(u+), preserving zeros outside Ah+1(u+) and incurring at most η error in ℓ1. The new state
is thus m+(m, a, z) := (h+, u+, g+)." Footnote 3, p.11: "It can happen that an observation z that
has 0 probability under βm := Φh(u, g) is actually observed … If this happens, choose any admissible
planner state at time h + 1, not necessarily with the recorded suffix." -/
noncomputable def mplus {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (η : ℝ) (ch : PlannerChoice S A O L)
    (m : PState S A O L) (a : A) (z : O × S) : PState S A O L :=
  if 0 < (killed P D ρ L).obsProb m.1 (beliefOf P D ρ L m) a (some z) then
    (m.1 + 1, suffixUpdate L m.1 m.2.1 a z,
      roundToFace η (admissibleSet P D ρ L (m.1 + 1) (suffixUpdate L m.1 m.2.1 a z))
        (ch.last (admissibleSet P D ρ L (m.1 + 1) (suffixUpdate L m.1 m.2.1 a z)))
        (updWeight P D ρ L m.1 m.2.1 m.2.2 a z))
  else ch.fallback m a z

/-- Backward recursion of (6) with `k` stages to go. -/
noncomputable def VhatAux {S A O : Type} [DecidableEq S] [Fintype S] [Fintype A] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (η : ℝ) (ch : PlannerChoice S A O L) :
    ℕ → PState S A O L → ℝ
  | 0, _ => 0
  | k + 1, m => ⨆ a : A, ∑ z : O × S,
      (killed P D ρ L).obsProb m.1 (beliefOf P D ρ L m) a (some z) *
        (P.r (m.1 + 1) z.1 + VhatAux P D ρ L η ch k (mplus P D ρ L η ch m a z))

/-- **Planner table** `V̂_h(m)` (6) (p.11): `V̂_H(m) := 0`, and for `h ∈ [1 : H−1]`,
`V̂_h(m) := max_{a∈A} Σ_{z=(y,ŝ)∈Z} P(z | β_m, a)(r_{h+1}(y) + V̂_{h+1}(m⁺(m, a, z)))`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.2, p.11, (6).

**Formalization Note.** `V̂(m)` runs the recursion for `H − h` stages, `h` the stage of `m`;
`max` over the finite nonempty `A` is a real `⨆`. -/
noncomputable def Vhat {S A O : Type} [DecidableEq S] [Fintype S] [Fintype A] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (η : ℝ) (ch : PlannerChoice S A O L)
    (m : PState S A O L) : ℝ :=
  VhatAux P D ρ L η ch (P.H - m.1) m

/-- The bracket of (6)–(7): `Σ_{z=(y,ŝ)∈Z} P(z | β_m, a)(r_{h+1}(y) + V̂_{h+1}(m⁺(m, a, z)))`. -/
noncomputable def Qhat {S A O : Type} [DecidableEq S] [Fintype S] [Fintype A] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (η : ℝ) (ch : PlannerChoice S A O L)
    (m : PState S A O L) (a : A) : ℝ :=
  ∑ z : O × S, (killed P D ρ L).obsProb m.1 (beliefOf P D ρ L m) a (some z) *
    (P.r (m.1 + 1) z.1 + Vhat P D ρ L η ch (mplus P D ρ L η ch m a z))

/-- **Admissible planner choices** (footnote 3, p.11; (7), p.11; A.6, p.17): the fallback is a
planner state of `M_{h+1}` whenever `M_{h+1} ≠ ∅`; the coordinate receiving the remaining mass
lies in the (nonempty) face; and the chosen action is a maximiser of (7),
`â_h(m) ∈ argmax_a Σ_z P(z | β_m, a)(r_{h+1}(y) + V̂_{h+1}(m⁺(m, a, z)))`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.2, p.11, (7), and footnote 3. -/
def IsPlannerChoice {S A O : Type} [DecidableEq S] [Fintype S] [Fintype A] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (η : ℝ)
    (ch : PlannerChoice S A O L) : Prop :=
  (∀ m a z, (plannerStates P D ρ L η (m.1 + 1)).Nonempty →
    ch.fallback m a z ∈ plannerStates P D ρ L η (m.1 + 1)) ∧
  (∀ 𝒜 : Finset (Option (Fin L)), 𝒜.Nonempty → ch.last 𝒜 ∈ 𝒜) ∧
  (∀ m a', Qhat P D ρ L η ch m a' ≤ Qhat P D ρ L η ch m (ch.act m))

/-- Planner memory after a killed-POMDP history from planner state `m`: each alive observation
`z` after action `a` moves the memory to `m⁺(·, a, z)`; after `†` the memory is kept (nothing is
earned after `†`). -/
noncomputable def memAfter {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (η : ℝ) (ch : PlannerChoice S A O L)
    (m : PState S A O L) : (t : ℕ) → Hist A (Option (O × S)) t → PState S A O L
  | 0, _ => m
  | t + 1, hist => match (hist 0).2 with
    | some z => mplus P D ρ L η ch (memAfter P D ρ L η ch m t (Fin.tail hist)) (hist 0).1 z
    | none => memAfter P D ρ L η ch m t (Fin.tail hist)

/-- **The finite planner's policy** from planner state `m` (pp.10–11): a deterministic history
policy of `P̃(L)` (started at the stage of `m`) playing `â(m_t) = ch.act m_t` in the current
memory `m_t`. From the initial state `m₁` this is the planner `π̂`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.2, p.11. -/
noncomputable def plannerPolicy {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O]
    [DecidableEq A] (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (η : ℝ)
    (ch : PlannerChoice S A O L) (m : PState S A O L) : PolicyFn A (Option (O × S)) :=
  toRand (fun t hist => ch.act (memAfter P D ρ L η ch m t hist))

/-- **Execution value** `W_h(β, m)` (Theorem 3, p.11): "the expected cumulative reward from time
h + 1 to H, when the hidden state distribution is β and the finite planner has state m".

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Theorem 3, p.11. -/
noncomputable def execValue {S A O : Type} [DecidableEq S] [Fintype S] [Fintype A] [Fintype O]
    [DecidableEq A] (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (η : ℝ)
    (ch : PlannerChoice S A O L) (h : ℕ) (β : Option (S × Option (Fin L)) → ℝ)
    (m : PState S A O L) : ℝ :=
  valueFrom (killed P D ρ L) h β (plannerPolicy P D ρ L η ch m)

/-- **Initial planner state** `m₁ = (1, ∅, e_⊥)` (§4.2, p.11).

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.2, p.11: "initialise the finite planner
at time 1 by m1 = (1, ∅, e⊥), indicating the history (suffix) at stage 1 is empty, and that no
reveal has occurred yet". -/
def initState {S A O : Type} (L : ℕ) : PState S A O L :=
  (1, (none, []), fun q => if q = none then 1 else 0)

/-- **Initial belief** `β₁(s, q) = µ₁(s) 1{q = ⊥}` (§4.2, p.11). -/
def initBelief {S A O : Type} (P : POMDP S A O) (L : ℕ) : Option (S × Option (Fin L)) → ℝ
  | some (s, none) => P.μ₁ s
  | _ => 0

end DecodablePOMDP


