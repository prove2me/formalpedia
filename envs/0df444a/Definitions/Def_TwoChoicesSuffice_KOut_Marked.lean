-- Prove2me | Definitions.Def_TwoChoicesSuffice_KOut_Marked
-- name    : TwoChoicesSuffice_KOut_Marked
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:24.090912+00:00
-- url     : https://prove2.me/theorems/f12e7b18-9f66-4922-9791-4d0e2a2d519d
-- title:
--   Marked two-out law, base graph $B$, augmentation $B^+$, $\Phi_R$ and the depth counts $M_j,N_j,T_j$
-- statement:
--   Draw a two-choice outcome $\sigma$, with $s_1(v),s_2(v)$ the choices at $v$. Conditional on $H^1_G(\sigma)$, draw a uniformly random proper colouring $c:V\to\{0,\dots,9\}$ of $H^1_G(\sigma)$; the **marked set** is $S=c^{-1}(0)$ and $U=V\setminus S$. Expectations are taken over the pairs $(\sigma,S)$:
--   $$
--   \mathbb E[f]=\frac1{|\Omega_2|}\sum_{\sigma}\frac1{Z_{10}(H^1_G(\sigma))}\sum_{c\text{ proper}}f\bigl(\sigma,c^{-1}(0)\bigr).
--   $$
--   The pair $(\sigma,S)$ is in general not uniform.
--
--   The **base graph** $B(\sigma,S)$ keeps the first choice of every vertex and the second choice of every vertex in $U$. The reserved vertices are $R=\{v\in S: s_2(v)\in U\}$, and the **relevant degrees** are $d_v=|N_G(v)\cap U|$ for $v\in R$ and $d_v=0$ otherwise. With a fixed total order $\pi$ of $V$, let $\prec$ sort vertices by increasing $d_v$, ties broken by $\pi$; leaders and the order of components of $B$ and $B^+$ use $\prec$. The **augmented base graph** $B^+(\sigma,S)$ adds to $B$ the reserved second choice of each $B$-leader $\alpha_C\in R$ exactly when it reaches a higher $B$-component, so $H^1_G(\sigma)\subseteq B\subseteq B^+\subseteq H^2_G(\sigma)$. The relevant-degree potential is
--   $$
--   \Phi_R(J)=\sum_{C\in\mathrm{CC}(J)}\max_{v\in C}d_v .
--   $$
--
--   An edge is **allowed** if it lies in $E^\circ=E_G\setminus\{uv: u,v\in S\}$. Owners and depths in $B$ are taken for $\prec$. For $j\ge0$, $M_j(B)$ and $N_j(B)$ count the allowed crossing edges of $B$ whose owner is at depth $j$ and is marked, respectively unmarked, and $T_j(B)=M_j(B)+N_j(B)$.
--
--   These objects carry the two-out case (Theorem 12).
--
--   **Formalization Note** `markedExpect G f` is the displayed average with `zeroSet c` for $S$; its inner denominator $Z_{10}(H^1_G(\sigma))$ is positive by `properColorings_prefixOne_nonempty`. `reserved`, `relDeg`, `baseGraph`, `augBase`, `relPotential`, `markedDepth`, `unmarkedDepth`, `totalDepth` are $R$, $d$, $B$, $B^+$, $\Phi_R$, $M_j$, $N_j$, $T_j$. The order $\pi$ is the `LinearOrder` instance of `V`. Marked counts are not restricted to owners in $R$.
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), §7.2 and §7.4.1 (marked set, base graph, relevant degrees, B⁺, Φ_R, E°, M_j, N_j, T_j), printed p. 15, PDF p. 16; PDF pp. 16–17, 21

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling
import Definitions.Def_TwoChoicesSuffice_KOut_Potentials
import Definitions.Def_TwoChoicesSuffice_KOut_Leaders
import Definitions.Def_TwoChoicesSuffice_KOut_Coloring

open scoped Classical

namespace TwoChoicesSuffice.KOut

variable {V : Type*} [Fintype V]

/-- The zero set `S = c⁻¹(0)` of a colouring (the marked vertices). -/
noncomputable def zeroSet {q : ℕ} [NeZero q] (c : V → Fin q) : Finset V :=
  Finset.univ.filter fun v => c v = 0

/-- Expectation under the marked two-out law of §7.2: draw the ordered two-choice outcome
`σ` uniformly from `outcomes G 2` (independent uniform choices with replacement); then,
conditional on the first-choice graph `H^1_G(σ)`, draw a uniformly random proper colouring
`c : V → {0,…,9}` of `H^1_G(σ)`, and let `S = c⁻¹(0)`. For a real function `f σ S` this is
`E[f] = |Ω|⁻¹ ∑_σ Z_10(H^1(σ))⁻¹ ∑_{c proper} f(σ, c⁻¹(0))`. The inner set of colourings
is never empty (`properColorings_prefixOne_nonempty`), so this is a genuine probability
average. Source: §7.2, PDF p. 16 (printed p. 15). -/
noncomputable def markedExpect (G : SimpleGraph V)
    (f : (V → Fin 2 → V) → Finset V → ℝ) : ℝ :=
  (∑ σ ∈ outcomes G 2,
      (∑ c ∈ properColorings 10 (prefixGraph G σ 1), f σ (zeroSet c)) /
        (numColorings 10 (prefixGraph G σ 1) : ℝ)) / ((outcomes G 2).card : ℝ)

/-- `R = {v ∈ S : s₂(v) ∈ U}`, the marked vertices whose second choice leaves `S`
(`U = V \ S`). Source: §7.2, PDF p. 16. -/
noncomputable def reserved (σ : V → Fin 2 → V) (S : Finset V) : Finset V :=
  S.filter fun v => σ v 1 ∉ S

/-- Relevant degrees: `d_v = |N_G(v) ∩ U|` for `v ∈ R`, and `d_v = 0` otherwise.
Source: §7.2, PDF p. 16. -/
noncomputable def relDeg (G : SimpleGraph V) (σ : V → Fin 2 → V) (S : Finset V) (v : V) :
    ℕ :=
  if v ∈ reserved σ S then (Finset.univ.filter fun w => G.Adj v w ∧ w ∉ S).card else 0

/-- The base graph `B(σ, S)`: the first choice of every vertex and the second choice of
every vertex of `U = V \ S`. Source: §7.2, PDF p. 16. -/
def baseGraph (G : SimpleGraph V) (σ : V → Fin 2 → V) (S : Finset V) : SimpleGraph V :=
  choiceGraph G σ (fun v i => i.val = 0 ∨ (i.val = 1 ∧ v ∉ S))

/-- The reserved choice `s₂(v)` of `v ∈ R` (dummy `v`, never an edge, for `v ∉ R`). -/
noncomputable def reservedChoice (σ : V → Fin 2 → V) (S : Finset V) (v : V) : V :=
  if v ∈ reserved σ S then σ v 1 else v

/-- The augmented base graph `B⁺(σ, S)`: to `B(σ, S)` add the reserved second choice of
each `B`-leader `α_C ∈ R` exactly when it reaches a higher `B`-component, leaders and
the order of components being taken for the relevant-degree order `≺` (increasing `d_v`,
ties broken by the fixed order `π` of `V`). Source: §7.2, PDF p. 17 (printed p. 16). -/
noncomputable def augBase (G : SimpleGraph V) [LinearOrder V] (σ : V → Fin 2 → V)
    (S : Finset V) : SimpleGraph V :=
  augment (relDeg G σ S) G (baseGraph G σ S) (reservedChoice σ S)

/-- `Φ_R(J) = ∑_{C ∈ CC(J)} max_{v ∈ C} d_v`, the component potential for the relevant
degrees. Source: §7.2, eq. (2), PDF p. 17. -/
noncomputable def relPotential (G : SimpleGraph V) (σ : V → Fin 2 → V) (S : Finset V)
    (J : SimpleGraph V) : ℕ :=
  compPotential (relDeg G σ S) J

/-- An edge `uv` is allowed (`∈ E° = E_G \ {uv : u, v ∈ S}`) unless both ends are marked. -/
def Allowed (S : Finset V) (u v : V) : Prop := ¬ (u ∈ S ∧ v ∈ S)

/-- `M_j(B)`: allowed crossing edges of `B = B(σ, S)` whose owner (endpoint in the higher
`B`-component, order `≺`) is at depth `j` in `B` and is marked (`∈ S`).
Source: §7.4.1, PDF p. 21 (printed p. 20). -/
noncomputable def markedDepth (G : SimpleGraph V) [LinearOrder V] (σ : V → Fin 2 → V)
    (S : Finset V) (j : ℕ) : ℕ :=
  ownedCount (relDeg G σ S) G (baseGraph G σ S) j (fun u v => Allowed S u v ∧ u ∈ S)

/-- `N_j(B)`: as `M_j(B)`, with an unmarked owner (`∈ U`). -/
noncomputable def unmarkedDepth (G : SimpleGraph V) [LinearOrder V] (σ : V → Fin 2 → V)
    (S : Finset V) (j : ℕ) : ℕ :=
  ownedCount (relDeg G σ S) G (baseGraph G σ S) j (fun u v => Allowed S u v ∧ u ∉ S)

/-- `T_j(B) = M_j(B) + N_j(B)`. -/
noncomputable def totalDepth (G : SimpleGraph V) [LinearOrder V] (σ : V → Fin 2 → V)
    (S : Finset V) (j : ℕ) : ℕ :=
  markedDepth G σ S j + unmarkedDepth G σ S j

end TwoChoicesSuffice.KOut


