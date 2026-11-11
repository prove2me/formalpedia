-- Prove2me | Definitions.Def_NonMarkovColorings_Main_NonMarkovCoupling
-- name    : NonMarkovColorings_Main_NonMarkovCoupling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:10:24.128978+00:00
-- url     : https://prove2.me/theorems/f9299ad3-00bd-42e8-83fe-0ebff8cdc3b5
-- title:
--   The local non-Markovian map $\mathrm{NM}_{t,H^*}$ (Conditions 3.3, 3.5, Definition 3.6), the local Jerrum map (Definition 3.9) and the global coupling $F_{X_0,Y_0}$ (Definition 3.10)
-- statement:
--   Setting of §3.3–3.4: labelings $X_0,Y_0$, $T_{cp}=C_{cp}n$, $\vec\sigma\in(V\times[k])^{T_{cp}}$, $X_t$ the evolution of $X_0$ by $\vec\sigma$, $Z_t,\mathcal P_t,\mathcal P$ the bounding chain. **Last/next successful updates:** $\tau^-_w(t)=\max\{s\in[1,t]: v_s=w,\ c_s\in A(X_{s-1},v_s)\}$ ($0$ if none), $\tau^+_w(t)=\min\{s\in(t,T_{cp}]:\dots\}$ ($T_{cp}+1$ if none); the **epoch** $I(w,t)=[\tau^-_w,\tau^+_w)$ when $\tau^-_w>0$, $I^\circ(w,t)=I(w,t)\setminus\{t\}$. **Exchangeable colors:** $\mathrm{Ex}(w,t)=\{X_{t-1}(w)\}\cup\{c\in A(X_{\tau^-_w-1},w):\forall s\in I^\circ(w,t),\ v_s\in N(w)\Rightarrow c_s\ne c\}$ if $\tau^-_w>0$, else $\emptyset$.
--
--   **Condition 3.3** (time $t$, two-element $H^*$): $c_t\in H(Z_{t-1},v_t)$; $p$ is the first element of $N(v_t)\cap\mathcal P_{t-1}$ in a fixed order; $H^*\subseteq Z_{t-1}(p)$, $\{X_{t-1}(p),c_t\}\subseteq H^*$, $|H^*|=2$; $|X_{t-1}(N_p(v_t))\cap H^*|=1$, its element is $c_b$ and $c_u\in H^*\setminus\{c_b\}$; every $w\in X_{t-1}^{-1}(c_b)\cap N_p(v_t)$ has $\tau^-_w>0$. Then
--   $$\mathrm{Avoid}(t)=\big(N^2_{v_t}(\mathcal P)\cap N_{\mathcal P}(v_t)\big)\cup\{w\in N_{\mathcal P}(v_t):\exists s\in I^\circ(w,t),\ v_s\in(N(w)\cap N^2_w(\mathcal P))\cup\{v_t\},\ c_s=X_{s-1}(w)\},$$
--   $\mathrm{Swap}_{\mathcal P}(c,t)=\{w\in N_{\mathcal P}(v_t): c\in\mathrm{Ex}(w,t)\}\setminus\mathrm{Avoid}(t)$; $\alpha:\mathrm{Swap}_{\mathcal P}(c_b,t)\to\mathrm{Swap}_{\mathcal P}(c_u,t)$ matches the $i$-th elements of the two sets listed by increasing $\deg z\cdot(|I(z,t)|/n+1)$, ties by a fixed order on $V$ (undefined beyond the shorter list); $\beta_z:\mathrm{Ex}(\alpha(z),t)\to\mathrm{Ex}(z,t)$ matches the $j$-th elements in the natural order of colors; $B=\{w\in N_{\mathcal P}(v_t): X_{t-1}(w)=c_b\}$. **Condition 3.5:** Condition 3.3, $\mathrm{BC}(X_0,Y_0,\vec\sigma)$, $X_{t-1}(N_p(v_t)\cap\mathcal P)\cap H^*=\emptyset$, $B\cap\mathrm{Avoid}(t)=\emptyset$, $\alpha$ defined on $B$, $\beta_w(X_{t-1}(\alpha(w)))$ defined and $\notin H^*$ for $w\in B$ with $\alpha(w)\ne w$, and $\alpha(B)\cap B=\{w\in B:\alpha(w)=w\}$.
--
--   **$\mathrm{NM}_{t,H^*}(\vec\sigma)$** (Definition 3.6) keeps the vertices and sets: (1) $c'_{\tau^-_w}=c_u$ for $w\in B$ with $\alpha(w)=w$; (2) $c'_{\tau^-_w}=\beta_w(X_{t-1}(\alpha(w)))$ and $c'_{\tau^-_{\alpha(w)}}=c_u$ for $w\in B$ with $\alpha(w)\ne w$; (3) $c'_s=c'_{\tau^-_w}$ for $w\in B\cup\alpha(B)$ and $s\in I^\circ(w,t)$ with $v_s\in N(w)$, $c_s=X_{s-1}(w)$; (4) $c'_t=H^*\setminus\{c_t\}$; (5) $c'_s=c_s$ otherwise. **$\mathrm{Jerrum}_{t,H}$** (Definition 3.9) replaces $c_t$ by $H\setminus\{c_t\}$ when $c_t\in H$.
--
--   **$F_{X_0,Y_0}(\vec\sigma)$** (Definition 3.10) is $\vec\sigma$ if $\mathrm{BC}$ fails, and otherwise $f_{\le T_{cp}}(\vec\sigma)$ with $f_0=\mathrm{id}$, $D_0=\{z^*\}$ and, writing $Y^{t-1}_{t-1}$ for $Y_0$ run $t-1$ steps on $f_{\le t-1}(\vec\sigma)$: (1) $v_t\notin B_1(D_{t-1})$: $f_t=\mathrm{id}$, $D_t=D_{t-1}$; (2) $v_t\in D_{t-1}$: $f_t=\mathrm{id}$, $D_t=D_{t-1}\setminus\{v_t\}$ if $c_t\in A(X_{t-1},v_t)$, else $D_{t-1}$; (3) otherwise, if $v_t\in\mathcal P_{\le t-1}$ then $f_t=\mathrm{id}$, $D_t=D_{t-1}$; else $p$ = first element of $N(v_t)\cap D_{t-1}$ in a fixed order, $H=\{X_{t-1}(p),Y^{t-1}_{t-1}(p)\}$: (3a) $|H|=1$: identity; (3b) $|H|=2$, $c_t\ne Y^{t-1}_{t-1}(p)$: $f_t=\mathrm{Jerrum}_{t,H}$; (3c) otherwise $f_t=\mathrm{Jerrum}_{t,H}$ if $H\subseteq X_{t-1}(N_p(v_t))$ ($D_t=D_{t-1}$), $\mathrm{NM}_{t,H}$ if $H\cap X_{t-1}(N_p(v_t))=\{c_t\}$ and Condition 3.5 holds ($D_t=D_{t-1}$), $\mathrm{NM}_{t,H}$ if $H\cap X_{t-1}(N_p(v_t))=H\setminus\{c_t\}$ and Condition 3.5 holds ($D_t=D_{t-1}\cup\{v_t\}$), $\mathrm{Jerrum}_{t,H}$ otherwise ($D_t=D_{t-1}\cup\{v_t\}$); whenever $v_t$ would be added, $D_t=D_{t-1}$ instead if $X_t(v_t)=Y^t_t(v_t)$. When $f_t=\mathrm{NM}_{t,H}$, its conditions and replacements $c_s\mapsto d_s$ are computed from the original input $(X_0,Y_0,\vec\sigma)$ and applied to $f_{\le t-1}(\vec\sigma)$ as color transpositions $(c_s\,d_s)$.
--
--   **Formalization Note.** Index `i : Fin (Tcp V Ccp)` is time $t=i+1$. `Orders V` holds the four fixed orders (`bc`: rule (4b); `parent`: $p$ of Condition 3.3; `tie`: ties in $\alpha$; `dpar`: $p$ in Definition 3.10). `lastSucc`, `nextSucc`, `epoch`, `epochP`, `exColors`, `nmParent`, `nmBlocked` ($c_b$), `nmUnblocked` ($c_u$), `nmAvoid`, `nmSwap`, `nmSorted`, `nmAlpha`, `nmBeta` (`none` = undefined), `nmB`, `nmAlphaB`, `Cond33`, `Cond35`, `nmChi`, `NM`, `jerrum`, `nmApply`, `globalStep`, `globalStage`, `globalCoupling G o Ccp X0 Y0 σ` $=F_{X_0,Y_0}(\vec\sigma)$ with $D_0=X_0\oplus Y_0$. All maps are total; where the paper leaves a value undefined (outside Conditions 3.3/3.5) a fixed junk value is used, never reached in the statements that assume those conditions. In rule (3), if several $w$ qualify (impossible under Condition 3.5, Fact 3.8) the first in the order `tie` is used. "$H\subset X_{t-1}(N_p(v_t))$" in (3c) is read as inclusion.
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), pp. 15–20 §3.3–3.4, Condition 3.3, Condition 3.5, Definitions 3.6, 3.9, 3.10

import Mathlib
import Definitions.Def_NonMarkovColorings_Main_GraphNotions
import Definitions.Def_NonMarkovColorings_Main_LabelingChain
import Definitions.Def_NonMarkovColorings_Main_BoundingChain

/-!
# The local non-Markovian map NM_{t,H*}, the local Jerrum map, and the global coupling F

Jain, Mizgerd, Vigoda, *Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling
and Local Uniformity*, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), §3.3 pp. 15–18
(τ±, epochs, Condition 3.3, Ex, Avoid, Swap_P, α, β, B, Condition 3.5, Definition 3.6),
§3.4 pp. 18–20 (Definition 3.9, Definition 3.10).

Conventions.
* Times. `σ : Fin T → V × Fin k`; index `j` is the paper's time `s = j + 1`, so
  `X_{s−1} = run G X0 σ j`. Paper times are natural numbers `t ∈ [1, T]`.
  `lastSucc … w t = τ⁻_w(t) = max{s ∈ [1, t] : v_s = w, c_s ∈ A(X_{s−1}, v_s)}` (`0` if none),
  `nextSucc … w t = τ⁺_w(t) = min{s ∈ (t, T] : …}` (`T + 1` if none),
  `epoch … w t = I(w, t) = [τ⁻, τ⁺)` as a set of indices (empty — "undefined" — when `τ⁻ = 0`),
  `epochP … w t = I°(w, t) = I(w, t) \ {t}`, `exColors … w t = Ex(w, t)`.
* Fixed orders. `Orders V` carries the four "fixed, but otherwise arbitrary" total orders on `V`:
  `bc` (witness in rule (4b) of the bounding chain, p. 14), `parent` (the parent `p` of
  Condition 3.3, p. 16), `tie` (tie-break of the orderings of `Swap_P` defining `α`, p. 17) and
  `dpar` (the parent `p` of case (3) of Definition 3.10, p. 19). Colors use the natural order of
  `Fin k` (`β`, p. 17).
* The local data at index `i` (paper time `t = i + 1`) with input set `H` (`H*`): `nmParent` is
  `p`, `nmBlocked` is `c_b`, `nmUnblocked` is `c_u`, `nmAvoid` is `Avoid(t)`, `nmSwap c` is
  `Swap_P(c, t)`, `nmAlpha` is `α` (`none` = undefined), `nmBeta z` is `β_z`, `nmB` is `B`.
  `P` is the global `P = ⋃_{t ≤ T_cp} P_t` of the bounding chain. These are total functions; the
  values outside Condition 3.3 / 3.5 are junk the paper leaves undefined (`p := v_t`,
  `c_b, c_u := c_t` when the unique element does not exist).
* `Cond33`, `Cond35` are Conditions 3.3 and 3.5 (Condition 3.5 includes `BC(X0, Y0, σ)`).
* `NM … σ i H` is Definition 3.6, computed from its own input `σ`: rule (4) at time `t`, then
  rules (1)–(2) at `τ⁻_w` for `w ∈ B ∪ α(B)`, then rule (3), then rule (5). Under Condition 3.5
  these edits are disjoint (Fact 3.8). Outside it, if several `w` qualify in rule (3) the first in
  the order `tie` is used (junk case).
* `jerrum i H η` is Definition 3.9 at time `t = i + 1`, applied to its input `η`.
* `globalCoupling … X0 Y0 σ` is Definition 3.10's `F_{X0,Y0}(σ)`: `σ` if `BC(X0, Y0, σ)` is
  false, otherwise `f_{≤T_cp}(σ)`. The stage `t` map acts on the intermediate sequence
  `η = f_{≤t−1}(σ)`; `Y^{t−1}_{t−1}` is `run G Y0 η (t − 1)`. All case conditions, `X_{t−1}`,
  `c_t`, `P_{≤t−1}` and Condition 3.5 are computed from the original input `(X0, Y0, σ)`. When
  the rule selects `NM_{t,H}`, the replacements `c_s ↦ d_s` with `d_s` the colors of
  `NM … σ i H` are applied to `η` as color transpositions `(c_s d_s)`. `D_0 = X0 ⊕ Y0` (`= {z*}`).
  `F` is meant for `|X0 ⊕ Y0| = 1`; the function is total.
-/

namespace NonMarkovColorings.Main

noncomputable section

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The four fixed total orders on `V` used by the construction. -/
structure Orders (V : Type*) where
  /-- Witness choice in rule (4b) of the bounding chain. -/
  bc : VertexOrder V
  /-- The parent `p` of Condition 3.3. -/
  parent : VertexOrder V
  /-- Tie-break in the orderings of `Swap_P(c_b, t)` and `Swap_P(c_u, t)`. -/
  tie : VertexOrder V
  /-- The parent `p` in case (3) of Definition 3.10. -/
  dpar : VertexOrder V

/-- `H \ {c}` for a two-element `H ∋ c` (the least element of `H \ {c}`; `c` if empty). -/
def otherColor {k : ℕ} (H : Finset (Fin k)) (c : Fin k) : Fin k :=
  ((H.erase c).sort (· ≤ ·)).head?.getD c

/-- `τ⁻_w(t)`: the last successful update of `w` at a time in `[1, t]` (`0` if none). -/
def lastSucc (G : SimpleGraph V) [DecidableRel G.Adj] {k T : ℕ} (X0 : V → Fin k)
    (σ : UpdSeq V k T) (w : V) (t : ℕ) : ℕ :=
  ((Finset.univ.filter fun j : Fin T =>
      j.val + 1 ≤ t ∧ (σ j).1 = w ∧ (σ j).2 ∈ avail G (run G X0 σ j.val) w).image
    fun j => j.val + 1).sup id

/-- `τ⁺_w(t)`: the next successful update of `w` at a time in `(t, T]` (`T + 1` if none). -/
def nextSucc (G : SimpleGraph V) [DecidableRel G.Adj] {k T : ℕ} (X0 : V → Fin k)
    (σ : UpdSeq V k T) (w : V) (t : ℕ) : ℕ :=
  let S := (Finset.univ.filter fun j : Fin T =>
      t < j.val + 1 ∧ (σ j).1 = w ∧ (σ j).2 ∈ avail G (run G X0 σ j.val) w).image
    fun j => j.val + 1
  if h : S.Nonempty then S.min' h else T + 1

/-- The update epoch `I(w, t) = [τ⁻_w, τ⁺_w)` (as indices `j`, time `j + 1`); empty when
`τ⁻_w = 0` (undefined in the paper). -/
def epoch (G : SimpleGraph V) [DecidableRel G.Adj] {k T : ℕ} (X0 : V → Fin k)
    (σ : UpdSeq V k T) (w : V) (t : ℕ) : Finset (Fin T) :=
  if 0 < lastSucc G X0 σ w t then
    Finset.univ.filter fun j : Fin T =>
      lastSucc G X0 σ w t ≤ j.val + 1 ∧ j.val + 1 < nextSucc G X0 σ w t
  else ∅

/-- The punctured epoch `I°(w, t) = I(w, t) \ {t}`. -/
def epochP (G : SimpleGraph V) [DecidableRel G.Adj] {k T : ℕ} (X0 : V → Fin k)
    (σ : UpdSeq V k T) (w : V) (t : ℕ) : Finset (Fin T) :=
  (epoch G X0 σ w t).filter fun j => j.val + 1 ≠ t

/-- The exchangeable colors `Ex(w, t) = {X_{t−1}(w)} ∪ {c ∈ A(X_{τ⁻_w − 1}, w) : no neighbour of
`w` proposes `c` during `I°(w, t)`}` when `τ⁻_w > 0`, and `∅` otherwise. -/
def exColors (G : SimpleGraph V) [DecidableRel G.Adj] {k T : ℕ} (X0 : V → Fin k)
    (σ : UpdSeq V k T) (w : V) (t : ℕ) : Finset (Fin k) :=
  if 0 < lastSucc G X0 σ w t then
    insert (run G X0 σ (t - 1) w)
      ((avail G (run G X0 σ (lastSucc G X0 σ w t - 1)) w).filter fun c =>
        ∀ j ∈ epochP G X0 σ w t, (σ j).1 ∈ G.neighborFinset w → (σ j).2 ≠ c)
  else ∅

section Local

variable (G : SimpleGraph V) [DecidableRel G.Adj] (o : Orders V) (Ccp : ℕ) {k : ℕ}
  (X0 Y0 : V → Fin k) (σ : UpdSeq V k (Tcp V Ccp))

/-- The parent `p`: the first element of `N(v_t) ∩ P_{t−1}` in the order `o.parent`
(junk `v_t` if empty). -/
def nmParent (i : Fin (Tcp V Ccp)) : V :=
  (o.parent.first (G.neighborFinset (σ i).1 ∩ bcP G o.bc X0 Y0 σ i.val)).getD (σ i).1

/-- `c_b`: the unique element of `X_{t−1}(N_p(v_t)) ∩ H*` (junk `c_t` if none). -/
def nmBlocked (i : Fin (Tcp V Ccp)) (H : Finset (Fin k)) : Fin k :=
  (((nbrOut G {nmParent G o Ccp X0 Y0 σ i} (σ i).1).image (run G X0 σ i.val) ∩ H).sort
    (· ≤ ·)).head?.getD (σ i).2

/-- `c_u`: the unique element of `H* \ {c_b}` (junk `c_t` if none). -/
def nmUnblocked (i : Fin (Tcp V Ccp)) (H : Finset (Fin k)) : Fin k :=
  ((H.erase (nmBlocked G o Ccp X0 Y0 σ i H)).sort (· ≤ ·)).head?.getD (σ i).2

/-- `Avoid(t) = (N²_{v_t}(P) ∩ N_P(v_t)) ∪ {w ∈ N_P(v_t) : ∃ s ∈ I°(w, t),
v_s ∈ (N(w) ∩ N²_w(P)) ∪ {v_t}, c_s = X_{s−1}(w)}`. -/
def nmAvoid (i : Fin (Tcp V Ccp)) : Finset V :=
  let P := bcPall G o.bc X0 Y0 σ
  let vt := (σ i).1
  (sphereOut G 2 {vt} P ∩ nbrOut G P vt) ∪
    (nbrOut G P vt).filter fun w => ∃ j ∈ epochP G X0 σ w (i.val + 1),
      (σ j).1 ∈ (G.neighborFinset w ∩ sphereOut G 2 {w} P) ∪ {vt} ∧
      (σ j).2 = run G X0 σ j.val w

/-- `Swap_P(c, t) = {w ∈ N_P(v_t) : c ∈ Ex(w, t)} \ Avoid(t)`. -/
def nmSwap (i : Fin (Tcp V Ccp)) (c : Fin k) : Finset V :=
  ((nbrOut G (bcPall G o.bc X0 Y0 σ) (σ i).1).filter fun w =>
      c ∈ exColors G X0 σ w (i.val + 1)) \ nmAvoid G o Ccp X0 Y0 σ i

/-- A set of vertices listed by increasing `deg z · (|I(z, t)|/n + 1)`, ties broken by the
order `o.tie` (`mergeSort` is stable). -/
def nmSorted (i : Fin (Tcp V Ccp)) (S : Finset V) : List V :=
  (o.tie.listOf S).mergeSort fun a b =>
    decide ((G.degree a : ℝ) * (((epoch G X0 σ a (i.val + 1)).card : ℝ) / Fintype.card V + 1) ≤
      (G.degree b : ℝ) * (((epoch G X0 σ b (i.val + 1)).card : ℝ) / Fintype.card V + 1))

/-- The complementary neighbour map `α : Swap_P(c_b, t) → Swap_P(c_u, t)`, `α(z_i) = z'_i`
(`none` = undefined). -/
def nmAlpha (i : Fin (Tcp V Ccp)) (H : Finset (Fin k)) (z : V) : Option V :=
  let L1 := nmSorted G o Ccp X0 σ i (nmSwap G o Ccp X0 Y0 σ i (nmBlocked G o Ccp X0 Y0 σ i H))
  let L2 := nmSorted G o Ccp X0 σ i (nmSwap G o Ccp X0 Y0 σ i (nmUnblocked G o Ccp X0 Y0 σ i H))
  if z ∈ L1 then L2[L1.idxOf z]? else none

/-- The complementary color map `β_z : Ex(α(z), t) → Ex(z, t)`, `β_z(c'_j) = c_j` in the natural
order of colors (`none` = undefined). -/
def nmBeta (i : Fin (Tcp V Ccp)) (H : Finset (Fin k)) (z : V) (c : Fin k) : Option (Fin k) :=
  match nmAlpha G o Ccp X0 Y0 σ i H z with
  | some a =>
    let E' := (exColors G X0 σ a (i.val + 1)).sort (· ≤ ·)
    let E := (exColors G X0 σ z (i.val + 1)).sort (· ≤ ·)
    if c ∈ E' then E[E'.idxOf c]? else none
  | none => none

/-- The blocking neighbours `B = {w ∈ N_P(v_t) : X_{t−1}(w) = c_b}`. -/
def nmB (i : Fin (Tcp V Ccp)) (H : Finset (Fin k)) : Finset V :=
  (nbrOut G (bcPall G o.bc X0 Y0 σ) (σ i).1).filter fun w =>
    run G X0 σ i.val w = nmBlocked G o Ccp X0 Y0 σ i H

/-- `α(B)`. -/
def nmAlphaB (i : Fin (Tcp V Ccp)) (H : Finset (Fin k)) : Finset V :=
  (nmB G o Ccp X0 Y0 σ i H).biUnion fun w => (nmAlpha G o Ccp X0 Y0 σ i H w).toFinset

/-- Condition 3.3 at time `t = i + 1` with input set `H = H*`. -/
def Cond33 (i : Fin (Tcp V Ccp)) (H : Finset (Fin k)) : Prop :=
  let vt := (σ i).1
  let ct := (σ i).2
  let Xp := run G X0 σ i.val
  let p := nmParent G o Ccp X0 Y0 σ i
  ct ∈ bcH G (bcZ G o.bc X0 Y0 σ i.val) vt ∧
  (G.neighborFinset vt ∩ bcP G o.bc X0 Y0 σ i.val).Nonempty ∧
  H ⊆ bcZ G o.bc X0 Y0 σ i.val p ∧ ({Xp p, ct} : Finset (Fin k)) ⊆ H ∧ H.card = 2 ∧
  ((nbrOut G {p} vt).image Xp ∩ H).card = 1 ∧
  ∀ w ∈ nbrOut G {p} vt, Xp w = nmBlocked G o Ccp X0 Y0 σ i H →
    0 < lastSucc G X0 σ w (i.val + 1)

/-- Condition 3.5 (non-Markovian well-defined) at time `t = i + 1` with input set `H = H*`. -/
def Cond35 (i : Fin (Tcp V Ccp)) (H : Finset (Fin k)) : Prop :=
  let vt := (σ i).1
  let Xp := run G X0 σ i.val
  let p := nmParent G o Ccp X0 Y0 σ i
  let B := nmB G o Ccp X0 Y0 σ i H
  let α := nmAlpha G o Ccp X0 Y0 σ i H
  Cond33 G o Ccp X0 Y0 σ i H ∧
  BC G o.bc Ccp X0 Y0 σ ∧
  (nbrOut G {p} vt ∩ bcPall G o.bc X0 Y0 σ).image Xp ∩ H = ∅ ∧
  B ∩ nmAvoid G o Ccp X0 Y0 σ i = ∅ ∧
  (∀ w ∈ B, (α w).isSome) ∧
  (∀ w ∈ B, α w ≠ some w → ∃ a c, α w = some a ∧
      nmBeta G o Ccp X0 Y0 σ i H w (Xp a) = some c ∧ c ∉ H) ∧
  nmAlphaB G o Ccp X0 Y0 σ i H ∩ B = B.filter fun w => α w = some w

/-- The new color `c'_{τ⁻_w}` given to `w ∈ B ∪ α(B)` by rules (1)–(2) of Definition 3.6:
`c_u` if `w ∈ B` with `α(w) = w`; `β_w(X_{t−1}(α(w)))` if `w ∈ B` with `α(w) ≠ w`; `c_u` if
`w = α(w')` for some other `w' ∈ B`. -/
def nmChi (i : Fin (Tcp V Ccp)) (H : Finset (Fin k)) (w : V) : Option (Fin k) :=
  let α := nmAlpha G o Ccp X0 Y0 σ i H
  if w ∈ nmB G o Ccp X0 Y0 σ i H then
    (if α w = some w then some (nmUnblocked G o Ccp X0 Y0 σ i H)
     else (α w).bind fun a => nmBeta G o Ccp X0 Y0 σ i H w (run G X0 σ i.val a))
  else if w ∈ nmAlphaB G o Ccp X0 Y0 σ i H then some (nmUnblocked G o Ccp X0 Y0 σ i H)
  else none

/-- Definition 3.6: the local non-Markovian transformation `NM_{t,H*}(σ)`, `t = i + 1`. -/
def NM (i : Fin (Tcp V Ccp)) (H : Finset (Fin k)) : UpdSeq V k (Tcp V Ccp) :=
  fun j =>
    let W := nmB G o Ccp X0 Y0 σ i H ∪ nmAlphaB G o Ccp X0 Y0 σ i H
    let u := (σ j).1
    ((σ j).1,
      if j = i then otherColor H (σ i).2
      else if u ∈ W ∧ lastSucc G X0 σ u (i.val + 1) = j.val + 1 then
        (nmChi G o Ccp X0 Y0 σ i H u).getD (σ j).2
      else
        match o.tie.first (W.filter fun w => j ∈ epochP G X0 σ w (i.val + 1) ∧
            u ∈ G.neighborFinset w ∧ (σ j).2 = run G X0 σ j.val w) with
        | some w => (nmChi G o Ccp X0 Y0 σ i H w).getD (σ j).2
        | none => (σ j).2)

end Local

/-- Definition 3.9: `Jerrum_{t,H}(η)` with `t = i + 1`: the color at time `t` is swapped within
`H`, all other entries unchanged. -/
def jerrum {k T : ℕ} (i : Fin T) (H : Finset (Fin k)) (η : UpdSeq V k T) : UpdSeq V k T :=
  fun j => if j = i then ((η j).1, if (η j).2 ∈ H then otherColor H (η j).2 else (η j).2)
    else η j

/-- The color transposition `(a b)` applied to `x`. -/
def transposeColor {k : ℕ} (a b x : Fin k) : Fin k :=
  if x = a then b else if x = b then a else x

section Global

variable (G : SimpleGraph V) [DecidableRel G.Adj] (o : Orders V) (Ccp : ℕ) {k : ℕ}
  (X0 Y0 : V → Fin k) (σ : UpdSeq V k (Tcp V Ccp))

/-- `f_t = NM_{t,H}` inside Definition 3.10: the replacements `c_s ↦ d_s` prescribed by
`NM_{t,H}` on the original input `σ` are applied to `η` as color transpositions `(c_s d_s)`. -/
def nmApply (i : Fin (Tcp V Ccp)) (H : Finset (Fin k)) (η : UpdSeq V k (Tcp V Ccp)) :
    UpdSeq V k (Tcp V Ccp) :=
  fun j => ((η j).1, transposeColor (σ j).2 (NM G o Ccp X0 Y0 σ i H j).2 (η j).2)

/-- One stage `t = i + 1` of Definition 3.10: from `(f_{≤t−1}(σ), D_{t−1})` to
`(f_{≤t}(σ), D_t)`, cases (1), (2), (3a)–(3c) and the final retention clause. -/
def globalStep (i : Fin (Tcp V Ccp)) (st : UpdSeq V k (Tcp V Ccp) × Finset V) :
    UpdSeq V k (Tcp V Ccp) × Finset V :=
  let η := st.1
  let D := st.2
  let vt := (σ i).1
  let ct := (σ i).2
  let Xp := run G X0 σ i.val
  let Yp := run G Y0 η i.val
  if vt ∉ ball G 1 D then (η, D)
  else if vt ∈ D then (η, if ct ∈ avail G Xp vt then D.erase vt else D)
  else if vt ∈ bcPle G o.bc X0 Y0 σ i.val then (η, D)
  else
    let p := (o.dpar.first (G.neighborFinset vt ∩ D)).getD vt
    let H : Finset (Fin k) := {Xp p, Yp p}
    if H.card = 1 then (η, D)
    else if ct ≠ Yp p then (jerrum i H η, D)
    else
      let S := (nbrOut G {p} vt).image Xp
      let res : UpdSeq V k (Tcp V Ccp) × Bool :=
        if H ⊆ S then (jerrum i H η, false)
        else if H ∩ S = {ct} ∧ Cond35 G o Ccp X0 Y0 σ i H then
          (nmApply G o Ccp X0 Y0 σ i H η, false)
        else if H ∩ S = H.erase ct ∧ Cond35 G o Ccp X0 Y0 σ i H then
          (nmApply G o Ccp X0 Y0 σ i H η, true)
        else (jerrum i H η, true)
      (res.1,
        if res.2 = true ∧ run G X0 σ (i.val + 1) vt ≠ run G Y0 res.1 (i.val + 1) vt
        then insert vt D else D)

/-- `(f_{≤t}(σ), D_t)` for `t = 0, 1, …`, with `f_0 = id` and `D_0 = X0 ⊕ Y0`. -/
def globalStage : ℕ → UpdSeq V k (Tcp V Ccp) × Finset V
  | 0 => (σ, diffSet X0 Y0)
  | j + 1 => if h : j < Tcp V Ccp then globalStep G o Ccp X0 Y0 σ ⟨j, h⟩ (globalStage j)
      else globalStage j

/-- Definition 3.10: the global coupling `F_{X0,Y0}(σ)`. -/
def globalCoupling : UpdSeq V k (Tcp V Ccp) :=
  if BC G o.bc Ccp X0 Y0 σ then (globalStage G o Ccp X0 Y0 σ (Tcp V Ccp)).1 else σ

end Global

end

end NonMarkovColorings.Main


