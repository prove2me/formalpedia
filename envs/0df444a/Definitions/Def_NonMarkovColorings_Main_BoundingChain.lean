-- Prove2me | Definitions.Def_NonMarkovColorings_Main_BoundingChain
-- name    : NonMarkovColorings_Main_BoundingChain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:09:38.311172+00:00
-- url     : https://prove2.me/theorems/d0ab070d-2183-4dc4-bf7d-283d54bb7b9a
-- title:
--   The bounding chain $Z_t$, the sets $\mathcal P_t$, $\mathcal P$, $\mathcal P_{\le t}$, and the event $\mathrm{BC}(X_0,Y_0,\vec\sigma)$ (§3.2, Definition 3.1)
-- statement:
--   Fix labelings $X_0,Y_0$, a natural number $C_{cp}$, $T_{cp}=C_{cp}n$, an update sequence $\vec\sigma$ of length $T_{cp}$ and a fixed total order on $V$. The **bounding chain** is $Z_t:V\to 2^{[k]}$ with $Z_0(v)=\{X_0(v),Y_0(v)\}$. For $Z$ and $v$ let
--   $$A(Z,v)=[k]\setminus\bigcup_{w\in N(v)}Z(w),\quad H(Z,v)=\bigcup_{w\in N(v),\,|Z(w)|>1}Z(w),\quad B(Z,v)=[k]\setminus(A\cup H).$$
--   With $\mathcal P_t=\{v:|Z_t(v)|>1\}$, the update $(v_t,c_t)$ gives (p. 14): (1) $Z_t(w)=Z_{t-1}(w)$ for $w\ne v_t$; (2) $c_t\in A(Z_{t-1},v_t)\Rightarrow Z_t(v_t)=\{c_t\}$; (3) $c_t\in B(Z_{t-1},v_t)\Rightarrow Z_t(v_t)=Z_{t-1}(v_t)$; (4) $c_t\in H(Z_{t-1},v_t)$: (a) if $v_t\in\mathcal P_{t-1}$, $Z_t(v_t)=Z_{t-1}(v_t)$; (b) otherwise $Z_t(v_t)=Z_{t-1}(w)\cup Z_{t-1}(v_t)$ for the first $w$ of $\{u\in N(v_t)\cap\mathcal P_{t-1}: c_t\in Z_{t-1}(u)\}$ in the fixed order. Then $\mathcal P=\bigcup_{0\le t\le T_{cp}}\mathcal P_t$ and $\mathcal P_{\le t}=\bigcup_{s\le t}\mathcal P_s$. **$\mathrm{BC}(X_0,Y_0,\vec\sigma)$** holds (Definition 3.1) iff (1) $G[\mathcal P]$ is acyclic and there is no vertex $v$ with a cycle in $G[\mathcal P\cup\{v\}]$; (2) for all $1\le t\le T_{cp}$, $v_t\in\bigcup_{s<t}\mathcal P_s\Rightarrow c_t\notin H(Z_{t-1},v_t)$; (3) $|\mathcal P|\le\exp(\exp(C_{cp}^2))$.
--
--   **Formalization Note.** `Tcp V Ccp = Ccp * card V`; `bcA`, `bcH`, `bcB`, `potSet`, `bcStep`, `bcZ`, `bcP`, `bcPall`, `bcPle`, `BC G ob Ccp X0 Y0 σ`; `ob : VertexOrder V` is the fixed order of rule (4b). Acyclicity is `SimpleGraph.IsAcyclic` of `G.induce`. If the set in (4b) were empty (impossible when $c_t\in H$) $Z_t(v_t)$ is kept.
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), pp. 13–14 §3.2, Definition 3.1; p. 34 (T_cp = C_cp n)

import Mathlib
import Definitions.Def_NonMarkovColorings_Main_GraphNotions
import Definitions.Def_NonMarkovColorings_Main_LabelingChain

/-!
# The bounding chain Z_t, the potential-disagreement sets P_t, P, P_{≤t}, and the event BC

Jain, Mizgerd, Vigoda, *Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling
and Local Uniformity*, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), §3.2 pp. 13–14,
Definition 3.1 p. 14; `T_cp = C_cp n` from Theorem 5.4 p. 34.

* `Tcp V Ccp = Ccp · n` is the coupling length, `n = |V|`, `C_cp` a natural number.
* For `Z : V → Finset (Fin k)`: `bcA G Z v = [k] \ ⋃_{w ∈ N(v)} Z(w)` (available),
  `bcH G Z v = ⋃_{w ∈ N(v), |Z(w)| > 1} Z(w)` (hazardous),
  `bcB G Z v = [k] \ (A ∪ H)` (blocked); `potSet Z = {v : |Z(v)| > 1}`.
* `bcStep G ob Z (v, c)` is the update rule (1)–(4) of p. 14: other vertices unchanged;
  `c ∈ A` ⇒ `Z(v) := {c}`; `c ∈ B` ⇒ unchanged; `c ∈ H`: (a) if `v ∈ P_{t−1}` unchanged,
  (b) otherwise `Z(v) := Z(w) ∪ Z(v)` for the first `w` (in the fixed order `ob`) of
  `{u ∈ N(v) ∩ P_{t−1} : c ∈ Z(u)}` (nonempty whenever `c ∈ H`; if it were empty `Z(v)` is kept).
* `bcZ G ob X0 Y0 σ t` is `Z_t` with `Z_0(v) = {X0(v), Y0(v)}`; time `t` uses update
  `σ ⟨t − 1, _⟩ = (v_t, c_t)`.
* `bcP … t = P_t`, `bcPall … = P = ⋃_{0 ≤ t ≤ T} P_t`, `bcPle … t = P_{≤t} = ⋃_{s ≤ t} P_s`.
* `BC G ob Ccp X0 Y0 σ` is Definition 3.1 for `σ` of length `T_cp`:
  (1) `G[P]` is acyclic and `G[P ∪ {v}]` is acyclic for every vertex `v`;
  (2) for every `1 ≤ t ≤ T_cp`, `v_t ∈ ⋃_{s<t} P_s` implies `c_t ∉ H(Z_{t−1}, v_t)`
      (index `j : Fin T_cp` is time `t = j + 1`, so `⋃_{s<t} P_s = P_{≤j}`);
  (3) `|P| ≤ exp(exp(C_cp²))`.
-/

namespace NonMarkovColorings.Main

noncomputable section

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The coupling length `T_cp = C_cp · n`. -/
abbrev Tcp (V : Type*) [Fintype V] (Ccp : ℕ) : ℕ := Ccp * Fintype.card V

/-- `A(Z, v) = [k] \ ⋃_{w ∈ N(v)} Z(w)`. -/
def bcA (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (Z : V → Finset (Fin k)) (v : V) :
    Finset (Fin k) :=
  Finset.univ \ (G.neighborFinset v).biUnion Z

/-- `H(Z, v) = ⋃_{w ∈ N(v), |Z(w)| > 1} Z(w)`. -/
def bcH (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (Z : V → Finset (Fin k)) (v : V) :
    Finset (Fin k) :=
  ((G.neighborFinset v).filter fun w => 1 < (Z w).card).biUnion Z

/-- `B(Z, v) = [k] \ (A(Z, v) ∪ H(Z, v))`. -/
def bcB (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (Z : V → Finset (Fin k)) (v : V) :
    Finset (Fin k) :=
  Finset.univ \ (bcA G Z v ∪ bcH G Z v)

/-- `{v : |Z(v)| > 1}`. -/
def potSet {k : ℕ} (Z : V → Finset (Fin k)) : Finset V :=
  Finset.univ.filter fun v => 1 < (Z v).card

/-- One step of the bounding chain with update `(v, c)` (rules (1)–(4), p. 14). -/
def bcStep (G : SimpleGraph V) [DecidableRel G.Adj] (ob : VertexOrder V) {k : ℕ}
    (Z : V → Finset (Fin k)) (vc : V × Fin k) : V → Finset (Fin k) :=
  Function.update Z vc.1
    (if vc.2 ∈ bcA G Z vc.1 then {vc.2}
     else if vc.2 ∈ bcH G Z vc.1 then
       (if vc.1 ∈ potSet Z then Z vc.1
        else match ob.first ((G.neighborFinset vc.1 ∩ potSet Z).filter fun u => vc.2 ∈ Z u) with
          | some w => Z w ∪ Z vc.1
          | none => Z vc.1)
     else Z vc.1)

/-- The bounding chain `Z_t` driven by `σ` from `Z_0(v) = {X0(v), Y0(v)}`. -/
def bcZ (G : SimpleGraph V) [DecidableRel G.Adj] (ob : VertexOrder V) {k T : ℕ}
    (X0 Y0 : V → Fin k) (σ : UpdSeq V k T) : ℕ → V → Finset (Fin k)
  | 0 => fun v => {X0 v, Y0 v}
  | j + 1 => if h : j < T then bcStep G ob (bcZ G ob X0 Y0 σ j) (σ ⟨j, h⟩)
      else bcZ G ob X0 Y0 σ j

/-- `P_t = {v : |Z_t(v)| > 1}`. -/
def bcP (G : SimpleGraph V) [DecidableRel G.Adj] (ob : VertexOrder V) {k T : ℕ}
    (X0 Y0 : V → Fin k) (σ : UpdSeq V k T) (t : ℕ) : Finset V :=
  potSet (bcZ G ob X0 Y0 σ t)

/-- `P = ⋃_{0 ≤ t ≤ T} P_t`. -/
def bcPall (G : SimpleGraph V) [DecidableRel G.Adj] (ob : VertexOrder V) {k T : ℕ}
    (X0 Y0 : V → Fin k) (σ : UpdSeq V k T) : Finset V :=
  (Finset.range (T + 1)).biUnion fun t => bcP G ob X0 Y0 σ t

/-- `P_{≤t} = ⋃_{0 ≤ s ≤ t} P_s`. -/
def bcPle (G : SimpleGraph V) [DecidableRel G.Adj] (ob : VertexOrder V) {k T : ℕ}
    (X0 Y0 : V → Fin k) (σ : UpdSeq V k T) (t : ℕ) : Finset V :=
  (Finset.range (t + 1)).biUnion fun s => bcP G ob X0 Y0 σ s

/-- Definition 3.1: `BC(X0, Y0, σ) = True`. -/
def BC (G : SimpleGraph V) [DecidableRel G.Adj] (ob : VertexOrder V) (Ccp : ℕ) {k : ℕ}
    (X0 Y0 : V → Fin k) (σ : UpdSeq V k (Tcp V Ccp)) : Prop :=
  ((G.induce ((bcPall G ob X0 Y0 σ : Finset V) : Set V)).IsAcyclic ∧
    ∀ v : V, (G.induce ((insert v (bcPall G ob X0 Y0 σ) : Finset V) : Set V)).IsAcyclic) ∧
  (∀ j : Fin (Tcp V Ccp), (σ j).1 ∈ bcPle G ob X0 Y0 σ j.val →
      (σ j).2 ∉ bcH G (bcZ G ob X0 Y0 σ j.val) (σ j).1) ∧
  ((bcPall G ob X0 Y0 σ).card : ℝ) ≤ Real.exp (Real.exp ((Ccp : ℝ) ^ 2))

end

end NonMarkovColorings.Main


