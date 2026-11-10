-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_LocalUpdate
-- name    : KSATSingleFlip_Connect_LocalUpdate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:07:28.531337+00:00
-- url     : https://prove2.me/theorems/c1fcd0e0-7c5f-4f62-9c0a-0b82f0fe0598
-- title:
--   LocalUpdate (Algorithm 1), the local-update flow $g_v$ and the planted Poisson tree $\mathrm{Tree}_{\mathrm{pl}}(\lambda^+)$
-- statement:
--   * Tree formulas (§4.2, p. 24): `IsTreeFormula Φ o L`: the factor graph is acyclic, every variable and clause is connected to the root $o$, and every variable has depth (half the factor-graph distance, `vdepth`) at most $L$. $V_v$ = `desc Φ o v` (the $u$ whose path from the root passes through $v$), $\Phi_v$ = `subtreeF` (clauses with scope in $V_v$), the child clauses of $v$ = `childClauses`.
--   * $\mu_{\Psi,x_S}(E)$ = `condP Ψ S x E`: the probability of $E$ under the uniform law on satisfying assignments of $\Psi$ agreeing with $x$ on $S$.
--   * Algorithm 1 (p. 25), with $a_k = (1+\exp(2(\max\{1,\ln\ln k\})^{3/4}))^{-1}$ (`aK`): retention coins $\eta_v\sim\mathrm{Bernoulli}(\vartheta)$ at depth 1 (`coinWeight`); $R$ starts as the depth-$L$ variables plus $V_v$ for every depth-1 $v$ with $\eta_v=0$ (`revealInit`); variables are processed in decreasing order of depth (`revealed`, `levelStep`): Line 8 (`pruneSet`) adds $\bigcup_u V_u$ over the children of each child clause $C$ of $v$ having at least two children $u$ with $q_{C,u} = \mu_{\Phi_u,x_{R\cap V_u}}(u\text{'s literal in }C\text{ true}) > 0$; Line 10 (`windowSet`) adds $V_v$ when $q_v = \mu_{\Phi_v,x_{R\cap V_v}}(\sigma_v=1)\notin[a_k,1-a_k]$. Variables of one depth are processed together: their subtrees are disjoint and each step reads $R$ only inside the subtree processed, so this equals the one-at-a-time loop. Line 11: $y\sim\mu_{\Phi,x_R}$. `luProb Φ o k L ϑ x y` $=\Pr(\mathrm{LocalUpdate}(x) = y)$; `luFlow` $= \mathbb E[\mathbf 1\{y_v\ne x_v\}/\max\{1,d_H(x,y)\}]$. Variables not connected to the root are frozen (added to $R$); on a tree formula there are none, and on a ball formula they are the variables outside the ball, which the paper keeps unchanged.
--   * $L_x$ = `Lx Φ x`: clauses with one or two $x$-true literals. $g_v(\Phi,x)$ = `gFlow k L ϑ Φ x v` (§4.3, p. 29): the flow at $v$ of LocalUpdate on $B_L(L_x,v)$ (root $v$) when $v$ is $(L,k^4)$-locally tree-structured in $L_x$, else $0$.
--   * $\mathrm{Tree}_{\mathrm{pl}}(\lambda^+)$ (Definition 2.3) truncated at depth $L$: signed trees `TreeD d r` (clause width $d+1 = k$); `plW` is the probability of a tree given its root spin: $\mathrm{Pois}(D)$ child clauses per variable with $D = (2^k-1)\lambda^+$, uniform child spins, signs uniform among the $2^k-1$ patterns satisfied by the spins; the root spin is uniform. `flat`/`treeFormula` number the variables (root $0$). `plantedFlow k λ⁺ L ϑ` $= \mathbb E[\mathbf 1\{y_o\ne x_o\}/\max\{1,d_H(x,y)\}]$ for $(\Phi,x)$ from the truncated tree and $y\leftarrow\mathrm{LocalUpdate}(x)$ (an $[0,\infty]$-valued sum over trees). $\varepsilon_k = (\ln k)^{10}/k$ (`epsK`).
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), §4.2 Algorithm 1 (printed pp. 24–25, PDF 26–27), §4.3 (p. 29, PDF 31), Definition 2.3 (p. 11, PDF 13)

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_Model
import Definitions.Def_KSATSingleFlip_Connect_FactorGraph

noncomputable section

open scoped Classical BigOperators ENNReal

namespace KSATSingleFlip.Connect

/-! # LocalUpdate (Algorithm 1), the local-update flow `g_v` and the planted tree `Tree_pl`

Wang, Yin, Yu, Zhang (2026), arXiv:2611.05981: §4.2 (printed pp. 24–25, Algorithm 1),
§4.3 (p. 29, the flow `g_v`), Definition 2.3 (p. 11, the planted Poisson tree). -/

section Tree

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `u` is connected to the root `o` in the factor graph of `Φ`. -/
def Conn (Φ : GFormula V) (o u : V) : Prop := (factorGraph Φ).Reachable (Sum.inl o) (Sum.inl u)

/-- The depth of a variable `u` connected to the root `o`: half its factor-graph distance. -/
def vdepth (Φ : GFormula V) (o u : V) : ℕ := (factorGraph Φ).dist (Sum.inl o) (Sum.inl u) / 2

/-- `Φ` is a tree formula rooted at `o` with depth at most `L` (§4.2, p. 24): its factor graph is a
tree containing every variable and clause, and every variable has depth at most `L`. -/
def IsTreeFormula (Φ : GFormula V) (o : V) (L : ℕ) : Prop :=
  (factorGraph Φ).IsAcyclic ∧ (∀ a, (factorGraph Φ).Reachable (Sum.inl o) a) ∧
    ∀ u, vdepth Φ o u ≤ L

/-- `V_v`: `v` and its descendant variables (the `u` whose path from the root passes through
`v`). -/
def desc (Φ : GFormula V) (o v : V) : Finset V :=
  Finset.univ.filter fun u => Conn Φ o v ∧ Conn Φ v u ∧ Conn Φ o u ∧
    (factorGraph Φ).dist (Sum.inl o) (Sum.inl u) =
      (factorGraph Φ).dist (Sum.inl o) (Sum.inl v) + (factorGraph Φ).dist (Sum.inl v) (Sum.inl u)

/-- `Φ_v`: the sub-formula on `V_v` (the clauses whose scope lies in `V_v`). -/
def subtreeF (Φ : GFormula V) (o v : V) : GFormula V := Φ.filter fun C => decide (vbl C ⊆ desc Φ o v)

/-- The child clauses of `v` (positions adjacent to `v` and one step farther from the root). -/
def childClauses (Φ : GFormula V) (o v : V) : Finset (Fin Φ.length) :=
  Finset.univ.filter fun j => (Φ.get j v).isSome ∧
    (factorGraph Φ).Reachable (Sum.inl o) (Sum.inr j) ∧
    (factorGraph Φ).dist (Sum.inl o) (Sum.inr j) = (factorGraph Φ).dist (Sum.inl o) (Sum.inl v) + 1

/-- `µ_{Ψ, x_S}(E)`: the probability of `E` under the uniform law on the satisfying assignments of
`Ψ` that agree with `x` on `S` (variables outside the scope of `Ψ` are free and cancel). -/
def condP (Ψ : GFormula V) (S : Finset V) (x : V → Bool) (E : (V → Bool) → Prop) : ℝ :=
  ((Finset.univ.filter fun σ => FSat σ Ψ ∧ (∀ u ∈ S, σ u = x u) ∧ E σ).card : ℝ) /
    ((Finset.univ.filter fun σ => FSat σ Ψ ∧ ∀ u ∈ S, σ u = x u).card : ℝ)

/-- `a_k = (1 + exp(2 (max{1, ln ln k})^{3/4}))^{-1}` (Algorithm 1, line 1). -/
def aK (k : ℕ) : ℝ :=
  1 / (1 + Real.exp (2 * Real.rpow (max 1 (Real.log (Real.log k))) (3 / 4)))

/-- The initial revealed set (Algorithm 1, line 3) for retention coins `η` (`η v = false` freezes
the depth-1 subtree `V_v`): the variables at depth `≥ L`, plus `V_v` for every depth-1 `v` with
`η v = false`. Variables not connected to the root are frozen as well (they do not belong to the
tree; on a tree formula there are none). -/
def revealInit (Φ : GFormula V) (o : V) (L : ℕ) (η : V → Bool) : Finset V :=
  (Finset.univ.filter fun u => ¬ Conn Φ o u ∨ L ≤ vdepth Φ o u) ∪
    (Finset.univ.filter fun v => Conn Φ o v ∧ vdepth Φ o v = 1 ∧ η v = false).biUnion
      fun v => desc Φ o v

/-- Lines 5–8 for the variable `v` with current revealed set `R`: the union of `V_u` over the
children `u` of every child clause `C` of `v` with at least two children `u` such that
`q_{C,u} = µ_{Φ_u, x_{R ∩ V_u}}(u's literal in C is true) > 0`. -/
def pruneSet (Φ : GFormula V) (o : V) (x : V → Bool) (R : Finset V) (v : V) : Finset V :=
  (childClauses Φ o v).biUnion fun j =>
    let ch := (vbl (Φ.get j)).erase v
    if 2 ≤ (ch.filter fun u =>
        0 < condP (subtreeF Φ o u) (R ∩ desc Φ o u) x (fun σ => Φ.get j u = some (σ u))).card
    then ch.biUnion fun u => desc Φ o u else ∅

/-- Lines 9–10 for `v` with current revealed set `R`: `V_v` when
`q_v = µ_{Φ_v, x_{R ∩ V_v}}(σ_v = 1) ∉ [a_k, 1 − a_k]`, else `∅`. -/
def windowSet (Φ : GFormula V) (o : V) (k : ℕ) (x : V → Bool) (R : Finset V) (v : V) : Finset V :=
  let qv := condP (subtreeF Φ o v) (R ∩ desc Φ o v) x (fun σ => σ v = true)
  if aK k ≤ qv ∧ qv ≤ 1 - aK k then ∅ else desc Φ o v

/-- Lines 4–10 for all variables of depth `d` (their subtrees are disjoint and each step only reads
`R` inside the subtree of the variable processed, so processing them one at a time in any order
gives this union). -/
def levelStep (Φ : GFormula V) (o : V) (k : ℕ) (x : V → Bool) (d : ℕ) (R : Finset V) :
    Finset V :=
  R ∪ (Finset.univ.filter fun v => Conn Φ o v ∧ vdepth Φ o v = d).biUnion fun v =>
    pruneSet Φ o x R v ∪ windowSet Φ o k x (R ∪ pruneSet Φ o x R v) v

/-- The final revealed set `R` of Algorithm 1 for retention coins `η`: the levels are processed in
decreasing order of depth `L, L − 1, …, 0`. -/
def revealed (Φ : GFormula V) (o : V) (k L : ℕ) (x : V → Bool) (η : V → Bool) : Finset V :=
  ((List.range (L + 1)).reverse).foldl (fun R d => levelStep Φ o k x d R) (revealInit Φ o L η)

/-- The probability of the retention coins `η`: independent `Bernoulli(ϑ)` at the depth-1 variables
(`η v = true` retains `V_v`); `η` is `true` (and irrelevant) elsewhere. -/
def coinWeight (Φ : GFormula V) (o : V) (ϑ : ℝ) (η : V → Bool) : ℝ :=
  ∏ v, if Conn Φ o v ∧ vdepth Φ o v = 1 then (if η v then ϑ else 1 - ϑ) else (if η v then 1 else 0)

/-- `Pr(LocalUpdate(x) = y)` for Algorithm 1 with data `(L, Φ rooted at o, ϑ)` and clause width
`k` (which enters through `a_k`): average over the retention coins `η` of `µ_{Φ, x_R}({y})`, the
uniform law on the satisfying assignments of `Φ` that agree with `x` on the revealed set `R`. -/
def luProb (Φ : GFormula V) (o : V) (k L : ℕ) (ϑ : ℝ) (x y : V → Bool) : ℝ :=
  ∑ η : V → Bool, coinWeight Φ o ϑ η *
    (let S := (sols Φ).filter fun σ => ∀ u ∈ revealed Φ o k L x η, σ u = x u
     if y ∈ S then 1 / (S.card : ℝ) else 0)

/-- The normalised flow at `v`: `E[1{y_v ≠ x_v} / max{1, d_H(x, y)}]` for `y ← LocalUpdate(x)`. -/
def luFlow (Φ : GFormula V) (o : V) (k L : ℕ) (ϑ : ℝ) (x : V → Bool) (v : V) : ℝ :=
  ∑ y, luProb Φ o k L ϑ x y * (if y v ≠ x v then 1 / (max 1 (hamming x y) : ℕ) else 0)

/-- `L_x`: the clauses of `Φ` with one or two `x`-true literals (§4.2, p. 25). -/
def Lx (Φ : GFormula V) (x : V → Bool) : GFormula V :=
  Φ.filter fun C => decide ((satSet x C).card = 1 ∨ (satSet x C).card = 2)

/-- The local-update flow `g_v(Φ, x)` (§4.3, p. 29) with parameters `L, ϑ` and clause width `k`:
the flow at `v` of LocalUpdate run on `B_L(L_x, v)` (outside the ball `x` is kept unchanged) when
`v` is `(L, k⁴)`-locally tree-structured in `L_x`, and `0` otherwise. -/
def gFlow (k L : ℕ) (ϑ : ℝ) (Φ : GFormula V) (x : V → Bool) (v : V) : ℝ :=
  if LocallyTree (Lx Φ x) v L (k ^ 4) then luFlow (ballF (Lx Φ x) v L) v k L ϑ x v else 0

end Tree

/-! ## The planted Poisson tree `Tree_pl(λ⁺)` (Definition 2.3), truncated at depth `L` -/

/-- Signed trees of remaining depth `r` with clause width `d + 1`: a leaf is its spin; a node is
its spin and the list of its child clauses, each with its `d + 1` literal signs (sign `0` is the
parent's literal, sign `i + 1` that of child `i`; a literal with sign `s` on `u` is true iff
`x u = s`) and its `d` child subtrees. -/
def TreeD (d : ℕ) : ℕ → Type
  | 0 => Bool
  | r + 1 => Bool × List ((Fin (d + 1) → Bool) × (Fin d → TreeD d r))

/-- The spin of the root of a signed tree. -/
def TreeD.spin (d : ℕ) : (r : ℕ) → TreeD d r → Bool
  | 0, s => s
  | _ + 1, t => t.1

/-- The probability of a signed tree under `Tree_pl` given its root spin, with child-clause rate
`D = (2^k − 1) λ⁺` (`k = d + 1`): `Pois(D)` child clauses per variable, uniform child spins, and
literal signs uniform among the `2^k − 1` patterns satisfied by the spins. -/
def plW (d : ℕ) (D : ℝ) : (r : ℕ) → TreeD d r → ℝ≥0∞
  | 0, _ => 1
  | r + 1, t =>
    ENNReal.ofReal (poisW D t.2.length) *
      (t.2.map fun cl =>
        let spins : Fin (d + 1) → Bool := Fin.cases t.1 fun i => TreeD.spin d r (cl.2 i)
        (1 / 2 : ℝ≥0∞) ^ d *
          (if ∃ i, cl.1 i = spins i then 1 / ((2 : ℝ≥0∞) ^ (d + 1) - 1) else 0) *
          ∏ i, plW d D r (cl.2 i)).prod

/-- Flatten a signed tree into numbered variables (pre-order from `off`; the root gets `off`):
the list of spins and the list of clauses, each a list of `(variable, sign)` literals. -/
def flat (d : ℕ) : (r : ℕ) → TreeD d r → ℕ → List Bool × List (List (ℕ × Bool))
  | 0, s, _ => ([s], [])
  | r + 1, t, off =>
    t.2.foldl
      (fun acc cl =>
        let st := (List.finRange d).foldl
          (fun (st : List Bool × List (List (ℕ × Bool)) × List ℕ) i =>
            let base := off + st.1.length
            let res := flat d r (cl.2 i) base
            (st.1 ++ res.1, st.2.1 ++ res.2, st.2.2 ++ [base]))
          (acc.1, acc.2, [])
        (st.1, st.2.1 ++
          [(off, cl.1 0) :: List.ofFn fun i : Fin d => (st.2.2.getD i.val 0, cl.1 i.succ)]))
      ([t.1], [])

/-- The tree formula on `Fin N` (`N` = number of variables) of a flattened tree. -/
def treeFormula (N : ℕ) (cls : List (List (ℕ × Bool))) : GFormula (Fin N) :=
  cls.map fun lits => fun i => (lits.find? fun p => p.1 = i.val).map Prod.snd

/-- The normalised root flow of LocalUpdate (with parameters `L`, `ϑ`, width `k`) on a sampled
signed tree, its spins being the input solution `x` and its root the variable `0`. -/
def treeRootFlow (k L : ℕ) (ϑ : ℝ) (t : TreeD (k - 1) L) : ℝ :=
  let fl := flat (k - 1) L t 0
  if h : 0 < fl.1.length then
    luFlow (treeFormula fl.1.length fl.2) ⟨0, h⟩ k L ϑ (fun i => fl.1.getD i.val false) ⟨0, h⟩
  else 0

/-- The planted root flow `E[1{y_o ≠ x_o}/max{1, d_H(x, y)}]` of Theorem 4.8(iii) for
`(Φ, x)` sampled to depth `L` from `Tree_pl(λ⁺)` (root spin uniform) and `y ← LocalUpdate(x)`. -/
def plantedFlow (k : ℕ) (lamp : ℝ) (L : ℕ) (ϑ : ℝ) : ℝ≥0∞ :=
  ∑' t : TreeD (k - 1) L,
    (1 / 2 : ℝ≥0∞) * plW (k - 1) (((2 : ℝ) ^ k - 1) * lamp) L t *
      ENNReal.ofReal (treeRootFlow k L ϑ t)

/-- `ε_k = (ln k)^{10}/k` (Theorem 4.8(iii)). -/
def epsK (k : ℕ) : ℝ := Real.log k ^ 10 / k

end KSATSingleFlip.Connect


