-- Prove2me | Definitions.Def_PolySwap_KMS_Cone
-- name    : PolySwap_KMS_Cone
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:39:36.957202+00:00
-- url     : https://prove2.me/theorems/e35c55a8-d978-42f5-ab47-3f265dc3f837
-- title:
--   Paths, (BT) and (TR) moves, 1-cones and their radii, diameter, connectedness and 1-connectedness
-- statement:
--   In a complex $X$ a **path** from $u$ to $v$ is a sequence $(u_0;\dots;u_k)$ of vertices with $u_0=u$, $u_k=v$ and every $u_iu_{i+1}$ an ordered edge; its length is $k$. Paths concatenate, $P_0\circ P_1$, and reverse, $P^{-1}$; a **loop** around $v$ is a path from $v$ to $v$, and $(v)$ is the trivial loop. For loops around a fixed $v_0$:
--   * $P\overset{(BT)}{\sim}P'$ if $P=Q_0\circ(u;v;u)\circ Q_1^{-1}$ and $P'=Q_0\circ(u)\circ Q_1^{-1}$ for paths $Q_0,Q_1$ from $v_0$ to $u$ (backtracking);
--   * $P\overset{(TR)}{\sim}P'$ if $P=Q_0\circ(u;v;w)\circ Q_1^{-1}$ and $P'=Q_0\circ(u;w)\circ Q_1^{-1}$ for a triangle $uvw$ of $X$ and paths $Q_0$ from $v_0$ to $u$, $Q_1$ from $v_0$ to $w$;
--   both taken symmetrically. A **1-cone** is $(v_0,(P_u)_{u\in X(0)},(T_{uv})_{uv})$: an apex $v_0\in X(0)$; $P_{v_0}=(v_0)$ and $P_u$ a path from $v_0$ to $u$; for every ordered edge $uv$ a sequence of loops $T_{uv}=(P_0,\dots,P_m)$ with $P_0=P_u\circ(u;v)\circ P_v^{-1}$, consecutive loops related by $(TR)$ or $(BT)$, and $P_m=(v_0)$. $|T_{uv}|$ counts the indices $i$ with $P_i\overset{(TR)}{\sim}P_{i+1}$, and
--   $$\mathrm{Rad}_0=\sup_{u}\mathrm{length}(P_u),\qquad\mathrm{Rad}_1=\sup_{uv}|T_{uv}|.$$
--   $\mathrm{diam}(X)$ is the diameter of the 1-skeleton. $X$ is **connected** if its 1-skeleton is a connected graph, and **1-connected** if its geometric realization is path-connected and simply connected.
--
--   **Formalization Note.** A path is a nonempty `List V` of vertices of $X$ with consecutive entries forming edges; `pcat P₀ P₁ = P₀ ++ P₁.tail`. Radii, distance and diameter are in `ℕ∞` (`⊤` for no path). `IsOneConnected` is the combinatorial edge-path form of Definition 2.28 given by Remark 2.29: $X$ is connected (with a vertex) and every loop around any vertex $v_0$ is carried to $(v_0)$ by finitely many $(BT)$/$(TR)$ moves; by the edge-path group theorem this is equivalent to the simple connectedness of $|X|$.
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), §2.1 (p. 10, connectedness), §2.6 (pp. 18–19, Definitions 2.25, 2.27, 2.28, Remark 2.29)

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex

open Classical

noncomputable section

namespace PolySwap.KMS

/-!
# Paths, backtracking and triangle moves, 1-cones, radii, diameter, 1-connectedness

Dikstein, Oppenheim, Valentiner-Branth, *Polynomial Swap Coboundary Expansion with Applications
to LTCs and PCPs*, STOC 2027 submission (manuscript sha256 b9cb2095…), §2.1 (p. 10,
connectedness), §2.6 (pp. 18–19, Definitions 2.25, 2.27, 2.28, Remark 2.29).

A path `(u₀; …; u_k)` is the list `[u₀, …, u_k]`; its length is `k`. Concatenation
`P₀ ∘ P₁` of a path ending at `u_k` with a path starting at `u_k` is `P₀ ++ P₁.tail`, and
`P⁻¹` is the reversed list.
-/

namespace WComplex

variable {V : Type*} (X : WComplex V)

/-- Concatenation `P₀ ∘ P₁ = (u₀; …; u_k; …; u_m)` of `P₀ = (u₀; …; u_k)` and
`P₁ = (u_k; …; u_m)`. -/
def pcat (P₀ P₁ : List V) : List V := P₀ ++ P₁.tail

/-- `P` is a path of `X`: a nonempty sequence of vertices of `X` in which consecutive vertices
form ordered edges. -/
def IsPath (P : List V) : Prop :=
  P ≠ [] ∧ (∀ u ∈ P, u ∈ X.vertices) ∧
    P.IsChain (fun u v => u ≠ v ∧ X.IsFace {u, v})

/-- `P` is a path from `u` to `v`. -/
def IsPathFrom (u v : V) (P : List V) : Prop :=
  X.IsPath P ∧ P.head? = some u ∧ P.getLast? = some v

/-- (BT), one direction (Definition 2.25): `P = Q₀ ∘ (u; v; u) ∘ Q₁⁻¹` and `P' = Q₀ ∘ (u) ∘ Q₁⁻¹`
for paths `Q₀, Q₁` from `v₀` to `u` and an edge `uv`. -/
def BTstep (v₀ : V) (P P' : List V) : Prop :=
  ∃ u v Q₀ Q₁, X.IsPathFrom v₀ u Q₀ ∧ X.IsPathFrom v₀ u Q₁ ∧ u ≠ v ∧ X.IsFace {u, v} ∧
    P = pcat (pcat Q₀ [u, v, u]) Q₁.reverse ∧ P' = pcat (pcat Q₀ [u]) Q₁.reverse

/-- (TR), one direction (Definition 2.25): `P = Q₀ ∘ (u; v; w) ∘ Q₁⁻¹` and
`P' = Q₀ ∘ (u; w) ∘ Q₁⁻¹` for a triangle `uvw` of `X` and paths `Q₀` from `v₀` to `u`, `Q₁`
from `v₀` to `w`. -/
def TRstep (v₀ : V) (P P' : List V) : Prop :=
  ∃ u v w Q₀ Q₁, u ≠ v ∧ v ≠ w ∧ u ≠ w ∧ X.IsFace {u, v, w} ∧
    X.IsPathFrom v₀ u Q₀ ∧ X.IsPathFrom v₀ w Q₁ ∧
    P = pcat (pcat Q₀ [u, v, w]) Q₁.reverse ∧ P' = pcat (pcat Q₀ [u, w]) Q₁.reverse

/-- The symmetric relation `P ∼(BT) P'`. -/
def BT (v₀ : V) (P P' : List V) : Prop := X.BTstep v₀ P P' ∨ X.BTstep v₀ P' P

/-- The symmetric relation `P ∼(TR) P'`. -/
def TR (v₀ : V) (P P' : List V) : Prop := X.TRstep v₀ P P' ∨ X.TRstep v₀ P' P

/-- The data of a 1-cone (Definition 2.27): an apex `v₀`, paths `P u` and contractions
`T u v` (sequences of loops around `v₀`). -/
structure OneCone (V : Type*) where
  /-- the apex `v₀` -/
  apex : V
  /-- the path `P_u` from the apex to `u` -/
  P : V → List V
  /-- the contraction `T_{uv} = (P₀, …, P_m)` -/
  T : V → V → List (List V)

/-- `C` is a 1-cone on `X` (Definition 2.27): `v₀ ∈ X(0)`; `P_{v₀}` is the trivial loop and
every other `P_u` is a path from `v₀` to `u`; for every ordered edge `uv`, `T_{uv} = (P₀, …, P_m)`
starts at `P₀ = P_u ∘ (u; v) ∘ P_v⁻¹`, consecutive loops are related by `(TR)` or `(BT)`, and
`P_m` is the trivial loop `(v₀)`. -/
def IsOneCone (C : OneCone V) : Prop :=
  C.apex ∈ X.vertices ∧ C.P C.apex = [C.apex] ∧
    (∀ u ∈ X.vertices, u ≠ C.apex → X.IsPathFrom C.apex u (C.P u)) ∧
    ∀ u v, u ≠ v → X.IsFace {u, v} →
      (C.T u v).head? = some (pcat (pcat (C.P u) [u, v]) (C.P v).reverse) ∧
      (C.T u v).IsChain (fun A B => X.TR C.apex A B ∨ X.BT C.apex A B) ∧
      (C.T u v).getLast? = some [C.apex]

/-- `|T_{uv}|`: the number of indices `i` with `P_i ∼(TR) P_{i+1}`. -/
def trCount (v₀ : V) (T : List (List V)) : ℕ :=
  (T.zip T.tail).countP (fun p => decide (X.TR v₀ p.1 p.2))

/-- `Rad₀(Cone) = sup_{u ∈ X(0)} length(P_u)`. -/
def rad0 (C : OneCone V) : ℕ∞ := ⨆ u ∈ X.vertices, (((C.P u).length - 1 : ℕ) : ℕ∞)

/-- `Rad₁(Cone) = sup_{uv ∈ X⃗(1)} |T_{uv}|`. -/
def rad1 (C : OneCone V) : ℕ∞ :=
  ⨆ u, ⨆ v, ⨆ (_ : u ≠ v ∧ X.IsFace {u, v}), ((X.trCount C.apex (C.T u v) : ℕ) : ℕ∞)

/-- The graph distance in the 1-skeleton (`⊤` if there is no path). -/
def edist (u v : V) : ℕ∞ := ⨅ (P : List V) (_ : X.IsPathFrom u v P), (((P.length - 1 : ℕ)) : ℕ∞)

/-- `diam(X)`: the diameter of the 1-skeleton (`⊤` if it is disconnected). -/
def diam : ℕ∞ := ⨆ u ∈ X.vertices, ⨆ v ∈ X.vertices, X.edist u v

/-- `X` is connected (p. 10): its 1-skeleton is a (nonempty) connected graph. -/
def IsConnected : Prop :=
  X.vertices.Nonempty ∧ ∀ u ∈ X.vertices, ∀ v ∈ X.vertices, ∃ P, X.IsPathFrom u v P

/-- `X` is 1-connected (Definition 2.28), in its combinatorial (edge-path) form (Remark 2.29):
`X` is connected and every loop around a vertex `v₀` is carried to the trivial loop `(v₀)` by a
finite sequence of `(BT)` and `(TR)` moves. -/
def IsOneConnected : Prop :=
  X.IsConnected ∧ ∀ v₀ ∈ X.vertices, ∀ P, X.IsPathFrom v₀ v₀ P →
    Relation.EqvGen (fun A B => X.TR v₀ A B ∨ X.BT v₀ A B) P [v₀]

end WComplex

end PolySwap.KMS


