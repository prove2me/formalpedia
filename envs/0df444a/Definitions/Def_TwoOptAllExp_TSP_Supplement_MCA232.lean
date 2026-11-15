-- Prove2me | Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA232
-- name    : TwoOptAllExp_TSP_Supplement_MCA232
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:44:17.001131+00:00
-- url     : https://prove2.me/theorems/2701ec52-2fb4-43f3-95a3-474784762967
-- title:
--   The $(2,3,2)$-MCA instance $I_n$ of Section 5: graph, layers, phases, strings $R_m,\Omega_m,\bar\Omega_m$ and the dependency graph $D_m$
-- statement:
--   Fix $n\ge1$ and $\lambda_i=2^{13i+4}$. The weighted graph $I_n=(G,w,b)$ has the vertices $v_{0,1},v_{0,8}$ (edge of weight $-7\lambda_0$); for $i\in[n]$ a path $v_{i,1},\dots,v_{i,8}$ with weights $-7\lambda_i,-5\lambda_i,-5\lambda_i,-3\lambda_i,-3\lambda_i,-\lambda_i,-\lambda_i$; vertices $v'_0,v'_1,v'_2$ with edges $v_{n,8}v'_0$ ($-\lambda_n$), $v_{n,1}v'_1$ ($\lambda_{n+1}$), $v'_1v'_2$ ($-2\lambda_{n+1}$) and $b_{v'_0}=-2\lambda_n$; for each $i\in[n]$ the gadget for $v_{i-1,1}$ (Table 8: $f_1v_{i,2},f_2v_{i,4},g_2v_{i,6}$ of weight $-\lambda_i$; $f_3f_1,f_4f_2$ of weight $-\lambda_i/2^2$ and $f_3f_2,f_4f_1$ of weight $+\lambda_i/2^2$; $f_zf_3,f_zf_4$ of weight $-\lambda_i/2^4$; $g_1f_z$ of weight $-\lambda_i/2^6$; $g_3g_1,g_4g_2$ of weight $-\lambda_i/2^8$ and $g_3g_2,g_4g_1$ of weight $+\lambda_i/2^8$; $v_{i-1,1}g_3,v_{i-1,1}g_4$ of weight $-\lambda_i/2^{10}$; biases $b_{f_3}=b_{f_4}=-\lambda_i/2^2$, $b_{f_z}=\lambda_i/2^4$, $b_{g_3}=b_{g_4}=-\lambda_i/2^8$, $b_{v_{i-1,1}}=\lambda_i/2^{10}$) and the gadget for $v_{i-1,8}$ (Table 9: $u_0v_{i-1,8},u_0u_1$ of weight $-\lambda_{i-1}$, $u_0q$ ($+1$), $u_1u_2$ ($-8$), $u_1v_{i,7}$ ($-1$), $u_2u_3$ ($-6$), $u_2v_{i,5}$ ($+1$), $u_3q$ ($-4$), $u_3v_{i,3}$ ($-1$), $qv_{i,8}$ ($-1$)). All other biases are $0$; there are $22n+5$ vertices. The initial assignment $\sigma_0$ is all zero.
--
--   The **layer** $F_0=\{v_{0,1},v_{0,8}\}$, and $F_i$ ($i\ge1$) consists of $v_{i,1},\dots,v_{i,8}$ and the fourteen gadget vertices indexed by $i$. The **phase** assignment $\tau_0$ is $1$ on $F_0$; $\tau_i$ is $1$ exactly on $v_{i,1},\dots,v_{i,8},f_{i,1},f_{i,2},g_{i,2},g_{i,4},u_{i,0},\dots,u_{i,3},q_i$. Layers $F_0,\dots,F_m$ are in phase $0$ if all their variables are $0$, in phase $1$ if each $F_i$ is assigned by $\tau_i$.
--
--   **Strings.** $R_0=(v_{0,1},v_{0,8})$, $R_m=(v_{m,1},v_{m,2},R_{m-1},v_{m,3},v_{m,4},R_{m-1},v_{m,5},v_{m,6},R_{m-1},v_{m,7},v_{m,8})$. With the blocks $\rho_i^{(1)},\dots,\rho_i^{(5)},\rho_i^{(0)}$ and $\alpha_i=(u_{i,0},u_{i,1},u_{i,2},u_{i,3},q_i)$ of pp. 30–31, $\Omega_m$ is obtained from $R_m$ by inserting $\rho_i^{(c\bmod 6)}$ before the $c$-th occurrence of $v_{i-1,1}$ and $\alpha_i$ after every occurrence of $v_{i-1,8}$ ($i\in[m]$); $\bar\Omega_m$ uses $\rho_i^{((c+3)\bmod6)}$. $T_m=|\Omega_m|$ and $\Xi_m^0=\Omega_m$, $\Xi_m^1=\bar\Omega_m$.
--
--   **Dependency graph.** $D_0$ has the edge $(1,2)$ on $\{1,2\}$. For $m\ge1$, $t=T_{m-1}$ and $\Omega_m=(\omega_1,\dots,\omega_{T_m})$, $D_m$ on $\{1,\dots,T_m\}$ has the edges $(s-1,s)$ with $\omega_{s-1}\in F_m\setminus\{q_m\}$, three copies of $D_{m-1}$ shifted by $7$, $t+19$, $2t+28$, the edges $(t+7,t+8)$, $(2t+19,2t+20)$, $(3t+28,3t+29)$, and $(t+11,t+13)$, $(t+12,2t+20)$, $(2t+22,2t+25)$, $(2t+24,3t+29)$, $(3t+30,3t+34)$, $(T_m-2,T_m)$. A **linear extension** is an ordering of all positions $1,\dots,T_m$ placing the source of every edge before its target; labeling it with a string $(\omega_1,\dots,\omega_T)$ gives $(\omega_{s_1},\dots,\omega_{s_T})$. A **maximal improving flip sequence restricted** to a vertex set $L$ flips only vertices of $L$, improvingly, until no vertex of $L$ is improving.
--
--   **Formalization Note** Vertices are named by an inductive type and the vertex set is an explicit finite set; $G$ is the graph of the listed edges, and the quotients $\lambda_i/2^k$ are exact. `val σ x` reads the value of a named vertex; `Fol`/`FolOn` assert that the named vertex exists in $I_n$ and follows. Strings, phases and $D_m$ are defined structurally, with no improvement predicate.
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, §5.3, pp. 26–28, Tables 8–9; Remark 18, p. 28; §5.4, pp. 30–32 (ρ, α, Ω, Ω̄, τ_i, phases, D_n), Ξ, p. 32

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_GraphObjective

namespace TwoOptAllExp.TSP.Supplement.MCA232

/-! # The (2,3,2)-MCA instance `I_n` of Section 5

Heimann, Hoang and Hougardy, November 2, 2026 preprint (STOC 2027 submission #112), §5.3,
pp. 26–28 (Tables 8–9, Figures 8–10), and the canonical flip sequence, phases and dependency
graph of §5.4, pp. 30–32. The instance is defined for `n ≥ 1`; the strings `R_m`, `Ω_m`, `Ω̄_m`
and the graphs `D_m` are defined for every `m ≥ 0`. -/

/-- Names of the vertices of the constructions (an index `i` is the layer). -/
inductive Vx
  /-- The path vertex `v_{i,j}`. -/
  | v (i j : ℕ)
  /-- The boundary vertex `v′_k`, `k ∈ {0, 1, 2}`. -/
  | vp (k : ℕ)
  /-- `f_{i,1}` of the gadget for `v_{i-1,1}` (Table 8). -/
  | f1 (i : ℕ)
  /-- `f_{i,2}`. -/
  | f2 (i : ℕ)
  /-- `f_{i,3}`. -/
  | f3 (i : ℕ)
  /-- `f_{i,4}`. -/
  | f4 (i : ℕ)
  /-- `f_{i,z}`. -/
  | fz (i : ℕ)
  /-- `g_{i,1}`. -/
  | g1 (i : ℕ)
  /-- `g_{i,2}`. -/
  | g2 (i : ℕ)
  /-- `g_{i,3}`. -/
  | g3 (i : ℕ)
  /-- `g_{i,4}`. -/
  | g4 (i : ℕ)
  /-- `u_{i,0}` of the gadget for `v_{i-1,8}` (Table 9). -/
  | u0 (i : ℕ)
  /-- `u_{i,1}`. -/
  | u1 (i : ℕ)
  /-- `u_{i,2}`. -/
  | u2 (i : ℕ)
  /-- `u_{i,3}`. -/
  | u3 (i : ℕ)
  /-- `q_i`. -/
  | q (i : ℕ)
  deriving DecidableEq

open Vx

/-- The fourteen auxiliary vertices indexed by `i` (the gadgets for `v_{i-1,1}` and `v_{i-1,8}`). -/
def auxVerts (i : ℕ) : Finset Vx :=
  {f1 i, f2 i, f3 i, f4 i, fz i, g1 i, g2 i, g3 i, g4 i, u0 i, u1 i, u2 i, u3 i, q i}

/-- The layer `F_i` (p. 28): `F_0 = {v_{0,1}, v_{0,8}}`; for `i ≥ 1`, the eight path vertices
`v_{i,1}, …, v_{i,8}` and the fourteen auxiliary vertices indexed by `i`. -/
def layer (i : ℕ) : Finset Vx :=
  if i = 0 then {v 0 1, v 0 8} else (Finset.Icc 1 8).image (v i) ∪ auxVerts i

/-- The vertex set of `I_n` (p. 26): the layers `F_0, …, F_n` and `v′_0, v′_1, v′_2`
(`22n + 5` vertices). -/
def vertFinset (n : ℕ) : Finset Vx :=
  (Finset.range (n + 1)).biUnion layer ∪ {vp 0, vp 1, vp 2}

/-- The vertices of `I_n`. -/
abbrev V (n : ℕ) : Type := ↥(vertFinset n)

/-- The scale `λ_i = 2^{13 i + 4}` (p. 26). -/
def lam (i : ℕ) : ℤ := 2 ^ (13 * i + 4)

/-- The weighted edges of `I_n` (pp. 26–27, Tables 8–9), each listed once; the quotients
`λ_i / 2^k` (`k ≤ 10`, `i ≥ 1`) are exact. -/
def edgeList (n : ℕ) : List (Vx × Vx × ℤ) :=
  [(v 0 1, v 0 8, -7 * lam 0)] ++
  (List.range' 1 n).flatMap (fun i =>
    [(v i 1, v i 2, -7 * lam i), (v i 2, v i 3, -5 * lam i), (v i 3, v i 4, -5 * lam i),
     (v i 4, v i 5, -3 * lam i), (v i 5, v i 6, -3 * lam i), (v i 6, v i 7, -lam i),
     (v i 7, v i 8, -lam i)]) ++
  [(v n 8, vp 0, -lam n), (v n 1, vp 1, lam (n + 1)), (vp 1, vp 2, -2 * lam (n + 1))] ++
  (List.range' 1 n).flatMap (fun i =>
    [(f1 i, v i 2, -lam i), (f2 i, v i 4, -lam i), (g2 i, v i 6, -lam i),
     (f3 i, f1 i, -(lam i / 2 ^ 2)), (f3 i, f2 i, lam i / 2 ^ 2),
     (f4 i, f1 i, lam i / 2 ^ 2), (f4 i, f2 i, -(lam i / 2 ^ 2)),
     (fz i, f3 i, -(lam i / 2 ^ 4)), (fz i, f4 i, -(lam i / 2 ^ 4)),
     (g1 i, fz i, -(lam i / 2 ^ 6)),
     (g3 i, g1 i, -(lam i / 2 ^ 8)), (g3 i, g2 i, lam i / 2 ^ 8),
     (g4 i, g1 i, lam i / 2 ^ 8), (g4 i, g2 i, -(lam i / 2 ^ 8)),
     (v (i - 1) 1, g3 i, -(lam i / 2 ^ 10)), (v (i - 1) 1, g4 i, -(lam i / 2 ^ 10)),
     (u0 i, v (i - 1) 8, -lam (i - 1)), (u0 i, u1 i, -lam (i - 1)), (u0 i, q i, 1),
     (u1 i, u2 i, -8), (u1 i, v i 7, -1),
     (u2 i, u3 i, -6), (u2 i, v i 5, 1),
     (u3 i, q i, -4), (u3 i, v i 3, -1),
     (q i, v i 8, -1)])

/-- The weight of the listed edge from `x` to `y` (in this orientation), or `0`. -/
def look (n : ℕ) (x y : Vx) : ℤ :=
  ((edgeList n).filter (fun e => e.1 = x ∧ e.2.1 = y)).foldr (fun e acc => e.2.2 + acc) 0

/-- `x` and `y` are joined by a listed edge (in either orientation). -/
def joined (n : ℕ) (x y : Vx) : Prop :=
  ∃ e ∈ edgeList n, (e.1 = x ∧ e.2.1 = y) ∨ (e.1 = y ∧ e.2.1 = x)

instance (n : ℕ) : DecidableRel (joined n) := fun x y => by
  unfold joined; infer_instance

/-- The vertex weights `b` of `I_n` (pp. 26–27): `b_{v′_0} = -2λ_n`, and for `i ∈ [n]`
`b_{f_{i,3}} = b_{f_{i,4}} = -λ_i/2^2`, `b_{f_{i,z}} = λ_i/2^4`, `b_{g_{i,3}} = b_{g_{i,4}} = -λ_i/2^8`,
`b_{v_{i-1,1}} = λ_i/2^{10}`; all other vertex weights are `0`. -/
def bias (n : ℕ) : Vx → ℤ
  | vp 0 => -2 * lam n
  | f3 i => if 1 ≤ i ∧ i ≤ n then -(lam i / 2 ^ 2) else 0
  | f4 i => if 1 ≤ i ∧ i ≤ n then -(lam i / 2 ^ 2) else 0
  | fz i => if 1 ≤ i ∧ i ≤ n then lam i / 2 ^ 4 else 0
  | g3 i => if 1 ≤ i ∧ i ≤ n then -(lam i / 2 ^ 8) else 0
  | g4 i => if 1 ≤ i ∧ i ≤ n then -(lam i / 2 ^ 8) else 0
  | v i j => if j = 1 ∧ i < n then lam (i + 1) / 2 ^ 10 else 0
  | _ => 0

/-- The weighted graph `I_n = (G, w, b)` of §5.3 (pp. 26–28). -/
def inst (n : ℕ) : WGraph (V n) where
  G := SimpleGraph.fromRel (fun x y : V n => joined n x.1 y.1)
  decAdj := fun x y => by
    simp only [SimpleGraph.fromRel_adj]; infer_instance
  w := Sym2.lift ⟨fun x y => look n x.1 y.1 + look n y.1 x.1, fun _ _ => add_comm _ _⟩
  b := fun x => bias n x.1

/-- The value of the vertex `x` under an assignment of `I_n` (`false` if `x` is not a vertex). -/
def val {n : ℕ} (σ : V n → Bool) (x : Vx) : Bool :=
  if h : x ∈ vertFinset n then σ ⟨x, h⟩ else false

/-- Flipping the vertex `x` (no change if `x` is not a vertex of `I_n`). -/
def flipX {n : ℕ} (σ : V n → Bool) (x : Vx) : V n → Bool :=
  if h : x ∈ vertFinset n then flip σ ⟨x, h⟩ else σ

/-- `x` is a vertex of `I_n` and `x ← φ on S` in `I_n`. -/
def FolOn (n : ℕ) (x : Vx) (φ : (V n → Bool) → Bool) (S : Set (V n → Bool)) : Prop :=
  ∃ h : x ∈ vertFinset n, (inst n).FollowsOn ⟨x, h⟩ φ S

/-- `x` is a vertex of `I_n` and `x ← φ` in `I_n`. -/
def Fol (n : ℕ) (x : Vx) (φ : (V n → Bool) → Bool) : Prop :=
  FolOn n x φ Set.univ

/-- The vertex `x` of `I_n` is improving at `σ`. -/
def Improving {n : ℕ} (σ : V n → Bool) (x : V n) : Prop :=
  IsImprovingVar (inst n).Φ σ x

/-- The all-zero initial assignment `σ₀` (p. 28). -/
def σ₀ (n : ℕ) : V n → Bool := fun _ => false

/-! ## Strings -/

/-- The path string `R_m` (Remark 18, p. 28): `R_0 = (v_{0,1}, v_{0,8})`,
`R_m = (v_{m,1}, v_{m,2}, R_{m-1}, v_{m,3}, v_{m,4}, R_{m-1}, v_{m,5}, v_{m,6}, R_{m-1}, v_{m,7}, v_{m,8})`. -/
def R : ℕ → List Vx
  | 0 => [v 0 1, v 0 8]
  | m + 1 => [v (m + 1) 1, v (m + 1) 2] ++ R m ++ [v (m + 1) 3, v (m + 1) 4] ++ R m ++
      [v (m + 1) 5, v (m + 1) 6] ++ R m ++ [v (m + 1) 7, v (m + 1) 8]

/-- The strings `ρ_i^{(k)}`, `k ∈ {0, …, 5}` (pp. 30–31); `k` is read modulo `6`. -/
def rho (i k : ℕ) : List Vx :=
  match k % 6 with
  | 1 => [f1 i, f3 i, fz i, g1 i, g3 i]
  | 2 => [f2 i, f3 i, fz i, g1 i, g3 i]
  | 3 => [g2 i, g4 i]
  | 4 => [f1 i, f4 i, fz i, g1 i, g4 i]
  | 5 => [f2 i, f4 i, fz i, g1 i, g4 i]
  | _ => [g2 i, g4 i]

/-- `α_i = (u_{i,0}, u_{i,1}, u_{i,2}, u_{i,3}, q_i)` (p. 31). -/
def alpha (i : ℕ) : List Vx := [u0 i, u1 i, u2 i, u3 i, q i]

/-- The insertion rule of p. 31 applied at position `k` (0-based) of `R_m`, holding the entry `x`:
before the `c`-th occurrence (`c` counted from `1`) of `v_{i-1,1}`, `i ∈ [m]`, insert
`ρ_i^{((c + s) mod 6)}`; after every occurrence of `v_{i-1,8}`, `i ∈ [m]`, insert `α_i`. -/
def expandAt (m s : ℕ) (k : ℕ) (x : Vx) : List Vx :=
  match x with
  | v j 1 => if j < m then rho (j + 1) (((R m).take (k + 1)).count x + s) ++ [x] else [x]
  | v j 8 => if j < m then x :: alpha (j + 1) else [x]
  | _ => [x]

/-- The string obtained from `R_m` by the insertion rule with offset `s`. -/
def insertBlocks (m s : ℕ) : List Vx :=
  (List.range (R m).length).flatMap (fun k => expandAt m s k ((R m).getD k (vp 0)))

/-- The canonical flip string `Ω_m` (p. 31). -/
def Omega (m : ℕ) : List Vx := insertBlocks m 0

/-- The string `Ω̄_m` (p. 31): as `Ω_m`, with `ρ_i^{((c+3) mod 6)}` inserted before the `c`-th
occurrence of `v_{i-1,1}`. -/
def OmegaBar (m : ℕ) : List Vx := insertBlocks m 3

/-- `T_m = |Ω_m|` (p. 31). -/
def T (m : ℕ) : ℕ := (Omega m).length

/-- `Ξ_m^ε` (p. 32): `Ω_m` for `ε = 0` and `Ω̄_m` for `ε = 1`. -/
def Xi (ε : Bool) (m : ℕ) : List Vx := if ε then OmegaBar m else Omega m

/-! ## Phases -/

/-- The value of the vertex `x` of the layer `F_i` under `τ_i` (p. 31): `τ_0` is `1` on both
vertices of `F_0`; for `i ≥ 1`, `τ_i` is `1` exactly on `v_{i,1}, …, v_{i,8}`, `f_{i,1}`, `f_{i,2}`,
`g_{i,2}`, `g_{i,4}`, `u_{i,0}, …, u_{i,3}`, `q_i`. -/
def tau : Vx → Bool
  | v _ _ => true
  | f1 _ | f2 _ | g2 _ | g4 _ | u0 _ | u1 _ | u2 _ | u3 _ | q _ => true
  | _ => false

/-- The layers `F_0, …, F_m` of `I_n` are in phase `ε` under `σ` (p. 31): phase `0` means all
their variables are `0`; phase `1` means every `F_i` is assigned according to `τ_i`. -/
def InPhase {n : ℕ} (σ : V n → Bool) (m : ℕ) (ε : Bool) : Prop :=
  ∀ i ≤ m, ∀ x ∈ layer i, val σ x = (ε && tau x)

/-- The vertices of the layers `F_0 ∪ ⋯ ∪ F_m`. -/
def lowLayers (m : ℕ) : Finset Vx := (Finset.range (m + 1)).biUnion layer

/-! ## The dependency graph `D_m` and its linear extensions -/

/-- The edges of `D_m` (pp. 31–32) on the positions `1, …, T_m`, recursively: `D_0` has the edge
`(1, 2)`; for `m ≥ 1`, with `t = T_{m-1}` and `Ω_m = (ω_1, …, ω_{T_m})`, the edges `(s-1, s)` for
`2 ≤ s ≤ T_m` with `ω_{s-1} ∈ F_m ∖ {q_m}`; the copies of `D_{m-1}` shifted by `7`, `t + 19`,
`2t + 28`; the edges `(t+7, t+8)`, `(2t+19, 2t+20)`, `(3t+28, 3t+29)`; and the edges
`(t+11, t+13)`, `(t+12, 2t+20)`, `(2t+22, 2t+25)`, `(2t+24, 3t+29)`, `(3t+30, 3t+34)`,
`(T_m - 2, T_m)`. -/
def Dedges : ℕ → List (ℕ × ℕ)
  | 0 => [(1, 2)]
  | m + 1 =>
    let t := T m
    let Tm := T (m + 1)
    let ω := Omega (m + 1)
    ((List.range' 2 (Tm - 1)).filter (fun s =>
        decide (ω.getD (s - 2) (vp 0) ∈ layer (m + 1) ∧ ω.getD (s - 2) (vp 0) ≠ q (m + 1)))).map
        (fun s => (s - 1, s)) ++
    ([7, t + 19, 2 * t + 28].flatMap (fun j => (Dedges m).map (fun e => (e.1 + j, e.2 + j)))) ++
    [(t + 7, t + 8), (2 * t + 19, 2 * t + 20), (3 * t + 28, 3 * t + 29)] ++
    [(t + 11, t + 13), (t + 12, 2 * t + 20), (2 * t + 22, 2 * t + 25), (2 * t + 24, 3 * t + 29),
     (3 * t + 30, 3 * t + 34), (Tm - 2, Tm)]

/-- The edge relation of `D_m`. -/
def DAdj (m : ℕ) (r s : ℕ) : Prop := (r, s) ∈ Dedges m

/-- A linear extension of `D_m` (§2, p. 6): an ordering `(s_1, …, s_{T_m})` of all positions
`1, …, T_m` such that every edge `(r, s)` of `D_m` has `r` placed before `s`. -/
def IsLinExt (m : ℕ) (s : List ℕ) : Prop :=
  s.Perm (List.range' 1 (T m)) ∧ ∀ e ∈ Dedges m, s.idxOf e.1 < s.idxOf e.2

/-- Labeling a sequence of positions `(s_1, …, s_ℓ)` with the entries of a string
`(ω_1, …, ω_T)`: `(ω_{s_1}, …, ω_{s_ℓ})`. -/
def label (str : List Vx) (s : List ℕ) : List Vx :=
  s.map (fun k => str.getD (k - 1) (vp 0))

/-- A maximal improving flip sequence restricted to a vertex set `L` of `I_n`, from `σ`: it flips
only vertices of `L` (all other vertices keep their values), every flip is improving, and at the
end no vertex of `L` is improving. -/
def IsMaxRestricted {n : ℕ} (L : Finset Vx) (σ : V n → Bool) (ys : List (V n)) : Prop :=
  (∀ y ∈ ys, y.1 ∈ L) ∧ IsImprovingFlipSeq (inst n).Φ σ ys ∧
    ∀ x : V n, x.1 ∈ L → ¬ Improving (applyFlips σ ys) x

end TwoOptAllExp.TSP.Supplement.MCA232


