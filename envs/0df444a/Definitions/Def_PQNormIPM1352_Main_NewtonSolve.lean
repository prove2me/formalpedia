-- Prove2me | Definitions.Def_PQNormIPM1352_Main_NewtonSolve
-- name    : PQNormIPM1352_Main_NewtonSolve
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:20.171771+00:00
-- url     : https://prove2.me/theorems/e79a4808-88e4-4df0-a9b4-148ab8423766
-- title:
--   Algorithms 2–4: MSolve, SchurSolve and NewtonSolve as programs of the cost model
-- statement:
--   These are the subroutines that compute an approximate Newton step for the barrier (6) at a point $x = (z, y, \gamma) \in \mathrm{int}(K)$, written as programs of the cost model.
--
--   1. **Algorithm 2 (MSolve).** Given a built solver `solveL` and $D = \mathrm{Diag}(d)$: $\tilde u = \texttt{solveL}(Db)$, return $D\tilde u$.
--   2. **Algorithm 3 (SchurSolve).** Given the entry list of $L$, $D$, $V = (v_1, v_2)$, $\delta$ and $b$: build $\texttt{solveL} = \mathrm{STSolve}(L,\delta)$; $\tilde x_1 = \mathrm{MSolve}(b)$, $\tilde u_1 = \mathrm{MSolve}(v_1)$, $\tilde u_2 = \mathrm{MSolve}(v_2)$, $\tilde U = (\tilde u_1, \tilde u_2)$; $\tilde x_2 = V^\top \tilde x_1$; solve the $2\times2$ system $(I + V^\top\tilde U)\tilde x_3 = \tilde x_2$ (Cramer's rule); return $\tilde x_1 - \tilde U\tilde x_3$.
--   3. **Algorithm 4 (NewtonSolve)** with exponents $p \ge q > 1$, barrier parameter $\eta$ and accuracy $\delta$:
--      - $p^* = p/(p-1)$, $q^* = q/(q-1)$; $Z = \sum_i z(i)$, $Y = \sum_j y(j)$;
--      - for each entry $(i,j)$: $r = \gamma(i,j)^2/(z(i)^{2/q^*}y(j)^{2/p})$, $r_1 = \frac{4r}{pq^*(1-r^2)}$, $r_2 = \frac{2}{1+r}\big(1 + \frac{2r}{1-r}(\frac1q - \frac1p)\big)$;
--      - the gradient $(g_z, g_y, g_\gamma) = \nabla F(x) - \eta\bar a$ by (15)–(17) and the Hessian blocks $H_{w\gamma}$, $H_\gamma$ (diagonal) by (23)–(25);
--      - $D = \mathrm{Diag}(z,y)$, $V = (\mathbf 1_m/(1-Z), 0;\ 0, \mathbf 1_n/(1-Y))$ and $L = \sum_{(i,j)\in S} L^{(i,j)}$ with $L^{(i,j)} = r_1\begin{pmatrix}1&-1\\-1&1\end{pmatrix} + \mathrm{Diag}\big(\frac1{q^*}r_2 + \frac1q,\ \frac1p r_2 + \frac1{p^*}\big)$ on the coordinates $(z(i), y(j))$;
--      - $\tilde g_w = g_w - H_{w\gamma}H_\gamma^{-1}g_\gamma$; $\tilde\Delta_w = \mathrm{SchurSolve}(L, D, V, \delta, -\tilde g_w)$;
--      - $\tilde g_\gamma = g_\gamma + H_{w\gamma}^\top\tilde\Delta_w$; $\tilde\Delta_\gamma = -H_\gamma^{-1}\tilde g_\gamma$; return $(\tilde\Delta_w, \tilde\Delta_\gamma)$.
--
--   Lemma 11 states that the output is a $\delta$-approximate Newton step computed in time $\tilde O(s\log(1/\delta))$.
--
--   **Formalization Note** The formulas (15)–(17) and (23)–(25) are written as the arithmetic the program performs: for example $z(i)^{2/q^*-1}y(j)^{2/p}$ is computed as $Q/z(i)$ with $Q = z(i)^{2/q^*}y(j)^{2/p}$, equal for $z(i) > 0$. The entry list of $L$ has $m + n + 2s$ entries ($m+n$ diagonal, $2s$ off-diagonal). Vectors are arrays indexed from $0$, with $z$ at $0,\dots,m-1$, $y$ at $m,\dots,m+n-1$ and $\gamma$ at $m+n,\dots$. The formulas for $L$ agree with $D(H\setminus\gamma - VV^\top)D$ (checked numerically on a random instance).
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), §5.1, Algorithms 2–4, pp. 16–17; Appendix B, eqs. (15)–(17), (23)–(25), pp. 25–26

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_Prog

/-!
# Algorithms 2–4: `MSolve`, `SchurSolve`, `NewtonSolve`

Pirazzini–Spielman, STOC 2027 submission #1352, §5.1, pp. 16–17, with the gradient (15)–(17) and
Hessian entries (23)–(25) of Appendix B, pp. 25–26.

All three are programs of the cost model (`Prog R`), written for an abstract real carrier `R`.
Vectors are arrays `ℕ → R`. The preprocessed instance is given by `m, n, s`, the label arrays
`row, col : ℕ → ℕ` (entry `k < s` sits at `(row k, col k)`, 0-based) and the values `a : ℕ → R`.
A point `x = (z, y, γ)` is the array with `z(i) = x i`, `y(j) = x (m + j)`, `γ(k) = x (m + n + k)`.
-/

namespace PQNormIPM1352.Main

open Prog

variable {R : Type}

local notation "v" => Ex.var

/-- `Function.update` on arrays. -/
def upd (f : ℕ → R) (i : ℕ) (t : R) : ℕ → R := Function.update f i t

/-- Algorithm 2 (`MSolve`, p. 16) on vectors of length `N`: `ũ = solveL(D b)`, return `D ũ`, where
`h` is the handle of `solveL` and `D = Diag(d)`. -/
def mSolve (N : ℕ) (zero : R) (h : ℕ) (d b : ℕ → R) : Prog R (ℕ → R) :=
  Prog.bind (forLoop N ([] : List R) fun i acc =>
      Prog.bind (v (d i) * v (b i)).eval fun t => ret (acc ++ [t])) fun db =>
  Prog.bind (solverApply h db) fun u =>
  forLoop N (fun _ => zero) fun i f =>
    Prog.bind (v (d i) * v (u.getD i zero)).eval fun t => ret (upd f i t)

/-- The inner product `∑_{i<N} u(i) w(i)`. -/
def dotN (N : ℕ) (zero : R) (u w : ℕ → R) : Prog R R :=
  forLoop N zero fun i acc => (v acc + v (u i) * v (w i)).eval

/-- Algorithm 3 (`SchurSolve`, p. 16): approximately solve `(D⁻¹ L D⁻¹ + V Vᵀ) x = b` for
`V = (v₁, v₂)`, with `L` given by its entry list:
1. `solveL = STSolve(L, δ)`;
2. `x̃₁ = MSolve(solveL, D, b)`;
3. `ũ₁ = MSolve(solveL, D, v₁)`, `ũ₂ = MSolve(solveL, D, v₂)`, `Ũ = (ũ₁, ũ₂)`;
4. `x̃₂ = Vᵀ x̃₁`;
5. solve the `2 × 2` system `(I + Vᵀ Ũ) x̃₃ = x̃₂` (Cramer's rule);
6. return `x̃₁ − Ũ x̃₃`. -/
def schurSolve (N : ℕ) (zero : R) (L : List (ℕ × ℕ × R)) (d v₁ v₂ : ℕ → R) (δ : R)
    (b : ℕ → R) : Prog R (ℕ → R) :=
  Prog.bind (solverBuild N L δ) fun h =>
  Prog.bind (mSolve N zero h d b) fun x₁ =>
  Prog.bind (mSolve N zero h d v₁) fun u₁ =>
  Prog.bind (mSolve N zero h d v₂) fun u₂ =>
  Prog.bind (dotN N zero v₁ x₁) fun x₂a =>
  Prog.bind (dotN N zero v₂ x₁) fun x₂b =>
  Prog.bind (dotN N zero v₁ u₁) fun s₁₁ =>
  Prog.bind (dotN N zero v₁ u₂) fun s₁₂ =>
  Prog.bind (dotN N zero v₂ u₁) fun s₂₁ =>
  Prog.bind (dotN N zero v₂ u₂) fun s₂₂ =>
  Prog.bind ((1 + v s₁₁) * (1 + v s₂₂) - v s₁₂ * v s₂₁).eval fun det =>
  Prog.bind (((1 + v s₂₂) * v x₂a - v s₁₂ * v x₂b) / v det).eval fun x₃a =>
  Prog.bind (((1 + v s₁₁) * v x₂b - v s₂₁ * v x₂a) / v det).eval fun x₃b =>
  forLoop N (fun _ => zero) fun i f =>
    Prog.bind (v (x₁ i) - v (u₁ i) * v x₃a - v (u₂ i) * v x₃b).eval fun t => ret (upd f i t)

/-- The per-entry data accumulated in Steps 3–6 of Algorithm 4. -/
structure EdgeAcc (R : Type) where
  /-- gradient `g_z` (without the `1/(1 − Z)` term) -/
  gz : ℕ → R
  /-- gradient `g_y` (without the `1/(1 − Y)` term) -/
  gy : ℕ → R
  /-- diagonal of `L`, z-block -/
  lz : ℕ → R
  /-- diagonal of `L`, y-block -/
  ly : ℕ → R
  /-- `r₁(i,j)` per entry -/
  r1 : ℕ → R
  /-- `g_γ` per entry -/
  gg : ℕ → R
  /-- `H_γ` (diagonal) per entry, (23) -/
  hg : ℕ → R
  /-- `H_{zγ}` per entry, (24) -/
  hzg : ℕ → R
  /-- `H_{yγ}` per entry, (25) -/
  hyg : ℕ → R

/-- Algorithm 4 (`NewtonSolve`, p. 17) at the point `x = (z, y, γ) ∈ int(K)` with barrier
parameter `η`, accuracy `δ`, exponents `p ≥ q > 1`:
1. `p* = p/(p−1)`, `q* = q/(q−1)`; 2. `Z = ∑ z(i)`, `Y = ∑ y(j)`;
3. `r(i,j) = γ(i,j)² / (z(i)^{2/q*} y(j)^{2/p})`, `r₁ = 4r / (p q* (1 − r²))`,
   `r₂ = (2/(1+r)) (1 + (2r/(1−r)) (1/q − 1/p))`;
4. the gradient `(g_z, g_y, g_γ) = ∇F(x) − η ā` by (15)–(17);
5. `H_{wγ}` and `H_γ` by (23)–(25);
6. `D = Diag(z, y)`, `V = (1_m/(1−Z), 0; 0, 1_n/(1−Y))`, `L = ∑_S L^{(i,j)}` with
   `L^{(i,j)} = r₁ (1, −1; −1, 1) + Diag((1/q*) r₂ + 1/q, (1/p) r₂ + 1/p*)` (zero-padded);
7. `g̃_w = g_w − H_{wγ} H_γ⁻¹ g_γ`; 8. `Δ̃_w = SchurSolve(L, D, V, δ, −g̃_w)`;
9. `g̃_γ = g_γ + H_{wγ}ᵀ Δ̃_w`; 10. `Δ̃_γ = −H_γ⁻¹ g̃_γ`; 11. return `Δ̃ = (Δ̃_w, Δ̃_γ)`. -/
def newtonSolve (m n s : ℕ) (row col : ℕ → ℕ) (a : ℕ → R) (p q δ η : R) (x : ℕ → R) :
    Prog R (ℕ → R) :=
  Prog.bind (cst 0) fun zero =>
  -- Step 1
  Prog.bind (v p / (v p - 1)).eval fun ps =>
  Prog.bind (v q / (v q - 1)).eval fun qs =>
  -- Step 2
  Prog.bind (forLoop m zero fun i acc => (v acc + v (x i)).eval) fun Z =>
  Prog.bind (forLoop n zero fun j acc => (v acc + v (x (m + j))).eval) fun Y =>
  -- Steps 3–6, one pass over the entries
  let init : EdgeAcc R := ⟨fun _ => zero, fun _ => zero, fun _ => zero, fun _ => zero,
    fun _ => zero, fun _ => zero, fun _ => zero, fun _ => zero, fun _ => zero⟩
  Prog.bind (forLoop s init fun k st =>
    let i := row k
    let j := col k
    let z := x i
    let y := x (m + j)
    let g := x (m + n + k)
    Prog.bind (v z ^ (2 / v qs) * v y ^ (2 / v p)).eval fun Q =>
    Prog.bind (v Q - v g * v g).eval fun den =>
    Prog.bind (v g * v g / v Q).eval fun r =>
    Prog.bind (4 * v r / (v p * v qs * (1 - v r * v r))).eval fun r1 =>
    Prog.bind ((2 / (1 + v r)) * (1 + (2 * v r / (1 - v r)) * (1 / v q - 1 / v p))).eval fun r2 =>
    Prog.bind (v (st.gz i) - (2 / v qs) * (v Q / v z) / v den - 1 / (v q * v z)).eval fun gz =>
    Prog.bind (v (st.gy j) - (2 / v p) * (v Q / v y) / v den - 1 / (v ps * v y)).eval fun gy =>
    Prog.bind (2 * v g / v den - v η * v (a k)).eval fun gg =>
    Prog.bind (2 * (v Q + v g * v g) / (v den * v den)).eval fun hg =>
    Prog.bind (0 - (4 / v qs) * v Q * v g / (v z * (v den * v den))).eval fun hzg =>
    Prog.bind (0 - (4 / v p) * v Q * v g / (v y * (v den * v den))).eval fun hyg =>
    Prog.bind (v (st.lz i) + v r1 + (1 / v qs) * v r2 + 1 / v q).eval fun lz =>
    Prog.bind (v (st.ly j) + v r1 + (1 / v p) * v r2 + 1 / v ps).eval fun ly =>
    ret { gz := upd st.gz i gz, gy := upd st.gy j gy, lz := upd st.lz i lz,
          ly := upd st.ly j ly, r1 := upd st.r1 k r1, gg := upd st.gg k gg,
          hg := upd st.hg k hg, hzg := upd st.hzg k hzg, hyg := upd st.hyg k hyg }) fun E =>
  -- Step 4, the terms `1/(1 − Z)` and `1/(1 − Y)` of (15), (16)
  Prog.bind (forLoop m E.gz fun i f =>
    Prog.bind (v (f i) + 1 / (1 - v Z)).eval fun t => ret (upd f i t)) fun gz =>
  Prog.bind (forLoop n E.gy fun j f =>
    Prog.bind (v (f j) + 1 / (1 - v Y)).eval fun t => ret (upd f j t)) fun gy =>
  -- Step 6, `V`, `D` and the entry list of `L` (indices: z-block `i`, y-block `m + j`)
  Prog.bind ((1 : Ex R) / (1 - v Z)).eval fun cZ =>
  Prog.bind ((1 : Ex R) / (1 - v Y)).eval fun cY =>
  let d : ℕ → R := x
  let v₁ : ℕ → R := fun i => if i < m then cZ else zero
  let v₂ : ℕ → R := fun i => if i < m then zero else cY
  Prog.bind (forLoop m ([] : List (ℕ × ℕ × R)) fun i acc => ret ((i, i, E.lz i) :: acc)) fun L₁ =>
  Prog.bind (forLoop n L₁ fun j acc => ret ((m + j, m + j, E.ly j) :: acc)) fun L₂ =>
  Prog.bind (forLoop s L₂ fun k acc =>
    Prog.bind (0 - v (E.r1 k)).eval fun t =>
      ret ((row k, m + col k, t) :: (m + col k, row k, t) :: acc)) fun L =>
  -- Step 7, `g̃_w = g_w − H_{wγ} H_γ⁻¹ g_γ`
  Prog.bind (forLoop s (gz, gy) fun k st =>
    Prog.bind (v (E.gg k) / v (E.hg k)).eval fun t =>
    Prog.bind (v (st.1 (row k)) - v (E.hzg k) * v t).eval fun tz =>
    Prog.bind (v (st.2 (col k)) - v (E.hyg k) * v t).eval fun ty =>
    ret (upd st.1 (row k) tz, upd st.2 (col k) ty)) fun gt =>
  -- the right-hand side `−g̃_w`
  Prog.bind (forLoop (m + n) (fun _ => zero) fun i f =>
    Prog.bind (0 - v (if i < m then gt.1 i else gt.2 (i - m))).eval fun t => ret (upd f i t)) fun b =>
  -- Step 8
  Prog.bind (schurSolve (m + n) zero L d v₁ v₂ δ b) fun dw =>
  -- Steps 9–10
  Prog.bind (forLoop s (fun _ => zero) fun k f =>
    Prog.bind (v (E.gg k) + v (E.hzg k) * v (dw (row k)) + v (E.hyg k) * v (dw (m + col k))).eval
      fun t =>
    Prog.bind ((0 - v t) / v (E.hg k)).eval fun dg => ret (upd f k dg)) fun dγ =>
  -- Step 11
  forLoop (m + n + s) (fun _ => zero) fun i f =>
    ret (upd f i (if i < m + n then dw i else dγ (i - (m + n))))

end PQNormIPM1352.Main


