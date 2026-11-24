-- Prove2me | Definitions.Def_ValiantBorder_towerRoutes
-- name    : ValiantBorder_towerRoutes
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:12:27.54806+00:00
-- url     : https://prove2.me/theorems/9a6b0280-65e4-4707-8414-2eab1a915796
-- title:
--   Towers, routes, and exchange laws on their flags
-- statement:
--   A tower is a sequence of finite incidence structures with maps between levels. A route joins two chambers by elementary steps. The bounds count steps in a route and the number of routes using a given edge, while the flags record the local exchange laws.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Tree.lean#L1260).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Tree.lean#L1260.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_cutLaws
/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field* (2026),
`anthropics/formal-math` at revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5.
The finite-group tower construction, routes, local laws and estimates occur in
`Nc/Tower/{Base,Chain,Inst,Tower}.lean` and `Paper/Tree.lean`. Apache-2.0. -/
namespace Nc.Tow

open Finset

/-- A tower of coverings, `J` steps, with `h` types. -/
structure Tower (h b D J r : ℕ) where
  /-- chambers -/
  X : ℕ → Type
  /-- typed edges -/
  Ed : ℕ → Type
  /-- vertices of type `i` -/
  V : ℕ → Fin h → Type
  /-- the chambers at a vertex -/
  Fl : Type
  /-- the near pairs at a vertex -/
  Nr : Type
  [fX : ∀ j, Fintype (X j)]
  [dX : ∀ j, DecidableEq (X j)]
  [fE : ∀ j, Fintype (Ed j)]
  [dE : ∀ j, DecidableEq (Ed j)]
  [fV : ∀ j i, Fintype (V j i)]
  [dV : ∀ j i, DecidableEq (V j i)]
  [fF : Fintype Fl]
  [dF : DecidableEq Fl]
  [fN : Fintype Nr]
  [dN' : DecidableEq Nr]
  /-- the ends of an edge -/
  e0 : ∀ {j}, Ed j → X j
  /-- the ends of an edge -/
  e1 : ∀ {j}, Ed j → X j
  e_ne : ∀ {j} (e : Ed j), e0 e ≠ e1 e
  /-- the type of an edge -/
  ty : ∀ {j}, Ed j → Fin h
  card_ed : ∀ j ≤ J, ∀ i, 2 * (univ.filter fun e : Ed j => ty e = i).card = r * Fintype.card (X j)
  deg : ∀ j ≤ J, ∀ (c : X j) i, (univ.filter fun e : Ed j => ty e = i ∧ (e0 e = c ∨ e1 e = c)).card ≤ r
  /-- the vertex of a chamber -/
  vx : ∀ {j} i, X j → V j i
  /-- the place of a chamber at its vertex -/
  co : ∀ {j} (i : Fin h), X j → Fl
  vx_co : ∀ {j}, j ≤ J → ∀ i, Function.Bijective fun c : X j => (vx i c, co i c)
  card_fl : Fintype.card Fl = b
  /-- the ends of a near pair -/
  cN : Nr → Fl
  /-- the ends of a near pair -/
  dN : Nr → Fl
  n_ne : ∀ ν, cN ν ≠ dN ν
  /-- the edges of types other than `i` are the near pairs at the vertices of type `i` -/
  nr : ∀ {j}, j ≤ J → ∀ i, {e : Ed j // ty e ≠ i} ≃ V j i × Nr
  nr_vx0 : ∀ {j} (hj : j ≤ J) i (e : {e : Ed j // ty e ≠ i}), vx i (e0 e.1) = (nr hj i e).1
  nr_vx1 : ∀ {j} (hj : j ≤ J) i (e : {e : Ed j // ty e ≠ i}), vx i (e1 e.1) = (nr hj i e).1
  nr_co : ∀ {j} (hj : j ≤ J) i (e : {e : Ed j // ty e ≠ i}),
    s(co i (e0 e.1), co i (e1 e.1)) = s(cN (nr hj i e).2, dN (nr hj i e).2)
  /-- the covering -/
  π : ∀ {j}, X j → X (j + 1)
  /-- the covering on edges -/
  πE : ∀ {j}, Ed j → Ed (j + 1)
  /-- the covering on vertices -/
  πV : ∀ {j} {i}, V j i → V (j + 1) i
  π_ends : ∀ {j}, j < J → ∀ e : Ed j, s(e0 (πE e), e1 (πE e)) = s(π (e0 e), π (e1 e))
  π_ty : ∀ {j}, j < J → ∀ e : Ed j, ty (πE e) = ty e
  card_X : ∀ j < J, Fintype.card (X j) = D * Fintype.card (X (j + 1))
  fibre : ∀ {j}, j < J → ∀ ē : Ed (j + 1), (univ.filter fun e : Ed j => πE e = ē).card ≤ D
  π_vx : ∀ {j}, j < J → ∀ i (c : X j), vx i (π c) = πV (vx i c)
  π_co : ∀ {j}, j < J → ∀ i (c : X j), co i (π c) = co i c
  /-- hosts -/
  host : ∀ {j} i, V j i → X (j + 1)
  host_inj : ∀ {j}, j < J → ∀ i, Function.Injective (host i : V j i → X (j + 1))
  host_vx : ∀ {j}, j < J → ∀ i (v : V j i), vx i (host i v) = πV v

attribute [instance] Tower.fX Tower.dX Tower.fE Tower.dE Tower.fV Tower.dV Tower.fF Tower.dF Tower.fN Tower.dN'

namespace Tower

variable {h b D J r : ℕ} (T : Tower h b D J r)

/-- The other end of an edge. -/
def step {j : ℕ} (e : T.Ed j) (c : T.X j) : T.X j := if T.e0 e = c then T.e1 e else T.e0 e

/-- The list of edges is a walk from `c` to `c'`. -/
def Walk {j : ℕ} : T.X j → List (T.Ed j) → T.X j → Prop
  | c, [], c' => c = c'
  | c, e :: l, c' => (T.e0 e = c ∨ T.e1 e = c) ∧ Walk (T.step e c) l c'

end Tower

/-- Routes: a walk from every chamber of `X 0` to every other one, at most `m` steps, in which every edge is used at
most `Uu` times in all. -/
structure Routes {h b D J r : ℕ} (T : Tower h b D J r) (m Uu : ℕ) where
  /-- the route -/
  rt : T.X 0 → T.X 0 → List (T.Ed 0)
  walk : ∀ c c', T.Walk c (rt c c') c'
  len : ∀ c c', (rt c c').length ≤ m
  use : ∀ e : T.Ed 0, ∑ c, ∑ c', (rt c c').count e ≤ Uu

end Nc.Tow
namespace Nc.G
variable {F : Type} [CommRing F]
/-- A bound for the lengths of the strings of a law. -/
structure Law.Le (L : Law F) (m : ℕ) : Prop where
  len_le : ∀ i ν, L.len i ν ≤ m


end Nc.G
namespace Nc.Tow.Tower
open Finset
variable {h b D J r : ℕ} (T : Nc.Tow.Tower h b D J r)
/-- The square of the norm of a load on pairs. -/
noncomputable def NN2 (n : Sym2 T.Fl → ℕ) : ℝ :=
  ((b : ℝ) * (b - 1) / 2) * ∑ q : Sym2 T.Fl, if q.IsDiag then 0 else (n q : ℝ) ^ 2


end Nc.Tow.Tower
namespace Nc.Tow
open Finset Nc.G
/-- The laws at the vertices of a tower. -/
structure FlagLaws (F : Type) [CommRing F] {h b D J r : ℕ} (T : Tower h b D J r) where
  /-- kinds of laws -/
  Di : Type
  [fD : Fintype Di]
  [dD : DecidableEq Di]
  /-- the laws -/
  L : Di → Law F
  /-- roles are the chambers at a vertex -/
  ro : ∀ d, (L d).Ro ≃ T.Fl
  /-- channels are the near pairs -/
  cn : ∀ d, (L d).Cn ≃ T.Nr
  ends : ∀ d ν, s(ro d ((L d).c ν), ro d ((L d).d ν)) = s(T.cN (cn d ν), T.dN (cn d ν))
  lam_pos : ∀ d, 1 ≤ (L d).lam
  nonempty : ∀ d, Nonempty (L d).I
  /-- the scale -/
  a₁ : ℕ
  a₁_pos : 0 < a₁
  /-- the constant of the contraction -/
  C₁ : ℝ
  C₁_nonneg : 0 ≤ C₁
  /-- its integer form -/
  G₁ : ℕ
  G₁_le : (G₁ : ℝ) ≤ 2 * C₁ * (a₁ : ℝ) ^ 2
  /-- every load is below one of finitely many -/
  L1 : ∀ (n : Sym2 T.Fl → ℕ) (t : ℕ), √(T.NN2 n) ≤ (a₁ : ℝ) * t → ∃ d, ∀ q : Sym2 T.Fl, ¬ q.IsDiag →
    n q ≤ (univ.filter fun e : (L d).Sl => s(ro d ((L d).a e), ro d ((L d).b e)) = q).card * t
  /-- the strings are short -/
  L2 : ∀ d i, r * b * ∑ ν, ((L d).lam + (L d).len i ν) ^ 2 ≤ G₁

attribute [instance] FlagLaws.fD FlagLaws.dD


end Nc.Tow
namespace Nc.Tow
open Finset Nc.G
variable {F : Type} [CommRing F] {h b D J r : ℕ} {T : Tower h b D J r}
/-- The conditions on the tower and the laws. -/
structure THypR (FL : FlagLaws F T) (ρ : ℝ) : Prop where
  r_pos : 0 < r
  b_pos : 0 < b
  h_pos : 0 < h
  bD : b ≤ 2 * D
  ρ_pos : 0 < ρ
  ρ_lt : ρ < 1
  gain : 1 + 8 * FL.C₁ ≤ ρ ^ 2 * h
  two : 2 ≤ ρ * D
  near : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f

/-- The conditions on the tower and the laws, with one constant. -/
structure TCst (FL : FlagLaws F T) (laws : List (Law F)) (c : ℕ) (ρ : ℝ) (p q : ℕ) : Prop extends THypR FL ρ where
  h_le : h ≤ c
  b_le : b ≤ c
  r_le : r ≤ c
  nr_le : Fintype.card T.Nr ≤ c
  g_le : FL.G₁ ≤ c
  di_le : Fintype.card FL.Di ≤ c
  fl_le : Fintype.card (Sym2 T.Fl) ≤ c
  sl_le : ∀ d, Fintype.card (FL.L d).Sl ≤ c
  bot : Fintype.card (T.X J) ≤ c
  bot_pos : 0 < Fintype.card (T.X J)
  cst : √h * r + √FL.C₁ * FL.a₁ ≤ c
  inv : 1 / (1 - ρ) ≤ c
  pq : 2 * p ≤ q
  pow : ρ ^ q * (D : ℝ) ^ p ≤ 1
  mem : ∀ d, FL.L d ∈ laws
  len : ∀ L ∈ laws, L.Le c ∧ L.lam ≤ c


end Nc.Tow


