-- Prove2me | Definitions.Def_PlanarMetricElections_Peer_Geometry
-- name    : PlanarMetricElections_Peer_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:50:27.125754+00:00
-- url     : https://prove2.me/theorems/be246996-2ec4-44b7-b07b-ba7a2f4dc91b
-- title:
--   The real plane, genuine norms, dominance, and the norm transfer
-- statement:
--   Points are pairs of real coordinates $x=(x_1,x_2)$. A planar norm is a real seminorm $N$ that is definite: $N(x)=0$ implies $x=0$. Its distance is $d_N(x,y)=N(x-y)$. The two explicit distances are
--
--   $$d_1(x,y)=|x_1-y_1|+|x_2-y_2|,\qquad d_\infty(x,y)=\max\{|x_1-y_1|,|x_2-y_2|\}.$$
--
--   Dominance is $\operatorname{Dom}_d(a,b)=\{x:d(a,x)<d(b,x)\}$. An open axis-parallel half-plane is one of $x_1<t$, $t<x_1$, $x_2<t$, or $t<x_2$, for a real threshold $t$.
--
--   The coordinate change $T(x)=(x_1+x_2,x_1-x_2)$ has inverse $T^{-1}(u)=((u_1+u_2)/2,(u_1-u_2)/2)$. It supports the transfer between the two norms. The local verification module proves both inverse laws and $d_1(Tx,Ty)=2d_\infty(x,y)$; no norm invariance is assumed. These definitions are the common geometric vocabulary of the mission.
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Sections 2 and 5, pp. 3–4, 9, 11 (PDF pp. 4–5, 10, 12)

import Mathlib

set_option autoImplicit false
noncomputable section

namespace PlanarMetricElections.Peer

abbrev Plane := ℝ × ℝ

/-- A genuine real norm, represented using Mathlib's seminorm plus definiteness. -/
abbrev PlanarNorm := {N : Seminorm ℝ Plane // ∀ x, N x = 0 → x = 0}

def normDistance (N : PlanarNorm) (x y : Plane) : ℝ := N.val (x - y)

def dOne (x y : Plane) : ℝ := |x.1 - y.1| + |x.2 - y.2|

def dInf (x y : Plane) : ℝ := max |x.1 - y.1| |x.2 - y.2|

def dominance (d : Plane → Plane → ℝ) (a b : Plane) : Set Plane :=
  {x | d a x < d b x}

/-- The four kinds of open axis-parallel half-plane. -/
def IsOpenAxisHalfPlane (H : Set Plane) : Prop :=
  ∃ t : ℝ, H = {x | x.1 < t} ∨ H = {x | t < x.1} ∨
    H = {x | x.2 < t} ∨ H = {x | t < x.2}

/-- Unnormalized 45-degree coordinate change; its inverse is given below. -/
def normTransfer (x : Plane) : Plane := (x.1 + x.2, x.1 - x.2)

def normTransferInv (x : Plane) : Plane := ((x.1 + x.2) / 2, (x.1 - x.2) / 2)

end PlanarMetricElections.Peer


