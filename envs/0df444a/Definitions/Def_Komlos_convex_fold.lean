-- Prove2me | Definitions.Def_Komlos_convex_fold
-- name    : Komlos_convex_fold
-- status  : Definition
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:53:40.433328+00:00
-- url     : https://prove2.me/theorems/2a4a08ad-fa9b-4310-8add-cab94680f144
-- title:
--   Closed convex fold along a vector
-- statement:
--   For a set $K\subseteq\mathbb R^m$ and a vector $u$, put
--   $$C_u(K)=\{y\in K:y+2u\in K\},\qquad J_u=\{tu:-1\le t\le1\}.$$
--   Define the closed fold by
--   $$F_u(K)=\overline{(K+J_u)\cap(C_u(K)+\mathbb Ru)}.$$
--   For compact convex $K$ and nonzero $u$, the set $C_u(K)+\mathbb Ru$ consists of the lines parallel to $u$ whose intersection with $K$ has length at least $2\|u\|$. On these lines, adding $J_u$ agrees with the union of the translates by $u$ and $-u$. Thus this is the closed version of the convex fold used in Banaszczyk's balancing argument. For $u=0$ it equals the closure of $K$.
-- source:
--   Shashwat Garg, Algorithms for Combinatorial Discrepancy, TU Eindhoven PhD thesis (2018), Chapter 3, Definition 14, printed p. 18. https://pure.tue.nl/ws/files/107722737/20181010_Garg.pdf . This algebraic description uses the two endpoints y and y+2u instead of fiber length, and takes closure. For compact convex K it gives the closed fold of that definition; at u=0 it uses the natural extension closure K.

import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set
open scoped Pointwise
set_option autoImplicit false

namespace Komlos
noncomputable def closedConvexFold (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin m)) : Set (EuclideanSpace ℝ (Fin m)) :=
  closure ((K + (fun t : ℝ => t • u) '' Icc (-1) 1) ∩
    ((K ∩ (fun y => y + (2 : ℝ) • u) ⁻¹' K) + Set.range (fun t : ℝ => t • u)))
end Komlos


