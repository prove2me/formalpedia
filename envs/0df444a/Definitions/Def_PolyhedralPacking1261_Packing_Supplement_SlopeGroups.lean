-- Prove2me | Definitions.Def_PolyhedralPacking1261_Packing_Supplement_SlopeGroups
-- name    : PolyhedralPacking1261_Packing_Supplement_SlopeGroups
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:37:51.414209+00:00
-- url     : https://prove2.me/theorems/2eff4629-f695-48c5-96ef-8e46d9862a13
-- title:
--   Section 3 setting: packed separated families, slope intervals, auxiliary bodies, the maps $T_I$ and tube directions
-- statement:
--   This layer fixes the objects of the proof of Theorem 8 (§3).
--
--   1. A family of $m$ bc-parallelepipeds $P_i$ (parameters $a_i,u_i,v_i,k_i$ of the base mission) with centers $p_i$ is **packed in the unit cube** when every $p_i+P_i$ lies in $[0,1]^3$ and distinct placed objects have disjoint interiors. It is **same-shadow separated** at scale $\tau$ when $d(i,j)=|u_i-u_j|+|v_i-v_j|>\tau$ for distinct $i,j$ with $k_i=k_j$. The **Section 3 setting** bundles $b,c>0$, individual fit of each object, a packing with centers $p_i$, $0<\tau\le2$ and separation.
--   2. **Slope intervals.** For an offset $\theta$, the line is cut into the intervals $[\theta+j\tau/100,\theta+(j+1)\tau/100)$, $j\in\mathbb Z$; interval $j$ has label $j \bmod 10$ and midpoint $u_I=\theta+(j+\tfrac12)\tau/100$. An object is **retained** under label $L$ when $a_i<\tau/100$ and $u_i$ lies in an interval of label $L$; objects in one interval form a slope group.
--   3. The **auxiliary body** (3) is
--   $$Q_i=p_i+\Big\{\lambda_1(\tfrac{\tau}{100},0,0)+\tfrac{\lambda_2}{4}(u_i,b,0)+\lambda_3(v_i,k_ib,c):\lambda_1,\lambda_2,\lambda_3\in[-\tfrac12,\tfrac12]\Big\}.$$
--   4. $T_I(x,y,z)=(bx-u_Iy,\ \tau y,\ z/c)$; $D_i=(b(v_i-k_iu_I),\,k_ib\tau,\,1)$ and $d_i=D_i/\|D_i\|$ with the Euclidean norm.
--
--   **Formalization Note** Points are coordinate triples; `toE3` is the identity identification with Euclidean space used for tubes and angles. The half-open interval convention and the offset $\theta$ are free choices the source leaves open.
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, §2 standing assumptions, PDF pp.6–7 (printed pp.5–6); §3 auxiliary bodies (3), the map T_I and D_i, d_i, PDF pp.11–14 (printed pp.10–13)

import Definitions.Def_PolyhedralPacking1261_Packing_Supplement_Containers
import Definitions.Def_PolyhedralPacking1261_Packing_Supplement_Kakeya

set_option autoImplicit false

namespace PolyhedralPacking1261.Packing.Supplement

open PolyhedralPacking1261.Packing

/-- The placed objects `p i + P_i` lie in the unit cube and have pairwise disjoint
ambient interiors (a translational packing into `[0,1]³`). -/
def PackedInUnitCube (b c : ℝ) {m : ℕ} (P : Fin m → BCParameters)
    (p : Fin m → Point3) : Prop :=
  (∀ i, shiftSet (p i) (bcBody b c (P i)) ⊆ unitCube) ∧
  ∀ i j, i ≠ j → Disjoint (interior (shiftSet (p i) (bcBody b c (P i))))
    (interior (shiftSet (p j) (bcBody b c (P j))))

/-- Distinct objects of the same shadow class are at shear distance more than `τ`. -/
def SameShadowSeparated (τ : ℝ) {m : ℕ} (P : Fin m → BCParameters) : Prop :=
  ∀ i j, i ≠ j → (P i).k = (P j).k → τ < shearDistance (P i) (P j)

/-- The fixed data of Section 3: a family of one type `(b,c)` with `b, c > 0`, each
object fitting individually, placed with centers `p i` as a packing in `[0,1]³`,
and `0 < τ ≤ 2` with strict same-shadow separation. -/
def LowerBoundSetting (b c τ : ℝ) {m : ℕ} (P : Fin m → BCParameters)
    (p : Fin m → Point3) : Prop :=
  0 < b ∧ 0 < c ∧ (∀ i, IndividuallyFits b c (P i)) ∧ PackedInUnitCube b c P p ∧
    0 < τ ∧ τ ≤ 2 ∧ SameShadowSeparated τ P

/-- Index of the interval of length `τ/100` containing `u`, for the partition of the
line into intervals `[θ + jτ/100, θ + (j+1)τ/100)`. -/
noncomputable def slopeInterval (θ τ u : ℝ) : ℤ :=
  ⌊(u - θ) / (τ / 100)⌋

/-- The cyclic label of that interval, in `{0, …, 9}`. -/
noncomputable def slopeLabel (θ τ u : ℝ) : ℤ :=
  slopeInterval θ τ u % 10

/-- Midpoint `u_I` of the interval with index `j`. -/
noncomputable def intervalMidpoint (θ τ : ℝ) (j : ℤ) : ℝ :=
  θ + ((j : ℝ) + 1 / 2) * (τ / 100)

/-- An object is retained under label `L`: it is thin (`a < τ/100`) and its offset `u`
lies in an interval of label `L`. -/
def Retained (θ τ : ℝ) (L : ℤ) (q : BCParameters) : Prop :=
  q.a < τ / 100 ∧ slopeLabel θ τ q.u = L

/-- The auxiliary body (3): center `center`, first edge `(τ/100,0,0)`, a quarter of the
second edge `(u,b,0)` and the full third edge `(v,kb,c)`. -/
def auxBody (b c τ : ℝ) (q : BCParameters) (center : Point3) : Set Point3 :=
  shiftSet center {x | ∃ s t w : ℝ, |s| ≤ (1 / 2 : ℝ) ∧ |t| ≤ (1 / 2 : ℝ) ∧
    |w| ≤ (1 / 2 : ℝ) ∧
    x = ![s * (τ / 100) + (t / 4) * q.u + w * q.v,
      (t / 4) * b + w * (q.k : ℝ) * b, w * c]}

/-- The linear map `T_I(x,y,z) = (b x − u_I y, τ y, z / c)`. -/
noncomputable def slopeMap (b c τ uI : ℝ) (x : Point3) : Point3 :=
  ![b * x 0 - uI * x 1, τ * x 1, x 2 / c]

/-- The isometric identification of coordinate triples with Euclidean three-space. -/
def toE3 (x : Point3) : E3 := WithLp.toLp 2 x

/-- The third edge `D_i = (b(v_i − k_i u_I), k_i b τ, 1)` of `T_I(Q_i)`. -/
noncomputable def transformedEdge (b τ uI : ℝ) (q : BCParameters) : Point3 :=
  ![b * (q.v - (q.k : ℝ) * uI), (q.k : ℝ) * b * τ, 1]

/-- The unit direction `d_i = D_i / ‖D_i‖` (Euclidean norm). -/
noncomputable def tubeDirection (b τ uI : ℝ) (q : BCParameters) : E3 :=
  ‖toE3 (transformedEdge b τ uI q)‖⁻¹ • toE3 (transformedEdge b τ uI q)

end PolyhedralPacking1261.Packing.Supplement


