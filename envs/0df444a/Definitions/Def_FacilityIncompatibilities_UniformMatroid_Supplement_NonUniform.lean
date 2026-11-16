-- Prove2me | Definitions.Def_FacilityIncompatibilities_UniformMatroid_Supplement_NonUniform
-- name    : FacilityIncompatibilities_UniformMatroid_Supplement_NonUniform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:11:42.798198+00:00
-- url     : https://prove2.me/theorems/49602ba2-1167-46cd-96a6-1702530f86f8
-- title:
--   Definition 2 and §1.2 — encoded FL-MI instances with non-uniform opening costs, and partition matroids
-- statement:
--   An **encoded FL-MI instance with non-uniform opening costs** consists of a number $n$ of clients $V_C=\{0,\dots,n-1\}$, a number $m$ of facilities $V_F=\{0,\dots,m-1\}$, a rational distance $d(x,y)$ for every pair of points $x,y\in V_C\cup V_F$, and a rational opening cost $f_i$ for every facility $i$. Together with a matroid $\mathcal M$ on the clients it determines an FL-MI instance $(V_C,V_F,d,f,\mathcal M)$ in the sense of the mission's model (Definition 1). Its **input word** is the binary string consisting of the self-delimiting codes of $n$ and $m$, the $(n+m)^2$ distances in row-major order, and then the costs $f_0,\dots,f_{m-1}$; its length is the input size of the polynomial-time claims. The matroid is not part of the input: algorithms query it through an independence oracle.
--
--   A matroid $\mathcal M$ on the clients is a **partition matroid** (Definition 2: FL-MI *with group constraints*) if the clients are partitioned into groups $G_g$, each with a bound $b_g\ge 0$, and a client set $X$ is independent exactly when
--
--   $$|X\cap G_g|\le b_g\quad\text{for every group } g.$$
--
--   These are the inputs of Theorem 4. A single group is capacitated facility location with uniform capacities.
--
--   **Formalization Note** The groups are given by a label map from the clients to $\{0,\dots,n-1\}$ (a partition of $n$ clients has at most $n$ nonempty parts) and natural-number bounds. Being a partition matroid is a property of $\mathcal M$; the partition is not given to the algorithm. The binary encodings (`natCode`, `ratCode`) and the independence oracle are those of the published encoding module.
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Definition 2, printed p.2 / PDF p.3; input conventions printed p.2 / PDF p.3 and §1.2, printed pp.3–4 / PDF pp.4–5

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Encoding

namespace FacilityIncompatibilities.UniformMatroid.Supplement

/-- **A rationally encoded FL-MI instance with non-uniform opening costs** (§1, printed p.2, and
§1.2, printed pp.3–4: "rational distances and opening costs"): `n` clients `Fin n`, `m`
facilities `Fin m`, the full rational distance table on `Fin n ⊕ Fin m`, and an opening cost
`f i` for every facility `i`. The client matroid is not part of the input: it is accessed through
the independence oracle `indepOracle` of the published encoding. -/
structure NUEncodedInstance where
  /-- number of clients -/
  n : ℕ
  /-- number of facilities -/
  m : ℕ
  /-- rational distance table on clients ⊕ facilities -/
  d : Fin n ⊕ Fin m → Fin n ⊕ Fin m → ℚ
  /-- the opening cost of each facility -/
  f : Fin m → ℚ

namespace NUEncodedInstance

/-- The real FL-MI instance of an encoded instance together with a client matroid `M`:
distances and opening costs cast to `ℝ`. -/
def toInstance (E : NUEncodedInstance) (M : Matroid (Fin E.n)) :
    Instance (Fin E.n) (Fin E.m) where
  d x y := (E.d x y : ℝ)
  f i := (E.f i : ℝ)
  M := M

/-- **The input word** of an encoded instance: `n` and `m` in self-delimiting binary, the
`(n + m)²` entries of the distance table in row-major order (points numbered by
`finSumFinEquiv`: clients `0, …, n−1`, then facilities `n, …, n+m−1`), then the opening costs
`f_0, …, f_{m−1}`, every rational written with `ratCode`. Its length is the binary input length
of the polynomial-time claims. -/
def encode (E : NUEncodedInstance) : List Bool :=
  QuantumHMMR.natCode E.n ++ QuantumHMMR.natCode E.m ++
    ((List.finRange (E.n + E.m)).flatMap fun a => (List.finRange (E.n + E.m)).flatMap fun b =>
      ratCode (E.d (finSumFinEquiv.symm a) (finSumFinEquiv.symm b))) ++
    (List.finRange E.m).flatMap fun i => ratCode (E.f i)

end NUEncodedInstance

/-- **Partition matroid** (Definition 2, printed p.2 / PDF p.3: "FL-MI with group constraints"):
the clients `Fin n` are partitioned into groups by a group label `grp j`, each group `g` has a
bound `b g ≥ 0`, and a client set `X` is independent iff it contains at most `b g` clients of
every group `g`.

**Formalization Note** Groups are labelled by `Fin n`: a partition of `n` clients has at most `n`
nonempty parts, and an empty part constrains nothing, so every partition matroid is covered.
The partition is a property of `M`, not part of any algorithm's input. -/
def IsPartitionMatroid {n : ℕ} (M : Matroid (Fin n)) : Prop :=
  ∃ (grp : Fin n → Fin n) (b : Fin n → ℕ), ∀ X : Set (Fin n),
    M.Indep X ↔ ∀ g, (X ∩ grp ⁻¹' {g}).ncard ≤ b g

end FacilityIncompatibilities.UniformMatroid.Supplement


