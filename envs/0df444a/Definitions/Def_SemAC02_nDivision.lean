-- Prove2me | Definitions.Def_SemAC02_nDivision
-- name    : SemAC02_nDivision
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:23.135358+00:00
-- url     : https://prove2.me/theorems/0933894a-09f8-4114-b516-cd5338bf2c8a
-- title:
--   $n$-divisions: the space $\mathcal B_{F_0}$ of functions on $\Omega$ and $H_{F_0}(k)$
-- statement:
--   Let $n,h\ge1$, $N=nh$, and partition the $N$ variables into parts $V_1,\dots,V_n$ of size $h$. Let $F_0$ consist of all products $xy$ of distinct variables in the same part. Then $\mathcal B_{F_0}=\mathcal B_N/\langle F_0\rangle$ is the algebra of functions on
--   $$
--   \Omega=\{x\in\{0,1\}^N:\ \text{at most one }1\text{ in each part}\}.
--   $$
--   The degree of an element of $\mathcal B_{F_0}$ is the least total degree of a polynomial representing it, $\mathcal B_{F_0}^{\le k}$ is the subspace of elements of degree at most $k$, and $H_{F_0}(k)=\dim\mathcal B_{F_0}^{\le k}$.
--
--   **Formalization Note** The variables are `Fin n × Fin h`; part $i$ is $\{i\}\times$`Fin h`. Elements of $\mathcal B_{F_0}$ are functions $\Omega\to\mathbb F_2$, and a polynomial maps to its restriction (`restrOmega`); $\mathcal B_{F_0}^{\le k}$ is the image of the polynomials of total degree at most $k$.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §4, p.24; §4.2, p.29, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_SemAC02_Ble

namespace SemAC02

open MvPolynomial

/-- The cube points of an `n`-division (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard
Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission), §4, p.26 and
§4.2, p.29): `N = nh` variables `(i, j)` partitioned into the parts `V_i = {i} × [h]`, and
`Ω = {x ∈ {0,1}^N : xy = 0 for distinct x, y in the same part}`, the points with at most one `1`
in each part. -/
def nDivOmega (n h : ℕ) : Set (Fin n × Fin h → Bool) :=
  {x | ∀ (i : Fin n) (j j' : Fin h), x (i, j) = true → x (i, j') = true → j = j'}

/-- Restriction to `Ω`: `B_{F_0} = B_N/⟨F_0⟩` is identified with the functions `Ω → 𝔽₂` (p.24,
p.29), and a polynomial maps to the function it computes on `Ω`. -/
noncomputable def restrOmega (n h : ℕ) :
    MvPolynomial (Fin n × Fin h) (ZMod 2) →ₗ[ZMod 2] (nDivOmega n h → ZMod 2) :=
  LinearMap.pi fun x : nDivOmega n h => (aeval (toF2 x.1)).toLinearMap

/-- `B_{F_0}^{≤k}` (p.24): the elements of `B_{F_0}` of degree at most `k`, where the degree of
an element is the least total degree of a polynomial representing it. -/
noncomputable def BleF0 (n h k : ℕ) : Submodule (ZMod 2) (nDivOmega n h → ZMod 2) :=
  (restrictTotalDegree (Fin n × Fin h) (ZMod 2) k).map (restrOmega n h)

/-- `H_{F_0}(k) := dim B_{F_0}^{≤k}` (p.24). -/
noncomputable def HF0 (n h k : ℕ) : ℕ := Module.finrank (ZMod 2) (BleF0 n h k)

end SemAC02


