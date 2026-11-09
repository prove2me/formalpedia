-- Prove2me | Definitions.Def_DirTeleMC_Phi
-- name    : DirTeleMC_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:31:27.632018+00:00
-- url     : https://prove2.me/theorems/0eab64d4-2109-4861-b0c4-6f4e800da164
-- title:
--   The potential, the increase and the linear cost
-- statement:
--   Fix a scale $\Gamma > 0$. For a load vector $L = (L(v))_{v \in V}$ (the **state**) let
--   $$\Phi(L) = \sum_{v\in V} \left(e^{L(v)/\Gamma} - 1\right),$$
--   and for a structure or path $S$ with load vector $L_S$ let $\Delta_L(S) = \Phi(L + L_S) - \Phi(L)$ be its **increase** and
--   $$c_L(S) = \frac{1}{\Gamma} \sum_{v \in V} e^{L(v)/\Gamma} L_S(v)$$
--   its **linear cost**. A vertex has the weight $e^{L(v)/\Gamma}(e^{1/\Gamma} - 1)$ in the state $L$, and the weight of a walk is the sum of the weights of the vertices it leaves, with multiplicity.
--
--   The potential prices the loads in the recursive greedy algorithm (Algorithm 1).
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), §B.4 "Potential", p.21 (PDF p.22); §B.6 "Linear cost", p.26 (PDF p.27)

import Mathlib
import Definitions.Def_DirTeleMC_IsJump

namespace DirTeleMC

variable {n : ℕ}

/-- **The potential** `Φ(L) = Σ_{v ∈ V} (e^{L(v)/Γ} − 1)`.
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), §B.4 "Potential", p.21: "Fix a scale Γ > 0. For a load vector L = (L(v))_{v∈V},
which gives every vertex of G a load, the state, let Φ(L) = Σ_{v∈V} (e^{L(v)/Γ} − 1)".

**Formalization Note.** The scale `Γ : ℝ` is a parameter; every result using `Φ` assumes `0 < Γ`. Load
vectors are `Fin n → ℕ`. -/
noncomputable def Phi (Γ : ℝ) (L : Fin n → ℕ) : ℝ :=
  ∑ v, (Real.exp ((L v : ℝ) / Γ) - 1)

/-- **The increase** `Δ_L(S) = Φ(L + L_S) − Φ(L)` of a structure (or path) with load vector `LS` in the state
`L` (§B.4, p.21). -/
noncomputable def incr (Γ : ℝ) (L LS : Fin n → ℕ) : ℝ := Phi Γ (L + LS) - Phi Γ L

/-- **The linear cost** `c_L(S) = (1/Γ) Σ_{v ∈ V} e^{L(v)/Γ} L_S(v)` (§B.6, p.26: "For a structure S and a state
L let c_L(S) = (1/Γ) Σ_{v∈V} e^{L(v)/Γ} L_S(v) be its linear cost; for a path P, the linear cost c_L(P) is defined
in the same way, with L_P in place of L_S"). -/
noncomputable def lin (Γ : ℝ) (L LS : Fin n → ℕ) : ℝ :=
  (1 / Γ) * ∑ v, Real.exp ((L v : ℝ) / Γ) * (LS v : ℝ)

/-- The load vector `L_P` of a walk `P`: `L_P(v)` is the number of arcs of `P` that leave `v` (§B.4, p.21). -/
def pathLoads (P : List (Fin n)) : Fin n → ℕ := fun v => departures P v

/-- The weight `e^{L(v)/Γ}(e^{1/Γ} − 1)` of a vertex in the state `L` (§B.4, p.21). -/
noncomputable def vertexWeight (Γ : ℝ) (L : Fin n → ℕ) (v : Fin n) : ℝ :=
  Real.exp ((L v : ℝ) / Γ) * (Real.exp (1 / Γ) - 1)

/-- The weight of a walk: the sum of the weights of the vertices it leaves, with multiplicity. -/
noncomputable def walkWeight (Γ : ℝ) (L : Fin n → ℕ) (P : List (Fin n)) : ℝ :=
  (P.dropLast.map (vertexWeight Γ L)).sum

end DirTeleMC


