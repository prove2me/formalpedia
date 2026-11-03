-- Prove2me | Definitions.Def_FreeOrderEPTAS_typeList
-- name    : FreeOrderEPTAS_typeList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:13.292107+00:00
-- url     : https://prove2.me/theorems/7ce71521-3b07-4f9e-b83a-060d7c19b0d9
-- title:
--   Job types and classes
-- statement:
--   Partition $[0,1]$ into $I_0=[0,\delta]$ and $I_q=((1+\epsilon)^{q-1}\delta,(1+\epsilon)^q\delta]$, $q\ge1$. The type of job $j$ is the vector $\mathcal T^j=(\mathcal T^j_{id})_{(i,d)\in A}$ with $\ell_{ijd}\in I_{\mathcal T^j_{id}}$. The distinct type vectors are $\mathcal T^{(1)},\dots,\mathcal T^{(T)}$, the class $J_t$ collects the jobs of type $\mathcal T^{(t)}$, and $\rho(j)$ is the class of $j$.
--
--   The number of classes is a function of $(\epsilon,\delta,m,D)$ only, which is what keeps the guessing affordable.
--
--   **Formalization Note** `seg ϵ δ v` is $0$ for $v\le\delta$ and $\lceil\log(v/\delta)/\log(1+\epsilon)\rceil$ otherwise, the smallest $q$ with $v\le(1+\epsilon)^q\delta$. Coordinates outside $A$ are set to $0$, which changes no equality of types.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §2.2, pp.9–10; ρ, p.11

import Mathlib
import Definitions.Def_FreeOrderEPTAS_SCInstance

namespace FreeOrderEPTAS

variable {m D n : ℕ}

/-- The index of the segment of §2.2 (arXiv:2007.13121v3, p.9) containing `v`, for the partition
`I_0 = [0, δ]`, `I_q = ((1 + ϵ)^{q-1} δ, (1 + ϵ)^q δ]`.

**Formalization Note.** For `v > δ` the smallest `q` with `v ≤ (1 + ϵ)^q δ` is
`⌈log(v/δ) / log(1 + ϵ)⌉`, which is positive; both logarithms have arguments `> 1` for `ϵ, δ > 0`. -/
noncomputable def seg (ϵ δ v : ℝ) : ℕ :=
  if v ≤ δ then 0 else ⌈Real.log (v / δ) / Real.log (1 + ϵ)⌉₊

/-- The type vector `T^j` of job `j` (p.9). It is indexed by `(i, d) ∈ A`; coordinates outside
`A` are set to `0`, which changes no equality of types. -/
noncomputable def typeVec (I : SCInstance m D n) (ϵ δ : ℝ) (j : Fin n) : Fin m → Fin D → ℕ :=
  fun i d => if d ∈ I.A i then seg ϵ δ (I.ℓ i j d) else 0

/-- The distinct type vectors `T^(1), …, T^(T)` (p.10). -/
noncomputable def typeList (I : SCInstance m D n) (ϵ δ : ℝ) : List (Fin m → Fin D → ℕ) :=
  ((List.finRange n).map (typeVec I ϵ δ)).dedup

/-- The number `T` of classes (p.10). -/
noncomputable def numTypes (I : SCInstance m D n) (ϵ δ : ℝ) : ℕ :=
  (typeList I ϵ δ).length

/-- `ρ(j)`, the class of job `j` (p.11). -/
noncomputable def rho (I : SCInstance m D n) (ϵ δ : ℝ) (j : Fin n) : Fin (numTypes I ϵ δ) :=
  ⟨(typeList I ϵ δ).idxOf (typeVec I ϵ δ j), by
    apply List.idxOf_lt_length_iff.mpr
    simp [typeList]⟩

/-- The type vector `T^(t)` of class `t` (p.10). -/
noncomputable def typeOf (I : SCInstance m D n) (ϵ δ : ℝ) (t : Fin (numTypes I ϵ δ)) :
    Fin m → Fin D → ℕ :=
  (typeList I ϵ δ).get t

end FreeOrderEPTAS


