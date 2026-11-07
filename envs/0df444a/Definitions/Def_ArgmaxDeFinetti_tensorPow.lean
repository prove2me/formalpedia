-- Prove2me | Definitions.Def_ArgmaxDeFinetti_tensorPow
-- name    : ArgmaxDeFinetti_tensorPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:25.421199+00:00
-- url     : https://prove2.me/theorems/c3f38e03-e0a0-4dae-ae24-7de5d3a2e311
-- title:
--   Tensor powers $u^{\otimes n}$ and the spaces $(\mathbb C^d)^{\otimes n}$
-- statement:
--   The $n$-site space $(\mathbb C^d)^{\otimes n}$ is identified with functions of the tensor index $(i_1,\dots,i_n)\in\{1,\dots,d\}^n$, and operators on it with matrices indexed by pairs of tensor indices. For $u\in\mathbb C^d$ the tensor power is
--   $$
--   u^{\otimes n}(i_1,\dots,i_n)=u_{i_1}u_{i_2}\cdots u_{i_n}.
--   $$
--   These are the vectors whose span is the symmetric subspace and whose projectors $|u\rangle\langle u|^{\otimes t}$ make up the Hartree states.
--
--   **Formalization Note** Indices are $0$-based (`Fin d`); for $n=0$ the tensor power is the constant $1$ on the one-point index set, matching $\mathrm{Sym}^0\mathcal H=\mathbb C$.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 (1.1), p.18 and §3.1, pp.22–23

import Mathlib

open Matrix

namespace ArgmaxDeFinetti

/-- `Vec n d` is the space `(ℂ^d)^{⊗n}` of `n`-site vectors: functions of the tensor index
`(i₁, …, iₙ) ∈ (Fin n → Fin d)`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2, p.18. -/
abbrev Vec (n d : ℕ) : Type := (Fin n → Fin d) → ℂ

/-- `Op n d` is the space `L((ℂ^d)^{⊗n})` of operators on `n` sites, as matrices indexed by tensor
indices, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2, p.18. -/
abbrev Op (n d : ℕ) : Type := Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ

/-- The tensor power `u^{⊗n} ∈ (ℂ^d)^{⊗n}` of a vector `u ∈ ℂ^d`:
`(u^{⊗n})(i₁, …, iₙ) = u_{i₁} ⋯ u_{iₙ}`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 (1.1) and §3.1, pp.18, 22–23.

**Formalization Note** `tensorPow u 0` is the constant `1` on the one-point index set
(`Sym⁰ H = ℂ`, p.18). -/
def tensorPow {d : ℕ} (u : Fin d → ℂ) (n : ℕ) : Vec n d :=
  fun i => ∏ k, u (i k)

end ArgmaxDeFinetti


