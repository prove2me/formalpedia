-- Prove2me | Definitions.Def_GaussTesting_Ell2
-- name    : GaussTesting_Ell2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:28.10407+00:00
-- url     : https://prove2.me/theorems/8f1c1257-a5e0-49aa-acf3-45d56b1e9159
-- title:
--   The Hilbert space $\ell^2(\iota)$, relabellings and elementary tensors
-- statement:
--   For an index set $\iota$, $\ell^2(\iota)$ is the Hilbert space of square-summable functions $f:\iota\to\mathbb C$, with orthonormal basis $\{|x\rangle : x\in\iota\}$. Two operations on vectors are provided:
--
--   1. **Relabelling.** For a bijection $e:\alpha\to\beta$ and $f\in\ell^2(\beta)$, $(f\circ e)(a)=f(e(a))$ is a vector of $\ell^2(\alpha)$.
--   2. **Elementary tensors.** For $u\in\ell^2(\alpha)$ and $v\in\ell^2(\beta)$, $(u\otimes v)(a,b)=u(a)\,v(b)$ is a vector of $\ell^2(\alpha\times\beta)$.
--
--   Every Hilbert space of the mission is $\ell^2$ of its standard basis: the $n$-mode fermionic Fock space $\bigwedge\mathbb C^n$ is $\ell^2(\{0,1\}^n)$ (occupation numbers, $1$ = occupied) and the $n$-mode bosonic Fock space is $\ell^2(\mathbb N^n)$. The $k$-fold tensor power $\mathcal H^{\otimes k}$ of $\mathcal H=\ell^2(\iota)$ is $\ell^2(\iota^k)$, the $s$-th coordinate of a label being register $s$.
--
--   **Formalization Note** `Ell2 ι` is Mathlib's `lp (fun _ : ι => ℂ) 2`; the two operations carry their square-summability proofs.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), §2, p.12; §2.2, p.17; §2.3, p.18

import Mathlib

namespace GaussTesting

/-- The Hilbert space `ℓ²(ι) = ℓ²(ι; ℂ)` with orthonormal basis indexed by `ι`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), §2, p.12 (pure states are unit vectors of a Hilbert space `ℋ`), §2.2, p.17
(fermionic Fock space `⋀ℂⁿ` with occupation basis `|x⟩`, `x ∈ {0,1}ⁿ`), §2.3, p.18 (bosonic Fock space
`⋁ℂⁿ` with basis `|x₁,…,x_n⟩`, `xᵢ ∈ ℕ₀`).

**Formalization Note.** Every Hilbert space of the paper is modelled as `ℓ²` of its basis: the fermionic
Fock space as `Ell2 (Fin n → Fin 2)` (occupation numbers, `1` = occupied) and the bosonic one as
`Ell2 (Fin n → ℕ)`. The `k`-fold tensor power `ℋ^{⊗k}` is `Ell2 (Fin k → ι)`, register `s : Fin k`
being the coordinate `x s`. -/
noncomputable abbrev Ell2 (ι : Type*) := lp (fun _ : ι => ℂ) 2

/-- Membership in `ℓ²` is square-summability. -/
theorem memℓp_two_iff {ι : Type*} (f : ι → ℂ) :
    Memℓp f 2 ↔ Summable (fun i => ‖f i‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  simp

/-- Relabelling the basis along a bijection `e : α ≃ β`: `(reindexVec e f)(a) = f(e a)`. -/
noncomputable def reindexVec {α β : Type*} (e : α ≃ β) (f : Ell2 β) : Ell2 α :=
  ⟨fun a => f (e a), by
    refine (memℓp_two_iff _).2 ?_
    have h : Summable (fun b => ‖f b‖ ^ 2) := (memℓp_two_iff _).1 f.2
    exact (e.summable_iff (f := fun b => ‖f b‖ ^ 2)).2 h⟩

/-- The elementary tensor `u ⊗ v ∈ ℓ²(α × β)`: `(u ⊗ v)(a, b) = u(a) v(b)`. -/
noncomputable def tensorVec {α β : Type*} (u : Ell2 α) (v : Ell2 β) : Ell2 (α × β) :=
  ⟨fun p => u p.1 * v p.2, by
    refine (memℓp_two_iff _).2 ?_
    have hu := (memℓp_two_iff _).1 u.2
    have hv := (memℓp_two_iff _).1 v.2
    simpa [norm_mul, mul_pow] using
      hu.mul_of_nonneg hv (fun _ => by positivity) (fun _ => by positivity)⟩

end GaussTesting


