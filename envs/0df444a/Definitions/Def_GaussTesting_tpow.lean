-- Prove2me | Definitions.Def_GaussTesting_tpow
-- name    : GaussTesting_tpow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:13.72687+00:00
-- url     : https://prove2.me/theorems/a4b97b6c-84bc-4b16-ae6d-daba98d40b47
-- title:
--   Tensor power $|\psi\rangle^{\otimes k}$
-- statement:
--   For a vector $|\psi\rangle\in\mathcal H=\ell^2(\iota)$ and $k\in\mathbb N$, the tensor power $|\psi\rangle^{\otimes k}\in\mathcal H^{\otimes k}=\ell^2(\iota^k)$ has coefficients
--
--   $$
--   \langle x_1,\dots,x_k|\psi^{\otimes k}\rangle=\prod_{j=1}^k\psi(x_j).
--   $$
--
--   These are the inputs of every $k$-copy test in the mission ($|\psi\rangle^{\otimes t}$ in Definition 1.2, $\psi^{\otimes k}$ in §3).
--
--   **Formalization Note** Registers are indexed by `Fin k`; the module proves that the coefficients are square-summable.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Definition 1.2, p.4; §3, p.21

import Definitions.Def_GaussTesting_Ell2

namespace GaussTesting

/-- Helper: the coefficients of `ψ^{⊗k}` are square-summable. -/
theorem summable_prod_sq {ι : Type*} (ψ : Ell2 ι) :
    ∀ k : ℕ, Summable (fun x : Fin k → ι => ∏ j, ‖ψ (x j)‖ ^ 2)
  | 0 => by simpa using (summable_of_hasFiniteSupport (Set.toFinite _) :
      Summable (fun _ : Fin 0 → ι => (1 : ℝ)))
  | k + 1 => by
    have h1 := (memℓp_two_iff _).1 ψ.2
    have h2 := summable_prod_sq ψ k
    have h3 := h1.mul_of_nonneg h2 (fun _ => by positivity)
      (fun _ => Finset.prod_nonneg (fun _ _ => by positivity))
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => ι)).summable_iff]
    convert h3 using 1
    ext p
    simp [Fin.prod_univ_succ, Fin.consEquiv]

/-- The tensor power `|ψ⟩^{⊗k} ∈ ℋ^{⊗k}`: `(ψ^{⊗k})(x₀, …, x_{k−1}) = ψ(x₀) ⋯ ψ(x_{k−1})`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Definition 1.2, p.4 (`|ψ⟩^{⊗t}`), §3, p.21 (`ψ^{⊗k}`).

**Formalization Note.** `ℋ^{⊗k}` is `ℓ²(Fin k → ι)` (see `Ell2`); register `j` of the tensor power is
the coordinate `x j`. `tpow 0 ψ` is the constant `1` on the one-point type `Fin 0 → ι`. -/
noncomputable def tpow {ι : Type*} (k : ℕ) (ψ : Ell2 ι) : Ell2 (Fin k → ι) :=
  ⟨fun x => ∏ j, ψ (x j), by
    refine (memℓp_two_iff _).2 ?_
    simpa [norm_prod, Finset.prod_pow] using summable_prod_sq ψ k⟩

end GaussTesting


