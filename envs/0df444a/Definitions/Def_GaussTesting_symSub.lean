-- Prove2me | Definitions.Def_GaussTesting_symSub
-- name    : GaussTesting_symSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:14.75346+00:00
-- url     : https://prove2.me/theorems/0291a0e3-e3a9-42c7-9c39-c82f17e66575
-- title:
--   The symmetric subspace $\mathrm{Sym}^m(\mathcal H)\subseteq\mathcal H^{\otimes m}$
-- statement:
--   For a permutation $\sigma$ of the $m$ registers, $P_\sigma$ permutes the tensor factors of $\mathcal H^{\otimes m}$: $(P_\sigma f)(x)=f(x\circ\sigma^{-1})$, which moves the content of register $i$ to register $\sigma(i)$. The symmetric subspace is
--
--   $$
--   \mathrm{Sym}^m(\mathcal H)=\{f\in\mathcal H^{\otimes m}: P_\sigma f=f\ \text{for every permutation }\sigma\},
--   $$
--
--   a closed subspace; its orthogonal projector is the paper's $\Pi^{(1,\dots,m)}_{\mathrm{sym}}$.
--
--   **Formalization Note** The set above is already closed; the Lean definition packages it as a `ClosedSubmodule` by taking its closure, which adds no vector.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), §2 (Multilinear algebra), p.12; Definition 3.1, p.21

import Definitions.Def_GaussTesting_Ell2

namespace GaussTesting

/-- The register permutation `P_σ` on `ℋ^{⊗m}`: `(P_σ f)(x) = f(x ∘ σ⁻¹)`, which moves the content of
register `i` to register `σ i`. -/
noncomputable def permVec {ι : Type*} {m : ℕ} (σ : Equiv.Perm (Fin m)) (f : Ell2 (Fin m → ι)) :
    Ell2 (Fin m → ι) :=
  reindexVec (Equiv.arrowCongr σ (Equiv.refl ι)) f

theorem permVec_apply {ι : Type*} {m : ℕ} (σ : Equiv.Perm (Fin m)) (f : Ell2 (Fin m → ι))
    (x : Fin m → ι) : permVec σ f x = f (fun i => x (σ.symm i)) := rfl

/-- The symmetric subspace `Sym^m(ℋ) ⊆ ℋ^{⊗m}`: the vectors fixed by every register permutation.
Its orthogonal projection (`proj (symSub ι m)`) is the paper's `Π^{(1,…,m)}_sym`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), §2 "Multilinear algebra", p.12 (`Sym^k(V) ⊆ V^{⊗k}`), Definition 3.1, p.21
(`Π^{(1,…,m)}_sym` is the projector onto `Sym^m(ℋ) ⊆ ℋ^{⊗m}`).

**Formalization Note.** The set `{f | ∀ σ, P_σ f = f}` is a closed linear subspace (each `P_σ` is an
isometry); `Submodule.closure` only packages it as a `ClosedSubmodule` and adds no vector. -/
noncomputable def symSub (ι : Type*) (m : ℕ) : ClosedSubmodule ℂ (Ell2 (Fin m → ι)) :=
  Submodule.closure
    { carrier := {f | ∀ σ : Equiv.Perm (Fin m), permVec σ f = f}
      add_mem' := by
        intro f g hf hg σ
        ext x
        simp only [permVec_apply, lp.coeFn_add, Pi.add_apply]
        rw [← permVec_apply, ← permVec_apply, hf σ, hg σ]
      zero_mem' := by intro σ; ext x; simp [permVec_apply]
      smul_mem' := by
        intro c f hf σ
        ext x
        simp only [permVec_apply, lp.coeFn_smul, Pi.smul_apply]
        rw [← permVec_apply, hf σ] }

end GaussTesting


