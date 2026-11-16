-- Prove2me | Definitions.Def_OptGaussTomo_Supplement_BlockIdx
-- name    : OptGaussTomo_Supplement_BlockIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:44:01.244617+00:00
-- url     : https://prove2.me/theorems/0a03115a-daad-4d42-8a72-fb21bde740aa
-- title:
--   Block decomposition $\mathcal H\cong\bigoplus_\lambda\mathcal L_\lambda\otimes\mathcal R_\lambda$ and the algebras $\mathcal A$, $\mathcal B$ (E.1)–(E.2)
-- statement:
--   Let $\Lambda$ be a countable index set and $a,b:\Lambda\to\mathbb N$. The Hilbert space
--
--   $$
--   \mathcal H\cong\bigoplus_{\lambda\in\Lambda}\mathcal L_\lambda\otimes\mathcal R_\lambda,\qquad \dim\mathcal L_\lambda=a(\lambda),\ \dim\mathcal R_\lambda=b(\lambda),
--   $$
--
--   is $\ell^2$ of the index set of triples $(\lambda,l,r)$ with $l<a(\lambda)$, $r<b(\lambda)$, labelling the product basis $|\lambda,l,r\rangle$. Inside $B(\mathcal H)$ sit the von Neumann algebras
--
--   $$
--   \mathcal A\cong\bigoplus_{\lambda}I_{\mathcal L_\lambda}\otimes L(\mathcal R_\lambda),\qquad
--   \mathcal B\cong\bigoplus_{\lambda}L(\mathcal L_\lambda)\otimes I_{\mathcal R_\lambda}:
--   $$
--
--   an operator lies in $\mathcal A$ if it is block diagonal in $\lambda$, acts on the block $\lambda$ as $I_{\mathcal L_\lambda}\otimes A_\lambda$, and is bounded (equivalently $\sup_\lambda\|A_\lambda\|<\infty$); likewise for $\mathcal B$ with $B_\lambda\otimes I_{\mathcal R_\lambda}$.
--
--   This is the set-up of Appendix E.1 in which the random purification channel of Theorem E.1 is constructed.
--
--   **Formalization Note** The fixed orthonormal basis of $\mathcal H$ used for the standard purification is the product basis induced by (E.1), the basis the paper's proof works in ((E.9)); in it $\mathcal A$ and $\mathcal B$ are closed under transposes.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), App. E.1, eqs. (E.1)–(E.2), p.63

import Mathlib
import Definitions.Def_OptGaussTomo_Supplement_mulOp

namespace OptGaussTomo.Supplement

/-- The **block decomposition** (E.1) `H ≅ ⊕_{λ∈Λ} L_λ ⊗ R_λ` (Chen, Fanizza, Girardi, Lami,
Mele, Walter, Witteveen, *Optimal tomography of bosonic and fermionic Gaussian states*,
arXiv:2607.11847, held version, sha256 0f7548a2…, App. E.1, eq. (E.1), p.63), with
`dim L_λ = a λ` and `dim R_λ = b λ`. `H` is `ℓ²` of this index type, whose elements
`⟨λ, (l, r)⟩` label the product basis `|λ, l, r⟩` induced by (E.1).

**Formalization Note.** This is the fixed orthonormal basis of `H` (p.62) used for the standard
purification; the proof works in it ("With respect to the bases induced by (E.1)", (E.9), p.64).
For countable `Λ` the index type is countable, so `H` is separable. -/
abbrev BlockIdx {Λ : Type} (a b : Λ → ℕ) : Type := Σ lam : Λ, Fin (a lam) × Fin (b lam)

/-- Membership in the von Neumann algebra `A ≅ ⊕_λ I_{L_λ} ⊗ L(R_λ)` of (E.2), p.63: `M` is
block diagonal in `λ`, acts on block `λ` as `I_{L_λ} ⊗ A_λ`, and is bounded (equivalently
`sup_λ ‖A_λ‖ < ∞`). -/
def InAlgA {Λ : Type} (a b : Λ → ℕ) (M : Matrix (BlockIdx a b) (BlockIdx a b) ℂ) : Prop :=
  (∀ x y : BlockIdx a b, x.1 ≠ y.1 → M x y = 0) ∧
  (∃ A : (lam : Λ) → Matrix (Fin (b lam)) (Fin (b lam)) ℂ,
    ∀ (lam : Λ) (l l' : Fin (a lam)) (r r' : Fin (b lam)),
      M ⟨lam, (l, r)⟩ ⟨lam, (l', r')⟩ = if l = l' then A lam r r' else 0) ∧
  IsBoundedCoeff M

/-- Membership in the von Neumann algebra `B ≅ ⊕_λ L(L_λ) ⊗ I_{R_λ}` of (E.2), p.63: `M` is
block diagonal in `λ`, acts on block `λ` as `B_λ ⊗ I_{R_λ}`, and is bounded. -/
def InAlgB {Λ : Type} (a b : Λ → ℕ) (M : Matrix (BlockIdx a b) (BlockIdx a b) ℂ) : Prop :=
  (∀ x y : BlockIdx a b, x.1 ≠ y.1 → M x y = 0) ∧
  (∃ B : (lam : Λ) → Matrix (Fin (a lam)) (Fin (a lam)) ℂ,
    ∀ (lam : Λ) (l l' : Fin (a lam)) (r r' : Fin (b lam)),
      M ⟨lam, (l, r)⟩ ⟨lam, (l', r')⟩ = if r = r' then B lam l l' else 0) ∧
  IsBoundedCoeff M

end OptGaussTomo.Supplement


