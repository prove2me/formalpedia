-- Prove2me | Definitions.Def_OptGaussTomo_Supplement_purifBlock
-- name    : OptGaussTomo_Supplement_purifBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:46:00.837738+00:00
-- url     : https://prove2.me/theorems/26e05697-c592-4579-abfb-e6f7e6190105
-- title:
--   The $\lambda$-th summand of the explicit formula (E.6)
-- statement:
--   In the set-up (E.1)–(E.2), let $|\Gamma\rangle_{\mathcal R_\lambda\tilde{\mathcal R}_\lambda}=\sum_r|r\rangle\otimes|\tilde r\rangle$ be the unnormalized maximally entangled vector. For an operator $\rho$ on $\mathcal H$, the $\lambda$-th summand of (E.6) is
--
--   $$
--   \operatorname{tr}_{\mathcal R_\lambda}[P_\lambda\rho P_\lambda]\otimes\frac{I_{\tilde{\mathcal L}_\lambda}}{\dim\mathcal L_\lambda}\otimes\frac{|\Gamma\rangle\langle\Gamma|_{\mathcal R_\lambda\tilde{\mathcal R}_\lambda}}{\dim\mathcal R_\lambda},
--   $$
--
--   placed in the block $(\mathcal L_\lambda\otimes\mathcal R_\lambda)\otimes(\tilde{\mathcal L}_\lambda\otimes\tilde{\mathcal R}_\lambda)$ of $\mathcal H\otimes\tilde{\mathcal H}$. Its entry at $\big((\lambda,l,r),(\lambda,\tilde l,\tilde r)\big),\big((\lambda,l',r'),(\lambda,\tilde l',\tilde r')\big)$ is
--
--   $$
--   \Big(\sum_s\rho_{(\lambda,l,s),(\lambda,l',s)}\Big)\cdot\frac{[\tilde l=\tilde l']}{a(\lambda)}\cdot\frac{[r=\tilde r]\,[r'=\tilde r']}{b(\lambda)},
--   $$
--
--   and all entries outside the block vanish. Summing over $\lambda$ gives the random purification channel $\mathcal P_{\mathcal A}$.
--
--   **Formalization Note** The identification $\cong$ in (E.6) reorders $\mathcal L_\lambda\otimes\tilde{\mathcal L}_\lambda\otimes\mathcal R_\lambda\otimes\tilde{\mathcal R}_\lambda$ into $(\mathcal L_\lambda\otimes\mathcal R_\lambda)\otimes(\tilde{\mathcal L}_\lambda\otimes\tilde{\mathcal R}_\lambda)$; the entry formula is that reordering.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Theorem E.1, eq. (E.6), p.63

import Mathlib
import Definitions.Def_OptGaussTomo_Supplement_BlockIdx

namespace OptGaussTomo.Supplement

open Classical in
/-- The `λ`-th summand of (E.6) (Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen,
*Optimal tomography of bosonic and fermionic Gaussian states*, arXiv:2607.11847, held version,
sha256 0f7548a2…, Theorem E.1, eq. (E.6), p.63):
`tr_{R_λ}[P_λ ρ P_λ] ⊗ I_{L̃_λ}/dim L_λ ⊗ |Γ⟩⟨Γ|_{R_λ R̃_λ}/dim R_λ`, placed in the block
`(L_λ ⊗ R_λ) ⊗ (L̃_λ ⊗ R̃_λ)` of `H ⊗ H̃ = ℓ²(X × X)`, where `|Γ⟩ = ∑_r |r⟩ ⊗ |r̃⟩`.
At `p = (⟨λ,l,r⟩, ⟨λ,l̃,r̃⟩)`, `q = (⟨λ,l',r'⟩, ⟨λ,l̃',r̃'⟩)` the entry is
`(∑_s ρ⟨λ,l,s⟩⟨λ,l',s⟩) · [l̃ = l̃']/a λ · [r = r̃][r' = r̃']/b λ`, and entries outside the block
are `0`.

**Formalization Note.** The identification `≅` of (E.6) reorders `L_λ ⊗ L̃_λ ⊗ R_λ ⊗ R̃_λ` into
`(L_λ ⊗ R_λ) ⊗ (L̃_λ ⊗ R̃_λ)`; the entry formula above is that reordering. Fin values in one block
are compared through their natural-number values. -/
noncomputable def purifBlock {Λ : Type} (a b : Λ → ℕ)
    (ρ : Matrix (BlockIdx a b) (BlockIdx a b) ℂ) (lam : Λ) :
    Matrix (BlockIdx a b × BlockIdx a b) (BlockIdx a b × BlockIdx a b) ℂ :=
  fun p q =>
    if h : p.1.1 = lam ∧ p.2.1 = lam ∧ q.1.1 = lam ∧ q.2.1 = lam then
      (∑ s : Fin (b lam),
          ρ ⟨lam, (Fin.cast (congrArg a h.1) p.1.2.1, s)⟩
            ⟨lam, (Fin.cast (congrArg a h.2.2.1) q.1.2.1, s)⟩)
        * ((if (p.2.2.1 : ℕ) = (q.2.2.1 : ℕ) then 1 else 0) / (a lam : ℂ))
        * ((if (p.1.2.2 : ℕ) = (p.2.2.2 : ℕ) then 1 else 0)
            * (if (q.1.2.2 : ℕ) = (q.2.2.2 : ℕ) then 1 else 0) / (b lam : ℂ))
    else 0

end OptGaussTomo.Supplement


