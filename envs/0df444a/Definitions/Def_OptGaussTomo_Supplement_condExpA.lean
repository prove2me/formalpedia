-- Prove2me | Definitions.Def_OptGaussTomo_Supplement_condExpA
-- name    : OptGaussTomo_Supplement_condExpA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:44:35.40569+00:00
-- url     : https://prove2.me/theorems/a2feb235-5dc1-4393-92ea-32dcf7758d0b
-- title:
--   The map $\mathcal E_{\mathcal A}$ of (E.3) and the amplification $\mathcal I\otimes\Phi$
-- statement:
--   In the set-up (E.1)–(E.2), the map $\mathcal E_{\mathcal A}$ on $B(\mathcal H)$ is
--
--   $$
--   \mathcal E_{\mathcal A}[M]\cong\bigoplus_{\lambda\in\Lambda}\frac{I_{\mathcal L_\lambda}}{\dim\mathcal L_\lambda}\otimes\operatorname{tr}_{\mathcal L_\lambda}[P_\lambda MP_\lambda],
--   $$
--
--   where $P_\lambda$ is the projection onto $\mathcal L_\lambda\otimes\mathcal R_\lambda$. In coordinates, the entry at $(|\lambda,l,r\rangle,|\mu,l',r'\rangle)$ is $0$ unless $\lambda=\mu$ and $l=l'$, and then equals $\frac1{a(\lambda)}\sum_{l''}M_{(\lambda,l'',r),(\lambda,l'',r')}$.
--
--   For a map $\Phi$ on operators of a second tensor factor, $\mathcal I\otimes\Phi$ acts on an operator $N$ on $\ell^2(X\times Y)$ slice by slice: $(\mathcal I\otimes\Phi)[N]_{(x,y),(x',y')}=\Phi(N_{x,x'})_{y,y'}$ with $N_{x,x'}=\big(N_{(x,u),(x',u')}\big)_{u,u'}$; for linear $\Phi$ it sends $|x\rangle\langle x'|\otimes M$ to $|x\rangle\langle x'|\otimes\Phi(M)$.
--
--   $\mathcal E_{\mathcal A}$ is the conditional expectation onto $\mathcal A$; it appears in (E.5) acting on the purifying system.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), App. E.1, eq. (E.3), p.63; Theorem E.1, eq. (E.5), p.63

import Mathlib
import Definitions.Def_OptGaussTomo_Supplement_BlockIdx

namespace OptGaussTomo.Supplement

open Classical in
/-- The map `E_A` of (E.3) (Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal
tomography of bosonic and fermionic Gaussian states*, arXiv:2607.11847, held version,
sha256 0f7548a2…, App. E.1, eq. (E.3), p.63):
`E_A[M] ≅ ⊕_λ (I_{L_λ}/dim L_λ) ⊗ tr_{L_λ}[P_λ M P_λ]`. Entry `(⟨λ,l,r⟩, ⟨μ,l',r'⟩)` is
`0` unless `λ = μ` and `l = l'`, and then `(1/a λ) ∑_{l''} M ⟨λ,l'',r⟩ ⟨λ,l'',r'⟩`.

**Formalization Note.** Fin values in the same block are compared through their natural-number
values, and `Fin.cast` moves an index between the equal types `Fin (b μ)` and `Fin (b λ)` when
`λ = μ`. -/
noncomputable def condExpA {Λ : Type} (a b : Λ → ℕ) (M : Matrix (BlockIdx a b) (BlockIdx a b) ℂ) :
    Matrix (BlockIdx a b) (BlockIdx a b) ℂ :=
  fun x y =>
    if h : x.1 = y.1 then
      (if (x.2.1 : ℕ) = (y.2.1 : ℕ) then
        ((a x.1 : ℂ))⁻¹ * ∑ l : Fin (a x.1),
          M ⟨x.1, (l, x.2.2)⟩ ⟨x.1, (l, Fin.cast (congrArg b h.symm) y.2.2)⟩
      else 0)
    else 0

/-- `I ⊗ Φ`: a map `Φ` on operators of the second factor applied to an operator on `ℓ²(X × Y)`,
slice by slice: `(I ⊗ Φ)[N] (p, q) = Φ(N_{p.1, q.1}) p.2 q.2`, where `N_{x,x'}` is the slice
`(y, y') ↦ N (x, y) (x', y')`. For a linear `Φ` and `N = |x⟩⟨x'| ⊗ M` this is `|x⟩⟨x'| ⊗ Φ(M)`. -/
def applySecond {X Y : Type} (Φ : Matrix Y Y ℂ → Matrix Y Y ℂ) (N : Matrix (X × Y) (X × Y) ℂ) :
    Matrix (X × Y) (X × Y) ℂ :=
  fun p q => Φ (fun i j => N (p.1, i) (q.1, j)) p.2 q.2

end OptGaussTomo.Supplement


