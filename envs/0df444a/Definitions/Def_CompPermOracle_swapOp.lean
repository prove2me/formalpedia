-- Prove2me | Definitions.Def_CompPermOracle_swapOp
-- name    : CompPermOracle_swapOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:06.373163+00:00
-- url     : https://prove2.me/theorems/4032d361-328b-4f17-9cbd-87e4b91d6a26
-- title:
--   Swap oracles $\tilde O_\varphi$, projectors $Q_{x,y}$, purified queries $P_x$, $P^{-1}_y$ and $|S_N\rangle$
-- statement:
--   Let $\mathcal A=\mathcal H([N]\cup\{\bot\})$ be the answer register. For $z\in[N]$, $S_z$ is the unitary on $\mathcal A$ that swaps $|\bot\rangle$ and $|z\rangle$ and fixes every other basis state. For $\varphi\in S_N$ the **swap oracles** are
--   $$
--   \tilde O_\varphi=\sum_{x}|x\rangle\langle x|\otimes S_{\varphi(x)},\qquad \tilde O_{\varphi^{-1}}=\sum_{x}|x\rangle\langle x|\otimes S_{\varphi^{-1}(x)}.
--   $$
--   On the permutation register $\mathcal P=\mathcal H(S_N)$, the assertion projector is $Q_{x,y}=\sum_{\varphi(x)=y}|\varphi\rangle\langle\varphi|$. The **purified queries** on $\mathcal A\otimes\mathcal P$ are
--   $$
--   P_x=\sum_y S_y\otimes Q_{x,y},\qquad P^{-1}_y=\sum_x S_x\otimes Q_{x,y},
--   $$
--   with coherently controlled versions $P=\sum_x|x\rangle\langle x|\otimes P_x$ and $P^{-1}=\sum_y|y\rangle\langle y|\otimes P^{-1}_y$. The uniform state is $|S_N\rangle=(N!)^{-1/2}\sum_\varphi|\varphi\rangle$.
--
--   These operators describe the random permutation model and its purification.
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Definitions 3.1, 3.2 and Remark 3.3, p.6

import Mathlib
import Definitions.Def_CompPermOracle_opTensor

namespace CompPermOracle

/-- The extended answer alphabet `[N] ∪ {⊥}`, with `⊥ = none` (Carolan, Majenz, arXiv:2609.28469
(version of 2026-11-03, sha256 52ebc507…), §3.1, p.6). -/
abbrev Ans (N : ℕ) := Option (Fin N)

/-- `S_z`, the unitary on `𝒜 = ℋ([N] ∪ {⊥})` which swaps `|⊥⟩` and `|z⟩` and fixes every other
computational-basis state (arXiv:2609.28469, §3.1, p.6). -/
noncomputable def swapOp {N : ℕ} (z : Fin N) : Hil (Ans N) →L[ℂ] Hil (Ans N) :=
  ∑ a : Ans N, ketBra (ket (Equiv.swap none (some z) a)) (ket a)

/-- The forward swap oracle `Õ_φ = ∑_x |x⟩⟨x| ⊗ S_{φ(x)}` (arXiv:2609.28469, Definition 3.1, eq. (2),
p.6). -/
noncomputable def swapOracle {N : ℕ} (φ : Equiv.Perm (Fin N)) :
    Hil (Fin N × Ans N) →L[ℂ] Hil (Fin N × Ans N) :=
  controlled fun x => swapOp (φ x)

/-- The inverse swap oracle `Õ_{φ⁻¹} = ∑_x |x⟩⟨x| ⊗ S_{φ⁻¹(x)}` (arXiv:2609.28469, Definition 3.1,
eq. (2), p.6). -/
noncomputable def swapOracleInv {N : ℕ} (φ : Equiv.Perm (Fin N)) :
    Hil (Fin N × Ans N) →L[ℂ] Hil (Fin N × Ans N) :=
  controlled fun x => swapOp (φ⁻¹ x)

/-- The assertion projector `Q_{x,y} = ∑_{φ(x)=y} |φ⟩⟨φ|` on `𝒫 = ℋ(S_N)` (arXiv:2609.28469,
Definition 3.2, eq. (3), p.6). -/
noncomputable def assertP {N : ℕ} (x y : Fin N) :
    Hil (Equiv.Perm (Fin N)) →L[ℂ] Hil (Equiv.Perm (Fin N)) :=
  ∑ φ ∈ Finset.univ.filter (fun φ : Equiv.Perm (Fin N) => φ x = y), ketBra (ket φ) (ket φ)

/-- The purified forward query `P_x = ∑_y S_y ⊗ Q_{x,y}` (arXiv:2609.28469, eq. (3), p.6). -/
noncomputable def purP {N : ℕ} (x : Fin N) :
    Hil (Ans N × Equiv.Perm (Fin N)) →L[ℂ] Hil (Ans N × Equiv.Perm (Fin N)) :=
  ∑ y : Fin N, opTensor (swapOp y) (assertP x y)

/-- The purified inverse query `P⁻¹_y = ∑_x S_x ⊗ Q_{x,y}` (arXiv:2609.28469, eq. (3), p.6). -/
noncomputable def purPInv {N : ℕ} (y : Fin N) :
    Hil (Ans N × Equiv.Perm (Fin N)) →L[ℂ] Hil (Ans N × Equiv.Perm (Fin N)) :=
  ∑ x : Fin N, opTensor (swapOp x) (assertP x y)

/-- The coherently controlled purified forward query `P = ∑_x |x⟩⟨x| ⊗ P_x` (arXiv:2609.28469,
p.6). -/
noncomputable def purPCtl {N : ℕ} :
    Hil (Fin N × (Ans N × Equiv.Perm (Fin N))) →L[ℂ] Hil (Fin N × (Ans N × Equiv.Perm (Fin N))) :=
  controlled purP

/-- The coherently controlled purified inverse query `P⁻¹ = ∑_y |y⟩⟨y| ⊗ P⁻¹_y` (arXiv:2609.28469,
p.6). -/
noncomputable def purPInvCtl {N : ℕ} :
    Hil (Fin N × (Ans N × Equiv.Perm (Fin N))) →L[ℂ] Hil (Fin N × (Ans N × Equiv.Perm (Fin N))) :=
  controlled purPInv

/-- The uniform state `|S_N⟩ = (N!)^{-1/2} ∑_φ |φ⟩` on `𝒫` (arXiv:2609.28469, Remark 3.3, p.6). -/
noncomputable def uniformPerm (N : ℕ) : Hil (Equiv.Perm (Fin N)) :=
  ((Real.sqrt (N.factorial : ℝ))⁻¹ : ℂ) • ∑ φ : Equiv.Perm (Fin N), ket φ

end CompPermOracle


