-- Prove2me | Definitions.Def_EntangledPIR_CopyB
-- name    : EntangledPIR_CopyB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:45.94643+00:00
-- url     : https://prove2.me/theorems/adfc319b-8945-484e-939f-92ed576419bf
-- title:
--   Registers of the $k\ell$ copies
-- statement:
--   Copy $(i,j)\in[k]\times[\ell]$ is a register $\mathsf B_{i,j}=\mathsf P'_{i,j}\otimes\mathsf E_{i,j}$, with $\mathsf P'_{i,j}$ of $d$ qubits, and $\mathsf B$ denotes all copies. The block $|t\rangle\langle t|\otimes\Theta$ on $\mathsf T\otimes\mathsf X$ is also defined here, for classical-quantum operators.
--
--   **Formalization Note** A product of operators on different copies is the published `ICSCompute.piTensor`, $\bigotimes_c O_c$ with entries $\prod_c O_c(p_c,q_c)$. Since such operators commute, all the products of §3 are of this form, with $O_c=1$ on untouched copies.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), §3, p.12

import Definitions.Def_EntangledPIR_Bits
import Definitions.Def_ICSCompute_piTensor

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), §3,
p.12: a register for each copy. Products of operators on different copies are the published
`ICSCompute.piTensor`, `⊗_c O_c` with entries `∏_c O_c(p_c, q_c)`.
-/

open Matrix

namespace EntangledPIR

/-- **Copy registers**, p.12: copy `(i, j)` is `B_{i,j} = P′_{i,j} ⊗ E_{i,j}`, with `P′_{i,j}` of
`d` qubits and a finite remainder `E_{i,j}`, for `(i, j) ∈ [k] × [ℓ]`. -/
abbrev CopyB {k ℓ : ℕ} (d : ℕ) (E : Fin k × Fin ℓ → Type) (c : Fin k × Fin ℓ) : Type :=
  Bits d × E c

/-- `B`, the registers of all `kℓ` copies, p.12. A basis state has one basis state per copy. -/
abbrev AllB {k ℓ : ℕ} (d : ℕ) (E : Fin k × Fin ℓ → Type) : Type :=
  (c : Fin k × Fin ℓ) → CopyB d E c

instance {k ℓ d : ℕ} (E : Fin k × Fin ℓ → Type) [∀ c, DecidableEq (E c)] :
    DecidableEq (AllB d E) :=
  fun a b => Fintype.decidablePiFintype a b

/-- The block `|t⟩⟨t|_T ⊗ Θ` on `T ⊗ X`, also used for block-diagonal
classical-quantum states. -/
def classicalBlock {T X : Type} [DecidableEq T] (t : T) (Θ : Matrix X X ℂ) :
    Matrix (T × X) (T × X) ℂ :=
  Matrix.of fun p q => if p.1 = t ∧ q.1 = t then Θ p.2 q.2 else 0

end EntangledPIR


